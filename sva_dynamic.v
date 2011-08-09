(* Compcert imports *)
Add LoadPath "./CompCert-Toolkit".
Require Import Maps.
Require Import Smallstep.
Require Import Integers.
Require Import Coqlib.
Require Import Globalenvs.
Require Import Events.
Require Import Memory.
Require Import AST.

(* Sva imports *)
Require Import sva_ast.
Require Import sva_allocator.

(* Coq standard library imports *)
Require Import ProofIrrelevance.
Require Import ListSet.

(* We could have formalized ES as the paper does as exp + stmt, but sums
 * are inconvenient to work with and the expression state and statement
 * state are really used in two different ways. 
 *
 * Removed char as primitive types and addr operations as they are not
 * crucial to the formalism.
 *
 * Notes : 1) Lots of HACKS currently marked by comments. 
 *         2) Probably should create a designated Error state.
 *)

(* Modeling the RegionStore *)
Module Int32Indexed.
Definition t := int.
Definition index (n : int) : positive :=
  match (Int.unsigned n) with
  | Z0 => xH
  | Zpos p => xO p
  | Zneg p => xI p
  end.
Lemma index_inj : forall (x y : int),
  index x = index y ->
  x = y.
Proof.
  unfold index. unfold Int.unsigned. intros x y H.
  destruct x as [x1 Px]. destruct y as [y1 Py]. simpl in H. 
  destruct x1; destruct y1; intros; 
  try discriminate; try generalize (proof_irrelevance _ Px Py); 
  try intros; try rewrite -> H0; try rewrite -> H; try reflexivity. inversion H.
  subst p. generalize(proof_irrelevance _ Px Py). intros. rewrite -> H0. reflexivity.
  inversion H. reflexivity.
Qed.
Definition eq := Int.eq_dec.
End Int32Indexed.

Module I32Map := IMap(Int32Indexed).

(* Environments for operational semantics *)

Definition VarEnv := PTree.t value. (* var -> value *)
Definition RegionStore := set Z. (* ListSet of blocks *)
Definition FreeList := list Values.block.
Record RegionInfo : Type := mk_region {
  F : FreeList;
  RS : RegionStore
}.
Definition LiveRegions := PTree.t RegionInfo. (* nodevar -> RegionInfo *)

(* Abstract machine states *)

Record State_exp : Type := state_e {
  Venv_exp : VarEnv;  
  L_exp : LiveRegions;  
  E_exp : exp;
  H_exp : sva_heap
}.

Record State_stmt : Type := state_s {
  Venv_stmt : VarEnv;
  L_stmt : LiveRegions;
  S_stmt : stmt;
  H_stmt : sva_heap
}.

(* Some function definitions *)

Definition update (l : LiveRegions) (b : Values.block) (ofs : int) (v : value) 
                  (h : sva_heap) : sva_heap :=
  match PTree.fold (fun cont rho ri =>
    match cont with
    | None =>
        if set_mem Z_eq_dec b (RS ri) 
        then Some (sva_store h b ofs Mint32 v)
        else None
    | Some h' => Some h'
    end
  ) l None with
  | None => h
  | Some h' => h'
  end.

(* Small-step relations for dynamic checks *)
Reserved Notation " e '==>e' e' " (at level 40).
Reserved Notation " s '==>s' s' " (at level 40).

Inductive stmt_step : (Genv.t nat nat) -> State_stmt -> trace -> State_stmt -> Prop :=
  | R1 : forall venv l s1 s2 venv' l' s1' h,
      state_s venv l s1 h ==>s state_s venv' l' s1' h ->
      state_s venv l (Seq s1 s2) h ==>s state_s venv' l' (Seq s1' s2) h
  | R1seq : forall venv l s2 h,
      state_s venv l (Seq Epsilon s2) h ==>s state_s venv l s2 h
  | R2 : forall venv l e x venv' l' e' h,
      state_e venv l e h ==>e state_e venv' l' e' h ->
      state_s venv l (Assign x e) h ==>s state_s venv' l' (Assign x e') h
  | R3 : forall venv l x v h,
      value_v v ->
      state_s venv l (Assign x (Val v)) h ==>s 
      state_s (PTree.set x v venv) l Epsilon h
  | R4 : forall venv l e1 e2 venv' l' e1' h,
      state_e venv l e1 h ==>e venv' l' e1' h ->
      state_s venv l (Store e1 e2) h ==>s state_s venv l' (Store e1' e2) h
  | R5 : forall venv l e v venv' l' e' h,
      value_v v ->
      state_e venv l e h ==>e state_e venv' l' e' h ->
      state_s venv l (Store (Val v) e) h ==>s state_s venv' l' (Store (Val v) e') h
  (* R6 changed from v1 != Uninit to v1 = Pointer *)
  | R6 : forall venv l v1 v2 b o h,
      value_v v1 ->
      v1 = Pointer b o ->
      value_v v2 ->
      state_s venv l (Store (Val v2) (Val v1)) h ==>s 
      state_s venv l Epsilon (update l b o v2 h)
  | R6error : forall venv l v1 v2 rho h n b,
      value_v v1 ->
      v1 = Uninit \/ v1 = Region rho \/ v1 = Int n \/ v1 = Byte b ->
      value_v v2 ->
      state_s venv l (Store (Val v2) (Val v1)) h ==>s state_s venv l ErrorStmt h
  | R7 : forall venv l e1 e2 e3 venv' l' e1' h,
      state_e venv l e1 h ==>e state_e venv' l' e1' h ->
      state_s venv l (StoreToU e1 e2 e3) h ==>s 
      state_s venv' l' (StoreToU e1' e2 e3) h
  | R8 : forall venv l v1 e2 e3 venv' l' e2' h,
      value_v v1 ->
      state_e venv l e2 h ==>e state_e venv' l' e2' h ->
      state_s venv l (StoreToU (Val v1) e2 e3) h ==>s 
      state_s venv' l' (StoreToU (Val v1) e2' e3) h
  | R9 : forall venv l v1 v2 e3 venv' l' e3' h,
      value_v v1 ->
      value_v v2 ->
      state_e venv l e3 h ==>e state_e venv' l' e3' h ->
      state_s venv l (StoreToU (Val v1) (Val v2) e3) h ==>s 
      state_s venv' l' (StoreToU (Val v1) (Val v2) e3') h
  | R10 : forall venv l b o rho v1 v2 ri foo h,
      value_v v1 ->
      v1 = Pointer b o ->
      value_v v2 ->
      PTree.get rho l = Some ri ->
      set_In b (RS ri) ->
      sva_load h b o Mint32 = Some foo ->
      state_s venv l (StoreToU (Val (Region rho)) (Val v2) (Val v1)) h ==>s
      state_s venv l Epsilon (update l b o v2 h)
  | R10error : forall venv l b o rho v1 v2 ri h,
      value_v v1 ->
      v1 = Pointer b o ->
      value_v v2 ->
      PTree.get rho l = Some ri ->
      set_In b (RS ri) ->
      sva_load h b o Mint32 = None ->
      state_s venv l (StoreToU (Val (Region rho)) (Val v2) (Val v1)) h ==>s
      state_s venv l ErrorStmt h
  | R12 : forall venv l e1 e2 venv' l' e1' h,
      state_e venv l e1 h ==>e state_e venv' l' e1' h ->
      state_s venv l (PoolFree e1 e2) h ==>s state_s venv' l' (PoolFree e1' e2) h
  | R13 : forall venv l v e2 venv' l' e2' h,
      value_v v ->
      state_e venv l e2 h ==>e state_e venv' l' e2' h ->
      state_s venv l (PoolFree (Val v) e2) h ==>s 
      state_s venv' l' (PoolFree (Val v) e2') h
  (* R14 changed from v1 != Uninit to v1 = Pointer *)
  | R14 : forall venv l v b o rho ri h,
      value_v v ->
      v = Pointer b o ->
      PTree.get rho l = Some ri ->
      state_s venv l (PoolFree (Val (Region rho)) (Val v)) h ==>s 
      state_s venv (PTree.set rho (mk_region (b::(F ri)) (RS ri)) l) Epsilon h
  | R14error : forall venv l v n b rho rho' ri h,
      value_v v ->
      v = Uninit \/ v = Region rho' \/ v = Int n \/ v = Byte b ->
      PTree.get rho l = Some ri ->
      state_s venv l (PoolFree (Val (Region rho)) (Val v)) h ==>s 
      state_s venv l ErrorStmt h
  | R15 : forall venv l rho tau x s h,
      PTree.get rho l = None ->
      state_s venv l (PoolInit rho tau x s) h ==>s 
      state_s (PTree.set x (Region rho) venv) 
              (PTree.set rho (mk_region nil (empty_set Z)) l) 
              (PoolPop s rho) 
              h
  | R16 : forall venv l s venv' l' s' rho h,
      state_s venv l s h ==>s state_s venv' l' s' h ->
      state_s venv l (PoolPop s rho) h ==>s state_s venv' l' (PoolPop s' rho) h
  | R17 : forall venv l rho h,
      state_s venv l (PoolPop Epsilon rho) h ==>s
      state_s venv (PTree.remove rho l) Epsilon h
where " s '==>s' s' " := (stmt_step (Genv.empty_genv nat nat) s nil s')

with stmt_exp : (Genv.t nat nat) -> State_exp -> trace -> State_exp -> Prop :=
  | R18 : forall venv x v l h,
      PTree.get x venv = Some v ->
      state_e venv l (Var x) h ==>e state_e venv l (Val v) h
  | R19 : forall venv l e1 e2 op venv' l' e1' h,
      state_e venv l e1 h ==>e state_e venv' l' e1' h ->
      state_e venv l (Binop e1 op e2) h ==>e state_e venv' l' (Binop e1' op e2) h
  | R20 : forall venv l v e2 op venv' l' e2' h,
      value_v v ->
      state_e venv l e2 h ==>e state_e venv' l' e2' h ->
      state_e venv l (Binop (Val v) op e2) h ==>e 
      state_e venv' l' (Binop (Val v) op e2') h
  (* Should probably also add one for pointer ops ... *)
  | R21 : forall venv l v1 v2 op n1 n2 h,
      value_v v1 ->
      v1 = Int n1 ->
      value_v v2 ->
      v2 = Int n2 ->
      (* warning ... this is a hack, but we don't need to do a computation *)
      state_e venv l (Binop (Val v1) op (Val v2)) h ==>e state_e venv l (Val v1) h
  | R22 : forall venv l e venv' l' e' h,
      state_e venv l e h ==>e state_e venv' l' e' h ->
      state_e venv l (Load e) h ==>e state_e venv' l' (Load e') h
  (* changed R23 from v != unint to v = Pointer *)
  | R23 : forall venv l v v' b o h,
      value_v v ->
      v = Pointer b o ->
      sva_load h b o Mint32 = Some v' ->
      state_e venv l (Load (Val v)) h ==>e state_e venv l (Val v') h 
  | R23error : forall venv l v rho b n h,
      value_v v ->
      v = Uninit \/ v = Region rho \/ v = Int n \/ v = Byte b ->
      state_e venv l (Load (Val v)) h ==>e state_e venv l ErrorExp h
  | R24 : forall venv l e1 e2 venv' l' e1' h,
      state_e venv l e1 h ==>e state_e venv' l' e1' h ->
      state_e venv l (LoadFromU e1 e2) h ==>e state_e venv l (LoadFromU e1' e2) h
  | R25 : forall venv l v e2 venv' l' e2' h,
      value_v v ->
      state_e venv l e2 h ==>e state_e venv' l' e2' h ->
      state_e venv l (LoadFromU (Val v) e2) h ==>e 
      state_e venv l (LoadFromU (Val v) e2') h
  | R26 : forall venv l rho v v' b o ri h,
      value_v v ->
      v = Pointer b o ->
      PTree.get rho l = Some ri ->
      set_In b (RS ri) ->
      sva_load h b o Mint32 = Some v' ->
      state_e venv l (LoadFromU (Val (Region rho)) (Val v)) h ==>e
      state_e venv l (Val v') h
  | R26error : forall venv l rho v b o ri h,
      value_v v ->
      v = Pointer b o ->
      PTree.get rho l = Some ri ->
      set_In b (RS ri) ->
      sva_load h b o Mint32 = None ->
      state_e venv l (LoadFromU (Val (Region rho)) (Val v)) h ==>e
      state_e venv l ErrorExp h
  | R28 : forall venv l e tau h,
      state_e venv l (Cast e tau) h ==>e state_e venv l e h
  | R29 : forall venv l e1 e2 venv' l' e1' tau h,
      state_e venv l e1 h ==>e state_e venv' l' e1' h ->
      state_e venv l (CastI2Ptr e1 e2 tau) h ==>e 
      state_e venv' l' (CastI2Ptr e1' e2 tau) h
  | R30 : forall venv l v e venv' l' e' tau h,
      value_v v ->
      state_e venv l e h ==>e state_e venv' l' e' h ->
      state_e venv l (CastI2Ptr (Val v) e tau) h ==>e 
      state_e venv' l' (CastI2Ptr (Val v) e' tau) h
  | R31 : forall venv l rho v n ri tau h,
      value_v v ->
      v = Int n ->
      PTree.get rho l = Some ri ->
      set_In (Int.unsigned n) (RS ri) ->
      state_e venv l (CastI2Ptr (Val (Region rho)) (Val v) tau) h ==>e 
      state_e venv l (Val v) h
  | R31error : forall venv l rho v n ri tau h,
      value_v v ->
      v = Int n ->
      PTree.get rho l = Some ri ->
      not (set_In (Int.unsigned n) (RS ri)) ->
      state_e venv l (CastI2Ptr (Val (Region rho)) (Val v) tau) h ==>e 
      state_e venv l ErrorExp h
  | R32 : forall venv l e1 e2 venv' l' e1' h,
      state_e venv l e1 h ==>e state_e venv l' e1' h ->
      state_e venv l (PoolAlloc e1 e2) h ==>e state_e venv' l' (PoolAlloc e1' e2) h
  | R33 : forall venv l v e2 venv' l' e2' h,
      value_v v ->
      state_e venv l e2 h ==>e state_e venv l' e2' h ->
      state_e venv l (PoolAlloc (Val v) e2) h ==>e 
      state_e venv' l' (PoolAlloc (Val v) e2') h
  | R34 : forall venv l rho b f ri v h,
      value_v v ->
      v = Int Int.one ->
      PTree.get rho l = Some ri ->
      (F ri) = b::f ->
      state_e venv l (PoolAlloc (Val (Region rho)) (Val v)) h ==>e
      state_e venv (PTree.set rho (mk_region f (RS ri)) l) (Val (Pointer b Int.zero)) h
  | R35 : forall venv l rho ri v h h' b,
      value_v v ->
      v = Int Int.one ->
      PTree.get rho l = Some ri ->
      (F ri) = nil ->
      sva_alloc h 1 = (h',b) ->
      state_e venv l (PoolAlloc (Val (Region rho)) (Val v)) h ==>e
      state_e venv 
              (PTree.set rho (mk_region nil (set_add Z_eq_dec b (RS ri))) l) 
              (Val (Pointer b Int.zero)) 
              h'
  | R36 : forall venv l rho n ri v h h' b,
      value_v v ->
      v = Int n ->
      PTree.get rho l = Some ri ->
      sva_alloc h (Int.unsigned n) = (h',b) ->
      state_e venv l (PoolAlloc (Val (Region rho)) (Val v)) h ==>e
      state_e venv l (Val (Pointer b Int.zero)) h
  (* removed addr operations for now ... *)
where " e '==>e' e' " := (stmt_exp (Genv.empty_genv nat nat) e nil e').