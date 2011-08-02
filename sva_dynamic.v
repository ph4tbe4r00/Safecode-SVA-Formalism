(* Compcert imports *)
Add LoadPath "./CompCert-Toolkit".
Require Import Maps.
Require Import Smallstep.
Require Import Integers.
Require Import Coqlib.
Require Import Globalenvs.
Require Import Events.

(* Sva imports *)
Require Import sva_ast.
Require Import sva_allocator.

(* Coq standard library imports *)
Require Import ProofIrrelevance.

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
Definition RegionStore := I32Map.t (option value). (* int (addresses) -> option value *)
Record RegionInfo : Type := mk_region {
  A : Allocator;
  RS : RegionStore
}.
Definition LiveRegions := PTree.t RegionInfo. (* nodevar -> RegionInfo *)

(* Abstract machine states *)
Record State_exp : Type := state_e {
  VEnv_exp : VarEnv;
  L_exp : LiveRegions;
  ES_exp : exp (* expression *)
}.

Record State_stmt : Type := state_s {
  VEnv_stmt : VarEnv;
  L_stmt : LiveRegions;
  ES_stmt : stmt (* statement *)
}.

(* Some function definitions *)

Definition byte1 (n : int) : byte :=
  Byte.repr (Int.unsigned (Int.shr n (Int.repr 24))).
Definition byte2 (n : int) : byte :=
  Byte.repr (Int.unsigned (Int.shr (Int.shl n (Int.repr 8)) (Int.repr 24))).
Definition byte3 (n : int) : byte :=
  Byte.repr (Int.unsigned (Int.shr (Int.shl n (Int.repr 16)) (Int.repr 24))).
Definition byte4 (n : int) : byte :=
  Byte.repr (Int.unsigned (Int.shr (Int.shl n (Int.repr 24)) (Int.repr 24))).

Definition off1 (n : int) : int :=
  n.
Definition off2 (n : int) : int :=
  Int.add n (Int.repr 1).
Definition off3 (n : int) : int :=
  Int.add n (Int.repr 2).
Definition off4 (n : int) : int :=
  Int.add n (Int.repr 3).

Definition update_allow (rho : nodevar) (addr : int) (region : RegionInfo) :=
  match (I32Map.get addr (RS region)) with
  | None => None
  | Some _ => Some rho
  end.

Definition update_allow2 (rho : nodevar) (addr : int) (region : RegionInfo) :=
  match (I32Map.get (off1 addr) (RS region)),
        (I32Map.get (off2 addr) (RS region)),
        (I32Map.get (off3 addr) (RS region)),
        (I32Map.get (off4 addr) (RS region)) with
  | Some _,Some _,Some _,Some _ => Some rho
  | _,_,_,_ => None
  end.

Definition update_set (l : LiveRegions) (region : RegionInfo) (rho : nodevar) 
                      (addr : int) (v : int) :=
  PTree.set rho 
    (mk_region (A region) (I32Map.set addr (Some (Int v)) (RS region))) l.

Definition update_set2 (l : LiveRegions) (region : RegionInfo) (rho : nodevar)
                       (addr : int) (v : int) :=
  PTree.set rho (mk_region (A region)
    (I32Map.set (off1 addr) (Some (Byte (byte1 v)))
    (I32Map.set (off2 addr) (Some (Byte (byte2 v)))
    (I32Map.set (off3 addr) (Some (Byte (byte3 v))) 
    (I32Map.set (off4 addr) (Some (Byte (byte4 v))) (RS region)))))) l.

Definition update_search (l : LiveRegions) (v1 : int) (v2 : int) check update_h :=
  match PTree.fold 
    (fun b i x =>
      match b with
      | None => check i v1 x
      | Some _ => b
      end ) l None with
  | None => l
  | Some rho =>
      match PTree.get rho l with
      | None => l
      | Some region => update_h l region rho v1 v2
      end
  end.

Definition update (l : LiveRegions) (v1 : int) (v2 : int) :=
  update_search l v1 v2 update_allow update_set.

Definition update2 (l : LiveRegions) (v1 : int) (v2 : int) :=
  update_search l v1 v2 update_allow2 update_set2.

Definition combine (b1 b2 b3 b4 : int) :=
  Int.or (Int.shl b1 (Int.repr 24)) (
  Int.or (Int.shl b2 (Int.repr 16)) (
  Int.or (Int.shl b3 (Int.repr 8)) b4)).

Definition getvalueh (l : LiveRegions) (v : int) check :=
  match PTree.fold 
    (fun b i x =>
      match b with
      | None => check i v x
      | Some _ => b
      end
    ) l None with
  | None => Some Uninit
  | Some rho =>
      match PTree.get rho l with
      | None => Some Uninit
      | Some region => I32Map.get v (RS region)
      end
  end.  

Definition getvalue (l : LiveRegions) (v : int) :=
  match (getvalueh l v update_allow) with
  | None => Val Uninit
  | Some v2 => Val v2
  end.

Definition getvalue2 (l : LiveRegions) (v : int) :=
  match (getvalueh l v update_allow2) with
  | None => Val Uninit
  | Some v2 => Val v2
  end.

Fixpoint initialize_h (rs : RegionStore) (a : int) (m : positive) :=
  match m with
  | xH => rs
  | xI m' => initialize_h (I32Map.set a (Some Uninit) rs) (Int.add a Int.one) m'
  | xO m' => initialize_h (I32Map.set a (Some Uninit) rs) (Int.add a Int.one) m'
  end.

Definition initialize (l : LiveRegions) (rho : nodevar) 
  (a : int) (m : int) (allocator : Allocator) :=
  match PTree.get rho l with
  | None => l
  | Some region => (
      match (Int.unsigned m) with
      | Zpos m' => PTree.set rho (mk_region allocator (initialize_h (RS region) a m')) l
      | ZO => l
      end )
  end.

(* Small-step relations for dynamic checks *)
Reserved Notation " e '==>e' e' " (at level 40).
Reserved Notation " s '==>s' s' " (at level 40).

Inductive stmt_step : (Genv.t nat nat) -> State_stmt -> trace -> State_stmt -> Prop :=
  | R1 : forall venv l s1 s2 venv' l' s1',
      state_s venv l s1 ==>s state_s venv' l' s1' ->
      state_s venv l (Seq s1 s2) ==>s state_s venv' l' (Seq s1' s2)
  (* Added R1seq ... *)
  | R1seq : forall venv l s2,
      state_s venv l (Seq Epsilon s2) ==>s state_s venv l s2
  | R2 : forall venv l e x venv' l' e',
      state_e venv l e ==>e state_e venv' l' e' ->
      state_s venv l (Assign x e) ==>s state_s venv' l' (Assign x e')
  | R3 : forall venv l x v,
      value_v v ->
      state_s venv l (Assign x (Val v)) ==>s state_s (PTree.set x v venv) l Epsilon
  | R4 : forall venv l e1 e2 venv' l' e1',
      state_e venv l e1 ==>e venv' l' e1' ->
      state_s venv l (Store e1 e2) ==>s state_s venv l' (Store e1' e2)
  | R5 : forall venv l e v venv' l' e',
      value_v v ->
      state_e venv l e ==>e state_e venv' l' e' ->
      state_s venv l (Store (Val v) e) ==>s state_s venv' l' (Store (Val v) e')
  (* R6 changed from v1 != Uninit to v1 = Int *)
  | R6 : forall venv l v1 v2 n n',
      value_v v1 ->
      v1 = (Int n) ->
      value_v v2 ->
      v2 = (Int n') ->
      state_s venv l (Store (Val v2) (Val v1)) ==>s state_s venv (update l n n') Epsilon
  (* Added error transition for R6 *)
  | R6error : forall venv l v1 v2 rho,
      value_v v1 ->
      v1 = Uninit \/ v1 = Region rho->
      value_v v2 ->
      state_s venv l (Store (Val v2) (Val v1)) ==>s state_s venv l ErrorStmt
  | R7 : forall venv l e1 e2 e3 venv' l' e1',
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_s venv l (StoreToU e1 e2 e3) ==>s state_s venv' l' (StoreToU e1' e2 e3)
  | R8 : forall venv l v1 e2 e3 venv' l' e2',
      value_v v1 ->
      state_e venv l e2 ==>e state_e venv' l' e2' ->
      state_s venv l (StoreToU (Val v1) e2 e3) ==>s state_s venv' l' (StoreToU (Val v1) e2' e3)
  | R9 : forall venv l v1 v2 e3 venv' l' e3',
      value_v v1 ->
      value_v v2 ->
      state_e venv l e3 ==>e state_e venv' l' e3' ->
      state_s venv l (StoreToU (Val v1) (Val v2) e3) ==>s 
      state_s venv' l' (StoreToU (Val v1) (Val v2) e3')
  | R10 : forall venv l n n' rho v1 v2 region foo1 foo2 foo3,
      value_v v1 ->
      value_v v2 ->
      v1 = Int n ->
      v2 = Int n' ->
      PTree.get rho l = Some region /\
      I32Map.get (Int.add n Int.one) (RS region) = Some foo1 /\
      I32Map.get (Int.add n (Int.repr 2)) (RS region) = Some foo2 /\
      I32Map.get (Int.add n (Int.repr 3)) (RS region) = Some foo3 ->
      state_s venv l (StoreToU (Val (Region rho)) (Val v2) (Val v1)) ==>s
      state_s venv (update2 l n n') Epsilon
  | R10error : forall venv l rho v1 v2,
      value_v v1 ->
      value_v v2 ->
      PTree.get rho l = None ->
      state_s venv l (StoreToU (Val (Region rho)) (Val v2) (Val v1)) ==>s
      state_s venv l ErrorStmt
  | R10error2 : forall venv l n rho v1 v2 region,
      value_v v1 ->
      value_v v2 ->
      v1 = Int n ->
      PTree.get rho l = Some region ->
      I32Map.get (Int.add n Int.one) (RS region) = None \/
      I32Map.get (Int.add n (Int.repr 2)) (RS region) = None \/
      I32Map.get (Int.add n (Int.repr 3)) (RS region) = None ->
      state_s venv l (StoreToU (Val (Region rho)) (Val v2) (Val v1)) ==>s
      state_s venv l ErrorStmt
  | R12 : forall venv l e1 e2 venv' l' e1',
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_s venv l (PoolFree e1 e2) ==>s state_s venv' l' (PoolFree e1' e2)
  | R13 : forall venv l v e2 venv' l' e2',
      value_v v ->
      state_e venv l e2 ==>e state_e venv' l' e2' ->
      state_s venv l (PoolFree (Val v) e2) ==>s state_s venv' l' (PoolFree (Val v) e2')
  (* R14 changed to v = int since it should be an address *)
  | R14 : forall venv l v n rho alloc rs,
      value_v v ->
      v = Int n ->
      PTree.get rho l = Some (mk_region alloc rs) ->
      state_s venv l (PoolFree (Val (Region rho)) (Val v)) ==>s 
      state_s venv (PTree.set rho (mk_region
        (mk_allocator (offset alloc) ((Int.unsigned n)::(freelist alloc))) rs) l) Epsilon
  | R14error : forall venv l v rho rho' f rs,
      value_v v ->
      v = Uninit \/ v = (Region rho') ->
      PTree.get rho l = Some (mk_region f rs) ->
      state_s venv l (PoolFree (Val (Region rho)) (Val v)) ==>s state_s venv l ErrorStmt
  | R15 : forall venv l rho tau x s,
      PTree.get rho l = None ->
      state_s venv l (PoolInit rho tau x s) ==>s 
      state_s (PTree.set x (Region rho) venv) 
              (PTree.set rho (mk_region new_allocator (I32Map.init None)) l) 
              (PoolPop s rho)
  | R16 : forall venv l s venv' l' s' rho,
      state_s venv l s ==>s state_s venv' l' s' ->
      state_s venv l (PoolPop s rho) ==>s state_s venv' l' (PoolPop s' rho)
  | R17 : forall venv l rho,
      state_s venv l (PoolPop Epsilon rho) ==>s
      state_s venv (PTree.remove rho l) Epsilon
where " s '==>s' s' " := (stmt_step (Genv.empty_genv nat nat) s nil s')

with stmt_exp : (Genv.t nat nat) -> State_exp -> trace -> State_exp -> Prop :=
  | R18 : forall venv x v l,
      PTree.get x venv = Some v ->
      state_e venv l (Var x) ==>e state_e venv l (Val v)
  | R19 : forall venv l e1 e2 op venv' l' e1',
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_e venv l (Binop e1 op e2) ==>e state_e venv' l' (Binop e1' op e2)
  | R20 : forall venv l v e2 op venv' l' e2',
      value_v v ->
      state_e venv l e2 ==>e state_e venv' l' e2' ->
      state_e venv l (Binop (Val v) op e2) ==>e state_e venv' l' (Binop (Val v) op e2')
  | R21 : forall venv l v1 v2 op n1 n2,
      value_v v1 ->
      v1 = Int n1 ->
      value_v v2 ->
      v2 = Int n2 ->
      (* warning ... this is a hack, but we don't need to do a computation *)
      state_e venv l (Binop (Val v1) op (Val v2)) ==>e state_e venv l (Val v1)
  | R22 : forall venv l e venv' l' e',
      state_e venv l e ==>e state_e venv' l' e' ->
      state_e venv l (Load e) ==>e state_e venv' l' (Load e')
(* changed R23 from v != unint to v = int *)
  | R23 : forall venv l v n,
      value_v v ->
      v = Int n ->
      state_e venv l (Load (Val v)) ==>e state_e venv l (getvalue l n)
  | R23error : forall venv l v rho ,
      value_v v ->
      v = (Region rho) \/ v = Uninit ->
      state_e venv l (Load (Val v)) ==>e state_e venv l ErrorExp
  | R24 : forall venv l e1 e2 venv' l' e1',
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_e venv l (LoadFromU e1 e2) ==>e state_e venv l (LoadFromU e1' e2)
  | R25 : forall venv l v e2 venv' l' e2',
      value_v v ->
      state_e venv l e2 ==>e state_e venv' l' e2' ->
      state_e venv l (LoadFromU (Val v) e2) ==>e state_e venv l (LoadFromU (Val v) e2')
  | R26 : forall venv l rho v n region foo1 foo2 foo3,
      value_v v ->
      v = Int n ->
      PTree.get rho l = Some region ->
      I32Map.get (Int.add n Int.one) (RS region) = Some foo1 ->
      I32Map.get (Int.add n (Int.repr 2)) (RS region) = Some foo2 ->
      I32Map.get (Int.add n (Int.repr 3)) (RS region) = Some foo3 ->
      state_e venv l (LoadFromU (Val (Region rho)) (Val v)) ==>e
      state_e venv l (getvalue2 l n)
  | R26error : forall venv l rho v,
      value_v v ->
      PTree.get rho l = None ->
      state_e venv l (LoadFromU (Val (Region rho)) (Val v)) ==>e
      state_e venv l ErrorExp
  | R26error2 : forall venv l n rho v region,
      value_v v ->
      v = Int n ->
      PTree.get rho l = Some region ->
      I32Map.get (Int.add n Int.one) (RS region) = None \/
      I32Map.get (Int.add n (Int.repr 2)) (RS region) = None \/
      I32Map.get (Int.add n (Int.repr 3)) (RS region) = None ->
      state_e venv l (LoadFromU (Val (Region rho)) (Val v)) ==>e
      state_e venv l ErrorExp
  | R28 : forall venv l e tau,
      state_e venv l (Cast e tau) ==>e state_e venv l e
  | R29 : forall venv l e1 e2 venv' l' e1' tau,
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_e venv l (CastI2Ptr e1 e2 tau) ==>e state_e venv' l' (CastI2Ptr e1' e2 tau)
  | R30 : forall venv l v e venv' l' e' tau,
      value_v v ->
      state_e venv l e ==>e state_e venv' l' e' ->
      state_e venv l (CastI2Ptr (Val v) e tau) ==>e state_e venv' l' (CastI2Ptr (Val v) e' tau)
  | R31 : forall venv l rho v n region tau foo,
      value_v v ->
      v = Int n ->
      PTree.get rho l = Some region ->
      I32Map.get n (RS region) = Some foo ->
      state_e venv l (CastI2Ptr (Val (Region rho)) (Val v) tau) ==>e state_e venv l (Val v)
  | R31error : forall venv l rho v tau,
      value_v v ->
      PTree.get rho l = None ->
      state_e venv l (CastI2Ptr (Val (Region rho)) (Val v) tau) ==>e state_e venv l ErrorExp
  | R31error2 : forall venv l rho v n region tau,
      value_v v ->
      v = Int n ->
      PTree.get rho l = Some region ->
      I32Map.get n (RS region) = None ->
      state_e venv l (CastI2Ptr (Val (Region rho)) (Val v) tau) ==>e state_e venv l ErrorExp
  | R32 : forall venv l e1 e2 venv' l' e1',
      state_e venv l e1 ==>e state_e venv l' e1' ->
      state_e venv l (PoolAlloc e1 e2) ==>e state_e venv' l' (PoolAlloc e1' e2)
  | R33 : forall venv l v e2 venv' l' e2',
      value_v v ->
      state_e venv l e2 ==>e state_e venv l' e2' ->
      state_e venv l (PoolAlloc (Val v) e2) ==>e state_e venv' l' (PoolAlloc (Val v) e2')
  (* R35 and R36 taken care of with new R34 *)
  | R34 : forall venv l rho a region allocator v n,
      value_v v ->
      v = Int n ->
      PTree.get rho l = Some region ->
      Some (a,allocator) = alloc (A region) (Int.unsigned n) ->
      state_e venv l (PoolAlloc (Val (Region rho)) (Val v)) ==>e
      state_e venv (initialize l rho a n allocator) (Val (Int a))
  (* Taking out addr for now ... *)
where " e '==>e' e' " := (stmt_exp (Genv.empty_genv nat nat) e nil e').