(* Compcert imports *)
Add LoadPath "./CompCert-Toolkit".
Require Import Maps.
Require Import Smallstep.
Require Import Integers.
Require Import Coqlib.

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

Module Int32Indexed.
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
End Int32Indexed.

(* Environments for operational semantics *)
Definition VarEnv := PTree.t value. (* var -> value *)
Definition RegionStore := PTree.t value. (* Z (addresses) -> value *)
Record RegionT : Type := region_t {
  A : Allocator;
  RS : RegionStore
}.
Definition LiveRegions := PTree.t RegionT. (* nodevar -> RegionT *)

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

(* getbyte(n,k) := (n << (8*(3-k))) >> 24 *)
Definition getbyte (n : int) (k : int) : int :=
  Int.shr (Int.shl n (Int.mul (Int.repr 8) (Int.sub (Int.repr 3) k))) (Int.repr 24).

Definition domain_check (i : positive) (v : int) (x : RegionT) :=
  match (PTree.get (Int32Indexed.index v) (RS x)) with
  | None => None
  | Some _ => Some i
  end.

Definition domain_check2 (i : positive) (v : int) (x : RegionT) :=
  match (PTree.get (Int32Indexed.index v) (RS x)),
        (PTree.get (Int32Indexed.index (Int.add v (Int.repr 1))) (RS x)),
        (PTree.get (Int32Indexed.index (Int.add v (Int.repr 2))) (RS x)),
        (PTree.get (Int32Indexed.index (Int.add v (Int.repr 3))) (RS x)) with
  | Some _,Some _,Some _,Some _ => Some i
  | _,_,_,_ => None
  end.

Definition updateh (l : LiveRegions) (v1 : int) (v2 : value) check :=
  match PTree.fold 
    (fun b i x =>
      match b with
      | None => check i v1 x
      | Some _ => b
      end
    ) l None with
  | None => l
  | Some rho =>
      match PTree.get rho l with
      | None => l
      | Some region => 
          PTree.set rho (region_t (A region) 
            (PTree.set (Int32Indexed.index v1) v2 (RS region))) l
      end
  end.

Definition update (l : LiveRegions) (v1 : int) (v2 : value) :=
  updateh l v1 v2 domain_check.

Definition update2 (l : LiveRegions) (v1 : int) (v2 : value) :=
  updateh l v1 v2 domain_check2.

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
      | Some region => PTree.get (Int32Indexed.index v) (RS region)
      end
  end.  

Definition getvalue (l : LiveRegions) (v : int) :=
  match (getvalueh l v domain_check) with
  | None => Val Uninit
  | Some v2 => Val v2
  end.

Definition getvalue2 (l : LiveRegions) (v : int) :=
  match (getvalueh l v domain_check2) with
  | None => Val Uninit
  | Some v2 => Val v2
  end.

Fixpoint initialize_h (rs : RegionStore) (a : int) (m : positive) :=
  match m with
  | xH => rs
  | xI m' => initialize_h (PTree.set (Int32Indexed.index a) Uninit rs) (Int.add a Int.one) m'
  | xO m' => initialize_h (PTree.set (Int32Indexed.index a) Uninit rs) (Int.add a Int.one) m'
  end.

Definition initialize (l : LiveRegions) (rho : nodevar) 
  (a : int) (m : int) (allocator : Allocator) :=
  match PTree.get rho l with
  | None => l
  | Some region => (
      match (Int.unsigned m) with
      | Zpos m' => PTree.set rho (region_t allocator (initialize_h (RS region) a m')) l
      | ZO => l
      end )
  end.

(* Small-step relations for dynamic checks *)
Reserved Notation " e '==>e' e' " (at level 40).
Reserved Notation " s '==>s' s' " (at level 40).

Inductive stmt_step : State_stmt -> State_stmt -> Prop :=
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
  | R6 : forall venv l v1 v2 n,
      value_v v1 ->
      v1 = (Int n) ->
      value_v v2 ->
      state_s venv l (Store (Val v2) (Val v1)) ==>s state_s venv (update l n v2) Epsilon
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
  | R10 : forall venv l n rho v1 v2 region foo1 foo2 foo3,
      value_v v1 ->
      value_v v2 ->
      v1 = Int n ->
      PTree.get rho l = Some region /\
      PTree.get (Int32Indexed.index (Int.add n Int.one)) (RS region) = Some foo1 /\
      PTree.get (Int32Indexed.index (Int.add n (Int.repr 2))) (RS region) = Some foo2 /\
      PTree.get (Int32Indexed.index (Int.add n (Int.repr 3))) (RS region) = Some foo3 ->
      state_s venv l (StoreToU (Val (Region rho)) (Val v2) (Val v1)) ==>s
      state_s venv (update2 l n v2) Epsilon
  | R10error : forall venv l n rho v1 v2,
      value_v v1 ->
      value_v v2 ->
      v1 = Int n ->
      PTree.get rho l = None ->
      state_s venv l (StoreToU (Val (Region rho)) (Val v2) (Val v1)) ==>s
      state_s venv (update2 l n v2) ErrorStmt
  | R10error2 : forall venv l n rho v1 v2 region,
      value_v v1 ->
      value_v v2 ->
      v1 = Int n ->
      PTree.get rho l = Some region ->
      PTree.get (Int32Indexed.index (Int.add n Int.one)) (RS region) = None \/
      PTree.get (Int32Indexed.index (Int.add n (Int.repr 2))) (RS region) = None \/
      PTree.get (Int32Indexed.index (Int.add n (Int.repr 3))) (RS region) = None ->
      state_s venv l (StoreToU (Val (Region rho)) (Val v2) (Val v1)) ==>s
      state_s venv (update2 l n v2) ErrorStmt
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
      PTree.get rho l = Some (region_t alloc rs) ->
      state_s venv l (PoolFree (Val (Region rho)) (Val v)) ==>s 
      state_s venv (PTree.set rho (region_t 
        (mk_allocator (offset alloc) ((Int.unsigned n)::(freelist alloc))) rs) l) Epsilon
  | R14error : forall venv l v rho rho' f rs,
      value_v v ->
      v = Uninit \/ v = (Region rho') ->
      PTree.get rho l = Some (region_t f rs) ->
      state_s venv l (PoolFree (Val (Region rho)) (Val v)) ==>s state_s venv l ErrorStmt
  | R15 : forall venv l rho tau x s,
      PTree.get rho l = None ->
      state_s venv l (PoolInit rho tau x s) ==>s 
      state_s (PTree.set x (Region rho) venv) 
              (PTree.set rho (region_t new_allocator (PTree.empty value)) l) 
              (PoolPop s rho)
  | R16 : forall venv l s venv' l' s' rho,
      state_s venv l s ==>s state_s venv' l' s' ->
      state_s venv l (PoolPop s rho) ==>s state_s venv' l' (PoolPop s' rho)
  | R17 : forall venv l rho,
      state_s venv l (PoolPop Epsilon rho) ==>s
      state_s venv (PTree.remove rho l) Epsilon
where " s '==>s' s' " := (stmt_step s s')

with stmt_exp : State_exp -> State_exp -> Prop :=
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
      PTree.get (Int32Indexed.index (Int.add n Int.one)) (RS region) = Some foo1 ->
      PTree.get (Int32Indexed.index (Int.add n (Int.repr 2))) (RS region) = Some foo2 ->
      PTree.get (Int32Indexed.index (Int.add n (Int.repr 3))) (RS region) = Some foo3 ->
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
      PTree.get (Int32Indexed.index (Int.add n Int.one)) (RS region) = None \/
      PTree.get (Int32Indexed.index (Int.add n (Int.repr 2))) (RS region) = None \/
      PTree.get (Int32Indexed.index (Int.add n (Int.repr 3))) (RS region) = None ->
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
      PTree.get (Int32Indexed.index n) (RS region) = Some foo ->
      state_e venv l (CastI2Ptr (Val (Region rho)) (Val v) tau) ==>e state_e venv l (Val v)
  | R31error : forall venv l rho v tau,
      value_v v ->
      PTree.get rho l = None ->
      state_e venv l (CastI2Ptr (Val (Region rho)) (Val v) tau) ==>e state_e venv l ErrorExp
  | R31error2 : forall venv l rho v n region tau,
      value_v v ->
      v = Int n ->
      PTree.get rho l = Some region ->
      PTree.get (Int32Indexed.index n) (RS region) = None ->
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
where " e '==>e' e' " := (stmt_exp e e').

