Add LoadPath "./CompCert-Toolkit".
Require Import sva_ast.
Require Import List.
Require Import Maps.
Require Import Smallstep.
Require Import Integers.
Require Import Coqlib.
Require Import ProofIrrelevance.

(* We could have formalized ES as the paper does as exp + stmt, but sums
 * are inconvenient to work with and the expression state and statement
 * state are really used in two different ways. 
 *
 * We are ignoring the heap at this point of the formalism as the paper
 * claims that it doesn't really affect anything. Hopefully this is the
 * case or we're screwed ... 
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

Definition VarEnv := PTree.t value. (* var -> value *)
Definition RegionStore := PTree.t value. (* int -> value *)
Definition FreeList := list value. (* list of addresses, right now its a hack for R14/R15 *)
Record RegionT : Type := region_t {
  F : FreeList;
  RS : RegionStore
}.
Definition LiveRegions := PTree.t RegionT. (* nodevar -> RegionT *)

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

(* getbyte(n,k) := (n << (8*(3-k))) >> 24 *)
Definition getbyte (n : int) (k : int) : int :=
  Int.shr (Int.shl n (Int.mul (Int.repr 8) (Int.sub (Int.repr 3) k))) (Int.repr 24).

Definition domain {A : Type} (m: PTree.t A) :=
  List.map (@fst PTree.elt A) (PTree.elements m).

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
          PTree.set rho (region_t (F region) 
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

(* hack just returning uninit ... *)
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

(* hack just returning uninit ... *)
Definition getvalue2 (l : LiveRegions) (v : int) :=
  match (getvalueh l v domain_check2) with
  | None => Val Uninit
  | Some v2 => Val v2
  end.

(* Small-step relations for dynamic checks *)
Reserved Notation " e '==>e' e' " (at level 40).
Reserved Notation " s '==>s' s' " (at level 40).

Inductive stmt_step : State_stmt -> State_stmt -> Prop :=
  | R1 : forall venv l s1 s2 venv' l' s1',
      state_s venv l s1 ==>s state_s venv' l' s1' ->
      state_s venv l (Seq s1 s2) ==>s state_s venv' l' (Seq s1' s2)
  (* Added R1seq becuase I think paper is missing this rule ... *)
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
  | R4char : forall venv l e1 e2 venv' l' e1',
      state_e venv l e1 ==>e venv' l' e1' ->
      state_s venv l (Storec e1 e2) ==>s state_s venv l' (Storec e1' e2)
  | R5 : forall venv l e v venv' l' e',
      value_v v ->
      state_e venv l e ==>e state_e venv' l' e' ->
      state_s venv l (Store (Val v) e) ==>s state_s venv' l' (Store (Val v) e')
  | R5char : forall venv l e v venv' l' e',
      value_v v ->
      state_e venv l e ==>e state_e venv' l' e' ->
      state_s venv l (Storec (Val v) e) ==>s state_s venv' l' (Storec (Val v) e')
  | R6 : forall venv l v1 v2 n rho,
      value_v v1 ->
      v1 = (Int n) \/ v1 = (Region rho) ->
      value_v v2 ->
      state_s venv l (Store (Val v2) (Val v1)) ==>s state_s venv (update l n v2) Epsilon
  | R6error : forall venv l v1 v2,
      value_v v1 ->
      v1 = Uninit ->
      value_v v2 ->
      state_s venv l (Store (Val v2) (Val v1)) ==>s state_s venv l ErrorStmt
  | R6char : forall venv l v1 v2 n rho,
      value_v v1 ->
      v1 = (Int n) \/ v1 = (Region rho) ->
      value_v v2 ->
      state_s venv l (Storec (Val v2) (Val v1)) ==>s state_s venv (update l n v2) Epsilon
  | R6charerror : forall venv l v1 v2,
      value_v v1 ->
      v1 = Uninit ->
      value_v v2 ->
      state_s venv l (Storec (Val v2) (Val v1)) ==>s state_s venv l ErrorStmt
  | R7 : forall venv l e1 e2 e3 venv' l' e1',
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_s venv l (StoreToU e1 e2 e3) ==>s state_s venv' l' (StoreToU e1' e2 e3)
  | R7char : forall venv l e1 e2 e3 venv' l' e1',
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_s venv l (StorecToU e1 e2 e3) ==>s state_s venv' l' (StorecToU e1' e2 e3)
  | R8 : forall venv l v1 e2 e3 venv' l' e2',
      value_v v1 ->
      state_e venv l e2 ==>e state_e venv' l' e2' ->
      state_s venv l (StoreToU (Val v1) e2 e3) ==>s state_s venv' l' (StoreToU (Val v1) e2' e3)
  | R8char : forall venv l v1 e2 e3 venv' l' e2',
      value_v v1 ->
      state_e venv l e2 ==>e state_e venv' l' e2' ->
      state_s venv l (StorecToU (Val v1) e2 e3) ==>s state_s venv' l' (StorecToU (Val v1) e2' e3)
  | R9 : forall venv l v1 v2 e3 venv' l' e3',
      value_v v1 ->
      value_v v2 ->
      state_e venv l e3 ==>e state_e venv' l' e3' ->
      state_s venv l (StoreToU (Val v1) (Val v2) e3) ==>s 
      state_s venv' l' (StoreToU (Val v1) (Val v2) e3')
  | R9char : forall venv l v1 v2 e3 venv' l' e3',
      value_v v1 ->
      value_v v2 ->
      state_e venv l e3 ==>e state_e venv' l' e3' ->
      state_s venv l (StorecToU (Val v1) (Val v2) e3) ==>s 
      state_s venv' l' (StorecToU (Val v1) (Val v2) e3')
  | R10 : forall venv l n rho v1 v2,
      value_v v1 ->
      value_v v2 ->
      v1 = Int n ->
      (* some crazy bs about intervals ... *)
      state_s venv l (StoreToU (Val (Region rho)) (Val v2) (Val v1)) ==>s
      state_s venv (update2 l n v2) Epsilon
  (* also need to add an error transition for R10 *)
  | R11 : forall venv l v1 v2 rho n,
      value_v v1 ->
      value_v v2 ->
      v1 = Int n ->
      state_s venv l (StorecToU (Val (Region rho)) (Val v1) (Val v2)) ==>s 
      state_s venv (update l n v2) Epsilon
  | R12 : forall venv l e1 e2 venv' l' e1',
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_s venv l (PoolFree e1 e2) ==>s state_s venv' l' (PoolFree e1' e2)
  | R13 : forall venv l v e2 venv' l' e2',
      value_v v ->
      state_e venv l e2 ==>e state_e venv' l' e2' ->
      state_s venv l (PoolFree (Val v) e2) ==>s state_s venv' l' (PoolFree (Val v) e2')
  | R14 : forall venv l v n rho f rs,
      value_v v ->
      v = (Int n) \/ v = (Region rho) ->
      PTree.get rho l = Some (region_t f rs) ->
      state_s venv l (PoolFree (Val (Region rho)) (Val v)) ==>s 
      state_s venv (PTree.set rho (region_t (v::f) rs) l) Epsilon
  | R14error : forall venv l v rho f rs,
      value_v v ->
      v = Uninit ->
      PTree.get rho l = Some (region_t f rs) ->
      state_s venv l (PoolFree (Val (Region rho)) (Val v)) ==>s state_s venv l ErrorStmt
  | R15 : forall venv l rho tau x s,
      PTree.get rho l = None ->
      state_s venv l (PoolInit rho tau x s) ==>s 
      state_s (PTree.set x (Region rho) venv) 
              (PTree.set rho (region_t nil (PTree.empty value)) l) 
              (PoolPop s rho)
  | R16 : forall venv l s venv' l' s' rho,
      state_s venv l s ==>s state_s venv' l' s' ->
      state_s venv l (PoolPop s rho) ==>s state_s venv' l' (PoolPop s' rho)
  | R17 : forall venv l x rho r,
      state_s (PTree.set x (Region rho) venv) (PTree.set rho r l) (PoolPop Epsilon rho) ==>s
      state_s venv l Epsilon
      (* some bs about the heap needs to be taken care of? *)
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
  | R21 : forall venv l v1 v2 op,
      value_v v1 ->
      value_v v2 ->
      (* warning ... right now this is a hack, but we don't need to do a
       * computation? *)
      state_e venv l (Binop (Val v1) op (Val v2)) ==>e state_e venv l (Val v1)
  | R22 : forall venv l e venv' l' e',
      state_e venv l e ==>e state_e venv' l' e' ->
      state_e venv l (Load e) ==>e state_e venv' l' (Load e')
  | R22char : forall venv l e venv' l' e',
      state_e venv l e ==>e state_e venv' l' e' ->
      state_e venv l (Loadc e) ==>e state_e venv' l' (Loadc e')
  | R23 : forall venv l v n rho,
      value_v v ->
      v = (Int n) \/ v = (Region rho) ->
      state_e venv l (Load (Val v)) ==>e state_e venv l (getvalue l n)
  (* also need to add error state for R23 *)
  | R24 : forall venv l e1 e2 venv' l' e1',
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_e venv l (LoadFromU e1 e2) ==>e state_e venv l (LoadFromU e1' e2)
  | R24char : forall venv l e1 e2 venv' l' e1',
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_e venv l (LoadcFromU e1 e2) ==>e state_e venv l (LoadcFromU e1' e2)
  | R25 : forall venv l v e2 venv' l' e2',
      value_v v ->
      state_e venv l e2 ==>e state_e venv' l' e2' ->
      state_e venv l (LoadFromU (Val v) e2) ==>e state_e venv l (LoadFromU (Val v) e2')
  | R25char : forall venv l v e2 venv' l' e2',
      value_v v ->
      state_e venv l e2 ==>e state_e venv' l' e2' ->
      state_e venv l (LoadcFromU (Val v) e2) ==>e state_e venv l (LoadcFromU (Val v) e2')
  | R26 : forall venv l rho v n,
      value_v v ->
      v = Int n ->
      (* need some crazy interval check here *)
      state_e venv l (LoadFromU (Val (Region rho)) (Val v)) ==>e
      state_e venv l (getvalue2 l n)
  (* also need error state for R26 *)
  | R27 : forall venv l v rho n,
      value_v v ->
      v = Int n ->
      state_e venv l (LoadcFromU (Val (Region rho)) (Val v)) ==>e state_e venv l (getvalue l n)
  | R28 : forall venv l e tau,
      state_e venv l (Cast e tau) ==>e state_e venv l e
  | R29 : forall venv l e1 e2 venv' l' e1' tau,
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_e venv l (CastI2Ptr e1 e2 tau) ==>e state_e venv' l' (CastI2Ptr e1' e2 tau)
  | R30 : forall venv l v e venv' l' e' tau,
      value_v v ->
      state_e venv l e ==>e state_e venv' l' e' ->
      state_e venv l (CastI2Ptr (Val v) e tau) ==>e state_e venv' l' (CastI2Ptr (Val v) e' tau)
  | R31 : forall venv l rho v v' tau,
      value_v v ->
      PTree.get rho l = Some v' ->
      state_e venv l (CastI2Ptr (Val (Region rho)) (Val v) tau) ==>e state_e venv l (Val v)
  (* also need error state for R31 *)
  | R32 : forall venv l e1 e2 venv' l' e1',
      state_e venv l e1 ==>e state_e venv l' e1' ->
      state_e venv l (PoolAlloc e1 e2) ==>e state_e venv' l' (PoolAlloc e1' e2)
  | R33 : forall venv l v e2 venv' l' e2',
      value_v v ->
      state_e venv l e2 ==>e state_e venv l' e2' ->
      state_e venv l (PoolAlloc (Val v) e2) ==>e state_e venv' l' (PoolAlloc (Val v) e2')
  (*
  | R34 : forall venv l rho f rs a,
      state_e venv (PTree.set rho (region_t (a::f) rs) l) (PoolAlloc (Val (Region rho)) (Val (Int 1))) ==>e
      state_e venv (PTree.set rho (region_t f rs) l) (Val a)
  *)
  (* R34, R35 and R36 are ... *)
  | R37 : forall venv l e1 e2 e3 venv' l' e1',
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_e venv l (Addr e1 e2 e3) ==>e state_e venv' l' (Addr e1' e2 e3)
  | R38 : forall venv l v1 e2 e3 venv' l' e2',
      value_v v1 ->
      state_e venv l e2 ==>e state_e venv' l' e2' ->
      state_e venv l (Addr (Val v1) e2 e3) ==>e state_e venv' l' (Addr (Val v1) e2' e3)
  | R39 : forall venv l v1 v2 e3 venv' l' e3',
      value_v v1 ->
      value_v v2 ->
      state_e venv l e3 ==>e state_e venv' l' e3' ->
      state_e venv l (Addr (Val v1) (Val v2) e3) ==>e state_e venv' l' (Addr (Val v1) (Val v2) e3')
  (* warning hack right now ... need to make it an offset calculation *)
  | R40 : forall venv l v1 v2 rho,
      value_v v1 ->
      value_v v2 ->
      state_e venv l (Addr (Val (Region rho)) (Val v1) (Val v2)) ==>e state_e venv l (Val v1)
where " e '==>e' e' " := (stmt_exp e e').

