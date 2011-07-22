Add LoadPath "./CompCert-Toolkit".
Require Export sva_ast.
Require Export Maps.

Definition varmap := PTree.t tipe.
Definition regionmap := PTree.t tipe.
Definition context := prod varmap regionmap.

(** TODO: lots of shit ...
    The plan is to first formalize the technical report, then add control flow, 
    then generalize to full C. *)

(* C |- e : tau *)
Inductive has_type_exp : context -> exp -> tipe -> Prop :=
  | SS0 : forall Gamma Delta x tau, 
      wf_context (Gamma,Delta) tau ->
      PTree.get x Gamma = Some tau ->
      has_type_exp (Gamma,Delta) (Var x) tau
  | SS1 : forall C n,
      has_type_exp C (Val (Int n)) Int_t
  | SS2 : forall C e1 e2 b,
      has_type_exp C e1 Int_t ->
      has_type_exp C e2 Int_t ->
      has_type_exp C (Binop e1 b e2) Int_t
  | SS3 : forall C tau tau' rho',
      wf_context C tau ->
      tau = Int_t \/ tau = Char_t \/ tau = Unknown_t \/ tau = (Pts_t rho' tau') ->
      has_type_exp C (Val Uninit) tau
  | SS4 : forall Gamma Delta e tau tau' rho rho',
      has_type_exp (Gamma,Delta) e (Pts_t tau rho) ->
      tau = Int_t \/ tau = (Pts_t tau' rho') \/ tau = (Handle_t rho' tau') ->
      PTree.get rho Delta = Some tau ->
      has_type_exp (Gamma,Delta) (Load e) tau
  | SS4char : forall Gamma Delta e rho,
      has_type_exp (Gamma,Delta) e (Pts_t Char_t rho) ->
      PTree.get rho Delta = Some Char_t ->
      has_type_exp (Gamma,Delta) (Loadc e) Char_t
  | SS5 : forall Gamma Delta e2 x tau rho,
      has_type_exp (Gamma,Delta) e2 (Pts_t tau rho) ->
      PTree.get rho Delta = Some Unknown_t ->
      has_type_exp (Gamma,Delta) x (Handle_t rho Unknown_t) ->
      has_type_exp (Gamma,Delta) (LoadFromU x e2) Int_t
  | SS5char : forall Gamma Delta e2 x tau rho,
      has_type_exp (Gamma,Delta) e2 (Pts_t tau rho) ->
      PTree.get rho Delta = Some Unknown_t ->
      has_type_exp (Gamma,Delta) x (Handle_t rho Unknown_t) ->
      has_type_exp (Gamma,Delta) (LoadcFromU x e2) Char_t
  | SS6 : forall Gamma Delta e2 x tau rho,
      PTree.get rho Delta = Some tau ->
      has_type_exp (Gamma,Delta) x (Handle_t rho tau) ->
      has_type_exp (Gamma,Delta) e2 Int_t ->
      has_type_exp (Gamma,Delta) (PoolAlloc x e2) (Pts_t tau rho)
  | SS7 : forall Gamma Delta e x tau rho,
      PTree.get rho Delta = Some tau ->
      has_type_exp (Gamma,Delta) x (Handle_t rho tau) ->
      has_type_exp (Gamma,Delta) e Int_t -> 
      has_type_exp (Gamma,Delta) (CastI2Ptr x e (Pts_t tau rho)) (Pts_t tau rho)
  | SS8 : forall C e tau tau' rho,
      wf_context C (Pts_t tau' rho) ->
      has_type_exp C e (Pts_t tau rho) ->
      has_type_exp C (Cast e (Pts_t tau' rho)) (Pts_t tau' rho)
  | SS9 : forall Gamma Delta  e2 e3 x tau rho,
      PTree.get rho Delta = Some tau ->
      has_type_exp (Gamma,Delta) x (Handle_t rho tau) ->
      has_type_exp (Gamma,Delta) e2 (Pts_t tau rho) ->
      has_type_exp (Gamma,Delta) e3 Int_t ->
      has_type_exp (Gamma,Delta) (Addr x e2 e3) (Pts_t tau rho)
  | SS10 : forall C e tau tau' rho',
      has_type_exp C e tau ->
      tau = Int_t \/ tau = Char_t \/ tau = Unknown_t \/ tau = (Pts_t rho' tau') ->
      has_type_exp C (Cast e tau) Int_t

(* C |- s : tau *)
with has_type_stmt : context -> stmt -> Prop :=
  | SS11 : forall C,
      has_type_stmt C Epsilon
  | SS12 : forall C s1 s2,
      has_type_stmt C s1 ->
      has_type_stmt C s2 ->
      has_type_stmt C (Seq s1 s2)
  | SS13 : forall C e x tau,
      has_type_exp C (Var x) tau ->
      has_type_exp C e tau ->
      has_type_stmt C (Assign x e) 
  | SS14 : forall Gamma Delta e1 e2 rho rho' tau tau',
      PTree.get rho Delta = Some tau ->
      has_type_exp (Gamma,Delta) e1 (Pts_t tau rho) ->
      has_type_exp (Gamma,Delta) e2 tau ->
      tau = Int_t \/ tau = (Pts_t tau' rho') \/ tau = (Handle_t rho' tau') ->
      has_type_stmt (Gamma,Delta) (Store e2 e1)
  | SS14char : forall Gamma Delta e1 e2 rho,
      PTree.get rho Delta = Some Char_t ->
      has_type_exp (Gamma,Delta) e1 (Pts_t Char_t rho) ->
      has_type_exp (Gamma,Delta) e2 Char_t ->
      has_type_stmt (Gamma,Delta) (Storec e2 e1)
  | SS15 : forall Gamma Delta e1 e2 x rho tau,
      PTree.get rho Delta = Some Unknown_t ->
      has_type_exp (Gamma,Delta) e1 (Pts_t tau rho) ->
      has_type_exp (Gamma,Delta) e2 tau ->
      has_type_exp (Gamma,Delta) x (Handle_t rho Unknown_t) ->
      has_type_stmt (Gamma,Delta) (StoreToU x e2 e1)
  | SS15char : forall Gamma Delta e1 e2 x rho tau,
      PTree.get rho Delta = Some Unknown_t ->
      has_type_exp (Gamma,Delta) e1 (Pts_t tau rho) ->
      has_type_exp (Gamma,Delta) e2 Char_t ->
      has_type_exp (Gamma,Delta) x (Handle_t rho Unknown_t) ->
      has_type_stmt (Gamma,Delta) (StorecToU x e2 e1)
  | SS16 : forall Gamma Delta e2 x rho tau,
      PTree.get rho Delta = Some tau ->
      has_type_exp (Gamma,Delta) (Var x) (Handle_t rho tau) ->
      has_type_exp (Gamma,Delta) e2 (Pts_t tau rho) ->
      has_type_stmt (Gamma,Delta) (PoolFree (Var x) e2)
  | SS17 : forall Gamma Delta s x rho tau,
      wf_context (Gamma,Delta) tau ->
      PTree.get x Gamma = None /\ PTree.get rho Delta = None ->
      has_type_stmt ((PTree.set x (Handle_t rho tau) Gamma),(PTree.set rho tau Delta)) s ->
      has_type_stmt (Gamma,Delta) (PoolInit rho tau x s)

(* C |- tau *)
with wf_context : context -> tipe -> Prop :=
  | SS18 : forall C,
      wf_context C Int_t
  | SS19 : forall C,
      wf_context C Unknown_t
  (* SS20 was removed *)
  | SS21 : forall Gamma Delta rho tau,
      PTree.get rho Delta = Some tau ->
      wf_context (Gamma,Delta) tau ->
      wf_context (Gamma,Delta) (Pts_t tau rho)
  | SS22 : forall Gamma Delta tau rho,
      PTree.get rho Delta = Some Unknown_t ->
      wf_context (Gamma,Delta) tau ->
      wf_context (Gamma,Delta) (Pts_t tau rho)
  | SS23 : forall Gamma Delta rho tau,
      PTree.get rho Delta = Some tau ->
      wf_context (Gamma,Delta) tau ->
      wf_context (Gamma,Delta) (Handle_t rho tau)
  | SS24 : forall C,
      wf_context C Char_t.

