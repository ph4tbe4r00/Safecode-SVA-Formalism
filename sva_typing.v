Require Export sva_ast.

(** TODO: lots of shit ...
    The plan is to first formalize the technical report, then add control flow, 
    then generalize to full C. *)

(* C |- e : tau *)
Inductive has_type_exp : context -> exp -> tipe -> Prop :=
  | SS0 : forall Gamma Delta x tau, 
      wf_context (Gamma,Delta) tau ->
      Gamma x = Some tau ->
      has_type_exp (Gamma,Delta) (Var x) tau
  | SS1 : forall C n,
      has_type_exp C (Val (Int_v n)) Int_t
  | SS2 : forall C e1 e2 b,
      has_type_exp C e1 Int_t ->
      has_type_exp C e2 Int_t ->
      has_type_exp C (Binop e1 b e2) Int_t
  | SS3 : forall C tau tau' rho',
      wf_context C tau ->
      tau = Int_t \/ tau = Char_t \/ tau = Unknown_t \/ tau = (Pts_t rho' tau') ->
      has_type_exp C (Val Uninit_v) tau
  | SS4 : forall C e tau tau' rho rho',
      has_type_exp C e (Pts_t tau rho) ->
      tau = Int_t \/ tau = (Pts_t tau' rho') \/ tau = (Handle_t rho' tau') ->
      wf_context C (Assoc_t rho tau) ->
      has_type_exp C (Load e) tau
  | SS4char : forall C e rho,
      has_type_exp C e (Pts_t Char_t rho) ->
      wf_context C (Assoc_t rho Char_t) ->
      has_type_exp C (Loadc e) Char_t
  | SS5 : forall C e2 x tau rho,
      has_type_exp C e2 (Pts_t tau rho) ->
      wf_context C (Assoc_t rho Unknown_t) ->
      has_type_exp C (Var x) (Handle_t rho Unknown_t) ->
      has_type_exp C (LoadFromU x e2) Int_t
  | SS5char : forall C e2 x tau rho,
      has_type_exp C e2 (Pts_t tau rho) ->
      wf_context C (Assoc_t rho Unknown_t) ->
      has_type_exp C (Var x) (Handle_t rho Unknown_t) ->
      has_type_exp C (LoadcFromU x e2) Char_t
  | SS6 : forall C e2 x tau rho,
      wf_context C (Assoc_t rho tau) ->
      has_type_exp C (Var x) (Handle_t rho tau) ->
      has_type_exp C e2 Int_t ->
      has_type_exp C (PoolAlloc x e2) (Pts_t tau rho)
  | SS7 : forall C e x tau rho,
      wf_context C (Assoc_t rho tau) ->
      has_type_exp C (Var x) (Handle_t rho tau) ->
      has_type_exp C e Int_t -> 
      has_type_exp C (CastI2Ptr x e (Pts_t tau rho)) (Pts_t tau rho)
  | SS8 : forall C e tau tau' rho,
      wf_context C tau' ->
      has_type_exp C e (Pts_t tau rho) ->
      has_type_exp C (Cast e (Pts_t tau' rho)) (Pts_t tau' rho)
  | SS9 : forall C e2 e3 x tau rho,
      wf_context C (Assoc_t rho tau) ->
      has_type_exp C (Var x) (Handle_t rho tau) ->
      has_type_exp C e2 (Pts_t tau rho) ->
      has_type_exp C e3 Int_t ->
      has_type_exp C (Addr x e2 e3) (Pts_t tau rho)
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
  | SS14 : forall C e1 e2 rho rho' tau tau',
      wf_context C (Assoc_t rho tau) ->
      has_type_exp C e1 (Pts_t tau rho) ->
      has_type_exp C e2 tau ->
      tau = Int_t \/ tau = (Pts_t tau' rho') \/ tau = (Handle_t rho' tau') ->
      has_type_stmt C (Store e2 e1)
  | SS14char : forall C e1 e2 rho,
      wf_context C (Assoc_t rho Char_t) ->
      has_type_exp C e1 (Pts_t Char_t rho) ->
      has_type_exp C e2 Char_t ->
      has_type_stmt C (Storec e2 e1)
  | SS15 : forall C e1 e2 x rho tau,
      wf_context C (Assoc_t rho Unknown_t) ->
      has_type_exp C e1 (Pts_t tau rho) ->
      has_type_exp C e2 tau ->
      has_type_exp C (Var x) (Handle_t rho Unknown_t) ->
      has_type_stmt C (StoreToU x e2 e1)
  | SS15char : forall C e1 e2 x rho tau,
      wf_context C (Assoc_t rho Unknown_t) ->
      has_type_exp C e1 (Pts_t tau rho) ->
      has_type_exp C e2 Char_t ->
      has_type_exp C (Var x) (Handle_t rho Unknown_t) ->
      has_type_stmt C (StorecToU x e2 e1)
  | SS16 : forall C e2 x rho tau,
      wf_context C (Assoc_t rho tau) ->
      has_type_exp C (Var x) (Handle_t rho tau) ->
      has_type_exp C e2 (Pts_t tau rho) ->
      has_type_stmt C (PoolFree (Var x) e2)
  | SS17 : forall Gamma Delta s x rho tau,
      wf_context (Gamma,Delta) tau ->
      Gamma x = None /\ Delta rho = None ->
      has_type_stmt ((extend Gamma x (Handle_t rho tau)),(extend Delta rho tau)) s ->
      has_type_stmt (Gamma,Delta) (PoolInit rho tau x s)

(* C |- tau *)
with wf_context : context -> tipe -> Prop :=
  | SS18 : forall C,
      wf_context C Int_t
  | SS19 : forall C,
      wf_context C Unknown_t
  | SS20 : forall Gamma Delta rho tau,
      Delta rho = Some tau ->
      wf_context (Gamma,Delta) (Assoc_t rho tau)
  | SS21 : forall C rho tau,
      wf_context C (Assoc_t rho tau) ->
      wf_context C (Pts_t tau rho)
  | SS22 : forall Gamma Delta tau rho,
      Delta rho = Some Unknown_t ->
      wf_context (Gamma,Delta) (Pts_t tau rho)
  | SS23 : forall C rho tau,
      wf_context C (Assoc_t rho tau) ->
      wf_context C (Handle_t rho tau)
  | SS24 : forall C,
      wf_context C Char_t.