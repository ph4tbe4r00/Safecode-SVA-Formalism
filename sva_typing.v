Require Export sva_ast.

(** TODO: everything ...
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
  (* missing SS3 and SS4 and SS10 ... how do we handle side conditions? *)
  | SS4char : forall C e rho,
      has_type_exp C e (Pts_t Char_t rho) ->
      has_type_exp C (Val (Region_v rho)) Char_t
  | SS5 : forall C e2 x tau rho,
      has_type_exp C e2 (Pts_t tau rho) ->
      has_type_exp C (Val (Region_v rho)) Unknown_t ->
      has_type_exp C (Var x) (Handle_t rho Unknown_t) ->
      has_type_exp C (LoadFromU x e2) Int_t
  | SS5char : forall C e2 x tau rho,
      has_type_exp C e2 (Pts_t tau rho) ->
      has_type_exp C (Val (Region_v rho)) Unknown_t ->
      has_type_exp C (Var x) (Handle_t rho Unknown_t) ->
      has_type_exp C (LoadcFromU x e2) Char_t
  | SS6 : forall C e2 x tau rho,
      has_type_exp C (Val (Region_v rho)) tau ->
      has_type_exp C (Var x) (Handle_t rho tau) ->
      has_type_exp C e2 Int_t ->
      has_type_exp C (PoolAlloc x e2) (Pts_t tau rho)
  | SS7 : forall C e x tau rho,
      has_type_exp C (Val (Region_v rho)) tau ->
      has_type_exp C (Var x) (Handle_t rho tau) ->
      has_type_exp C e Int_t -> 
      has_type_exp C (CastI2Ptr x e (Pts_t tau rho)) (Pts_t tau rho)
  | SS8 : forall C e tau tau' rho,
      wf_context C tau' ->
      has_type_exp C e (Pts_t tau rho) ->
      has_type_exp C (Cast e (Pts_t tau' rho)) (Pts_t tau' rho)
  | SS9 : forall C e2 e3 x tau rho,
      has_type_exp C (Val (Region_v rho)) tau ->
      has_type_exp C (Var x) (Handle_t rho tau) ->
      has_type_exp C e2 (Pts_t tau rho) ->
      has_type_exp C e3 Int_t ->
      has_type_exp C (Addr x e2 e3) (Pts_t tau rho)
  (* SS10 is missing becuase of side conditions ... *)

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
  (* missing SS14 because of side conditions ... *)
  | SS15 : forall C e1 e2 x rho tau,
      has_type_exp C (Val (Region_v rho)) Unknown_t ->
      has_type_exp C e1 (Pts_t tau rho) ->
      has_type_exp C e2 tau ->
      has_type_exp C (Var x) (Handle_t rho Unknown_t) ->
      has_type_stmt C (StoreToU x e2 e1)
  | SS15char : forall C e1 e2 x rho tau,
      has_type_exp C (Val (Region_v rho)) Unknown_t ->
      has_type_exp C e1 (Pts_t tau rho) ->
      has_type_exp C e2 Char_t ->
      has_type_exp C (Var x) (Handle_t rho Unknown_t) ->
      has_type_stmt C (StorecToU x e2 e1)
  | SS16 : forall C e2 x rho tau,
      has_type_exp C (Val (Region_v rho)) tau ->
      has_type_exp C (Var x) (Handle_t rho tau) ->
      has_type_exp C e2 (Pts_t tau rho) ->
      has_type_stmt C (PoolFree (Var x) e2)
  (* SS17 is missing a side condition ... *)
  | SS17 : forall Gamma Delta s x rho tau,
      wf_context (Gamma,Delta) tau ->
      has_type_stmt ((extend Gamma x (Handle_t rho tau)),(extend Delta rho tau)) s ->
      has_type_stmt (Gamma,Delta) (PoolInit rho tau x s)

(* C |- tau *)
with wf_context : context -> tipe -> Prop :=
  | SS18 : forall C,
      wf_context C Int_t
  | SS19 : forall C,
      wf_context C Unknown_t
  (*
  | SS20 : forall Gamma Delta rho tau,
      Delta rho = Some tau ->
      wf_context (Gamma,Delta) 
  | SS21 : forall *)
  (* | SS22 : forall Gamma Delta tau rho,
      Delta rho = Unknown_t ->
      wf_context (Gamma,Delta) (Pts_t tau rho) *)
  (* | SS23 : forall C rho tau
  | SS24 : forall C,
      wf_context C Char_t*).