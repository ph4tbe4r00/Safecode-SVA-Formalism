Require Export sva_ast.

(* We could have formalized ES or exp + stmt, but sums are annoying ... 
 * Right now, we can get away with partial_map's because we represent
 * var and nodevar with ids. However, we're not going to run this thing,
 * just prove properties, so this representation should be fine. 
 *
 * We're also ignoring the heap at this point of the formalism ... as the
 * paper claims it doesn't really affect anything. Hopefully that is the
 * case or we're screwed. 
 *)

Definition RS := partial_map value.

Record State_exp : Type := state_e {
  VEnv_exp : partial_map value; (* var -> value *)
  L_exp : partial_map RS; (* nodevar -> region store *)
  ES_exp : exp (* expression *)
}.

Record State_stmt : Type := state_s {
  VEnv_stmt : partial_map value; (* var -> value *)
  L_stmt : partial_map RS; (* nodevar -> region store *)
  ES_stmt : stmt (* statement *)
}.

(* Small-step relations for dynamic checks *)
Reserved Notation " e '==>e' e' " (at level 40).
Reserved Notation " s '==>s' s' " (at level 40).

Inductive stmt_step : State_stmt -> State_stmt -> Prop :=
  | R1 : forall venv l s1 s2 venv' l' s1',
      state_s venv l s1 ==>s state_s venv' l' s1' ->
      state_s venv l (Seq s1 s2) ==>s state_s venv' l' (Seq s1' s2)
  | R2 : forall venv l e x venv' l' e',
      state_e venv l e ==>e state_e venv' l' e' ->
      state_s venv l (Assign x e) ==>s state_s venv' l' (Assign x e')
  | R3 : forall venv l x v v',
      v = Val v' ->
      state_s venv l (Assign x v) ==>s state_s (extend venv x v') l Epsilon
  | R4 : forall venv l e1 e2 venv' l' e1',
      state_e venv l e1 ==>e venv' l' e1' ->
      state_s venv l (Store e1 e2) ==>s state_s venv l' (Store e1' e2)
  | R5 : forall venv l e v v' venv' l' e',
      v = Val v' ->
      state_e venv l e ==>e state_e venv' l' e' ->
      state_s venv l (Store v e) ==>s state_s venv' l' (Store v e')
  | R5char : forall venv l e v v' venv' l' e',
      v = Val v' ->
      state_e venv l e ==>e state_e venv' l' e' ->
      state_s venv l (Storec v e) ==>s state_s venv' l' (Storec v e')
  (* R6 needs update ... *)
  | R7 : forall venv l e1 e2 e3 venv' l' e1',
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_s venv l (StoreToU e1 e2 e3) ==>s state_s venv' l' (StoreToU e1' e2 e3)
  | R7char : forall venv l e1 e2 e3 venv' l' e1',
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_s venv l (StorecToU e1 e2 e3) ==>s state_s venv' l' (StorecToU e1' e2 e3)
  | R8 : forall venv l v1 v1' e2 e3 venv' l' e2',
      v1 = Val v1' ->
      state_e venv l e2 ==>e state_e venv' l' e2' ->
      state_s venv l (StoreToU v1 e2 e3) ==>s state_s venv' l' (StoreToU v1 e2' e3)
  | R8char : forall venv l v1 v1' e2 e3 venv' l' e2',
      v1 = Val v1' ->
      state_e venv l e2 ==>e state_e venv' l' e2' ->
      state_s venv l (StorecToU v1 e2 e3) ==>s state_s venv' l' (StorecToU v1 e2' e3)
  | R9 : forall venv l v1 v1' v2 v2' e3 venv' l' e3',
      v1 = Val v1' ->
      v2 = Val v2' ->
      state_e venv l e3 ==>e state_e venv' l' e3' ->
      state_s venv l (StoreToU v1 v2 e3) ==>s state_s venv' l' (StoreToU v1 v2 e3')
  | R9char : forall venv l v1 v1' v2 v2' e3 venv' l' e3',
      v1 = Val v1' ->
      v2 = Val v2' ->
      state_e venv l e3 ==>e state_e venv' l' e3' ->
      state_s venv l (StorecToU v1 v2 e3) ==>s state_s venv' l' (StorecToU v1 v2 e3')
  (* R10 need update ... *)
  (*
  | R11 : forall venv l v1 v1' v2 v2' rho,
      v1 = Val v1' ->
      v2 = Val v2' ->
      state_s venv l (StorecToU (Region_v rho) v1 v2) ==>s state_s venv
  *)
  | R12 : forall venv l e1 e2 venv' l' e1',
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_s venv l (PoolFree e1 e2) ==>s state_s venv' l' (PoolFree e1' e2)
  | R13 : forall venv l v v' e2 venv' l' e2',
      v = Val v' ->
      state_e venv l e2 ==>e state_e venv' l' e2' ->
      state_s venv l (PoolFree v e2) ==>s state_s venv' l' (PoolFree v e2')
  (* R14 and R15 need union ... *)
  | R16 : forall venv l s venv' l' s' rho,
      state_s venv l s ==>s state_s venv' l' s' ->
      state_s venv l (PoolPop s rho) ==>s state_s venv' l' (PoolPop s' rho)
  (* R17 needs union *)
where " s '==>s' s' " := (stmt_step s s')

with stmt_exp : State_exp -> State_exp -> Prop :=
  | R18 : forall venv x v l,
      state_e (extend venv x v) l (Var x) ==>e state_e (extend venv x v) l (Val v)
  | R19 : forall venv l e1 e2 op venv' l' e1',
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_e venv l (Binop e1 op e2) ==>e state_e venv' l' (Binop e1' op e2)
  | R20 : forall venv l v e2 op venv' l' e2',
      Val v ->
      state_e venv l e2 ==>e state_e venv' l' e2' ->
      state_e venv l (Binop v op e2) ==>e state_e venv' l' (Binop v op e2')
  | R21 : forall venv l v1 v1' v2 v2' op,
      v1 = Val v1' ->
      v2 = Val v2' ->
      (* warning ... right now this is a hack, but we don't need to do a
       * computation? *)
      state_e venv l (Binop v1 op v2) ==>e state_e venv l v1
  | R22 : forall venv l e venv' l' e',
      state_e venv l e ==>e state_e venv' l' e' ->
      state_e venv l (Load e) ==>e state_e venv' l' (Load e')
  | R22char : forall venv l e venv' l' e',
      state_e venv l e ==>e state_e venv' l' e' ->
      state_e venv l (Loadc e) ==>e state_e venv' l' (Loadc e')
  (* R23 needs getvalue *)
  | R24 : forall venv l e1 e2 venv' l' e1',
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_e venv l (LoadFromU e1 e2) ==>e state_e venv l (LoadFromU e1' e2)
  | R24char : forall venv l e1 e2 venv' l' e1',
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_e venv l (LoadcFromU e1 e2) ==>e state_e venv l (LoadcFromU e1' e2)
  | R25 : forall venv l v v' e2 venv' l' e2',
      v = Val v' ->
      state_e venv l e2 ==>e state_e venv' l' e2' ->
      state_e venv l (LoadFromU v e2) ==>e state_e venv l (LoadFromU v e2')
  | R25char : forall venv l v v' e2 venv' l' e2',
      v = Val v' ->
      state_e venv l e2 ==>e state_e venv' l' e2' ->
      state_e venv l (LoadcFromU v e2) ==>e state_e venv l (LoadcFromU v e2')
  (* R26 looks beastly ... *)
  (* R27 needs getvalue ... *)
  | R28 : forall venv l e tau,
      state_e venv l (Cast e tau) ==>e state_e venv l e
  | R29 : forall venv l e1 e2 venv' l' e1' tau,
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_e venv l (CastI2Ptr e1 e2 tau) ==>e state_e venv' l' (CastI2Ptr e1' e2 tau)
  | R30 : forall venv l v v' e venv' l' e' tau,
      v = Val v' ->
      state_e venv l e ==>e state_e venv' l' e' ->
      state_e venv l (CastI2Ptr v e tau) ==>e state_e venv' l' (CastI2Ptr v e' tau)
  (*
  | R31 : forall venv l rho v v' v'' tau,
      v = Val v' ->
      (l rho) v = Some v'' ->
      state_e venv l (CastI2Ptr (Region_v rho) v tau) ==>e state_e venv l v
  *)
  | R32 : forall venv l e1 e2 venv' l' e1',
      state_e venv l e1 ==>e state_e venv l' e1' ->
      state_e venv l (PoolAlloc e1 e2) ==>e state_e venv' l' (PoolAlloc e1' e2)
  | R33 : forall venv l v v' e2 venv' l' e2',
      v = Val v' ->
      state_e venv l e2 ==>e state_e venv l' e2' ->
      state_e venv l (PoolAlloc v e2) ==>e state_e venv' l' (PoolAlloc v e2')
  (* R34, R35, R36 need union *)
where " e '==>e' e' " := (stmt_exp e e').

