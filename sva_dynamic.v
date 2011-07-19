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
  (* TODO: a lot more rules ... *)
where " s '==>s' s' " := (stmt_step s s')

with stmt_exp : State_exp -> State_exp -> Prop :=
  | R19 : forall venv l e1 e2 op venv' l' e1',
      state_e venv l e1 ==>e state_e venv' l' e1' ->
      state_e venv l (Binop e1 op e2) ==>e state_e venv' l' (Binop e1' op e2)
  (* TODO: a lot more rules ... *)
where " e '==>e' e' " := (stmt_exp e e').

