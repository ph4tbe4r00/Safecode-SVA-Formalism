Require Export sva_ast.

(** TODO: everything ...
    The plan is to first formalize the technical report, then add control flow, 
    then generalize to full C. *)

(* C |- e : tau *)
Inductive has_type_exp : context -> exp -> tipe -> Prop :=
  | SS0 : forall e c t, has_type_exp c e t.

(* C |- s : tau *)
Inductive has_type_stmt : context -> stmt -> tipe -> Prop :=
  | SS11 : forall s c t, has_type_stmt c s t.

(* C |- tau *)
Inductive wf_type : context -> tipe -> Prop :=
  | SS18 : forall c t, wf_type c t.