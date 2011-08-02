Add LoadPath "./CompCert-Toolkit".
Require Import sva_typing.
Require Import sva_dynamic.
Require Import SfLib.
Require Import Maps.

Tactic Notation "exp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SS0" | Case_aux c "SS1" | Case_aux c "SS2"
  | Case_aux c "SS3" | Case_aux c "SS4" (* | Case_aux c "SS4char" *)
  | Case_aux c "SS5" (* | Case_aux c "SS5char" *) | Case_aux c "SS6"
  | Case_aux c "SS7" | Case_aux c "SS8" (* | Case_aux c "SS9" *)
  | Case_aux c "SS10" ].

(* Lemma 1: Well-formed type from technical report *)
Lemma wf_type : forall (c : context) (e : exp) (tau : tipe),
  has_type_exp c e tau -> wf_context c tau.
Proof.
  intros c e tau H. 
  exp_cases (induction H) Case;
  try (constructor; apply H).
  Case "SS0". apply H.
  Case "SS3". apply H.
  Case "SS4". inversion IHhas_type_exp. apply H7. apply H7.
  Case "SS6". inversion IHhas_type_exp1. constructor. apply H5. apply H7.
  Case "SS7". inversion IHhas_type_exp1. constructor. apply H5. apply H7.
  Case "SS8". apply H.
Qed.

Inductive crazyshit : tipe -> Prop :=
  | Int_wf : crazyshit Int_t
  | Pts_wf : crazyshit Int_t
  | Handle_wf : crazyshit Int_t
  | Unknown_wf : crazyshit Int_t.

Inductive wf_env : context -> VarEnv -> LiveRegions -> Prop :=
  | blah : forall Gamma Delta venv l x rho foo foo' bar bar',
      iff (PTree.get x Gamma = Some foo) (PTree.get x venv = Some foo') ->
      iff (PTree.get rho Delta = Some bar) (PTree.get rho l = Some bar') ->
      (PTree.get x venv = Some foo) -> 
      wf_env (Gamma, Delta) venv l.
