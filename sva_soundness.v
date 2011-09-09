(** SVA soundness proofs *)

(* CompCert Imports *)
Add LoadPath "./CompCert-Toolkit".
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Smallstep.
Require Import Globalenvs.
Require Import Events.
Require Import Tactics.

(* SF imports *)
Require Import SfLib.

(* SVA imports *)
Require Import sva_typing.
Require Import sva_dynamic.
Require Import sva_allocator.

(* Coq standard library imports *)
Require Import ListSet.

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

Inductive crazyshit : tipe -> VarEnv -> LiveRegions -> sva_heap -> value -> Prop :=
  | Int_wf : forall n venv l h,
      crazyshit Int_t venv l h (Int n)
  | Pts_wf : forall venv l tau rho h,
      crazyshit (Pts_t tau rho) venv l h Uninit
  | Pts_wf2 : forall venv l tau rho b ri h,
      PTree.get rho l = Some ri ->
      set_In b (RS ri) -> 
      crazyshit (Pts_t tau rho) venv l h (Pointer b Int.zero)
  | Handle_wf : forall venv l tau rho h,
      crazyshit (Handle_t rho tau) venv l h (Region rho)
  | Unknown_wf : forall venv l b h,
      crazyshit Unknown_t venv l h (Byte b).

Inductive wf_env : context -> VarEnv -> LiveRegions -> sva_heap -> Prop :=
  | blah : forall Gamma Delta venv l h,
      ( forall x tau v,
        iff (PTree.get x Gamma = Some tau) (PTree.get x venv = Some v) ) ->
      ( forall rho tau region,
        iff (PTree.get rho Delta = Some tau) (PTree.get rho l = Some region) ) ->
      ( forall x tau v,
        PTree.get x venv = Some v -> 
        has_type_exp (Gamma,Delta) (Var x) tau ->
        crazyshit tau venv l h v ) ->
      ( forall rho tau b ri,
        PTree.get rho l = Some ri ->
        PTree.get rho Delta = Some tau ->
        set_In b (RS ri) ->
        crazyshit tau venv l h (Pointer b Int.zero) ) ->
      ( forall rho ri b,
        PTree.get rho l = Some ri ->
        In b (F ri) ->
        set_In b (RS ri) ) ->
      ( forall rho1 rho2 b1 b2 ri1 ri2,
        rho1 <> rho2 ->
        PTree.get rho1 l = Some ri1 ->
        PTree.get rho2 l = Some ri2 ->
        set_In b1 (RS ri1) -> not (set_In b1 (RS ri2)) /\
        set_In b2 (RS ri2) -> not (set_In b2 (RS ri1)) ) ->
      wf_env (Gamma, Delta) venv l h.

(*
Lemma UpdateLemma1 : forall Gamma Delta venv l h rho tau b o v ri,
  wf_env (Gamma,Delta) venv l h ->
  PTree.get rho Delta = Some tau ->
  PTree.get rho l = Some ri ->
  set_In b (RS ri) ->
  crazyshit tau venv l h v ->
  wf_env (Gamma,Delta) venv l (sva_store h b o Mint32 v).
Proof.
  intros. unfold sva_store.
  destruct (Memory.Mem.store Mint32 (sva_mem h) b (Int.unsigned o) (val2CCval v)).
  inversion H. *)

Definition ge0 := Genv.empty_genv nat nat.

Lemma trace_E0 : forall t1 t2,
  E0 = t1 ** t2 ->
  t1 = E0 /\ t2 = E0.
Proof.
  destruct t1; intros; unfold E0; try solve [ auto | discriminate]. 
Qed.

Lemma TrivWTF : forall venv l e h venv' l' e' h',
  l = l' -> e = e' -> h = h' -> venv = venv' ->
  (state_e venv l e h) = (state_e venv' l' e' h').
  intros. subst. reflexivity.
Qed.

Lemma TrivWTF2 : forall venv l e h venv' l' e' h',
  (state_e venv l e h) = (state_e venv' l' e' h') ->
  (l = l' /\ e = e' /\ h = h' /\ venv = venv').
  intros. split. inversion H. reflexivity.
  split. inversion H. reflexivity.
  split. inversion H. reflexivity.
  inversion H. reflexivity.
Qed.

Lemma MoreTrivWtf : forall venv l e h venv' l' e' h' t,
  step_exp tt (state_e venv l e h) t (state_e venv' l' e' h') ->
  t = E0.
Proof.
  intros. inversion H; simpl; reflexivity.
Qed.

Lemma MoreTrivWtf2 : forall s1 s2 t,
  star step_exp tt s1 t s2 ->
  t = E0.
Proof.
  intros. induction H. reflexivity.
  subst. inversion H; simpl; reflexivity.
Qed.

(* Another ugly proof that we need to Adam "Crush" Chlipala the shit out of *)
Lemma R2star : forall s s',
  star step_exp tt s E0 s' ->
  forall venv l e h venv' l' e' h' x,
  s = (state_e venv l e h) ->
  s' = (state_e venv' l' e' h') ->
  star step_stmt tt (state_s venv l (Assign x e) h) E0 (state_s venv' l' (Assign x e') h').
Proof.
  intros s s' H. induction H. intros. subst. inversion H0. subst. constructor. 
  intros. subst. destruct s2 as (venv'', l'', e'', h''). 
  assert (t1 = E0). apply MoreTrivWtf in H. assumption. subst.
  assert (t2 = E0). apply MoreTrivWtf2 in H0. assumption. subst.
  simpl. apply star_step with E0 (state_s venv'' l'' (Assign x e'') h'') E0.
  apply R2. assumption. apply IHstar. reflexivity. reflexivity. simpl. reflexivity.
Qed.

Theorem thm1 : forall Gamma Delta e tau venv l h,
  has_type_exp (Gamma,Delta) e tau ->
  wf_env (Gamma,Delta) venv l h ->
  ( exists venv', exists l', exists h',
    star step_exp tt (state_e venv l e h) E0 (state_e venv' l' ErrorExp h')) \/
  ( exists v, exists venv', exists l', exists h', 
    star step_exp tt (state_e venv l e h) E0 (state_e venv' l' (Val v) h') /\
    value_v v /\    
    wf_env (Gamma,Delta) venv' l' h' /\
    crazyshit tau venv' l' h' v).
Proof.
  intros. exp_cases (induction H) Case.
  Case "SS0".
    inversion H0. subst. right. evar (v : value). exists v.
    exists venv. exists l. exists h. specialize H4 with x tau v. inversion H4. 
    apply H2 in H1. 
    split. apply star_step with E0 (state_e venv l (Val v) h) E0.
    constructor. assumption. constructor. simpl. reflexivity.
    split. destruct v; constructor. 
    split. assumption. specialize H6 with x tau v. apply H6 in H1. assumption.
    constructor. assumption. apply H3 in H1. assumption.
  Case "SS1".
    inversion H0. right. evar (v : value). exists v. exists venv. exists l. exists h. 
    split. instantiate (1 := (Int n)) in (Value of v). constructor. 
    split. destruct v; constructor.
    split. constructor; assumption.
    constructor.
  Case "SS2".
    remember H0. clear Heqw. apply IHhas_type_exp1 in w. apply IHhas_type_exp2 in H0.
    clear IHhas_type_exp1. clear IHhas_type_exp2. rename H0 into IHhas_type_exp2.
    rename w into IHhas_type_exp1. 
    inversion IHhas_type_exp1.
    SCase "Error".
      left. inversion H0; clear H0. inversion H2; clear H2. inversion H0; clear H0.
      exists x. exists x0. exists x1. 

      (* Need to have one rule that says if we're in the error state, then any
         expression that uses that subexpression also translates to the error state. *)

      admit.
    SCase "Progress".
      admit.
  Case "SS3".
    admit.
  Case "SS4".
    admit.
  Case "SS5".
    admit.
  Case "SS6".
    admit.
  Case "SS7".
    admit.
  Case "SS8".
    admit.
  Case "SS10".
    admit.
Qed.