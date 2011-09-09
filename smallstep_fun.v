(* CompCert Imports *)
Add LoadPath "./CompCert-Toolkit".
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Smallstep.
Require Import Globalenvs.
Require Import Events.

(* SF imports *)
Require Import SfLib.

Require Import Tactics.

Inductive tm : Type :=
  | tm_const : nat -> tm
  | tm_plus : tm -> tm -> tm.

Inductive value : tm -> Prop :=
  v_const : forall n, value (tm_const n).

Reserved Notation " t '==>' t' " (at level 40).

Inductive toystep : unit -> tm -> trace -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          tm_plus (tm_const n1) (tm_const n2)
      ==> tm_const (Peano.plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 ==> t1' ->
        tm_plus t1 t2 ==> tm_plus t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 ->                     (* <----- n.b. *) 
        t2 ==> t2' ->
        tm_plus v1 t2 ==> tm_plus v1 t2'

  where " t '==>' t' " := (toystep tt t E0 t').

Check star.

Lemma bullshit : forall s1 s2 t,
  star toystep tt s1 t s2 ->
  t = E0.
Proof.
  intros. induction H. reflexivity. subst.
  inversion H; reflexivity.
Qed.

Lemma stepmany_congr_2 : forall t1 t2 t2',
     value t1 ->
     star toystep tt t2 E0 t2' ->
     star toystep tt (tm_plus t1 t2) E0 (tm_plus t1 t2').
Proof.
  intros. induction H0. constructor. inversion IHstar. subst.
  assert (t0 = E0). inversion H0; reflexivity. subst. simpl. 
  apply star_step with E0 (tm_plus t1 s3) E0. constructor. assumption. assumption.
  assumption. simpl. reflexivity.
  subst. assert (t0 = E0). inversion H0; reflexivity. subst.
  assert (t3 = E0). inversion H3; reflexivity. subst. simpl. 
  simpl in H1. simpl in IHstar.
  assert (t4 = E0). apply bullshit in H4. assumption. subst.
  apply star_step with E0 (tm_plus t1 s2) E0.
  constructor. assumption. assumption. apply IHstar. simpl. reflexivity.
Qed.

Record State_toy : Type := state_t {
  term : tm;
  foo : nat
}.

Reserved Notation " t '==>2' t' " (at level 40).

Inductive toystep2 : unit -> State_toy -> trace -> State_toy -> Prop :=
  | ST_PlusConstConst' : forall n1 n2 n3,
      state_t (tm_plus (tm_const n1) (tm_const n2)) n3 ==>2 
      state_t (tm_const (Peano.plus n1 n2)) n3
  | ST_Plus1' : forall t1 t1' t2 n1,
      state_t t1 n1 ==>2 state_t t1' n1 ->
      state_t (tm_plus t1 t2) n1 ==>2 state_t (tm_plus t1' t2) n1
  | ST_Plus2' : forall v1 t2 t2' n1,
      value v1 ->                     
      state_t t2 n1 ==>2 state_t t2' n1 ->
      state_t (tm_plus v1 t2) n1 ==>2 state_t (tm_plus v1 t2') n1

  where " t '==>2' t' " := (toystep2 tt t E0 t').

Lemma bullshit2 : forall s1 s2 t,
  star toystep2 tt s1 t s2 ->
  t = E0.
Proof.
  intros. induction H. reflexivity. subst.
  inversion H; reflexivity.
Qed.

Lemma bullshit3 : forall s1 s2 t,
  toystep2 tt s1 t s2 ->
  t = E0.
Proof.
  intros. inversion H; reflexivity.
Qed.

(* This is a really, really ugly proof. *)
Lemma stepmany_toystep2 : forall s1 s2,
     star toystep2 tt s1 E0 s2 ->
     forall t1 t2 t2' n,
     value t1 ->
     s1 = state_t t2 n ->
     s2 = state_t t2' n ->
     star toystep2 tt (state_t (tm_plus t1 t2) n) E0 (state_t (tm_plus t1 t2') n).
Proof.
  intros s1 s2 H. induction H. intros. subst. inversion H1. subst. constructor.
  intros. assert (t2 = E0). apply bullshit2 in H0. assumption.
  assert (t1 = E0). apply bullshit3 in H. assumption. subst. simpl. 
  destruct s2. apply star_step with E0 (state_t (tm_plus t0 term0) n) E0.
  apply ST_Plus2'. assumption. 
  assert (foo0 = n). inversion H0. reflexivity. inversion H. reflexivity.
  reflexivity. reflexivity. subst. assumption. apply IHstar. assumption.
  assert (foo0 = n). inversion H0. reflexivity. inversion H. reflexivity.
  reflexivity. reflexivity. subst. reflexivity. reflexivity. simpl. reflexivity.
Qed.