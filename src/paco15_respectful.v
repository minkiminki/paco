Require Import paco15.
Require Export Program.
Set Implicit Arguments.

Section Respectful15.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.
Variable T14 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), Type.

Local Notation rel := (rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone15 gf.

Inductive sound15 (clo: rel -> rel): Prop :=
| sound15_intro
    (MON: monotone15 clo)
    (SOUND:
       forall r (PFIX: r <15= gf (clo r)),
         r <15= paco15 gf bot15)
.
Hint Constructors sound15.

Structure respectful15 (clo: rel -> rel) : Prop :=
  respectful15_intro {
      MON: monotone15 clo;
      RESPECTFUL:
        forall l r (LE: l <15= r) (GF: l <15= gf r),
          clo l <15= gf (clo r);
    }.
Hint Constructors respectful15.

Inductive gres15 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 : Prop :=
| gres15_intro
    clo
    (RES: respectful15 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14)
.
Hint Constructors gres15.
Lemma gfclo15_mon: forall clo, sound15 clo -> monotone15 (compose gf clo).
Proof. intros; destruct H; eauto using gf_mon. Qed.
Hint Resolve gfclo15_mon : paco.

Lemma sound15_is_gf: forall clo (UPTO: sound15 clo),
    paco15 (compose gf clo) bot15 <15= paco15 gf bot15.
Proof.
  intros. punfold PR. edestruct UPTO.
  eapply (SOUND (paco15 (compose gf clo) bot15)); [|eauto].
  intros. punfold PR0.
  eapply (gfclo15_mon UPTO); eauto. intros. destruct PR1; eauto. contradiction.
Qed.

Lemma respectful15_is_sound15: respectful15 <1= sound15.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \15/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; eauto.
  intros. set (rr e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 := exists n, rclo clo n r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14).
  assert (rr x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) by (exists 0; eauto); clear PR.
  cut (forall n, rclo clo n r <15= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 H; pcofix CIH; intros.
    unfold rr in *; destruct H0; eauto 10 using gf_mon. }
  induction n; intros; [simpl; eauto using gf_mon|].
  simpl in *; destruct PR; [eauto using gf_mon|].
  eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; instantiate; simpl; eauto.
Qed.

Lemma respectful15_compose
      clo0 clo1
      (RES0: respectful15 clo0)
      (RES1: respectful15 clo1):
  respectful15 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; eauto.
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; eauto.
    + intros. eapply RESPECTFUL1; eauto.
Qed.

Lemma grespectful15_respectful15: respectful15 gres15.
Proof.
  econstructor; repeat intro.
  - destruct IN; destruct RES; exists clo; eauto.
  - destruct PR; destruct RES; eapply gf_mon with (r:=clo r); eauto.
Qed.

Lemma gfgres15_mon: monotone15 (compose gf gres15).
Proof.
  destruct grespectful15_respectful15; eauto using gf_mon.
Qed.
Hint Resolve gfgres15_mon : paco.

Lemma grespectful15_greatest: forall clo (RES: respectful15 clo), clo <16= gres15.
Proof. eauto. Qed.

Lemma grespectful15_incl: forall r, r <15= gres15 r.
Proof.
  intros; eexists (fun x => x); eauto.
Qed.
Hint Resolve grespectful15_incl.

Lemma grespectful15_compose: forall clo (RES: respectful15 clo) r,
    clo (gres15 r) <15= gres15 r.
Proof.
  intros; eapply grespectful15_greatest with (clo := compose clo gres15);
    eauto using respectful15_compose, grespectful15_respectful15.
Qed.

Lemma grespectful15_incl_rev: forall r,
    gres15 (paco15 (compose gf gres15) r) <15= paco15 (compose gf gres15) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful15_compose, grespectful15_respectful15.
  destruct grespectful15_respectful15; eapply RESPECTFUL0, PR; intros; [apply grespectful15_incl; eauto|].
  punfold PR0.
  eapply gfgres15_mon; eauto; intros; destruct PR1; eauto.
Qed.

Inductive rclo15 clo (r: rel): rel :=
| rclo15_incl
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14):
    @rclo15 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
| rclo15_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
    (R': r' <15= rclo15 clo r)
    (CLOR':clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14):
    @rclo15 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
| rclo15_gf
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
    (R': r' <15= rclo15 clo r)
    (CLOR':@gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14):
    @rclo15 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
.
Lemma rclo15_mon clo:
  monotone15 (rclo15 clo).
Proof.
  repeat intro. induction IN; eauto using rclo15.
Qed.
Hint Resolve rclo15_mon: paco.

Lemma rclo15_base
      clo
      (MON: monotone15 clo):
  clo <16= rclo15 clo.
Proof.
  simpl. intros. econstructor 2; eauto.
  eapply MON; eauto using rclo15.
Qed.

Lemma rclo15_step
      (clo: rel -> rel) r:
  clo (rclo15 clo r) <15= rclo15 clo r.
Proof.
  intros. econstructor 2; eauto.
Qed.

Lemma rclo15_rclo15
      clo r
      (MON: monotone15 clo):
  rclo15 clo (rclo15 clo r) <15= rclo15 clo r.
Proof.
  intros. induction PR; eauto using rclo15.
Qed.

Structure weak_respectful15 (clo: rel -> rel) : Prop :=
  weak_respectful15_intro {
      WEAK_MON: monotone15 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <15= r) (GF: l <15= gf r),
          clo l <15= gf (rclo15 clo r);
    }.
Hint Constructors weak_respectful15.

Lemma weak_respectful15_respectful15
      clo (RES: weak_respectful15 clo):
  respectful15 (rclo15 clo).
Proof.
  inversion RES. econstructor; eauto with paco. intros.
  induction PR; intros.
  - eapply gf_mon; eauto. intros.
    apply rclo15_incl. auto.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo15_mon; eauto.
    + intros. apply rclo15_rclo15; auto.
  - eapply gf_mon; eauto using rclo15.
Qed.

Lemma upto15_init:
  paco15 (compose gf gres15) bot15 <15= paco15 gf bot15.
Proof.
  apply sound15_is_gf; eauto.
  apply respectful15_is_sound15.
  apply grespectful15_respectful15.
Qed.

Lemma upto15_final:
  paco15 gf <16= paco15 (compose gf gres15).
Proof.
  pcofix CIH. intros. punfold PR. pfold.
  eapply gf_mon; [|apply grespectful15_incl].
  eapply gf_mon; [eauto|]. intros. right. inversion PR0; auto.
Qed.

Lemma upto15_step
      r clo (RES: weak_respectful15 clo):
  clo (paco15 (compose gf gres15) r) <15= paco15 (compose gf gres15) r.
Proof.
  intros. apply grespectful15_incl_rev.
  assert (RES' := weak_respectful15_respectful15 RES).
  eapply grespectful15_greatest. eauto.
  eapply rclo15_base; eauto.
  inversion RES. auto.
Qed.

Lemma upto15_step_under
      r clo (RES: weak_respectful15 clo):
  clo (gres15 r) <15= gres15 r.
Proof.
  intros. apply weak_respectful15_respectful15 in RES; eauto.
  eapply grespectful15_compose; eauto. eauto using rclo15.
Qed.

End Respectful15.

Hint Constructors sound15.
Hint Constructors respectful15.
Hint Constructors gres15.
Hint Resolve gfclo15_mon : paco.
Hint Resolve gfgres15_mon : paco.
Hint Resolve grespectful15_incl.
Hint Resolve rclo15_mon: paco.
Hint Constructors weak_respectful15.

Ltac pupto15_init := eapply upto15_init; eauto with paco.
Ltac pupto15_final := first [eapply upto15_final; eauto with paco | eapply grespectful15_incl].
Ltac pupto15 H := first [eapply upto15_step|eapply upto15_step_under]; [|eapply H|]; eauto with paco.
