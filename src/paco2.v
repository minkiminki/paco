Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO2.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.

Record sig2T :=
  exist2T { 
      proj2T0: @T0;
      proj2T1: @T1 proj2T0;
    }.

Definition uncurry2 (R: rel2 T0 T1): rel1 sig2T := fun x => R (proj2T0 x) (proj2T1 x).

Definition curry2 (R: rel1 sig2T): rel2 T0 T1 :=
  fun x0 x1 => R (exist2T x1).

Lemma uncurry_map2 r0 r1 (LE : r0 <2== r1) : uncurry2 r0 <1== uncurry2 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev2 r0 r1 (LE: uncurry2 r0 <1== uncurry2 r1) : r0 <2== r1.
Proof.
  repeat_intros 2. intros H. apply (LE (exist2T x1) H).
Qed.

Lemma curry_map2 r0 r1 (LE: r0 <1== r1) : curry2 r0 <2== curry2 r1.
Proof. 
  repeat_intros 2. intros H. apply (LE (exist2T x1) H).
Qed.

Lemma curry_map_rev2 r0 r1 (LE: curry2 r0 <2== curry2 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_2 r : curry2 (uncurry2 r) <2== r.
Proof. unfold le2. repeat_intros 2. intros H. apply H. Qed.

Lemma uncurry_bij2_2 r : r <2== curry2 (uncurry2 r).
Proof. unfold le2. repeat_intros 2. intros H. apply H. Qed.

Lemma curry_bij1_2 r : uncurry2 (curry2 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_2 r : r <1== uncurry2 (curry2 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_2 r0 r1 (LE: uncurry2 r0 <1== r1) : r0 <2== curry2 r1.
Proof.
  apply uncurry_map_rev2. eapply le1_trans; [apply LE|]. apply curry_bij2_2.
Qed.

Lemma uncurry_adjoint2_2 r0 r1 (LE: r0 <2== curry2 r1) : uncurry2 r0 <1== r1.
Proof.
  apply curry_map_rev2. eapply le2_trans; [|apply LE]. apply uncurry_bij2_2.
Qed.

Lemma curry_adjoint1_2 r0 r1 (LE: curry2 r0 <2== r1) : r0 <1== uncurry2 r1.
Proof.
  apply curry_map_rev2. eapply le2_trans; [apply LE|]. apply uncurry_bij2_2.
Qed.

Lemma curry_adjoint2_2 r0 r1 (LE: r0 <1== uncurry2 r1) : curry2 r0 <2== r1.
Proof.
  apply uncurry_map_rev2. eapply le1_trans; [|apply LE]. apply curry_bij1_2.
Qed.

(** ** Predicates of Arity 2
*)

Definition paco2(gf : rel2 T0 T1 -> rel2 T0 T1)(r: rel2 T0 T1) : rel2 T0 T1 :=
  curry2 (paco (fun R0 => uncurry2 (gf (curry2 R0))) (uncurry2 r)).

Definition upaco2(gf : rel2 T0 T1 -> rel2 T0 T1)(r: rel2 T0 T1) := paco2 gf r \2/ r.
Arguments paco2 : clear implicits.
Arguments upaco2 : clear implicits.
Hint Unfold upaco2.

Definition monotone2 (gf: rel2 T0 T1 -> rel2 T0 T1) :=
  forall x0 x1 r r' (IN: gf r x0 x1) (LE: r <2= r'), gf r' x0 x1.

Definition _monotone2 (gf: rel2 T0 T1 -> rel2 T0 T1) :=
  forall r r'(LE: r <2= r'), gf r <2== gf r'.

Lemma monotone2_eq (gf: rel2 T0 T1 -> rel2 T0 T1) :
  monotone2 gf <-> _monotone2 gf.
Proof. unfold monotone2, _monotone2, le2. split; intros; eapply H; eassumption. Qed.

Lemma monotone2_map (gf: rel2 T0 T1 -> rel2 T0 T1)
      (MON: _monotone2 gf) :
  _monotone (fun R0 => uncurry2 (gf (curry2 R0))).
Proof.
  repeat_intros 3. apply uncurry_map2. apply MON; apply curry_map2; assumption.
Qed.

Section Arg2.

Variable gf : rel2 T0 T1 -> rel2 T0 T1.
Arguments gf : clear implicits.

Theorem _paco2_mon: _monotone2 (paco2 gf).
Proof.
  repeat_intros 3. eapply curry_map2, _paco_mon; apply uncurry_map2; assumption.
Qed.

Theorem _paco2_acc: forall
  l r (OBG: forall rr (INC: r <2== rr) (CIH: l <2== rr), l <2== paco2 gf rr),
  l <2== paco2 gf r.
Proof.
  intros. apply uncurry_adjoint1_2.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_2 in INC. apply uncurry_adjoint1_2 in CIH.
  apply uncurry_adjoint2_2.
  eapply le2_trans. eapply (OBG _ INC CIH).
  apply curry_map2.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_2.
Qed.

Theorem _paco2_mult_strong: forall r,
  paco2 gf (upaco2 gf r) <2== paco2 gf r.
Proof.
  intros. apply curry_map2.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco2_fold: forall r,
  gf (upaco2 gf r) <2== paco2 gf r.
Proof.
  intros. apply uncurry_adjoint1_2.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco2_unfold: forall (MON: _monotone2 gf) r,
  paco2 gf r <2== gf (upaco2 gf r).
Proof.
  intros. apply curry_adjoint2_2.
  eapply _paco_unfold; apply monotone2_map; assumption.
Qed.

Theorem paco2_acc: forall
  l r (OBG: forall rr (INC: r <2= rr) (CIH: l <2= rr), l <2= paco2 gf rr),
  l <2= paco2 gf r.
Proof.
  apply _paco2_acc.
Qed.

Theorem paco2_mon: monotone2 (paco2 gf).
Proof.
  apply monotone2_eq.
  apply _paco2_mon.
Qed.

Theorem upaco2_mon: monotone2 (upaco2 gf).
Proof.
  repeat_intros 4. intros R  LE0.
  destruct R.
  - left. eapply paco2_mon. apply H. apply LE0.
  - right. apply LE0, H.
Qed.
Theorem paco2_mult_strong: forall r,
  paco2 gf (upaco2 gf r) <2= paco2 gf r.
Proof.
  apply _paco2_mult_strong.
Qed.

Corollary paco2_mult: forall r,
  paco2 gf (paco2 gf r) <2= paco2 gf r.
Proof. intros; eapply paco2_mult_strong, paco2_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco2_fold: forall r,
  gf (upaco2 gf r) <2= paco2 gf r.
Proof.
  apply _paco2_fold.
Qed.

Theorem paco2_unfold: forall (MON: monotone2 gf) r,
  paco2 gf r <2= gf (upaco2 gf r).
Proof.
  repeat_intros 1. eapply _paco2_unfold; apply monotone2_eq; assumption.
Qed.

End Arg2.

Arguments paco2_acc : clear implicits.
Arguments paco2_mon : clear implicits.
Arguments upaco2_mon : clear implicits.
Arguments paco2_mult_strong : clear implicits.
Arguments paco2_mult : clear implicits.
Arguments paco2_fold : clear implicits.
Arguments paco2_unfold : clear implicits.

Global Instance paco2_inst  (gf : rel2 T0 T1->_) r x0 x1 : paco_class (paco2 gf r x0 x1) :=
{ pacoacc    := paco2_acc gf;
  pacomult   := paco2_mult gf;
  pacofold   := paco2_fold gf;
  pacounfold := paco2_unfold gf }.

Lemma upaco2_clear gf x0 x1:
  upaco2 gf bot2 x0 x1 <-> paco2 gf bot2 x0 x1.
Proof. split; intros; [destruct H;[apply H|destruct H]|left; apply H]. Qed.

End PACO2.

Global Opaque paco2.

Hint Unfold upaco2.
Hint Resolve paco2_fold.
Hint Unfold monotone2.

