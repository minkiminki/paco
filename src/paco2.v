Require Export paconotation pacotacuser.
Require Import pacotac.
Set Implicit Arguments.

(** ** Predicates of Arity 2
*)

Section Arg2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable gf : rel2 T0 T1 -> rel2 T0 T1.
Arguments gf : clear implicits.

CoInductive paco2( r: rel2 T0 T1) x0 x1 : Prop :=
| paco2_pfold pco
    (LE : pco <2= (paco2 r \2/ r))
    (SIM: gf pco x0 x1)
.
Definition upaco2( r: rel2 T0 T1) := paco2 r \2/ r.
End Arg2_def.
Arguments paco2 [ T0 T1 ].
Arguments upaco2 [ T0 T1 ].
Hint Unfold upaco2.

Section Arg2_2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable gf_0 gf_1 : rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

CoInductive paco2_2_0( r_0 r_1: rel2 T0 T1) x0 x1 : Prop :=
| paco2_2_0_pfold pco_0 pco_1
    (LE : pco_0 <2= (paco2_2_0 r_0 r_1 \2/ r_0))
    (LE : pco_1 <2= (paco2_2_1 r_0 r_1 \2/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0 x1)
with paco2_2_1( r_0 r_1: rel2 T0 T1) x0 x1 : Prop :=
| paco2_2_1_pfold pco_0 pco_1
    (LE : pco_0 <2= (paco2_2_0 r_0 r_1 \2/ r_0))
    (LE : pco_1 <2= (paco2_2_1 r_0 r_1 \2/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0 x1)
.
Definition upaco2_2_0( r_0 r_1: rel2 T0 T1) := paco2_2_0 r_0 r_1 \2/ r_0.
Definition upaco2_2_1( r_0 r_1: rel2 T0 T1) := paco2_2_1 r_0 r_1 \2/ r_1.
End Arg2_2_def.
Arguments paco2_2_0 [ T0 T1 ].
Arguments upaco2_2_0 [ T0 T1 ].
Hint Unfold upaco2_2_0.
Arguments paco2_2_1 [ T0 T1 ].
Arguments upaco2_2_1 [ T0 T1 ].
Hint Unfold upaco2_2_1.

Section Arg2_3_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable gf_0 gf_1 gf_2 : rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

CoInductive paco2_3_0( r_0 r_1 r_2: rel2 T0 T1) x0 x1 : Prop :=
| paco2_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <2= (paco2_3_0 r_0 r_1 r_2 \2/ r_0))
    (LE : pco_1 <2= (paco2_3_1 r_0 r_1 r_2 \2/ r_1))
    (LE : pco_2 <2= (paco2_3_2 r_0 r_1 r_2 \2/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0 x1)
with paco2_3_1( r_0 r_1 r_2: rel2 T0 T1) x0 x1 : Prop :=
| paco2_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <2= (paco2_3_0 r_0 r_1 r_2 \2/ r_0))
    (LE : pco_1 <2= (paco2_3_1 r_0 r_1 r_2 \2/ r_1))
    (LE : pco_2 <2= (paco2_3_2 r_0 r_1 r_2 \2/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0 x1)
with paco2_3_2( r_0 r_1 r_2: rel2 T0 T1) x0 x1 : Prop :=
| paco2_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <2= (paco2_3_0 r_0 r_1 r_2 \2/ r_0))
    (LE : pco_1 <2= (paco2_3_1 r_0 r_1 r_2 \2/ r_1))
    (LE : pco_2 <2= (paco2_3_2 r_0 r_1 r_2 \2/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0 x1)
.
Definition upaco2_3_0( r_0 r_1 r_2: rel2 T0 T1) := paco2_3_0 r_0 r_1 r_2 \2/ r_0.
Definition upaco2_3_1( r_0 r_1 r_2: rel2 T0 T1) := paco2_3_1 r_0 r_1 r_2 \2/ r_1.
Definition upaco2_3_2( r_0 r_1 r_2: rel2 T0 T1) := paco2_3_2 r_0 r_1 r_2 \2/ r_2.
End Arg2_3_def.
Arguments paco2_3_0 [ T0 T1 ].
Arguments upaco2_3_0 [ T0 T1 ].
Hint Unfold upaco2_3_0.
Arguments paco2_3_1 [ T0 T1 ].
Arguments upaco2_3_1 [ T0 T1 ].
Hint Unfold upaco2_3_1.
Arguments paco2_3_2 [ T0 T1 ].
Arguments upaco2_3_2 [ T0 T1 ].
Hint Unfold upaco2_3_2.

(* Less than or equal - internal use only *)
Notation "p <_paco_2= q" :=
  (forall _paco_x0 _paco_x1 (PR: p _paco_x0 _paco_x1 : Prop), q _paco_x0 _paco_x1 : Prop)
  (at level 50, no associativity).

(** 1 Mutual Coinduction *)

Section Arg2_1.

Definition monotone2 T0 T1 (gf: rel2 T0 T1 -> rel2 T0 T1) :=
  forall x0 x1 r r' (IN: gf r x0 x1) (LE: r <2= r'), gf r' x0 x1.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable gf : rel2 T0 T1 -> rel2 T0 T1.
Arguments gf : clear implicits.

Theorem paco2_acc: forall
  l r (OBG: forall rr (INC: r <2= rr) (CIH: l <_paco_2= rr), l <_paco_2= paco2 gf rr),
  l <2= paco2 gf r.
Proof.
  intros; assert (SIM: paco2 gf (r \2/ l) x0 x1) by eauto.
  clear PR; repeat (try left; do 3 paco_revert; paco_cofix_auto).
Qed.

Theorem paco2_mon: monotone2 (paco2 gf).
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Theorem paco2_mult_strong: forall r,
  paco2 gf (upaco2 gf r) <2= paco2 gf r.
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Corollary paco2_mult: forall r,
  paco2 gf (paco2 gf r) <2= paco2 gf r.
Proof. intros; eapply paco2_mult_strong, paco2_mon; eauto. Qed.

Theorem paco2_fold: forall r,
  gf (upaco2 gf r) <2= paco2 gf r.
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco2_unfold: forall (MON: monotone2 gf) r,
  paco2 gf r <2= gf (upaco2 gf r).
Proof. unfold monotone2; intros; destruct PR; eauto. Qed.

End Arg2_1.

Hint Unfold monotone2.
Hint Resolve paco2_fold.

Arguments paco2_acc            [ T0 T1 ].
Arguments paco2_mon            [ T0 T1 ].
Arguments paco2_mult_strong    [ T0 T1 ].
Arguments paco2_mult           [ T0 T1 ].
Arguments paco2_fold           [ T0 T1 ].
Arguments paco2_unfold         [ T0 T1 ].

Instance paco2_inst  T0 T1 (gf : rel2 T0 T1->_) r x0 x1 : paco_class (paco2 gf r x0 x1) :=
{ pacoacc    := paco2_acc gf;
  pacomult   := paco2_mult gf;
  pacofold   := paco2_fold gf;
  pacounfold := paco2_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg2_2.

Definition monotone2_2 T0 T1 (gf: rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1) :=
  forall x0 x1 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1) (LE_0: r_0 <2= r'_0)(LE_1: r_1 <2= r'_1), gf r'_0 r'_1 x0 x1.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable gf_0 gf_1 : rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem paco2_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <2= rr) (CIH: l <_paco_2= rr), l <_paco_2= paco2_2_0 gf_0 gf_1 rr r_1),
  l <2= paco2_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco2_2_0 gf_0 gf_1 (r_0 \2/ l) r_1 x0 x1) by eauto.
  clear PR; repeat (try left; do 3 paco_revert; paco_cofix_auto).
Qed.

Theorem paco2_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <2= rr) (CIH: l <_paco_2= rr), l <_paco_2= paco2_2_1 gf_0 gf_1 r_0 rr),
  l <2= paco2_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco2_2_1 gf_0 gf_1 r_0 (r_1 \2/ l) x0 x1) by eauto.
  clear PR; repeat (try left; do 3 paco_revert; paco_cofix_auto).
Qed.

Theorem paco2_2_0_mon: monotone2_2 (paco2_2_0 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Theorem paco2_2_1_mon: monotone2_2 (paco2_2_1 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Theorem paco2_2_0_mult_strong: forall r_0 r_1,
  paco2_2_0 gf_0 gf_1 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1) <2= paco2_2_0 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Theorem paco2_2_1_mult_strong: forall r_0 r_1,
  paco2_2_1 gf_0 gf_1 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1) <2= paco2_2_1 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Corollary paco2_2_0_mult: forall r_0 r_1,
  paco2_2_0 gf_0 gf_1 (paco2_2_0 gf_0 gf_1 r_0 r_1) (paco2_2_1 gf_0 gf_1 r_0 r_1) <2= paco2_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco2_2_0_mult_strong, paco2_2_0_mon; eauto. Qed.

Corollary paco2_2_1_mult: forall r_0 r_1,
  paco2_2_1 gf_0 gf_1 (paco2_2_0 gf_0 gf_1 r_0 r_1) (paco2_2_1 gf_0 gf_1 r_0 r_1) <2= paco2_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco2_2_1_mult_strong, paco2_2_1_mon; eauto. Qed.

Theorem paco2_2_0_fold: forall r_0 r_1,
  gf_0 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1) <2= paco2_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco2_2_1_fold: forall r_0 r_1,
  gf_1 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1) <2= paco2_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco2_2_0_unfold: forall (MON: monotone2_2 gf_0) (MON: monotone2_2 gf_1) r_0 r_1,
  paco2_2_0 gf_0 gf_1 r_0 r_1 <2= gf_0 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone2_2; intros; destruct PR; eauto. Qed.

Theorem paco2_2_1_unfold: forall (MON: monotone2_2 gf_0) (MON: monotone2_2 gf_1) r_0 r_1,
  paco2_2_1 gf_0 gf_1 r_0 r_1 <2= gf_1 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone2_2; intros; destruct PR; eauto. Qed.

End Arg2_2.

Hint Unfold monotone2_2.
Hint Resolve paco2_2_0_fold.
Hint Resolve paco2_2_1_fold.

Arguments paco2_2_0_acc            [ T0 T1 ].
Arguments paco2_2_1_acc            [ T0 T1 ].
Arguments paco2_2_0_mon            [ T0 T1 ].
Arguments paco2_2_1_mon            [ T0 T1 ].
Arguments paco2_2_0_mult_strong    [ T0 T1 ].
Arguments paco2_2_1_mult_strong    [ T0 T1 ].
Arguments paco2_2_0_mult           [ T0 T1 ].
Arguments paco2_2_1_mult           [ T0 T1 ].
Arguments paco2_2_0_fold           [ T0 T1 ].
Arguments paco2_2_1_fold           [ T0 T1 ].
Arguments paco2_2_0_unfold         [ T0 T1 ].
Arguments paco2_2_1_unfold         [ T0 T1 ].

Instance paco2_2_0_inst  T0 T1 (gf_0 gf_1 : rel2 T0 T1->_) r_0 r_1 x0 x1 : paco_class (paco2_2_0 gf_0 gf_1 r_0 r_1 x0 x1) :=
{ pacoacc    := paco2_2_0_acc gf_0 gf_1;
  pacomult   := paco2_2_0_mult gf_0 gf_1;
  pacofold   := paco2_2_0_fold gf_0 gf_1;
  pacounfold := paco2_2_0_unfold gf_0 gf_1 }.

Instance paco2_2_1_inst  T0 T1 (gf_0 gf_1 : rel2 T0 T1->_) r_0 r_1 x0 x1 : paco_class (paco2_2_1 gf_0 gf_1 r_0 r_1 x0 x1) :=
{ pacoacc    := paco2_2_1_acc gf_0 gf_1;
  pacomult   := paco2_2_1_mult gf_0 gf_1;
  pacofold   := paco2_2_1_fold gf_0 gf_1;
  pacounfold := paco2_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg2_3.

Definition monotone2_3 T0 T1 (gf: rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1) :=
  forall x0 x1 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1) (LE_0: r_0 <2= r'_0)(LE_1: r_1 <2= r'_1)(LE_2: r_2 <2= r'_2), gf r'_0 r'_1 r'_2 x0 x1.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable gf_0 gf_1 gf_2 : rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem paco2_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <2= rr) (CIH: l <_paco_2= rr), l <_paco_2= paco2_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <2= paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco2_3_0 gf_0 gf_1 gf_2 (r_0 \2/ l) r_1 r_2 x0 x1) by eauto.
  clear PR; repeat (try left; do 3 paco_revert; paco_cofix_auto).
Qed.

Theorem paco2_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <2= rr) (CIH: l <_paco_2= rr), l <_paco_2= paco2_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <2= paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco2_3_1 gf_0 gf_1 gf_2 r_0 (r_1 \2/ l) r_2 x0 x1) by eauto.
  clear PR; repeat (try left; do 3 paco_revert; paco_cofix_auto).
Qed.

Theorem paco2_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <2= rr) (CIH: l <_paco_2= rr), l <_paco_2= paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <2= paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 (r_2 \2/ l) x0 x1) by eauto.
  clear PR; repeat (try left; do 3 paco_revert; paco_cofix_auto).
Qed.

Theorem paco2_3_0_mon: monotone2_3 (paco2_3_0 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Theorem paco2_3_1_mon: monotone2_3 (paco2_3_1 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Theorem paco2_3_2_mon: monotone2_3 (paco2_3_2 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Theorem paco2_3_0_mult_strong: forall r_0 r_1 r_2,
  paco2_3_0 gf_0 gf_1 gf_2 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Theorem paco2_3_1_mult_strong: forall r_0 r_1 r_2,
  paco2_3_1 gf_0 gf_1 gf_2 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Theorem paco2_3_2_mult_strong: forall r_0 r_1 r_2,
  paco2_3_2 gf_0 gf_1 gf_2 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Corollary paco2_3_0_mult: forall r_0 r_1 r_2,
  paco2_3_0 gf_0 gf_1 gf_2 (paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco2_3_0_mult_strong, paco2_3_0_mon; eauto. Qed.

Corollary paco2_3_1_mult: forall r_0 r_1 r_2,
  paco2_3_1 gf_0 gf_1 gf_2 (paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco2_3_1_mult_strong, paco2_3_1_mon; eauto. Qed.

Corollary paco2_3_2_mult: forall r_0 r_1 r_2,
  paco2_3_2 gf_0 gf_1 gf_2 (paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco2_3_2_mult_strong, paco2_3_2_mon; eauto. Qed.

Theorem paco2_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco2_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco2_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco2_3_0_unfold: forall (MON: monotone2_3 gf_0) (MON: monotone2_3 gf_1) (MON: monotone2_3 gf_2) r_0 r_1 r_2,
  paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <2= gf_0 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone2_3; intros; destruct PR; eauto. Qed.

Theorem paco2_3_1_unfold: forall (MON: monotone2_3 gf_0) (MON: monotone2_3 gf_1) (MON: monotone2_3 gf_2) r_0 r_1 r_2,
  paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <2= gf_1 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone2_3; intros; destruct PR; eauto. Qed.

Theorem paco2_3_2_unfold: forall (MON: monotone2_3 gf_0) (MON: monotone2_3 gf_1) (MON: monotone2_3 gf_2) r_0 r_1 r_2,
  paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <2= gf_2 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone2_3; intros; destruct PR; eauto. Qed.

End Arg2_3.

Hint Unfold monotone2_3.
Hint Resolve paco2_3_0_fold.
Hint Resolve paco2_3_1_fold.
Hint Resolve paco2_3_2_fold.

Arguments paco2_3_0_acc            [ T0 T1 ].
Arguments paco2_3_1_acc            [ T0 T1 ].
Arguments paco2_3_2_acc            [ T0 T1 ].
Arguments paco2_3_0_mon            [ T0 T1 ].
Arguments paco2_3_1_mon            [ T0 T1 ].
Arguments paco2_3_2_mon            [ T0 T1 ].
Arguments paco2_3_0_mult_strong    [ T0 T1 ].
Arguments paco2_3_1_mult_strong    [ T0 T1 ].
Arguments paco2_3_2_mult_strong    [ T0 T1 ].
Arguments paco2_3_0_mult           [ T0 T1 ].
Arguments paco2_3_1_mult           [ T0 T1 ].
Arguments paco2_3_2_mult           [ T0 T1 ].
Arguments paco2_3_0_fold           [ T0 T1 ].
Arguments paco2_3_1_fold           [ T0 T1 ].
Arguments paco2_3_2_fold           [ T0 T1 ].
Arguments paco2_3_0_unfold         [ T0 T1 ].
Arguments paco2_3_1_unfold         [ T0 T1 ].
Arguments paco2_3_2_unfold         [ T0 T1 ].

Instance paco2_3_0_inst  T0 T1 (gf_0 gf_1 gf_2 : rel2 T0 T1->_) r_0 r_1 r_2 x0 x1 : paco_class (paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1) :=
{ pacoacc    := paco2_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco2_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco2_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco2_3_0_unfold gf_0 gf_1 gf_2 }.

Instance paco2_3_1_inst  T0 T1 (gf_0 gf_1 gf_2 : rel2 T0 T1->_) r_0 r_1 r_2 x0 x1 : paco_class (paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1) :=
{ pacoacc    := paco2_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco2_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco2_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco2_3_1_unfold gf_0 gf_1 gf_2 }.

Instance paco2_3_2_inst  T0 T1 (gf_0 gf_1 gf_2 : rel2 T0 T1->_) r_0 r_1 r_2 x0 x1 : paco_class (paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1) :=
{ pacoacc    := paco2_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco2_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco2_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco2_3_2_unfold gf_0 gf_1 gf_2 }.

