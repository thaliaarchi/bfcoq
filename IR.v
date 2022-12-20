Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.Byte.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.PArith.PArith.
Import IfNotations.
From Coq Require Export Lia.
Require Import BF.Byte.
Require Import BF.VM.
Require Import BF.Token.
Require Import BF.AST.

Inductive ir : Type :=
  | IRight (n : positive) (i : ir)
  | ILeft (n : positive) (i : ir)
  | IAdd (n : byte) (i : ir)
  | IOutput (i : ir)
  | IInput (i : ir)
  | ILoop (body : ir) (i : ir)
  | IEnd.

Inductive ir_execute : ir -> vm -> vm -> Prop :=
  | E_IRight : forall n next v v'',
      ir_execute next (vm_move_right n v) v'' ->
      ir_execute (IRight n next) v v''
  | E_ILeft : forall n next v v' v'',
      vm_move_left n v = Some v' ->
      ir_execute next v' v'' ->
      ir_execute (ILeft n next) v v''
  | E_IAdd : forall n next v v'',
      ir_execute next (vm_add n v) v'' ->
      ir_execute (IAdd n next) v v''
  | E_IOutput : forall next v v'',
      ir_execute next (vm_output v) v'' ->
      ir_execute (IOutput next) v v''
  | E_IInput : forall next v v' v'',
      vm_input v = Some v' ->
      ir_execute next v' v'' ->
      ir_execute (IInput next) v v''
  | E_ILoop_0 : forall body next l r o i v',
      ir_execute next (VM l x00 r o i) v' ->
      ir_execute (ILoop body next) (VM l x00 r o i) v'
  | E_ILoop : forall body next l c r o i v' v'',
      c <> x00 ->
      ir_execute body (VM l c r o i) v' ->
      ir_execute (ILoop body next) v' v'' ->
      ir_execute (ILoop body next) (VM l c r o i) v''
  | E_IEnd : forall v,
      ir_execute IEnd v v.

Definition ir_equiv (i1 i2 : ir) : Prop := forall v v',
  ir_execute i1 v v' <-> ir_execute i2 v v'.

Definition ir_transform_sound (trans : ir -> ir) : Prop := forall i,
  ir_equiv i (trans i).

Definition ir_cons_right (n : positive) (i : ir) : ir :=
  match i with
  | IRight m i' => IRight (m + n) i'
  | _ => IRight n i
  end.

Fixpoint ir_cons_left (n : positive) (i : ir) : ir :=
  match i with
  | ILeft m i' => ILeft (m + n) i'
  | IRight m i' => match n ?= m with
                   | Eq => i'
                   | Lt => IRight (m - n) i'
                   | Gt => ir_cons_left (n - m) i'
                   end
  | _ => ILeft n i
  end%positive.

Fixpoint ir_cons_add (n : byte) (i : ir) : ir :=
  match i with
  | IAdd m i' => ir_cons_add (byte_add m n) i'
  | _ => IAdd n i
  end.

Fixpoint ast_lower (a : ast) : ir :=
  match a with
  | ARight a' => IRight 1 (ast_lower a')
  | ALeft a' => ILeft 1 (ast_lower a')
  | AInc a' => IAdd x01 (ast_lower a')
  | ADec a' => IAdd xff (ast_lower a')
  | AOutput a' => IOutput (ast_lower a')
  | AInput a' => IInput (ast_lower a')
  | ALoop body a' => ILoop (ast_lower body) (ast_lower a')
  | AEnd => IEnd
  end.

Fixpoint ir_raise (i : ir) : ast :=
  match i with
  | IRight n i' => ast_cons_right n (ir_raise i')
  | ILeft n i' => ast_cons_left n (ir_raise i')
  | IAdd n i' => ast_cons_add n (ir_raise i')
  | IOutput i' => AOutput (ir_raise i')
  | IInput i' => AInput (ir_raise i')
  | ILoop body i' => ALoop (ir_raise body) (ir_raise i')
  | IEnd => AEnd
  end.

Fixpoint ir_combine (i : ir) : ir :=
  match i with
  | IRight n i' => ir_cons_right n (ir_combine i')
  | ILeft n i' => ir_cons_left n (ir_combine i')
  | IAdd n i' => ir_cons_add n (ir_combine i')
  | IOutput i' => IOutput (ir_combine i')
  | IInput i' => IInput (ir_combine i')
  | ILoop body i' => ILoop (ir_combine body) (ir_combine i')
  | IEnd => IEnd
  end.

Example test_ir_execute : forall a,
  parse (lex ",>+++[-<++>]<-.") = Some a ->
  ir_execute (ast_lower a) (vm_make [x02]) (VM [] x07 [] [x07] []).
Proof.
  intros. inversion H; subst; clear H.
  repeat (econstructor || discriminate).
Qed.

Open Scope positive_scope.

Theorem ir_cons_right_left_refl : forall i n,
  ir_cons_left n (ir_cons_right n i) = i.
Proof.
  induction i; intros; cbn;
  try (rewrite Pos.compare_refl; reflexivity).
  assert (n0 < n + n0) by lia. rewrite H.
  f_equal. lia.
Qed.

Theorem ir_cons_right_right : forall i n m,
  ir_cons_right m (ir_cons_right n i) = ir_cons_right (n + m) i.
Proof.
  induction i; intros; cbn; try reflexivity.
  f_equal. lia.
Qed.

Theorem ir_cons_left_left : forall i n m,
  ir_cons_left m (ir_cons_left n i) = ir_cons_left (n + m) i.
Proof.
  induction i; intros; cbn; try (f_equal; lia).
  destruct (n0 ?= n) eqn:Hcomp1.
  - rewrite Pos.compare_eq_iff in Hcomp1. subst.
    assert (n + m > n) by lia. rewrite H.
    f_equal. lia.
  - rewrite Pos.compare_lt_iff in Hcomp1.
    destruct (n0 + m ?= n) eqn:Hcomp2; cbn.
    + rewrite Pos.compare_eq_iff in Hcomp2. subst.
      assert (m = n0 + m - n0) by lia. rewrite <- H.
      rewrite Pos.compare_refl. reflexivity.
    + rewrite Pos.compare_lt_iff in Hcomp2.
      assert (m < n - n0) by lia. rewrite H.
      f_equal. lia.
    + rewrite Pos.compare_gt_iff in Hcomp2.
      assert (m > n - n0) by lia. rewrite H.
      f_equal; lia.
  - rewrite Pos.compare_gt_iff in Hcomp1.
    destruct (n0 + m ?= n) eqn:Hcomp2.
    + rewrite Pos.compare_eq_iff in Hcomp2. subst.
      apply Pos.lt_not_add_l in Hcomp1. inversion Hcomp1.
    + rewrite Pos.compare_lt_iff in Hcomp2.
      apply (Pos.lt_trans (n0 + m) n n0) in Hcomp2.
      apply Pos.lt_not_add_l in Hcomp2. inversion Hcomp2.
      assumption.
    + rewrite IHi. f_equal. lia.
Qed.

Close Scope positive_scope.

Theorem ast_lower_sound : forall a v v',
  ast_execute a v v' -> ir_execute (ast_lower a) v v'.
Proof.
  intros. induction H; cbn.
  - apply E_IRight, IHast_execute.
  - eapply E_ILeft. apply H. apply IHast_execute.
  - apply E_IAdd, IHast_execute.
  - apply E_IAdd, IHast_execute.
  - apply E_IOutput, IHast_execute.
  - eapply E_IInput. apply H. apply IHast_execute.
  - apply E_ILoop_0, IHast_execute.
  - eapply E_ILoop. apply H. apply IHast_execute1. apply IHast_execute2.
  - apply E_IEnd.
Qed.

Theorem ir_execute_cons_right : forall i n v v'',
  ir_execute (ir_cons_right n i) v v'' <->
  ir_execute i (vm_move_right n v) v''.
Proof.
  split.
  - induction i; intros;
    inversion H; subst; try assumption.
    apply E_IRight.
    rewrite vm_move_right_right, Pos.add_comm. assumption.
  - induction i; intros;
    apply E_IRight; try assumption.
    inversion H; subst.
    rewrite vm_move_right_right, Pos.add_comm in H4. assumption.
Qed.

Theorem ir_execute_cons_left : forall i n v v' v'',
  vm_move_left n v = Some v' ->
  ir_execute (ir_cons_left n i) v v'' <->
  ir_execute i v' v''.
Proof.
  split.
  - induction i; intros; cbn in *.
    + apply E_IRight. destruct vm_move_left; inversion H; subst.
Admitted.

Theorem ir_execute_cons_add : forall i n v v'',
  ir_execute (ir_cons_add n i) v v'' <->
  ir_execute i (vm_add n v) v''.
Proof.
  split;
  generalize dependent v''; generalize dependent v; generalize dependent n.
  - induction i; intros;
    try (inversion H; subst; assumption).
    apply E_IAdd. rewrite vm_add_add, byte_add_comm. apply IHi, H.
  - induction i; intros;
    inversion H; subst; repeat constructor; try assumption.
    rewrite vm_add_add, byte_add_comm in H4. apply IHi, H4.
Qed.

Theorem ir_combine_sound :
  ir_transform_sound ir_combine.
Proof.
  unfold ir_transform_sound, ir_equiv.
  split.
  - intros. induction H; cbn;
    try (econstructor; eassumption).
    + rewrite ir_execute_cons_right; assumption.
    + rewrite ir_execute_cons_left; eassumption.
    + rewrite ir_execute_cons_add; assumption.
  - generalize dependent v'; generalize dependent v.
    induction i; intros; cbn in *.
    + rewrite ir_execute_cons_right in H. apply E_IRight, IHi, H.
    + rewrite ir_execute_cons_left in H. eapply E_ILeft.
      admit. apply IHi. eassumption. admit.
    + rewrite ir_execute_cons_add in H. apply E_IAdd, IHi, H.
    + inversion H; subst. apply E_IOutput, IHi, H1.
    + inversion H; subst. eapply E_IInput. admit. apply IHi, H2.
    + inversion H; subst.
      * apply E_ILoop_0, IHi2, H4.
      * eapply E_ILoop. assumption. apply IHi1, H3. admit.
    + assumption.
Admitted.
