From BF Require Import Base Byte VM Token AST.

Inductive ir : Type :=
  | IRight (n : positive) (i : ir)
  | ILeft (n : positive) (i : ir)
  | IAdd (n : byte) (i : ir)
  | IOutput (i : ir)
  | IInput (i : ir)
  | ILoop (body : ir) (i : ir)
  | IEnd.

Inductive execute : ir -> vm -> vm -> Prop :=
  | E_IRight : forall n next v v'',
      execute next (VM.move_right n v) v'' ->
      execute (IRight n next) v v''
  | E_ILeft : forall n next v v' v'',
      VM.move_left n v = Some v' ->
      execute next v' v'' ->
      execute (ILeft n next) v v''
  | E_IAdd : forall n next v v'',
      execute next (VM.add n v) v'' ->
      execute (IAdd n next) v v''
  | E_IOutput : forall next v v'',
      execute next (VM.output v) v'' ->
      execute (IOutput next) v v''
  | E_IInput : forall next v v' v'',
      VM.input v = Some v' ->
      execute next v' v'' ->
      execute (IInput next) v v''
  | E_ILoop_0 : forall body next l r o i v',
      execute next (VM l x00 r o i) v' ->
      execute (ILoop body next) (VM l x00 r o i) v'
  | E_ILoop : forall body next l c r o i v' v'',
      c <> x00 ->
      execute body (VM l c r o i) v' ->
      execute (ILoop body next) v' v'' ->
      execute (ILoop body next) (VM l c r o i) v''
  | E_IEnd : forall v,
      execute IEnd v v.

Definition equiv (i1 i2 : ir) : Prop := forall v v',
  execute i1 v v' <-> execute i2 v v'.

Definition transform_sound (trans : ir -> ir) : Prop := forall i,
  equiv i (trans i).

Definition cons_right (n : positive) (i : ir) : ir :=
  match i with
  | IRight m i' => IRight (m + n) i'
  | _ => IRight n i
  end.

Fixpoint cons_left (n : positive) (i : ir) : ir :=
  match i with
  | ILeft m i' => ILeft (m + n) i'
  | IRight m i' => match n ?= m with
                   | Eq => i'
                   | Lt => IRight (m - n) i'
                   | Gt => cons_left (n - m) i'
                   end
  | _ => ILeft n i
  end%positive.

Fixpoint cons_add (n : byte) (i : ir) : ir :=
  match i with
  | IAdd m i' => cons_add (Byte.add m n) i'
  | _ => IAdd n i
  end.

Fixpoint lower_ast (a : ast) : ir :=
  match a with
  | ARight a' => IRight 1 (lower_ast a')
  | ALeft a' => ILeft 1 (lower_ast a')
  | AInc a' => IAdd x01 (lower_ast a')
  | ADec a' => IAdd xff (lower_ast a')
  | AOutput a' => IOutput (lower_ast a')
  | AInput a' => IInput (lower_ast a')
  | ALoop body a' => ILoop (lower_ast body) (lower_ast a')
  | AEnd => IEnd
  end.

Fixpoint raise_ast (i : ir) : ast :=
  match i with
  | IRight n i' => AST.cons_right n (raise_ast i')
  | ILeft n i' => AST.cons_left n (raise_ast i')
  | IAdd n i' => AST.cons_add n (raise_ast i')
  | IOutput i' => AOutput (raise_ast i')
  | IInput i' => AInput (raise_ast i')
  | ILoop body i' => ALoop (raise_ast body) (raise_ast i')
  | IEnd => AEnd
  end.

Fixpoint combine (i : ir) : ir :=
  match i with
  | IRight n i' => cons_right n (combine i')
  | ILeft n i' => cons_left n (combine i')
  | IAdd n i' => cons_add n (combine i')
  | IOutput i' => IOutput (combine i')
  | IInput i' => IInput (combine i')
  | ILoop body i' => ILoop (combine body) (combine i')
  | IEnd => IEnd
  end.

Example test_execute : forall a,
  parse (lex ",>+++[-<++>]<-.") = Some a ->
  execute (lower_ast a) (VM.make [x02]) (VM [] x07 [] [x07] []).
Proof.
  intros. inversion H; subst; clear H.
  repeat (econstructor || discriminate).
Qed.

Open Scope positive_scope.

Theorem cons_right_left_refl : forall i n,
  cons_left n (cons_right n i) = i.
Proof.
  induction i; intros; cbn;
  try (rewrite Pos.compare_refl; reflexivity).
  assert (n0 < n + n0) by lia. rewrite H.
  f_equal. lia.
Qed.

Theorem cons_right_right : forall i n m,
  cons_right m (cons_right n i) = cons_right (n + m) i.
Proof.
  induction i; intros; cbn; try reflexivity.
  f_equal. lia.
Qed.

Theorem cons_left_left : forall i n m,
  cons_left m (cons_left n i) = cons_left (n + m) i.
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

Theorem lower_ast_sound : forall a v v',
  AST.execute a v v' -> execute (lower_ast a) v v'.
Proof.
  intros. induction H; cbn.
  - apply E_IRight, IHexecute.
  - eapply E_ILeft. apply H. apply IHexecute.
  - apply E_IAdd, IHexecute.
  - apply E_IAdd, IHexecute.
  - apply E_IOutput, IHexecute.
  - eapply E_IInput. apply H. apply IHexecute.
  - apply E_ILoop_0, IHexecute.
  - eapply E_ILoop. apply H. apply IHexecute1. apply IHexecute2.
  - apply E_IEnd.
Qed.

Theorem execute_cons_right : forall i n v v'',
  execute (cons_right n i) v v'' <->
  execute i (VM.move_right n v) v''.
Proof.
  split.
  - induction i; intros;
    inversion H; subst; try assumption.
    apply E_IRight.
    rewrite VM.move_right_right, Pos.add_comm. assumption.
  - induction i; intros;
    apply E_IRight; try assumption.
    inversion H; subst.
    rewrite VM.move_right_right, Pos.add_comm in H4. assumption.
Qed.

Theorem execute_cons_left : forall i n v v' v'',
  VM.move_left n v = Some v' ->
  execute (cons_left n i) v v'' <->
  execute i v' v''.
Proof.
  split.
  - induction i; intros; cbn in *.
    + apply E_IRight. destruct VM.move_left; inversion H; subst.
Admitted.

Theorem execute_cons_add : forall i n v v'',
  execute (cons_add n i) v v'' <->
  execute i (VM.add n v) v''.
Proof.
  split;
  generalize dependent v''; generalize dependent v; generalize dependent n.
  - induction i; intros;
    try (inversion H; subst; assumption).
    apply E_IAdd. rewrite VM.add_add, Byte.add_comm. apply IHi, H.
  - induction i; intros;
    inversion H; subst; repeat constructor; try assumption.
    rewrite VM.add_add, Byte.add_comm in H4. apply IHi, H4.
Qed.

Theorem combine_sound :
  transform_sound combine.
Proof.
  unfold transform_sound, equiv.
  split.
  - intros. induction H; cbn;
    try (econstructor; eassumption).
    + rewrite execute_cons_right; assumption.
    + rewrite execute_cons_left; eassumption.
    + rewrite execute_cons_add; assumption.
  - generalize dependent v'; generalize dependent v.
    induction i; intros; cbn in *.
    + rewrite execute_cons_right in H. apply E_IRight, IHi, H.
    + rewrite execute_cons_left in H. eapply E_ILeft.
      admit. apply IHi. eassumption. admit.
    + rewrite execute_cons_add in H. apply E_IAdd, IHi, H.
    + inversion H; subst. apply E_IOutput, IHi, H1.
    + inversion H; subst. eapply E_IInput. admit. apply IHi, H2.
    + inversion H; subst.
      * apply E_ILoop_0, IHi2, H4.
      * eapply E_ILoop. assumption. apply IHi1, H3. admit.
    + assumption.
Admitted.
