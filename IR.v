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
  | E_IRight : forall n i v v'',
      execute i (VM.move_right n v) v'' ->
      execute (IRight n i) v v''
  | E_ILeft : forall n i v v' v'',
      VM.move_left n (Some v) = Some v' ->
      execute i v' v'' ->
      execute (ILeft n i) v v''
  | E_IAdd : forall n i v v'',
      execute i (VM.add_cell n v) v'' ->
      execute (IAdd n i) v v''
  | E_IOutput : forall i v v'',
      execute i (VM.output v) v'' ->
      execute (IOutput i) v v''
  | E_IInput : forall i v v' v'',
      VM.input v = Some v' ->
      execute i v' v'' ->
      execute (IInput i) v v''
  | E_ILoop : forall body i v v' v'',
      VM.get_cell v =? #00 = false ->
      execute body v v' ->
      execute (ILoop body i) v' v'' ->
      execute (ILoop body i) v v''
  | E_ILoop_0 : forall body i v v',
      VM.get_cell v =? #00 = true ->
      execute i v v' ->
      execute (ILoop body i) v v'
  | E_IEnd : forall v,
      execute IEnd v v.

Definition equiv (i1 i2 : ir) : Prop := forall v v',
  execute i1 v v' <-> execute i2 v v'.

Definition transform_sound (trans : ir -> ir) : Prop := forall i,
  equiv i (trans i).

Fixpoint cons_right (n : positive) (i : ir) : ir :=
  match i with
  | IRight m i' => IRight (n + m) i'
  | ILeft m i' => match n ?= m with
                  | Eq => i'
                  | Lt => ILeft (m - n) i'
                  | Gt => cons_right (n - m) i'
                  end
  | _ => IRight n i
  end%positive.

Definition cons_left (n : positive) (i : ir) : ir :=
  match i with
  | ILeft m i' => ILeft (n + m) i'
  | _ => ILeft n i
  end.

Definition cons_add (n : byte) (i : ir) : ir :=
  match i with
  | IAdd m i' => IAdd (n + m) i'
  | _ => IAdd n i
  end.

Fixpoint lower_ast (a : ast) : ir :=
  match a with
  | ARight a' => IRight 1 (lower_ast a')
  | ALeft a' => ILeft 1 (lower_ast a')
  | AInc a' => IAdd #01 (lower_ast a')
  | ADec a' => IAdd #ff (lower_ast a')
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
  execute (lower_ast a) (VM.make [#02]) (VM [] #07 [] [#07] []).
Proof.
  intros. inversion H; subst; clear H.
  repeat (apply E_IRight
       || (eapply E_ILeft; [reflexivity |])
       || apply E_IAdd
       || apply E_IOutput
       || (eapply E_IInput; [reflexivity |])
       || (eapply E_ILoop; [reflexivity | |])
       || (eapply E_ILoop_0; [reflexivity |])
       || apply E_IEnd).
  (* TODO: Normalize right tape and bytes *)
Admitted.

Theorem lower_ast_sound : forall a v v',
  AST.execute a v v' <-> execute (lower_ast a) v v'.
Proof.
  split.
  - intros. induction H; cbn; econstructor; eassumption.
  - generalize dependent v'; generalize dependent v.
    induction a; cbn; intros.
    + inversion H; subst. apply E_ARight, IHa. assumption.
    + inversion H; subst. eapply E_ALeft. eassumption. apply IHa. assumption.
    + inversion H; subst. apply E_AInc, IHa. assumption.
    + inversion H; subst. apply E_ADec, IHa. assumption.
    + inversion H; subst. apply E_AOutput, IHa. assumption.
    + inversion H; subst. eapply E_AInput, IHa; eassumption.
    + dependent induction H.
      * eapply E_ALoop. assumption. apply IHa1. eassumption.
        apply IHexecute2; intros.
        -- apply IHa2. assumption.
        -- apply IHa1. assumption.
        -- reflexivity.
      * apply E_ALoop_0, IHa2; assumption.
    + inversion H; subst. apply E_AEnd.
Qed.

Ltac destruct_compare n m :=
  destruct (n ?= m)%positive eqn:Hcomp;
  [rewrite Pos.compare_eq_iff in Hcomp; subst
  | rewrite Pos.compare_lt_iff in Hcomp
  | rewrite Pos.compare_gt_iff in Hcomp].

Theorem cons_right_correct : forall i n v v',
  execute (cons_right n i) v v' <-> execute (IRight n i) v v'.
Proof.
  split;
  generalize dependent v'; generalize dependent v; generalize dependent n.
  - induction i; cbn; intros; try assumption.
    + inversion H; subst.
      apply E_IRight, E_IRight. rewrite VM.move_right_add. assumption.
    + destruct_compare n0 n.
      * eapply E_IRight, E_ILeft. apply VM.move_right_left_refl.
        admit. assumption.
      * inversion H; subst.
        eapply E_IRight, E_ILeft. rewrite VM.move_right_left_lt.
        eassumption. admit. apply Hcomp. assumption.
      * apply IHi in H. inversion H; subst.
        eapply E_IRight, E_ILeft. apply VM.move_right_left_gt.
        admit. apply Hcomp. assumption.
  - induction i; cbn; intros; try assumption;
    inversion H; inversion H4; subst.
    + rewrite VM.move_right_add in H9.
      apply E_IRight. assumption.
    + destruct_compare n0 n.
      * rewrite VM.move_right_left_refl in H7. inversion H7; subst.
        assumption. admit.
      * rewrite VM.move_right_left_lt in H7.
        eapply E_ILeft. eassumption. assumption. admit. apply Hcomp.
      * rewrite VM.move_right_left_gt in H7. inversion H7; subst.
        apply IHi. apply E_IRight. assumption. admit. assumption.
Admitted.

Theorem cons_left_correct : forall i n v v',
  execute (cons_left n i) v v' <-> execute (ILeft n i) v v'.
Proof.
  split;
  generalize dependent v'; generalize dependent v; generalize dependent n.
  - destruct i; cbn; intros; try assumption.
    inversion H; subst.
    rewrite Pos.add_comm, <- VM.move_left_add in H2.
    apply VM.move_left_split in H2 as [v'1 []].
    eapply E_ILeft, E_ILeft; eassumption.
  - destruct i; cbn; intros; try assumption.
    inversion H; inversion H5; subst.
    rewrite Pos.add_comm. eapply E_ILeft. rewrite <- VM.move_left_add.
    rewrite H2. eassumption. assumption.
Qed.

Theorem cons_add_correct : forall i n v v',
  execute (cons_add n i) v v' <-> execute (IAdd n i) v v'.
Proof.
  split.
  - destruct i; cbn; intros; try assumption.
    inversion H; subst.
    apply E_IAdd, E_IAdd. rewrite VM.add_add. assumption.
  - destruct i; cbn; intros; try assumption.
    inversion H; inversion H4; subst.
    apply E_IAdd. rewrite <- VM.add_add. assumption.
Qed.

Theorem combine_sound :
  transform_sound combine.
Proof.
  unfold transform_sound, equiv.
  split.
  - intros. induction H; cbn;
    try (econstructor; eassumption).
    + rewrite cons_right_correct. apply E_IRight. assumption.
    + rewrite cons_left_correct. eapply E_ILeft; eassumption.
    + rewrite cons_add_correct. apply E_IAdd. assumption.
  - generalize dependent v'; generalize dependent v.
    induction i; intros; cbn in *.
    + rewrite cons_right_correct in H. inversion H; subst.
      apply E_IRight, IHi. assumption.
    + rewrite cons_left_correct in H. inversion H; subst.
      eapply E_ILeft. eassumption. apply IHi. assumption.
    + rewrite cons_add_correct in H. inversion H; subst.
      apply E_IAdd, IHi. assumption.
    + inversion H; subst. constructor. apply IHi. assumption.
    + inversion H; subst. econstructor. eassumption. apply IHi. assumption.
    + dependent induction H.
      * eapply E_ILoop. assumption. apply IHi1. eassumption.
        apply IHexecute2; try assumption. reflexivity.
      * apply E_ILoop_0, IHi2; assumption.
    + assumption.
Qed.

Theorem lower_ast_combine_sound : forall a v v',
  AST.execute a v v' -> execute (combine (lower_ast a)) v v'.
Proof.
  intros. apply lower_ast_sound, combine_sound in H. assumption.
Qed.
