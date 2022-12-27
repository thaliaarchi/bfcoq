From BF Require Import Base Byte VM Token AST.

Inductive comir : Type :=
  | CRight (n : positive) (c : comir)
  | CLeft (n : positive) (c : comir)
  | CAdd (n : byte) (c : comir)
  | COutput (c : comir)
  | CInput (c : comir)
  | CLoop (body : comir) (c : comir)
  | CEnd.

Inductive execute : comir -> vm -> vm -> Prop :=
  | E_CRight : forall n c v v'',
      execute c (VM.move_right n v) v'' ->
      execute (CRight n c) v v''
  | E_CLeft : forall n c v v' v'',
      VM.move_left n (Some v) = Some v' ->
      execute c v' v'' ->
      execute (CLeft n c) v v''
  | E_CAdd : forall n c v v'',
      execute c (VM.add_cell n v) v'' ->
      execute (CAdd n c) v v''
  | E_COutput : forall c v v'',
      execute c (VM.output v) v'' ->
      execute (COutput c) v v''
  | E_CInput : forall c v v' v'',
      VM.input v = Some v' ->
      execute c v' v'' ->
      execute (CInput c) v v''
  | E_CLoop : forall body c v v' v'',
      v.(cell) =? #00 = false ->
      execute body v v' ->
      execute (CLoop body c) v' v'' ->
      execute (CLoop body c) v v''
  | E_CLoop_0 : forall body c v v',
      v.(cell) =? #00 = true ->
      execute c v v' ->
      execute (CLoop body c) v v'
  | E_CEnd : forall v v',
      VM.eq v v' = true ->
      execute CEnd v v'.

Definition equiv (i1 i2 : comir) : Prop := forall v v',
  execute i1 v v' <-> execute i2 v v'.

Definition transform_sound (trans : comir -> comir) : Prop := forall c,
  equiv c (trans c).

Fixpoint cons_right (n : positive) (c : comir) : comir :=
  match c with
  | CRight m c' => CRight (n + m) c'
  | CLeft m c' => match n ?= m with
                  | Eq => c'
                  | Lt => CLeft (m - n) c'
                  | Gt => cons_right (n - m) c'
                  end
  | _ => CRight n c
  end%positive.

Definition cons_left (n : positive) (c : comir) : comir :=
  match c with
  | CLeft m c' => CLeft (n + m) c'
  | _ => CLeft n c
  end.

Definition cons_add (n : byte) (c : comir) : comir :=
  match c with
  | CAdd m c' => CAdd (n + m) c'
  | _ => CAdd n c
  end.

Fixpoint lower_ast (a : ast) : comir :=
  match a with
  | ARight a' => CRight 1 (lower_ast a')
  | ALeft a' => CLeft 1 (lower_ast a')
  | AInc a' => CAdd #01 (lower_ast a')
  | ADec a' => CAdd #ff (lower_ast a')
  | AOutput a' => COutput (lower_ast a')
  | AInput a' => CInput (lower_ast a')
  | ALoop body a' => CLoop (lower_ast body) (lower_ast a')
  | AEnd => CEnd
  end.

Fixpoint raise_ast (c : comir) : ast :=
  match c with
  | CRight n c' => AST.cons_right n (raise_ast c')
  | CLeft n c' => AST.cons_left n (raise_ast c')
  | CAdd n c' => AST.cons_add n (raise_ast c')
  | COutput c' => AOutput (raise_ast c')
  | CInput c' => AInput (raise_ast c')
  | CLoop body c' => ALoop (raise_ast body) (raise_ast c')
  | CEnd => AEnd
  end.

Fixpoint combine (c : comir) : comir :=
  match c with
  | CRight n c' => cons_right n (combine c')
  | CLeft n c' => cons_left n (combine c')
  | CAdd n c' => cons_add n (combine c')
  | COutput c' => COutput (combine c')
  | CInput c' => CInput (combine c')
  | CLoop body c' => CLoop (combine body) (combine c')
  | CEnd => CEnd
  end.

Example test_execute : forall a,
  parse (lex ",>+++[-<++>]<-.") = Some a ->
  execute (lower_ast a) (VM.make [#02]) (VM [] #07 [] [#07] [] VM.norm_nil).
Proof.
  intros. inversion H; subst; clear H.
  repeat (apply E_CRight
       || (eapply E_CLeft; [reflexivity |])
       || apply E_CAdd
       || apply E_COutput
       || (eapply E_CInput; [reflexivity |])
       || (eapply E_CLoop; [reflexivity | |])
       || (eapply E_CLoop_0; [reflexivity |])
       || (apply E_CEnd; apply VM.eq_refl)).
  apply E_CEnd. reflexivity.
Qed.

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
    + inversion H; subst. apply E_AEnd. assumption.
Qed.

Ltac destruct_compare n m :=
  destruct (n ?= m)%positive eqn:Hcomp;
  [rewrite Pos.compare_eq_iff in Hcomp; subst
  | rewrite Pos.compare_lt_iff in Hcomp
  | rewrite Pos.compare_gt_iff in Hcomp].

Theorem cons_right_correct : forall c n v v',
  execute (cons_right n c) v v' <-> execute (CRight n c) v v'.
Proof.
  split;
  generalize dependent v'; generalize dependent v; generalize dependent n.
  - induction c; cbn; intros; try assumption.
    + inversion H; subst.
      apply E_CRight, E_CRight. rewrite VM.move_right_add. assumption.
    + destruct_compare n0 n.
      * eapply E_CRight, E_CLeft. apply VM.move_right_left_refl. assumption.
      * inversion H; subst.
        eapply E_CRight, E_CLeft. rewrite VM.move_right_left_lt.
        eassumption. apply Hcomp. assumption.
      * apply IHc in H. inversion H; subst.
        eapply E_CRight, E_CLeft. apply VM.move_right_left_gt.
        apply Hcomp. assumption.
  - induction c; cbn; intros; try assumption;
    inversion H; inversion H4; subst.
    + rewrite VM.move_right_add in H9.
      apply E_CRight. assumption.
    + destruct_compare n0 n.
      * rewrite VM.move_right_left_refl in H7. inversion H7; subst. assumption.
      * rewrite VM.move_right_left_lt in H7.
        eapply E_CLeft. eassumption. assumption. apply Hcomp.
      * rewrite VM.move_right_left_gt in H7. inversion H7; subst.
        apply IHc. apply E_CRight. assumption. assumption.
Qed.

Theorem cons_left_correct : forall c n v v',
  execute (cons_left n c) v v' <-> execute (CLeft n c) v v'.
Proof.
  split;
  generalize dependent v'; generalize dependent v; generalize dependent n.
  - destruct c; cbn; intros; try assumption.
    inversion H; subst.
    rewrite Pos.add_comm, <- VM.move_left_add in H2.
    apply VM.move_left_split in H2 as [v'1 []].
    eapply E_CLeft, E_CLeft; eassumption.
  - destruct c; cbn; intros; try assumption.
    inversion H; inversion H5; subst.
    rewrite Pos.add_comm. eapply E_CLeft. rewrite <- VM.move_left_add.
    rewrite H2. eassumption. assumption.
Qed.

Theorem cons_add_correct : forall c n v v',
  execute (cons_add n c) v v' <-> execute (CAdd n c) v v'.
Proof.
  split.
  - destruct c; cbn; intros; try assumption.
    inversion H; subst.
    apply E_CAdd, E_CAdd. rewrite VM.add_add. assumption.
  - destruct c; cbn; intros; try assumption.
    inversion H; inversion H4; subst.
    apply E_CAdd. rewrite <- VM.add_add. assumption.
Qed.

Theorem combine_sound :
  transform_sound combine.
Proof.
  unfold transform_sound, equiv.
  split.
  - intros. induction H; cbn;
    try (econstructor; eassumption).
    + rewrite cons_right_correct. apply E_CRight. assumption.
    + rewrite cons_left_correct. eapply E_CLeft; eassumption.
    + rewrite cons_add_correct. apply E_CAdd. assumption.
  - generalize dependent v'; generalize dependent v.
    induction c; intros; cbn in *.
    + rewrite cons_right_correct in H. inversion H; subst.
      apply E_CRight, IHc. assumption.
    + rewrite cons_left_correct in H. inversion H; subst.
      eapply E_CLeft. eassumption. apply IHc. assumption.
    + rewrite cons_add_correct in H. inversion H; subst.
      apply E_CAdd, IHc. assumption.
    + inversion H; subst. constructor. apply IHc. assumption.
    + inversion H; subst. econstructor. eassumption. apply IHc. assumption.
    + dependent induction H.
      * eapply E_CLoop. assumption. apply IHc1. eassumption.
        apply IHexecute2; try assumption. reflexivity.
      * apply E_CLoop_0, IHc2; assumption.
    + assumption.
Qed.

Theorem lower_ast_combine_sound : forall a v v',
  AST.execute a v v' -> execute (combine (lower_ast a)) v v'.
Proof.
  intros. apply lower_ast_sound, combine_sound in H. assumption.
Qed.
