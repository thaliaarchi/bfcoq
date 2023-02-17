From BF Require Import Base Byte RelVM AST.

Inductive relir : Type :=
  | RMove (n : Z) (r : relir)
  | RAdd (n : byte) (off : Z) (r : relir)
  | ROutput (off : Z) (r : relir)
  | RInput (off : Z) (r : relir)
  | RLoop (body : relir) (r : relir)
  | REnd.

Inductive execute : relir -> vm -> vm -> Prop :=
  | E_RMove n r v v' v'' :
      RelVM.move n v = Some v' ->
      execute r v' v'' ->
      execute (RMove n r) v v''
  | E_RAdd n off r v v' v'' :
      RelVM.add_cell n off v = Some v' ->
      execute r v' v'' ->
      execute (RAdd n off r) v v''
  | E_ROutput off r v v' v'' :
      RelVM.output off v = Some v' ->
      execute r v' v'' ->
      execute (ROutput off r) v v''
  | E_RInput off r v v' v'' :
      RelVM.input off v = Some v' ->
      execute r v' v'' ->
      execute (RInput off r) v v''
  | E_RLoop body r v v' v'' :
      RelVM.cell v =? #00 = false ->
      execute body v v' ->
      execute (RLoop body r) v' v'' ->
      execute (RLoop body r) v v''
  | E_RLoop_0 body r v v' :
      RelVM.cell v =? #00 = true ->
      execute r v v' ->
      execute (RLoop body r) v v'
  | E_REnd v v' :
      RelVM.eq v v' = true ->
      execute REnd v v'.

Fixpoint lower_ast (a : ast) : relir :=
  match a with
  | ARight a' => RMove 1 (lower_ast a')
  | ALeft a' => RMove (-1) (lower_ast a')
  | AInc a' => RAdd #01 0 (lower_ast a')
  | ADec a' => RAdd #ff 0 (lower_ast a')
  | AOutput a' => ROutput 0 (lower_ast a')
  | AInput a' => RInput 0 (lower_ast a')
  | ALoop body a' => RLoop (lower_ast body) (lower_ast a')
  | AEnd => REnd
  end.

Theorem lower_ast_sound : forall a v v',
  AST.execute_rel a v v' <-> execute (lower_ast a) v v'.
Proof.
  split.
  - intros. induction H; cbn; econstructor; eassumption.
  - generalize dependent v'; generalize dependent v.
    induction a; cbn; intros;
    try (inversion H; subst; econstructor; try apply IHa; eassumption).
    dependent induction H.
    + eapply ER_ALoop. assumption. apply IHa1. eassumption.
      apply IHexecute2. apply IHa2. apply IHa1. reflexivity.
    + apply ER_ALoop_0, IHa2; assumption.
Qed.

Fixpoint append (r1 r2 : relir) : relir :=
  match r1 with
  | RMove n r1' => RMove n (append r1' r2)
  | RAdd n off r1' => RAdd n off (append r1' r2)
  | ROutput off r1' => ROutput off (append r1' r2)
  | RInput off r1' => RInput off (append r1' r2)
  | RLoop body r1' => RLoop body (append r1' r2)
  | REnd => r2
  end.

Theorem append_end_l : forall r,
  append REnd r = r.
Proof. reflexivity. Qed.

Theorem append_end_r : forall r,
  append r REnd = r.
Proof.
  induction r; cbn;
  try rewrite IHr; try rewrite IHr2; reflexivity. Qed.

Theorem execute_append : forall r1 r2 v v' v'',
  execute r1 v v' ->
  execute r2 v' v'' ->
  execute (append r1 r2) v v''.
Proof.
  induction r1; intros; cbn;
  try (inversion H; subst; econstructor; [eassumption | eapply IHr1; eassumption]).
  - dependent induction H.
    + eapply E_RLoop. assumption. eassumption. now apply IHexecute2.
    + eapply E_RLoop_0. assumption. eapply IHr1_2; eassumption.
  - inversion H; subst. admit.
Admitted.

Theorem execute_append_split : forall r1 r2 v v'',
  execute (append r1 r2) v v'' ->
  exists v', execute r1 v v' /\ execute r2 v' v''.
Proof.
  induction r1; cbn; intros.
  - inversion H; subst. apply IHr1 in H5 as [v'1 []].
    exists v'1. split; [eapply E_RMove |]; eassumption.
  - inversion H; subst. apply IHr1 in H6 as [v'1 []].
    exists v'1. split; [eapply E_RAdd |]; eassumption.
  - inversion H; subst. apply IHr1 in H5 as [v'1 []].
    exists v'1. split; [eapply E_ROutput |]; eassumption.
  - inversion H; subst. apply IHr1 in H5 as [v'1 []].
    exists v'1. split; [eapply E_RInput |]; eassumption.
  - admit.
  - exists v. split. apply E_REnd. apply RelVM.eq_refl. assumption.
Admitted.
