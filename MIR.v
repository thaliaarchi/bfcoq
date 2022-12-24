From BF Require Import Base Byte VM IR.

Inductive mir : Type :=
  | MRight (n : positive) (m : mir)
  | MLeft (n : positive) (m : mir)
  | MAdd (n : byte) (m : mir)
  | MConst (n : byte) (m : mir)
  | MOutput (m : mir)
  | MInput (m : mir)
  | MLoop (body : mir) (m : mir)
  | MEnd.

Inductive execute : mir -> vm -> vm -> Prop :=
  | E_MRight : forall n m v v'',
      execute m (VM.move_right n v) v'' ->
      execute (MRight n m) v v''
  | E_MLeft : forall n m v v' v'',
      VM.move_left n (Some v) = Some v' ->
      execute m v' v'' ->
      execute (MLeft n m) v v''
  | E_MAdd : forall n m v v'',
      execute m (VM.add_cell n v) v'' ->
      execute (MAdd n m) v v''
  | E_MConst : forall n m v v'',
      execute m (VM.set_cell n v) v'' ->
      execute (MConst n m) v v''
  | E_MOutput : forall m v v'',
      execute m (VM.output v) v'' ->
      execute (MOutput m) v v''
  | E_MInput : forall m v v' v'',
      VM.input v = Some v' ->
      execute m v' v'' ->
      execute (MInput m) v v''
  | E_MLoop : forall body m v v' v'',
      VM.get_cell v =? #00 = false ->
      execute body v v' ->
      execute (MLoop body m) v' v'' ->
      execute (MLoop body m) v v''
  | E_MLoop_0 : forall body m v v',
      VM.get_cell v =? #00 = true ->
      execute m v v' ->
      execute (MLoop body m) v v'
  | E_MEnd : forall v,
      execute MEnd v v.

Definition equiv (m1 m2 : mir) : Prop := forall v v',
  execute m1 v v' <-> execute m2 v v'.

Definition transform_sound (trans : mir -> mir) : Prop := forall m,
  equiv m (trans m).

Fixpoint lower_ir (i : ir) : mir :=
  match i with
  | IRight n i' => MRight n (lower_ir i')
  | ILeft n i' => MLeft n (lower_ir i')
  | IAdd n i' => MAdd n (lower_ir i')
  | IOutput i' => MOutput (lower_ir i')
  | IInput i' => MInput (lower_ir i')
  | ILoop body i' =>
      match body with
      | IAdd n IEnd => if Byte.odd n then MConst #00 (lower_ir i')
                       else MLoop (lower_ir body) (lower_ir i')
      | _ => MLoop (lower_ir body) (lower_ir i')
      end
  | IEnd => MEnd
  end.

Theorem lower_ir_sound : forall i v v',
  IR.execute i v v' <-> execute (lower_ir i) v v'.
Proof.
  split.
  - intros. induction H; cbn; try (econstructor; eassumption); admit.
  - generalize dependent v'; generalize dependent v.
    induction i; cbn; intros.
    + inversion H; subst. constructor. apply IHi. assumption.
    + inversion H; subst. econstructor. eassumption. apply IHi. assumption.
    + inversion H; subst. constructor. apply IHi. assumption.
    + inversion H; subst. constructor. apply IHi. assumption.
    + inversion H; subst. econstructor. eassumption. apply IHi. assumption.
Admitted.
