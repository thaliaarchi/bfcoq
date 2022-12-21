From BF Require Import Base VM IR.

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
  | E_MRight : forall n next v v'',
      execute next (VM.move_right n v) v'' ->
      execute (MRight n next) v v''
  | E_MLeft : forall n next v v' v'',
      VM.move_left n (Some v) = Some v' ->
      execute next v' v'' ->
      execute (MLeft n next) v v''
  | E_MAdd : forall n next v v'',
      execute next (VM.add n v) v'' ->
      execute (MAdd n next) v v''
  | E_MConst : forall n next v v'',
      execute next (VM.set n v) v'' ->
      execute (MConst n next) v v''
  | E_MOutput : forall next v v'',
      execute next (VM.output v) v'' ->
      execute (MOutput next) v v''
  | E_MInput : forall next v v' v'',
      VM.input v = Some v' ->
      execute next v' v'' ->
      execute (MInput next) v v''
  | E_MLoop_0 : forall body next l r o i v',
      execute next (VM l x00 r o i) v' ->
      execute (MLoop body next) (VM l x00 r o i) v'
  | E_MLoop : forall body next l c r o i v' v'',
      c <> x00 ->
      execute body (VM l c r o i) v' ->
      execute (MLoop body next) v' v'' ->
      execute (MLoop body next) (VM l c r o i) v''
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
      | IAdd n IEnd => if Byte.odd n then MConst x00 (lower_ir i')
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
Admitted.
