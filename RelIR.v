From BF Require Import Base Byte RelVM AST.

Inductive relir : Type :=
  | RMove (n : Z) (r : relir)
  | RAdd (n : byte) (off : Z) (r : relir)
  | ROutput (off : Z) (r : relir)
  | RInput (off : Z) (r : relir)
  | RLoop (body : relir) (r : relir)
  | REnd.

Inductive execute : relir -> vm -> vm -> Prop :=
  | E_RMove : forall n r v v' v'',
      RelVM.move n v = Some v' ->
      execute r v' v'' ->
      execute (RMove n r) v v''
  | E_RAdd : forall n off r v v' v'',
      RelVM.add_cell n off v = Some v' ->
      execute r v' v'' ->
      execute (RAdd n off r) v v''
  | E_ROutput : forall off r v v' v'',
      RelVM.output off v = Some v' ->
      execute r v' v'' ->
      execute (ROutput off r) v v''
  | E_RInput : forall off r v v' v'',
      RelVM.input off v = Some v' ->
      execute r v' v'' ->
      execute (RInput off r) v v''
  | E_RLoop : forall body r v v' v'',
      RelVM.cell v =? #00 = false ->
      execute body v v' ->
      execute (RLoop body r) v' v'' ->
      execute (RLoop body r) v v''
  | E_RLoop_0 : forall body r v v',
      RelVM.cell v =? #00 = true ->
      execute r v v' ->
      execute (RLoop body r) v v'
  | E_REnd : forall v v',
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
