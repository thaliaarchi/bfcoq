From BF Require Import Base VM Token.

Inductive ast : Type :=
  | ARight (a : ast)
  | ALeft (a : ast)
  | AInc (a : ast)
  | ADec (a : ast)
  | AOutput (a : ast)
  | AInput (a : ast)
  | ALoop (body : ast) (a : ast)
  | AEnd.

Inductive execute : ast -> vm -> vm -> Prop :=
  | E_ARight : forall next v v'',
      execute next (VM.shift_right v) v'' ->
      execute (ARight next) v v''
  | E_ALeft : forall next v v' v'',
      VM.shift_left v = Some v' ->
      execute next v' v'' ->
      execute (ALeft next) v v''
  | E_AInc : forall next v v'',
      execute next (VM.add x01 v) v'' ->
      execute (AInc next) v v''
  | E_ADec : forall next v v'',
      execute next (VM.add xff v) v'' ->
      execute (ADec next) (v) v''
  | E_AOutput : forall next l c r o i v'',
      execute next (VM l c r (c :: o) i) v'' ->
      execute (AOutput next) (VM l c r o i) v''
  | E_AInput : forall next v v' v'',
      VM.input v = Some v' ->
      execute next v' v'' ->
      execute (AInput next) v v''
  | E_ALoop_0 : forall body next l r o i v',
      execute next (VM l x00 r o i) v' ->
      execute (ALoop body next) (VM l x00 r o i) v'
  | E_ALoop : forall body next l c r o i v' v'',
      c <> x00 ->
      execute body (VM l c r o i) v' ->
      execute (ALoop body next) v' v'' ->
      execute (ALoop body next) (VM l c r o i) v''
  | E_AEnd : forall v,
      execute AEnd v v.

Definition equiv (a1 a2 : ast) : Prop := forall v v',
  execute a1 v v' <-> execute a2 v v'.

Definition transform_sound (trans : ast -> ast) : Prop := forall a,
  equiv a (trans a).

Fixpoint parse' (ts : list token) : ast * list ast :=
  match ts with
  | t :: ts' =>
      let (body, next) := parse' ts' in
      match t with
      | TRight => (ARight body, next)
      | TLeft => (ALeft body, next)
      | TInc => (AInc body, next)
      | TDec => (ADec body, next)
      | TOutput => (AOutput body, next)
      | TInput => (AInput body, next)
      | THead => match next with
                 | next :: next' => (ALoop body next, next')
                 | [] => (AEnd, [AEnd]) (* unclosed loop *)
                 end
      | TTail => (AEnd, body :: next)
      end
  | [] => (AEnd, [])
  end.

Definition parse (ts : list token) : option ast :=
  match parse' ts with
  | (prog, []) => Some prog
  | _ => None
  end.

Fixpoint flatten (a : ast) : list token :=
  match a with
  | ARight a' => TRight :: flatten a'
  | ALeft a' => TLeft :: flatten a'
  | AInc a' => TInc :: flatten a'
  | ADec a' => TDec :: flatten a'
  | AOutput a' => TOutput :: flatten a'
  | AInput a' => TInput :: flatten a'
  | ALoop body a' => THead :: flatten body ++ TTail :: flatten a'
  | AEnd => []
  end.

Definition cons_right (n : positive) (a : ast) : ast :=
  repeat_apply ARight (Pos.to_nat n) a.

Definition cons_left (n : positive) (a : ast) : ast :=
  repeat_apply ALeft (Pos.to_nat n) a.

Definition cons_add (n : byte) (a : ast) : ast :=
  match Byte.to_Z n with
  | Z0 => a
  | Zpos p => repeat_apply AInc (Pos.to_nat p) a
  | Zneg p => repeat_apply ADec (Pos.to_nat p) a
  end.

Example test_execute : forall a,
  parse (lex ",>+++[-<++>]<-.") = Some a ->
  execute a (VM.make [x02]) (VM [] x07 [] [x07] []).
Proof.
  intros. inversion H; subst; clear H.
  repeat (econstructor || discriminate).
Qed.
