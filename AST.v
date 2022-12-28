From BF Require Import Base Byte RelVM VM Token.

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
  | E_ARight : forall a v v'',
      execute a (VM.shift_right v) v'' ->
      execute (ARight a) v v''
  | E_ALeft : forall a v v' v'',
      VM.shift_left v = Some v' ->
      execute a v' v'' ->
      execute (ALeft a) v v''
  | E_AInc : forall a v v'',
      execute a (VM.add_cell #01 v) v'' ->
      execute (AInc a) v v''
  | E_ADec : forall a v v'',
      execute a (VM.add_cell #ff v) v'' ->
      execute (ADec a) (v) v''
  | E_AOutput : forall a v v'',
      execute a (VM.output v) v'' ->
      execute (AOutput a) v v''
  | E_AInput : forall a v v' v'',
      VM.input v = Some v' ->
      execute a v' v'' ->
      execute (AInput a) v v''
  | E_ALoop : forall body a v v' v'',
      v.(cell) =? #00 = false ->
      execute body v v' ->
      execute (ALoop body a) v' v'' ->
      execute (ALoop body a) v v''
  | E_ALoop_0 : forall body a v v',
      v.(cell) =? #00 = true ->
      execute a v v' ->
      execute (ALoop body a) v v'
  | E_AEnd : forall v v',
      VM.eq v v' = true ->
      execute AEnd v v'.

Inductive execute_rel : ast -> RelVM.vm -> RelVM.vm -> Prop :=
  | ER_ARight : forall a v v' v'',
      RelVM.move 1 v = Some v' ->
      execute_rel a v' v'' ->
      execute_rel (ARight a) v v''
  | ER_ALeft : forall a v v' v'',
      RelVM.move (-1) v = Some v' ->
      execute_rel a v' v'' ->
      execute_rel (ALeft a) v v''
  | ER_AInc : forall a v v' v'',
      RelVM.add_cell #01 0 v = Some v' ->
      execute_rel a v' v'' ->
      execute_rel (AInc a) v v''
  | ER_ADec : forall a v v' v'',
      RelVM.add_cell #ff 0 v = Some v' ->
      execute_rel a v' v'' ->
      execute_rel (ADec a) (v) v''
  | ER_AOutput : forall a v v' v'',
      RelVM.output 0 v = Some v' ->
      execute_rel a v' v'' ->
      execute_rel (AOutput a) v v''
  | ER_AInput : forall a v v' v'',
      RelVM.input 0 v = Some v' ->
      execute_rel a v' v'' ->
      execute_rel (AInput a) v v''
  | ER_ALoop : forall body a v v' v'',
      RelVM.cell v =? #00 = false ->
      execute_rel body v v' ->
      execute_rel (ALoop body a) v' v'' ->
      execute_rel (ALoop body a) v v''
  | ER_ALoop_0 : forall body a v v',
      RelVM.cell v =? #00 = true ->
      execute_rel a v v' ->
      execute_rel (ALoop body a) v v'
  | ER_AEnd : forall v v',
      RelVM.eq v v' = true ->
      execute_rel AEnd v v'.

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

Theorem flatten_parse : forall ts a,
  parse ts = Some a ->
  flatten a = ts.
Proof. Admitted.

Theorem parse_flatten : forall a,
  parse (flatten a) = Some a.
Proof. Admitted.

Definition cons_right (n : positive) (a : ast) : ast :=
  repeat_apply ARight (Pos.to_nat n) a.

Definition cons_left (n : positive) (a : ast) : ast :=
  repeat_apply ALeft (Pos.to_nat n) a.

Definition cons_add (n : byte) (a : ast) : ast :=
  match Integers.Byte.signed n with
  | Z0 => a
  | Zpos p => repeat_apply AInc (Pos.to_nat p) a
  | Zneg p => repeat_apply ADec (Pos.to_nat p) a
  end.

Example test_execute : forall a,
  parse (lex ",>+++[-<++>]<-.") = Some a ->
  execute a (VM.make [#02]) (VM [] #07 [] [#07] [] VM.norm_nil).
Proof.
  intros. inversion H; subst; clear H.
  repeat (apply E_ARight
       || (eapply E_ALeft; [reflexivity |])
       || apply E_AInc
       || apply E_ADec
       || apply E_AOutput
       || (eapply E_AInput; [reflexivity |])
       || (eapply E_ALoop; [reflexivity | |])
       || (eapply E_ALoop_0; [reflexivity |])
       || (apply E_AEnd; apply VM.eq_refl)).
  apply E_AEnd. reflexivity.
Qed.
