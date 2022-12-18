Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Byte.
Require Import Coq.ZArith.ZArith.
Require Import BF.Byte.
Require Import BF.VM.
Require Import BF.Token.

Inductive ast : Type :=
  | ARight (a : ast)
  | ALeft (a : ast)
  | AInc (a : ast)
  | ADec (a : ast)
  | AOutput (a : ast)
  | AInput (a : ast)
  | ALoop (body : ast) (a : ast)
  | AEnd.

Inductive ast_execute : ast -> vm -> vm -> Prop :=
  | E_ARight_nil : forall next l c o i v'',
      ast_execute next (VM (c :: l) x00 [] o i) v'' ->
      ast_execute (ARight next) (VM l c [] o i) v''
  | E_ARight : forall next l c x r' o i v'',
      ast_execute next (VM (c :: l) x r' o i) v'' ->
      ast_execute (ARight next) (VM l c (x :: r') o i) v''
  | E_ALeft_nil : forall next x l' o i v'',
      ast_execute next (VM l' x [] o i) v'' ->
      ast_execute (ALeft next) (VM (x :: l') x00 [] o i) v''
  | E_ALeft : forall next x l' c r o i v'',
      ast_execute next (VM l' x (c :: r) o i) v'' ->
      ast_execute (ALeft next) (VM (x :: l') c r o i) v''
  | E_AInc : forall next l c r o i v'',
      ast_execute next (VM l (byte_add x01 c) r o i) v'' ->
      ast_execute (AInc next) (VM l c r o i) v''
  | E_ADec : forall next l c r o i v'',
      ast_execute next (VM l (byte_add xff c) r o i) v'' ->
      ast_execute (ADec next) (VM l c r o i) v''
  | E_AOutput : forall next l c r o i v'',
      ast_execute next (VM l c r (c :: o) i) v'' ->
      ast_execute (AOutput next) (VM l c r o i) v''
  | E_AInput : forall next l c r o x i' v'',
      ast_execute next (VM l x r o i') v'' ->
      ast_execute (AInput next) (VM l c r o (x :: i')) v''
  | E_ALoop_0 : forall body next l r o i v',
      ast_execute next (VM l x00 r o i) v' ->
      ast_execute (ALoop body next) (VM l x00 r o i) v'
  | E_ALoop : forall body next l c r o i v' v'',
      c <> x00 ->
      ast_execute body (VM l c r o i) v' ->
      ast_execute (ALoop body next) v' v'' ->
      ast_execute (ALoop body next) (VM l c r o i) v''
  | E_AEnd : forall v,
      ast_execute AEnd v v.

Fixpoint parse' (ts : list token) : ast * list ast :=
  match ts with
  | t :: ts' =>
      match parse' ts' with (body, next) =>
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
      end end
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

Definition ast_cons_move (n : Z) (a : ast) : ast :=
  match n with
  | Z0 => a
  | Zpos p => repeat_apply ARight (Pos.to_nat p) a
  | Zneg p => repeat_apply ALeft (Pos.to_nat p) a
  end.

Definition ast_cons_add (n : byte) (a : ast) : ast :=
  match byte_to_Z n with
  | Z0 => a
  | Zpos p => repeat_apply AInc (Pos.to_nat p) a
  | Zneg p => repeat_apply ADec (Pos.to_nat p) a
  end.

Example test_ast_execute : forall a,
  parse (lex "++>+++[-<++>]<-.") = Some a ->
  ast_execute a (vm_make []) (VM [] x07 [] [x07] []).
Proof.
  intros. inversion H; subst; clear H.
  repeat (constructor || (eapply E_ALoop; [discriminate | |])).
Qed.
