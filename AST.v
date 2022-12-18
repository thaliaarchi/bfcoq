Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Strings.Byte.
Require Import Coq.ZArith.ZArith.
Require Import BF.Byte.
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

Fixpoint ast_cons_repeat (node : ast -> ast) (n : nat) (a : ast) : ast :=
  match n with
  | O => a
  | S n' => node (ast_cons_repeat node n' a)
  end.

Definition ast_cons_move (n : Z) (a : ast) : ast :=
  match n with
  | Z0 => a
  | Zpos p => ast_cons_repeat ARight (Pos.to_nat p) a
  | Zneg p => ast_cons_repeat ALeft (Pos.to_nat p) a
  end.

Definition ast_cons_add (n : byte) (a : ast) : ast :=
  match byte_to_Z n with
  | Z0 => a
  | Zpos p => ast_cons_repeat AInc (Pos.to_nat p) a
  | Zneg p => ast_cons_repeat ADec (Pos.to_nat p) a
  end.
