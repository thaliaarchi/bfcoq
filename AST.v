Require Import Coq.Lists.List. Import ListNotations.
Require Import BF.Token.

Inductive ast : Type :=
  | ARight
  | ALeft
  | AInc
  | ADec
  | AOutput
  | AInput
  | ALoop (body : list ast).

Fixpoint parse_inner (ts : list token) : list ast * list (list ast) :=
  match ts with
  | t :: ts' =>
      match parse_inner ts' with (body, next) =>
      match t with
      | TRight => (ARight :: body, next)
      | TLeft => (ALeft :: body, next)
      | TInc => (AInc :: body, next)
      | TDec => (ADec :: body, next)
      | TOutput => (AOutput :: body, next)
      | TInput => (AInput :: body, next)
      | THead => match next with
                 | next :: next' => (ALoop body :: next, next')
                 | [] => ([], [[]]) (* unclosed loop *)
                 end
      | TTail => ([], body :: next)
      end end
  | [] => ([], [])
  end.

Definition parse (ts : list token) : option (list ast) :=
  match parse_inner ts with
  | (prog, []) => Some prog
  | _ => None
  end.
