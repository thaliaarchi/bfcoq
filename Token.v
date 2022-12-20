From BF Require Import Base.

Inductive token : Type :=
  | TRight (* > *)
  | TLeft (* < *)
  | TInc (* + *)
  | TDec (* - *)
  | TOutput (* . *)
  | TInput (* , *)
  | THead (* [ *)
  | TTail. (* ] *)

Definition of_ascii (a : ascii) : option token :=
  match a with
  | ">" => Some TRight
  | "<" => Some TLeft
  | "+" => Some TInc
  | "-" => Some TDec
  | "." => Some TOutput
  | "," => Some TInput
  | "[" => Some THead
  | "]" => Some TTail
  | _ => None
  end%char.

Definition to_ascii (t : token) : ascii :=
  match t with
  | TRight => ">"
  | TLeft => "<"
  | TInc => "+"
  | TDec => "-"
  | TOutput => "."
  | TInput => ","
  | THead => "["
  | TTail => "]"
  end.

Fixpoint lex (s : string) : list token :=
  match s with
  | String a s' => match of_ascii a with
                   | Some t => t :: lex s'
                   | None => lex s'
                   end
  | EmptyString => []
  end.
