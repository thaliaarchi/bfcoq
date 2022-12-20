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

Fixpoint lex (s : string) : list token :=
  match s with
  | String ">" s' => TRight :: lex s'
  | String "<" s' => TLeft :: lex s'
  | String "+" s' => TInc :: lex s'
  | String "-" s' => TDec :: lex s'
  | String "." s' => TOutput :: lex s'
  | String "," s' => TInput :: lex s'
  | String "[" s' => THead :: lex s'
  | String "]" s' => TTail :: lex s'
  | String _ s' => lex s'
  | EmptyString => []
  end.
