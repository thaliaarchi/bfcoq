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

Fixpoint to_string (ts : list token) : string :=
  match ts with
  | t :: ts' => String (to_ascii t) (to_string ts')
  | [] => EmptyString
  end.

Fixpoint strip_comments (s : string) : string :=
  match s with
  | String a s' => match of_ascii a with
                   | Some _ => String a (strip_comments s')
                   | None => strip_comments s'
                   end
  | EmptyString => EmptyString
  end.

Ltac ascii_cases s :=
  induction s as [| a s IHs];
  [| destruct a as [[] [] [] [] [] [] [] []]; cbn; rewrite IHs];
  reflexivity.

Theorem strip_comments_lex : forall s,
  lex (strip_comments s) = lex s.
Proof. ascii_cases s. Qed.

Theorem lex_to_string : forall s,
  to_string (lex s) = strip_comments s.
Proof. ascii_cases s. Qed.
