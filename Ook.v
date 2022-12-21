From BF Require Import Base Token.

Inductive punct : Type :=
  | PPeriod (* . *)
  | PQuestion (* ? *)
  | PBang. (* ! *)

Definition punct_of_ascii (a : ascii) : option punct :=
  match a with
  | "." => Some PPeriod
  | "?" => Some PQuestion
  | "!" => Some PBang
  | _ => None
  end%char.

Definition punct_to_ascii (p : punct) : ascii :=
  match p with
  | PPeriod => "."
  | PQuestion => "?"
  | PBang => "!"
  end.

Fixpoint lex_puncts (s : string) : list punct :=
  match s with
  | String "O" (String "o" (String "k" (String a s'))) =>
      match punct_of_ascii a with
      | Some p => p :: lex_puncts s'
      | None => lex_puncts s'
      end
  | String _ s' => lex_puncts s'
  | EmptyString => []
  end.

Definition punct_to_string (p : punct) : string :=
  String "O" (String "o" (String "k" (String (punct_to_ascii p) EmptyString))).

Definition puncts_to_string (ps : list punct) : string :=
  concat " " (map punct_to_string ps).

Theorem punct_of_to_ascii : forall a p,
  punct_of_ascii a = Some p ->
  punct_to_ascii p = a.
Proof.
  destruct a as [[] [] [] [] [] [] [] []]; intros;
  try discriminate;
  inversion H; reflexivity.
Qed.

Theorem punct_to_of_ascii : forall p,
  punct_of_ascii (punct_to_ascii p) = Some p.
Proof. destruct p; reflexivity. Qed.

Inductive token : Type :=
  | OToken (t : Token.token)
  | OBanana.

Definition token_of_punct (p1 p2 : punct) : token :=
  match p1, p2 with
  | PPeriod, PQuestion => OToken TRight
  | PQuestion, PPeriod => OToken TLeft
  | PPeriod, PPeriod => OToken TInc
  | PBang, PBang => OToken TDec
  | PPeriod, PBang => OToken TInput
  | PBang, PPeriod => OToken TOutput
  | PBang, PQuestion => OToken THead
  | PQuestion, PBang => OToken TTail
  | PQuestion, PQuestion => OBanana
  end.

Definition token_to_punct (t : token) : punct * punct :=
  match t with
  | OToken TRight => (PPeriod, PQuestion)
  | OToken TLeft => (PQuestion, PPeriod)
  | OToken TInc => (PPeriod, PPeriod)
  | OToken TDec => (PBang, PBang)
  | OToken TInput => (PPeriod, PBang)
  | OToken TOutput => (PBang, PPeriod)
  | OToken THead => (PBang, PQuestion)
  | OToken TTail => (PQuestion, PBang)
  | OBanana => (PQuestion, PQuestion)
  end.

Fixpoint tokens_of_puncts (ps : list punct) : list token * option punct :=
  match ps with
  | p1 :: p2 :: ps' => let (ts, p) := tokens_of_puncts ps' in
                       (token_of_punct p1 p2 :: ts, p)
  | [p] => ([], Some p)
  | [] => ([], None)
  end.

Fixpoint tokens_to_puncts (ts : list token) : list punct :=
  match ts with
  | t :: ts' => let (p1, p2) := token_to_punct t in
                p1 :: p2 :: tokens_to_puncts ts'
  | [] => []
  end.

Definition lex (s : string) : list token * option punct :=
  tokens_of_puncts (lex_puncts s).

Definition to_string (ts : list token) : string :=
  puncts_to_string (tokens_to_puncts ts).

Theorem tokens_to_of_puncts : forall ps,
  tokens_of_puncts (tokens_to_puncts ps) = (ps, None).
Proof. Admitted.

Theorem tokens_of_to_puncts_even : forall ps ts,
  tokens_of_puncts ps = (ts, None) ->
  tokens_to_puncts ts = ps.
Proof. Admitted.

Theorem tokens_of_to_puncts_odd : forall ps ts rem,
  tokens_of_puncts (ps ++ [rem]) = (ts, Some rem) ->
  tokens_to_puncts ts = ps.
Proof. Admitted.
