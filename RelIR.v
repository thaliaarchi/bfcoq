From BF Require Import Base Byte.

Inductive relir : Type :=
  | RAdd (n : byte) (off : Z) (r : relir)
  | ROutput (off : Z) (r : relir)
  | RInput (off : Z) (r : relir)
  | RLoop (body : relir) (left : N) (move : Z) (r : relir)
  | REnd.
