From BF Require Import Base Byte AST.

Inductive relir : Type :=
  | RMove (move : Z) (r : relir)
  | RAdd (n : byte) (off : Z) (r : relir)
  | ROutput (off : Z) (r : relir)
  | RInput (off : Z) (r : relir)
  | RLoop (body : relir) (r : relir)
  | REnd.

Fixpoint lower_ast (a : ast) : relir :=
  match a with
  | ARight a' => RMove 1 (lower_ast a')
  | ALeft a' => RMove (-1) (lower_ast a')
  | AInc a' => RAdd #01 0 (lower_ast a')
  | ADec a' => RAdd #ff 0 (lower_ast a')
  | AOutput a' => ROutput 0 (lower_ast a')
  | AInput a' => RInput 0 (lower_ast a')
  | ALoop body a' => RLoop (lower_ast body) (lower_ast a')
  | AEnd => REnd
  end.
