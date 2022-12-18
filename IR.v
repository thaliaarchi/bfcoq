Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.Byte. Open Scope byte_scope.
Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Import IfNotations.
Require Import BF.AST.

Inductive ir : Type :=
  | IMove (n : Z) (i : ir)
  | IAdd (n : byte) (i : ir)
  | IOutput (i : ir)
  | IInput (i : ir)
  | ILoop (body : ir) (i : ir)
  | IEnd.

Fixpoint ast_lower (a : ast) : ir :=
  match a with
  | ARight a' => IMove 1 (ast_lower a')
  | ALeft a' => IMove (-1) (ast_lower a')
  | AInc a' => IAdd x01 (ast_lower a')
  | ADec a' => IAdd xff (ast_lower a')
  | AOutput a' => IOutput (ast_lower a')
  | AInput a' => IInput (ast_lower a')
  | ALoop body a' => ILoop (ast_lower body) (ast_lower a')
  | AEnd => IEnd
  end.

Definition byte_add (x y : byte) : byte :=
  byte_of_ascii (ascii_of_N (Byte.to_N x + Byte.to_N y)).

Fixpoint ir_combine (i : ir) : ir :=
  match i with
  | IMove n i' =>
      let i' := ir_combine i' in
      if i' is IMove m i'' then IMove (n + m) i'' else IMove n i'
  | IAdd n i' =>
      let i' := ir_combine i' in
      if i' is IAdd m i'' then IAdd (byte_add n m) i'' else IAdd n i'
  | IOutput i' => IOutput (ir_combine i')
  | IInput i' => IInput (ir_combine i')
  | ILoop body i' => ILoop (ir_combine body) (ir_combine i')
  | IEnd => IEnd
  end.
