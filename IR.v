Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.Byte.
Require Import Coq.ZArith.ZArith.
Require Import Coq.PArith.PArith.
Import IfNotations.
Require Import BF.Byte.
Require Import BF.AST.

Inductive ir : Type :=
  | IMove (n : Z) (i : ir)
  | IAdd (n : byte) (i : ir)
  | IOutput (i : ir)
  | IInput (i : ir)
  | ILoop (body : ir) (i : ir)
  | IEnd.

Definition ir_cons_move (n : Z) (i : ir) : ir :=
  match i with
  | IMove m i' => if n + m =? 0 then i'
                  else IMove (n + m) i'
  | _ => IMove n i
  end%Z.

Definition ir_cons_add (n : byte) (i : ir) : ir :=
  match i with
  | IAdd m i' => if byte_add n m =? x00 then i'
                 else IAdd (byte_add n m) i'
  | _ => IAdd n i
  end%byte.

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

Fixpoint ir_raise (i : ir) : ast :=
  match i with
  | IMove n i' => ast_cons_move n (ir_raise i')
  | IAdd n i' => ast_cons_add n (ir_raise i')
  | IOutput i' => AOutput (ir_raise i')
  | IInput i' => AInput (ir_raise i')
  | ILoop body i' => ALoop (ir_raise body) (ir_raise i')
  | IEnd => AEnd
  end.

Fixpoint ir_combine (i : ir) : ir :=
  match i with
  | IMove n i' => ir_cons_move n i'
  | IAdd n i' => ir_cons_add n i'
  | IOutput i' => IOutput (ir_combine i')
  | IInput i' => IInput (ir_combine i')
  | ILoop body i' => ILoop (ir_combine body) (ir_combine i')
  | IEnd => IEnd
  end.
