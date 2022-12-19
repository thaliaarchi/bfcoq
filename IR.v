Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.Byte.
Require Import Coq.ZArith.ZArith.
Require Import Coq.PArith.PArith.
Import IfNotations.
Require Import BF.Byte.
Require Import BF.VM.
Require Import BF.Token.
Require Import BF.AST.

Inductive ir : Type :=
  | IRight (n : positive) (i : ir)
  | ILeft (n : positive) (i : ir)
  | IAdd (n : byte) (i : ir)
  | IOutput (i : ir)
  | IInput (i : ir)
  | ILoop (body : ir) (i : ir)
  | IEnd.

Inductive ir_execute : ir -> vm -> vm -> Prop :=
  | E_IRight : forall n next v v'',
      ir_execute next (vm_move_right n v) v'' ->
      ir_execute (IRight n next) v v''
  | E_ILeft : forall n next v v' v'',
      vm_move_left n v = Some v' ->
      ir_execute next v' v'' ->
      ir_execute (ILeft n next) v v''
  | E_IAdd : forall n next v v'',
      ir_execute next (vm_add n v) v'' ->
      ir_execute (IAdd n next) v v''
  | E_IOutput : forall next v v'',
      ir_execute next (vm_output v) v'' ->
      ir_execute (IOutput next) v v''
  | E_IInput : forall next v v' v'',
      vm_input v = Some v' ->
      ir_execute next v' v'' ->
      ir_execute (IInput next) v v''
  | E_ILoop_0 : forall body next l r o i v',
      ir_execute next (VM l x00 r o i) v' ->
      ir_execute (ILoop body next) (VM l x00 r o i) v'
  | E_ILoop : forall body next l c r o i v' v'',
      c <> x00 ->
      ir_execute body (VM l c r o i) v' ->
      ir_execute (ILoop body next) v' v'' ->
      ir_execute (ILoop body next) (VM l c r o i) v''
  | E_IEnd : forall v,
      ir_execute IEnd v v.

Definition ir_cons_right (n : positive) (i : ir) : ir :=
  match i with
  | IRight m i' => IRight (n + m) i'
  | _ => IRight n i
  end.

Definition ir_cons_left (n : positive) (i : ir) : ir :=
  match i with
  | ILeft m i' => ILeft (n + m) i'
  | IRight m i' => match n ?= m with
                   | Eq => i'
                   | Lt => IRight (m - n) i'
                   | Gt => match i' with
                           | ILeft o i'' => ILeft (n - o) i''
                           | _ => ILeft (n - m) i'
                           end
                   end
  | _ => ILeft n i
  end%positive.

Definition ir_cons_add (n : byte) (i : ir) : ir :=
  match i with
  | IAdd m i' => if byte_add n m =? x00 then i'
                 else IAdd (byte_add n m) i'
  | _ => IAdd n i
  end%byte.

Fixpoint ast_lower (a : ast) : ir :=
  match a with
  | ARight a' => ir_cons_right 1 (ast_lower a')
  | ALeft a' => ir_cons_left 1 (ast_lower a')
  | AInc a' => ir_cons_add x01 (ast_lower a')
  | ADec a' => ir_cons_add xff (ast_lower a')
  | AOutput a' => IOutput (ast_lower a')
  | AInput a' => IInput (ast_lower a')
  | ALoop body a' => ILoop (ast_lower body) (ast_lower a')
  | AEnd => IEnd
  end.

Fixpoint ir_raise (i : ir) : ast :=
  match i with
  | IRight n i' => ast_cons_right n (ir_raise i')
  | ILeft n i' => ast_cons_left n (ir_raise i')
  | IAdd n i' => ast_cons_add n (ir_raise i')
  | IOutput i' => AOutput (ir_raise i')
  | IInput i' => AInput (ir_raise i')
  | ILoop body i' => ALoop (ir_raise body) (ir_raise i')
  | IEnd => AEnd
  end.

Fixpoint ir_combine (i : ir) : ir :=
  match i with
  | IRight n i' => ir_cons_right n i'
  | ILeft n i' => ir_cons_left n i'
  | IAdd n i' => ir_cons_add n i'
  | IOutput i' => IOutput (ir_combine i')
  | IInput i' => IInput (ir_combine i')
  | ILoop body i' => ILoop (ir_combine body) (ir_combine i')
  | IEnd => IEnd
  end.

Example test_ir_execute : forall a,
  parse (lex ",>+++[-<++>]<-.") = Some a ->
  ir_execute (ast_lower a) (vm_make [x02]) (VM [] x07 [] [x07] []).
Proof.
  intros. inversion H; subst; clear H.
  repeat (econstructor || discriminate).
Qed.
