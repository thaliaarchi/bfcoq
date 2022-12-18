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
  | IMove (n : Z) (i : ir)
  | IAdd (n : byte) (i : ir)
  | IOutput (i : ir)
  | IInput (i : ir)
  | ILoop (body : ir) (i : ir)
  | IEnd.

Inductive ir_execute : ir -> vm -> vm -> Prop :=
  | E_IMove : forall n next v v' v'',
      vm_move n v = Some v' ->
      ir_execute next v' v'' ->
      ir_execute (IMove n next) v v''
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

Example test_ir_execute : forall a,
  parse (lex ",>+++[-<++>]<-.") = Some a ->
  ir_execute (ast_lower a) (vm_make [x02]) (VM [] x07 [] [x07] []).
Proof.
  intros. inversion H; subst; clear H.
  repeat (econstructor || discriminate).
Qed.
