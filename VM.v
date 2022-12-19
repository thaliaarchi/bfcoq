Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Strings.Byte.
Require Import Coq.ZArith.ZArith.
Import IfNotations.
Require Import BF.Byte.

Fixpoint repeat_apply {A : Type} (f : A -> A) (n : nat) (a : A) : A :=
  match n with
  | O => a
  | S n' => f (repeat_apply f n' a)
  end.

Fixpoint repeat_apply_option {A : Type} (f : A -> option A) (n : nat) (a : A) : option A :=
  match n with
  | O => Some a
  | S n' => if repeat_apply_option f n' a is Some a' then f a' else None
  end.

Inductive vm : Type :=
  VM (l : list byte) (* cells to the left *)
     (c : byte) (* current cell *)
     (r : list byte) (* cells to the right *)
     (o : list byte) (* outputs *)
     (i : list byte). (* inputs *)

Definition vm_make (i : list byte) : vm := VM [] x00 [] [] i.

Definition vm_right (v : vm) : vm :=
  match v with
  | VM l c (r :: r') o i => VM (c :: l) r r' o i
  | VM l c [] o i => VM (c :: l) x00 [] o i
  end.

Definition vm_left (v : vm) : option vm :=
  match v with
  | VM (l :: l') x00 [] o i => Some (VM l' l [] o i)
  | VM (l :: l') c r o i => Some (VM l' l (c :: r) o i)
  | _ => None
  end.

Definition vm_move_right (n : positive) (v : vm) : vm :=
  repeat_apply vm_right (Pos.to_nat n) v.

Definition vm_move_left (n : positive) (v : vm) : option vm :=
  repeat_apply_option vm_left (Pos.to_nat n) v.

Definition vm_add (n : byte) (v : vm) : vm :=
  match v with VM l c r o i => VM l (byte_add n c) r o i end.

Definition vm_output (v : vm) : vm :=
  match v with VM l c r o i => VM l c r (c :: o) i end.

Definition vm_input (v : vm) : option vm :=
  match v with
  | VM l _ r o (c :: i') => Some (VM l c r o i')
  | _ => None
  end.
