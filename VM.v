From BF Require Import Base Byte.

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

Theorem repeat_apply_assoc : forall A f n (a : A),
  f (repeat_apply f n a) = repeat_apply f n (f a).
Proof.
  induction n; intros.
  - reflexivity.
  - cbn. rewrite IHn. reflexivity.
Qed.

Inductive vm : Type :=
  VM (l : list byte) (* cells to the left *)
     (c : byte) (* current cell *)
     (r : list byte) (* cells to the right *)
     (o : list byte) (* outputs *)
     (i : list byte). (* inputs *)

Definition make (i : list byte) : vm := VM [] x00 [] [] i.

Definition shift_right (v : vm) : vm :=
  match v with
  | VM l c (r :: r') o i => VM (c :: l) r r' o i
  | VM l c [] o i => VM (c :: l) x00 [] o i
  end.

Definition shift_left (v : vm) : option vm :=
  match v with
  | VM (l :: l') x00 [] o i => Some (VM l' l [] o i)
  | VM (l :: l') c r o i => Some (VM l' l (c :: r) o i)
  | _ => None
  end.

Definition move_right (n : positive) (v : vm) : vm :=
  repeat_apply shift_right (Pos.to_nat n) v.

Definition move_left (n : positive) (v : vm) : option vm :=
  repeat_apply_option shift_left (Pos.to_nat n) v.

Definition add (n : byte) (v : vm) : vm :=
  match v with VM l c r o i => VM l (Byte.add n c) r o i end.

Definition output (v : vm) : vm :=
  match v with VM l c r o i => VM l c r (c :: o) i end.

Definition input (v : vm) : option vm :=
  match v with
  | VM l _ r o (i :: i') => Some (VM l i r o i')
  | _ => None
  end.

Fixpoint normalize_tape_right (r : list byte) : list byte :=
  match r with
  | [] | [x00] => []
  | x00 :: r' => match normalize_tape_right r' with
                 | [] => []
                 | r'' => x00 :: r''
                 end
  | r :: r' => r :: normalize_tape_right r'
  end.

Definition normalize (v : vm) : vm :=
  match v with VM l c r o i => VM l c (normalize_tape_right r) o i end.

Theorem normalize_idemp : forall v,
  normalize (normalize v) = normalize v.
Proof.
  destruct v. unfold normalize. f_equal.
  induction r.
  - reflexivity.
  - destruct a; try (cbn; rewrite IHr; reflexivity).
Admitted.

Theorem shift_right_normalize_assoc : forall v,
  normalize (shift_right v) = shift_right (normalize v).
Proof.
  destruct v. induction r.
  - reflexivity.
  - admit.
Admitted.

Theorem shift_right_left_refl : forall v,
  v = normalize v ->
  shift_left (shift_right v) = Some v.
Proof.
  intros. destruct v. unfold shift_right, shift_left.
  induction r.
  - reflexivity.
  - destruct a; try reflexivity.
    destruct r; [discriminate | reflexivity].
Qed.

Theorem move_right_left_refl : forall n v,
  v = normalize v ->
  move_left n (move_right n v) = Some v.
Proof.
  unfold move_right, move_left.
  intro n. induction (Pos.to_nat n); intros.
  - reflexivity.
  - cbn. rewrite repeat_apply_assoc, IHn0.
    rewrite shift_right_left_refl. reflexivity. assumption.
    rewrite shift_right_normalize_assoc, <- H. reflexivity.
Qed.

Theorem move_right_right : forall n m v,
  move_right m (move_right n v) = move_right (n + m) v.
Proof.
  destruct v. unfold move_right. rewrite Pos2Nat.inj_add.
  induction (Pos.to_nat n); cbn.
  - reflexivity.
  - rewrite <- repeat_apply_assoc. rewrite IHn0. reflexivity.
Qed.

Theorem add_add : forall n m v,
  add m (add n v) = add (Byte.add n m) v.
Proof.
  destruct v. cbn.
  rewrite Byte.add_assoc, (Byte.add_comm m n). reflexivity.
Qed.
