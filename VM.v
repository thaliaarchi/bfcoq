From BF Require Import Base Byte.

Fixpoint repeat_apply {A : Type} (f : A -> A) (n : nat) (a : A) : A :=
  match n with
  | O => a
  | S n' => f (repeat_apply f n' a)
  end.

Definition apply_if_some {A : Type} (f : A -> option A) : option A -> option A :=
  fun a => if a is Some a' then f a' else None.

Lemma repeat_apply_assoc : forall A f n (a : A),
  f (repeat_apply f n a) = repeat_apply f n (f a).
Proof.
  induction n; intros.
  - reflexivity.
  - cbn. rewrite IHn. reflexivity.
Qed.

Lemma repeat_apply_add : forall A f n m (a : A),
  repeat_apply f m (repeat_apply f n a) = repeat_apply f (n + m) a.
Proof.
  induction n; intros.
  - reflexivity.
  - cbn. rewrite <- repeat_apply_assoc. rewrite IHn. reflexivity.
Qed.

Lemma repeat_apply_option_add : forall A f m n (a : option A),
  repeat_apply (apply_if_some f) m (repeat_apply (apply_if_some f) n a)
  =
  repeat_apply (apply_if_some f) (n + m) a.
Proof.
  induction m; intros.
  - subst. rewrite Nat.add_0_r. reflexivity.
  - rewrite <- Nat.add_succ_comm. cbn. rewrite IHm. reflexivity.
Qed.

Lemma repeat_apply_none : forall (A : Type) (f : A -> option A) n,
  repeat_apply (apply_if_some f) n None = None.
Proof.
  induction n.
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

Definition move_left (n : positive) (v : option vm) : option vm :=
  repeat_apply (apply_if_some shift_left) (Pos.to_nat n) v.

Definition add (n : byte) (v : vm) : vm :=
  let (l, c, r, o, i) := v in VM l (Byte.add n c) r o i.

Definition output (v : vm) : vm :=
  let (l, c, r, o, i) := v in VM l c r (c :: o) i.

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
  let (l, c, r, o, i) := v in VM l c (normalize_tape_right r) o i.

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
  unfold shift_right, shift_left.
  intros. destruct v. induction r.
  - reflexivity.
  - destruct a; try reflexivity.
    destruct r; [discriminate | reflexivity].
Qed.

Theorem move_right_left_refl : forall n v,
  v = normalize v ->
  move_left n (Some (move_right n v)) = Some v.
Proof.
  unfold move_right, move_left.
  intro n. induction (Pos.to_nat n); intros.
  - reflexivity.
  - cbn. rewrite repeat_apply_assoc with (f := shift_right), IHn0.
    cbn. rewrite shift_right_left_refl. reflexivity. assumption.
    rewrite shift_right_normalize_assoc, <- H. reflexivity.
Qed.

Theorem move_right_right : forall n m v,
  move_right m (move_right n v) = move_right (n + m) v.
Proof.
  unfold move_right. intros. rewrite Pos2Nat.inj_add.
  induction (Pos.to_nat n).
  - reflexivity.
  - cbn. rewrite <- repeat_apply_assoc. rewrite IHn0. reflexivity.
Qed.

Theorem move_left_left : forall n m v,
  move_left m (move_left n v) = move_left (n + m) v.
Proof.
  unfold move_left; intros. rewrite Pos2Nat.inj_add.
  apply repeat_apply_option_add.
Qed.

Theorem add_add : forall n m v,
  add m (add n v) = add (Byte.add n m) v.
Proof.
  destruct v. cbn.
  rewrite Byte.add_assoc, (Byte.add_comm m n). reflexivity.
Qed.
