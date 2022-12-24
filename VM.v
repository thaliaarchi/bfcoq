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
  induction n; intros; [| cbn; rewrite IHn]; reflexivity. Qed.

Lemma repeat_apply_add : forall A f n m (a : A),
  repeat_apply f n (repeat_apply f m a) = repeat_apply f (n + m) a.
Proof.
  induction n; intros; [| cbn; rewrite IHn]; reflexivity. Qed.

Lemma repeat_apply_none : forall A (f : A -> option A) n,
  repeat_apply (apply_if_some f) n None = None.
Proof.
  induction n; intros; [| cbn; rewrite IHn]; reflexivity. Qed.

Inductive vm : Type :=
  VM (l : list byte) (* cells to the left *)
     (c : byte) (* current cell *)
     (r : list byte) (* cells to the right *)
     (o : list byte) (* outputs *)
     (i : list byte). (* inputs *)

Definition make (i : list byte) : vm := VM [] #00 [] [] i.

Definition shift_right (v : vm) : vm :=
  match v with
  | VM l c (r :: r') o i => VM (c :: l) r r' o i
  | VM l c [] o i => VM (c :: l) #00 [] o i
  end.

Definition shift_left (v : vm) : option vm :=
  match v with
  | VM (l :: l') c r o i => Some (VM l' l (c :: r) o i)
  | _ => None
  end.

Definition move_right (n : positive) (v : vm) : vm :=
  repeat_apply shift_right (Pos.to_nat n) v.

Definition move_left (n : positive) (v : option vm) : option vm :=
  repeat_apply (apply_if_some shift_left) (Pos.to_nat n) v.

Definition get_cell (v : vm) : byte :=
  let (_, c, _, _, _) := v in c.

Definition set_cell (n : byte) (v : vm) : vm :=
  let (l, _, r, o, i) := v in VM l n r o i.

Definition add_cell (n : byte) (v : vm) : vm :=
  let (l, c, r, o, i) := v in VM l (c + n) r o i.

Definition output (v : vm) : vm :=
  let (l, c, r, o, i) := v in VM l c r (c :: o) i.

Definition input (v : vm) : option vm :=
  match v with
  | VM l _ r o (i :: i') => Some (VM l i r o i')
  | _ => None
  end.

Fixpoint normalize_tape_right (r : list byte) : list byte :=
  match r with
  | [] => []
  | r0 :: r' => match normalize_tape_right r' with
                | [] => if r0 =? #00 then [] else [r0]
                | r'' => r0 :: r''
                end
  end.

Definition normalize (v : vm) : vm :=
  let (l, c, r, o, i) := v in VM l c (normalize_tape_right r) o i.

Fixpoint all_0 (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' => (b =? #00) && all_0 bs'
  end.

Fixpoint eq_tape_right (r1 r2 : list byte) : bool :=
  match r1, r2 with
  | [], [] => true
  | x :: r1', y :: r2' => (x =? y) && eq_tape_right r1' r2'
  | r1, [] => all_0 r1
  | [], r2 => all_0 r2
  end.

Theorem normalize_idemp : forall v,
  normalize (normalize v) = normalize v.
Proof. Admitted.

Theorem shift_right_normalize_assoc : forall v,
  normalize (shift_right v) = shift_right (normalize v).
Proof. Admitted.

Theorem shift_right_left_refl : forall v,
  v = normalize v ->
  shift_left (shift_right v) = Some v.
Proof. Admitted.

Theorem move_right_add : forall n m v,
  move_right m (move_right n v) = move_right (n + m) v.
Proof.
  unfold move_right. intros. rewrite Pos2Nat.inj_add.
  induction (Pos.to_nat n).
  - reflexivity.
  - cbn. rewrite <- repeat_apply_assoc. rewrite IHn0. reflexivity.
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

Theorem move_right_left_lt : forall n m v,
  v = normalize v ->
  (n < m)%positive ->
  move_left m (Some (move_right n v)) = move_left (m - n) (Some v).
Proof. Admitted.

Theorem move_right_left_gt : forall n m v,
  v = normalize v ->
  (m < n)%positive ->
  move_left m (Some (move_right n v)) = Some (move_right (n - m) v).
Proof. Admitted.

Theorem move_left_add : forall n m v,
  move_left n (move_left m v) = move_left (n + m) v.
Proof.
  unfold move_left; intros. rewrite Pos2Nat.inj_add.
  apply repeat_apply_add.
Qed.

Theorem move_left_combine : forall n m v v' v'',
  move_left m (Some v) = Some v' ->
  move_left n (Some v') = Some v'' ->
  move_left (n + m) (Some v) = Some v''.
Proof.
  intros. rewrite <- move_left_add, H, H0. reflexivity.
Qed.

Theorem move_left_split : forall n m v v'',
  move_left n (move_left m (Some v)) = Some v'' ->
  exists v', move_left m (Some v) = Some v' /\
             move_left n (Some v') = Some v''.
Proof.
  intros. remember (move_left m (Some v)). destruct o.
  - exists v0. split. reflexivity. assumption.
  - unfold move_left in H. rewrite repeat_apply_none in H. discriminate.
Qed.

Theorem add_add : forall n m v,
  add_cell m (add_cell n v) = add_cell (n + m) v.
Proof.
  destruct v. cbn.
  rewrite <- Integers.Byte.add_assoc. reflexivity.
Qed.
