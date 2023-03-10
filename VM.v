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

Fixpoint normalize (bs : list byte) : list byte :=
  match bs with
  | b :: bs' => match normalize bs' with
                | [] => if b =? #00 then [] else [b]
                | bs'' => b :: bs''
                end
  | [] => []
  end.

Fixpoint normalized (bs : list byte) : bool :=
  match bs with
  | [] => true
  | [b] => negb (b =? #00)
  | b :: bs' => normalized bs'
  end.

Lemma norm_normalize : forall bs,
  normalized (normalize bs) = true.
Proof.
  induction bs.
  - reflexivity.
  - cbn. destruct (normalize bs) eqn:Hnorm.
    + destruct (a =? #00) eqn:Heq; [| cbn; rewrite Heq]; reflexivity.
    + apply IHbs.
Qed.

Lemma normalize_idemp : forall bs,
  normalized bs = true -> normalize bs = bs.
Proof.
  induction bs.
  - reflexivity.
  - cbn. destruct bs; intros.
    + apply Bool.negb_true_iff in H. rewrite H. reflexivity.
    + apply IHbs in H. rewrite H. reflexivity.
Qed.

Lemma norm_nil : normalized [] = true.
Proof. reflexivity. Qed.

Lemma norm_tail : forall b bs,
  normalized (b :: bs) = true -> normalized bs = true.
Proof. destruct bs. reflexivity. intros. assumption. Qed.

Lemma norm_cons : forall b1 b2 bs,
  normalized (b1 :: bs) = true -> normalized (b2 :: b1 :: bs) = true.
Proof. intros. assumption. Qed.

Definition single (b : byte) : list byte :=
  if b =? #00 then [] else [b].

Lemma norm_single : forall b,
  normalized (single b) = true.
Proof.
  unfold single. intros. destruct (b =? #00) eqn:Heq.
  - reflexivity.
  - cbn. rewrite Heq. reflexivity.
Qed.

Record vm : Type := VM {
  cells_left : list byte;
  cell : byte;
  cells_right : list byte;
  outputs : list byte;
  inputs : list byte;
  norm : normalized cells_right = true;
}.

Definition make (i : list byte) : vm :=
  VM [] #00 [] [] i norm_nil.

Definition shift_right (v : vm) : vm :=
  match v with
  | VM l c (x :: r') o i H =>
      VM (c :: l) x r' o i (norm_tail _ _ H)
  | VM l c [] o i H =>
      VM (c :: l) #00 [] o i H
  end.

Definition shift_left (v : vm) : option vm :=
  match v with
  | VM (lh :: l') c [] o i H =>
      Some (VM l' lh (single c) o i (norm_single _))
  | VM (lh :: l') c r o i H =>
      Some (VM l' lh (c :: r) o i (norm_cons _ _ _ H))
  | _ => None
  end.

Definition move_right (n : positive) (v : vm) : vm :=
  repeat_apply shift_right (Pos.to_nat n) v.

Definition move_left (n : positive) (v : option vm) : option vm :=
  repeat_apply (apply_if_some shift_left) (Pos.to_nat n) v.

Definition set_cell (n : byte) (v : vm) : vm :=
  let (l, _, r, o, i, H) := v in VM l n r o i H.

Definition add_cell (n : byte) (v : vm) : vm :=
  let (l, c, r, o, i, H) := v in VM l (c + n) r o i H.

Definition output (v : vm) : vm :=
  let (l, c, r, o, i, H) := v in VM l c r (c :: o) i H.

Definition input (v : vm) : option vm :=
  match v with
  | VM l _ r o (i :: i') H => Some (VM l i r o i' H)
  | _ => None
  end.

Fixpoint list_byte_eq (l1 l2 : list byte) : bool :=
  match l1, l2 with
  | h1 :: l1', h2 :: l2' => (h1 =? h2) && list_byte_eq l1' l2'
  | [], [] => true
  | _, _ => false
  end.

Definition eq (v1 v2 : vm) : bool :=
  let (l1, c1, r1, o1, i1, _) := v1 in
  let (l2, c2, r2, o2, i2, _) := v2 in
  list_byte_eq l1 l2 && (c1 =? c2) && list_byte_eq r1 r2
    && list_byte_eq o1 o2 && list_byte_eq i1 i2.

Theorem list_byte_eq_refl : forall l, list_byte_eq l l = true.
Proof.
  induction l.
  - reflexivity.
  - cbn. rewrite Integers.Byte.eq_true, IHl. reflexivity.
Qed.

Theorem eq_refl : forall v, eq v v = true.
Proof.
  destruct v. cbn. repeat rewrite list_byte_eq_refl.
  rewrite Integers.Byte.eq_true. reflexivity.
Qed.

Theorem shift_right_left_refl : forall v,
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
  move_left n (Some (move_right n v)) = Some v.
Proof.
  unfold move_right, move_left.
  intro n. induction (Pos.to_nat n); intros.
  - reflexivity.
  - cbn. rewrite repeat_apply_assoc with (f := shift_right), IHn0.
    cbn. rewrite shift_right_left_refl. reflexivity.
Qed.

Theorem move_right_left_lt : forall n m v,
  (n < m)%positive ->
  move_left m (Some (move_right n v)) = move_left (m - n) (Some v).
Proof.
  unfold move_right, move_left.
  intros. rewrite Pos2Nat.inj_sub by assumption.
  remember (Pos.to_nat n) as n0. remember (Pos.to_nat m) as m0.
  generalize dependent v; generalize dependent m0.
  induction n0; intros.
  - rewrite Nat.sub_0_r. reflexivity.
  - simpl. rewrite repeat_apply_assoc. rewrite IHn0.
Admitted.

Theorem move_right_left_gt : forall n m v,
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
