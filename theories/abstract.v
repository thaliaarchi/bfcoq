Require Import NArith.
Require Import ZArith.
Require Import List. Import ListNotations.
Import IfNotations.

Local Open Scope bool_scope.

Ltac invert H := inversion H; subst; clear H.

Ltac prop_bool :=
  repeat match goal with
         | H : _ && _ = true |- _ => apply Bool.andb_true_iff in H as []
         | H : _ && _ = false |- _ => apply Bool.andb_false_iff in H
         | H : _ || _ = true |- _ => apply Bool.orb_true_iff in H
         | H : _ || _ = false |- _ => apply Bool.orb_false_iff in H as []
         | |- _ && _ = true => apply Bool.andb_true_iff
         | |- _ && _ = false => apply Bool.andb_false_iff
         | |- _ || _ = true => apply Bool.orb_true_iff
         | |- _ || _ = false => apply Bool.orb_false_iff
         end.

Module Byte.

Local Open Scope N_scope.

Record byte := MkByte {
  val : N;
  range : val < 256;
}.

Definition zero : byte := MkByte 0 eq_refl.
Definition one : byte := MkByte 1 eq_refl.
Definition max : byte := MkByte 255 eq_refl.

Definition of_N (n : N) : byte.
  now apply (MkByte (n mod 256)), N.mod_lt.
Defined.

Definition add (b1 b2 : byte) : byte :=
  of_N (b1.(val) + b2.(val)).

Definition inc (b : byte) : byte := add one b.
Definition dec (b : byte) : byte := add max b.

Definition eq (b1 b2 : byte) : Prop := N.eq b1.(val) b2.(val).

Definition eq_refl : forall b, eq b b.
Proof. intros. apply N.eq_refl. Qed.

Definition eq_sym : forall b1 b2, eq b1 b2 -> eq b2 b1.
Proof. intros ? ?. apply N.eq_sym. Qed.

Definition eq_trans : forall b1 b2 b3, eq b1 b2 -> eq b2 b3 -> eq b1 b3.
Proof. intros ? ? ?. apply N.eq_trans. Qed.

Add Relation byte eq
  reflexivity proved by eq_refl
  symmetry proved by eq_sym
  transitivity proved by eq_trans
  as eq_rel.

Definition eqb (b1 b2 : byte) : bool := N.eqb b1.(val) b2.(val).

Theorem eqb_eq : forall b1 b2, eqb b1 b2 = true <-> eq b1 b2.
Proof. intros. unfold eqb. apply N.eqb_eq. Qed.

Theorem eqb_neq : forall b1 b2, eqb b1 b2 = false <-> ~ eq b1 b2.
Proof. intros. unfold eqb. apply N.eqb_neq. Qed.

Definition eqb_refl : forall b, eqb b b = true.
Proof. intros. apply N.eqb_refl. Qed.

Definition eqb_sym : forall b1 b2, eqb b1 b2 = eqb b2 b1.
Proof. intros. apply N.eqb_sym. Qed.

Definition eqb_trans :
  forall b1 b2 b3, eqb b1 b2 = true -> eqb b2 b3 = true -> eqb b1 b3 = true.
Proof. intros ? ? ?. repeat rewrite eqb_eq. apply eq_trans. Qed.

End Byte.

Notation byte := Byte.byte.

Module VM.

Open Scope N_scope.

Inductive bound :=
  | BFinite (n : N)
  | BInfinite.

Definition N_bounded (n : N) (b : bound) : Prop :=
  if b is BFinite b then n < b else True.

Definition Z_bounded (n : Z) (lbound rbound : bound) : Prop :=
  match n with
  | Zneg p => N_bounded (Npos p) lbound
  | _ => N_bounded (Z.to_N n) rbound
  end.

Definition tape_bounded (tape : list byte) (b : bound) : Prop :=
  if b is BFinite n then N.of_nat (length tape) <= n else True.

Record vm := MkVM {
  ptr : Z;
  ltape : list byte;
  rtape : list byte;
  inputs : list byte;
  outputs : list byte;

  lbound : bound;
  rbound : bound;
  ptr_bounded : Z_bounded ptr lbound rbound;
  ltape_bounded : tape_bounded ltape lbound;
  rtape_bounded : tape_bounded rtape rbound;
}.

Definition classic : vm.
Proof. now apply (MkVM 0 [] [] [] [] (BFinite 0) (BFinite 30000)). Defined.

Definition unbounded : vm.
Proof. now apply (MkVM 0 [] [] [] [] BInfinite BInfinite). Defined.

Fixpoint tape_empty (t : list byte) : bool :=
  match t with
  | c :: t' => Byte.eqb c Byte.zero && tape_empty t'
  | [] => true
  end.

Fixpoint tape_eqb (t1 t2 : list byte) : bool :=
  match t1, t2 with
  | c1 :: t1', c2 :: t2' => Byte.eqb c1 c2 && tape_eqb t1' t2'
  | [], t | t, [] => tape_empty t
  end.

Fixpoint io_eqb (l1 l2 : list byte) : bool :=
  match l1, l2 with
  | a1 :: l1', a2 :: l2' => Byte.eqb a1 a2 && io_eqb l1' l2'
  | [], [] => true
  | _, _ => false
  end.

Definition bound_eqb (b1 b2 : bound) : bool :=
  match b1, b2 with
  | BFinite n1, BFinite n2 => N.eqb n1 n2
  | BInfinite, BInfinite => true
  | _, _ => false
  end.

Definition eqb (v1 v2 : vm) : bool :=
  let (i1, l1, r1, in1, out1, lb1, rb1, _, _, _) := v1 in
  let (i2, l2, r2, in2, out2, lb2, rb2, _, _, _) := v2 in
  Z.eqb i1 i2 &&
  tape_eqb l1 l2 && tape_eqb r1 r2 &&
  io_eqb in1 in2 && io_eqb out1 out2 &&
  bound_eqb lb1 lb2 && bound_eqb rb1 rb2.

Theorem tape_eqb_refl : forall t, tape_eqb t t = true.
Proof.
  induction t. reflexivity. cbn. now rewrite Byte.eqb_refl, IHt. Qed.

Theorem tape_eqb_sym : forall t1 t2, tape_eqb t1 t2 = tape_eqb t2 t1.
Proof.
  induction t1; destruct t2; try reflexivity.
  cbn. now rewrite Byte.eqb_sym, IHt1. Qed.

Theorem tape_eqb_nil_r : forall t, tape_eqb t [] = tape_empty t.
Proof. now induction t. Qed.

Theorem tape_eqb_empty : forall t1 t2,
  tape_eqb t1 t2 = true -> tape_empty t1 = tape_empty t2.
Proof.
  induction t1; cbn; intros. { now rewrite H. }
  induction t2; cbn. { assumption. }
  apply Bool.andb_true_iff in H as [].
  unfold Byte.eqb in *. apply N.eqb_eq in H. now erewrite H, IHt1. Qed.

Theorem tape_empty_empty_eqb : forall t1 t2,
  tape_empty t1 = true -> tape_empty t2 = true -> tape_eqb t1 t2 = true.
Proof.
  induction t1; cbn.
  - intros. assumption.
  - destruct t2; cbn; intros.
    + assumption.
    + prop_bool. rewrite Byte.eqb_eq in *.
      split. now rewrite H0. now apply IHt1. Qed.

Theorem tape_empty_eqb_empty : forall t1 t2,
  tape_empty t1 = true -> tape_eqb t1 t2 = true -> tape_empty t2 = true.
Proof.
  induction t1; cbn.
  - intros. assumption.
  - destruct t2; cbn; intros.
    + reflexivity.
    + prop_bool. rewrite Byte.eqb_eq in *.
      split. now rewrite <- H0. now apply IHt1. Qed.

Theorem tape_eqb_trans : forall t1 t2 t3,
  tape_eqb t1 t2 = true -> tape_eqb t2 t3 = true -> tape_eqb t1 t3 = true.
Proof.
  induction t1; cbn; intros.
  - apply tape_eqb_empty in H0. now rewrite <- H0.
  - induction t2, t3; cbn in *.
    + assumption.
    + prop_bool. split.
      * rewrite Byte.eqb_eq in *. now rewrite H0.
      * now apply tape_empty_empty_eqb.
    + prop_bool. split.
      * rewrite Byte.eqb_eq in *. now rewrite H.
      * eapply tape_empty_eqb_empty. eassumption. now rewrite tape_eqb_sym.
    + prop_bool. split.
      * rewrite Byte.eqb_eq in *. now rewrite H.
      * eapply IHt1; eassumption.
Qed.

Theorem io_eqb_refl : forall l, io_eqb l l = true.
Proof.
  induction l. reflexivity. cbn. now rewrite Byte.eqb_refl, IHl. Qed.

Theorem io_eqb_sym : forall l1 l2, io_eqb l1 l2 = io_eqb l2 l1.
Proof.
  induction l1; destruct l2; try reflexivity.
  cbn. now rewrite Byte.eqb_sym, IHl1. Qed.

Theorem io_eqb_trans : forall l1 l2 l3,
  io_eqb l1 l2 = true -> io_eqb l2 l3 = true -> io_eqb l1 l3 = true.
Proof.
  induction l1; destruct l2, l3; try discriminate. { reflexivity. }
  cbn. intros. prop_bool. split.
  - rewrite Byte.eqb_eq in *. now rewrite H.
  - eapply IHl1; eassumption. Qed.

Theorem bound_eqb_refl : forall b, bound_eqb b b = true.
Proof.
  destruct b; try reflexivity. apply N.eqb_refl. Qed.

Theorem bound_eqb_sym : forall b1 b2, bound_eqb b1 b2 = bound_eqb b2 b1.
Proof.
  destruct b1, b2; try reflexivity. apply N.eqb_sym. Qed.

Theorem bound_eqb_trans : forall b1 b2 b3,
  bound_eqb b1 b2 = true -> bound_eqb b2 b3 = true -> bound_eqb b1 b3 = true.
Proof.
  destruct b1, b2, b3; try reflexivity; try discriminate.
  cbn. repeat rewrite N.eqb_eq. apply N.eq_trans. Qed.

Theorem eqb_refl : forall v, eqb v v = true.
Proof.
  destruct v. cbn.
  now rewrite Z.eqb_refl, tape_eqb_refl, tape_eqb_refl,
              io_eqb_refl, io_eqb_refl, bound_eqb_refl, bound_eqb_refl. Qed.

Theorem eqb_sym : forall v1 v2, eqb v1 v2 = eqb v2 v1.
Proof.
  destruct v1, v2. cbn. repeat rewrite <- Bool.andb_assoc.
  rewrite Z.eqb_sym. f_equal.
  repeat (rewrite tape_eqb_sym; f_equal).
  repeat (rewrite io_eqb_sym; f_equal).
  repeat (rewrite bound_eqb_sym; f_equal). Qed.

Theorem eqb_trans : forall v1 v2 v3,
  eqb v1 v2 = true -> eqb v2 v3 = true -> eqb v1 v3 = true.
Proof.
  destruct v1, v2, v3. cbn. intros.
  repeat apply Bool.andb_true_iff in H as [], H0 as [].
  repeat rewrite Bool.andb_true_iff. repeat split;
  rewrite Z.eqb_eq in *;
  try (eapply Z.eq_trans || eapply tape_eqb_trans ||
       eapply io_eqb_trans || eapply bound_eqb_trans); try eassumption. Qed.

Definition eq (v1 v2 : vm) : Prop := eqb v1 v2 = true.

Theorem eq_refl : forall v, eq v v.
Proof. apply eqb_refl. Qed.

Theorem eq_sym : forall v1 v2, eq v1 v2 -> eq v2 v1.
Proof. unfold eq. intros. rewrite <- H. apply eqb_sym. Qed.

Theorem eq_trans : forall v1 v2 v3, eq v1 v2 -> eq v2 v3 -> eq v1 v3.
Proof. apply eqb_trans. Qed.

Add Relation vm eq
  reflexivity proved by eq_refl
  symmetry proved by eq_sym
  transitivity proved by eq_trans
  as eq_rel.

End VM.

Module AbstractVM.

Local Open Scope N_scope.

Inductive value :=
  | VSelf
  | VInput
  | VConst (b : byte)
  | VAddC (b : byte) (v : value).

Inductive effect :=
  | EGuard (offset : Z)
  | EInput (ptr : Z)
  | EOutput (v : value).

Definition Z_bounded (n : Z) (lmax rmax : N) : Prop :=
  match n with
  | Zneg p => Npos p < lmax
  | _ => Z.to_N n < rmax
  end.

Definition tape_bounded (tape : list value) (max : N) : Prop :=
  N.of_nat (length tape) <= max.

Record abstract_vm := MkAbstractVM {
  ptr : Z;
  ltape : list value;
  rtape : list value;
  effects : list effect;

  lmax : N;
  rmax : N;
  ptr_bounded : Z_bounded ptr lmax rmax;
  ltape_bounded : tape_bounded ltape lmax;
  rtape_bounded : tape_bounded rtape rmax;
}.

Definition make : abstract_vm.
Proof. now apply (MkAbstractVM 0 [] [] [] 0 1). Defined.

Definition cons_effect (e : effect) (v : abstract_vm) : abstract_vm :=
  let (p, l, r, es, lm, rm, pb, lb, rb) := v in
  MkAbstractVM p l r (e :: es) lm rm pb lb rb.

Definition get_cell (off : Z) (v : abstract_vm) : value :=
  match (v.(ptr) + off)%Z with
  | Zneg p => nth_default VSelf v.(ltape) (Pos.to_nat p)
  | _ as n => nth_default VSelf v.(rtape) (Z.to_nat n)
  end.

Fixpoint list_map_nth {A} (default : A) (f : A -> A) (l : list A) (n : nat) : list A :=
  match n, l with
  | O, [] => [f default]
  | O, h :: l' => f h :: l'
  | S n', [] => default :: list_map_nth default f [] n'
  | S n', h :: l' => h :: list_map_nth default f l' n'
  end.

Theorem list_map_nth_length : forall A default f (l : list A) n,
  length (list_map_nth default f l n) = Nat.max (S n) (length l).
Proof.
  induction l; induction n; intros; try reflexivity; cbn.
  now rewrite IHn. now rewrite IHl. Qed.

Definition map_cell (f : value -> value) (v : abstract_vm) : abstract_vm.
Proof.
  destruct v, ptr0.
  - apply (MkAbstractVM 0 ltape0 (list_map_nth VSelf f rtape0 0) effects0 lmax0 rmax0).
    + assumption.
    + assumption.
    + unfold tape_bounded. rewrite list_map_nth_length.
      destruct rtape0.
      * apply N.le_succ_l in ptr_bounded0. apply ptr_bounded0.
      * apply rtape_bounded0.
  - apply (MkAbstractVM (Z.pos p) ltape0 (list_map_nth VSelf f rtape0 (Pos.to_nat p)) effects0 lmax0 rmax0).
    + assumption.
    + assumption.
    + unfold tape_bounded. rewrite list_map_nth_length.
      destruct (le_gt_dec (S (Pos.to_nat p)) (length rtape0)).
      * apply Nat.max_r in l. rewrite l. apply rtape_bounded0.
      * apply Nat.lt_le_incl, Nat.max_l in g. rewrite g.
        cbn. rewrite Pos2SuccNat.id_succ.
        apply N.le_succ_l in ptr_bounded0. apply ptr_bounded0.
  - apply (MkAbstractVM (Z.neg p) (list_map_nth VSelf f ltape0 (Pos.to_nat p)) rtape0 effects0 lmax0 rmax0).
    + assumption.
    + unfold tape_bounded. rewrite list_map_nth_length.
      destruct (le_gt_dec (S (Pos.to_nat p)) (length ltape0)).
      * apply Nat.max_r in l. rewrite l. apply ltape_bounded0.
      * apply Nat.lt_le_incl, Nat.max_l in g. rewrite g.
        cbn. rewrite Pos2SuccNat.id_succ.
        apply N.le_succ_l in ptr_bounded0. apply ptr_bounded0.
    + assumption.
Defined.

Definition eval_inc := map_cell (VAddC Byte.one).
Definition eval_dec := map_cell (VAddC Byte.max).

Definition eval_left (v : abstract_vm) : abstract_vm.
Admitted.

Definition eval_right (v : abstract_vm) : abstract_vm.
Admitted.

Definition eval_input (v : abstract_vm) : abstract_vm :=
  let v := map_cell (fun _ => VInput) v in
  cons_effect (EInput v.(ptr)) v.

Definition eval_output (v : abstract_vm) : abstract_vm :=
  cons_effect (EOutput (get_cell 0 v)) v.

Inductive ast_block :=
  | IInc (bl : ast_block)
  | IDec (bl : ast_block)
  | ILeft (bl : ast_block)
  | IRight (bl : ast_block)
  | IInput (bl : ast_block)
  | IOutput (bl : ast_block)
  | IEnd.

Inductive block :=
  | BAdd (b : byte) (off : Z) (bl : block)
  | BInput (off : Z) (bl : block)
  | BOutput (off : Z) (bl : block)
  | BGuard (nl nr : N) (bl : block)
  | BMove (n : Z).

End AbstractVM.
