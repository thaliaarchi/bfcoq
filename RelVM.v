From BF Require Import Base Byte.
Require Import Coq.Lists.List.

Record vm := VM {
  tape : list byte;
  ptr : N;
  inputs : list byte;
  outputs : list byte;
}.

Definition set_tape (t : list byte) (v : vm) : vm :=
  let (_, p, i, o) := v in VM t p i o.
Definition set_ptr (p : N) (v : vm) : vm :=
  let (t, _, i, o) := v in VM t p i o.
Definition set_inputs (i : list byte) (v : vm) : vm :=
  let (t, p, _, o) := v in VM t p i o.
Definition set_outputs (o : list byte) (v : vm) : vm :=
  let (t, p, i, _) := v in VM t p i o.

Definition ptr_rel (off : Z) (v : vm) : option N :=
  let i := ((Z.of_N v.(ptr)) + off)%Z in
  match i with
  | Z0 => Some N0
  | Zpos p => Some (Npos p)
  | Zneg _ => None
  end.

Definition move (n : Z) (v : vm) : option vm :=
  match ptr_rel n v with
  | Some p => Some (set_ptr p v)
  | None => None
  end.

Fixpoint extend {A : Type} (n : nat) (l : list A) (default : A) : list A :=
  match n with
  | O => l
  | S n' => match l with
            | [] => default :: extend n' [] default
            | h :: l' => h :: extend n' l' default
            end
  end.

Lemma extend_length : forall A n (l : list A) x,
  n <= length (extend n l x).
Proof.
  induction n; intros.
  - apply Nat.le_0_l.
  - destruct l; cbn; rewrite <- Nat.succ_le_mono; apply IHn.
Qed.

Fixpoint list_map_nth {A : Type} (f : A -> A) (default : A) (n : nat) (l : list A) : list A :=
  match n, l with
  | O, [] => [f default]
  | O, h :: l' => f h :: l'
  | S n', [] => default :: list_map_nth f default n' []
  | S n', h :: l' => h :: list_map_nth f default n' l'
  end.

Definition tape_map_nth (f : byte -> byte) (n : nat) (v : vm) : vm :=
  set_tape (list_map_nth f #00 n v.(tape)) v.
