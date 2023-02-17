From BF Require Import Base Byte VM.

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

Fixpoint list_map_nth {A : Type} (f : A -> A) (default : A) (n : nat) (l : list A) : list A :=
  match n, l with
  | O, [] => [f default]
  | O, h :: l' => f h :: l'
  | S n', [] => default :: list_map_nth f default n' []
  | S n', h :: l' => h :: list_map_nth f default n' l'
  end.

Definition map_cell (f : byte -> byte) (off : Z) (v : vm) : option vm :=
  match ptr_rel off v with
  | Some p => Some (set_tape (list_map_nth f #00 (N.to_nat p) v.(tape)) v)
  | None => None
  end.

Definition cell (v : vm) : byte :=
  nth (N.to_nat v.(ptr)) v.(tape) #00.

Definition cell_at (off : Z) (v : vm) : option byte :=
  match ptr_rel off v with
  | Some p => Some (nth (N.to_nat p) v.(tape) #00)
  | None => None
  end.

Definition set_cell (n : byte) := map_cell (fun _ => n).

Definition add_cell (n : byte) := map_cell (fun c => c + n).

Definition output (off : Z) (v : vm) : option vm :=
  match cell_at off v with
  | Some c => Some (set_outputs (c :: v.(outputs)) v)
  | None => None
  end.

Definition input (off : Z) (v : vm) : option vm :=
  match v.(inputs) with
  | h :: i' => set_cell h off (set_inputs i' v)
  | [] => None
  end.

Definition eq (v1 v2 : vm) : bool :=
  let (t1, p1, o1, i1) := v1 in
  let (t2, p2, o2, i2) := v2 in
  VM.list_byte_eq t1 t2 && (p1 =? p2)%N
    && VM.list_byte_eq o1 o2 && VM.list_byte_eq i1 i2.

Theorem eq_refl : forall v,
  eq v v = true.
Proof.
  destruct v. cbn.
  repeat rewrite list_byte_eq_refl. now rewrite N.eqb_refl. Qed.
