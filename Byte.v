Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.Byte. Open Scope byte_scope.
Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import Coq.PArith.PArith. Open Scope positive_scope.

Definition byte_to_Z (b : byte) : Z :=
  match Byte.to_N b with
  | N0 => Z0
  | Npos p => if p <? 128 then Zpos p else Zneg (p - 256)
  end.

Definition byte_add (x y : byte) : byte :=
  byte_of_ascii (ascii_of_N (Byte.to_N x + Byte.to_N y)).

Definition byte_succ (b : byte) : byte :=
  match b with
	| x00 => x01 | x01 => x02 | x02 => x03 | x03 => x04 | x04 => x05 | x05 => x06 | x06 => x07 | x07 => x08
  | x08 => x09 | x09 => x0a | x0a => x0b | x0b => x0c | x0c => x0d | x0d => x0e | x0e => x0f | x0f => x10
  | x10 => x11 | x11 => x12 | x12 => x13 | x13 => x14 | x14 => x15 | x15 => x16 | x16 => x17 | x17 => x18
  | x18 => x19 | x19 => x1a | x1a => x1b | x1b => x1c | x1c => x1d | x1d => x1e | x1e => x1f | x1f => x20
  | x20 => x21 | x21 => x22 | x22 => x23 | x23 => x24 | x24 => x25 | x25 => x26 | x26 => x27 | x27 => x28
  | x28 => x29 | x29 => x2a | x2a => x2b | x2b => x2c | x2c => x2d | x2d => x2e | x2e => x2f | x2f => x30
  | x30 => x31 | x31 => x32 | x32 => x33 | x33 => x34 | x34 => x35 | x35 => x36 | x36 => x37 | x37 => x38
  | x38 => x39 | x39 => x3a | x3a => x3b | x3b => x3c | x3c => x3d | x3d => x3e | x3e => x3f | x3f => x40
  | x40 => x41 | x41 => x42 | x42 => x43 | x43 => x44 | x44 => x45 | x45 => x46 | x46 => x47 | x47 => x48
  | x48 => x49 | x49 => x4a | x4a => x4b | x4b => x4c | x4c => x4d | x4d => x4e | x4e => x4f | x4f => x50
  | x50 => x51 | x51 => x52 | x52 => x53 | x53 => x54 | x54 => x55 | x55 => x56 | x56 => x57 | x57 => x58
  | x58 => x59 | x59 => x5a | x5a => x5b | x5b => x5c | x5c => x5d | x5d => x5e | x5e => x5f | x5f => x60
  | x60 => x61 | x61 => x62 | x62 => x63 | x63 => x64 | x64 => x65 | x65 => x66 | x66 => x67 | x67 => x68
  | x68 => x69 | x69 => x6a | x6a => x6b | x6b => x6c | x6c => x6d | x6d => x6e | x6e => x6f | x6f => x70
  | x70 => x71 | x71 => x72 | x72 => x73 | x73 => x74 | x74 => x75 | x75 => x76 | x76 => x77 | x77 => x78
  | x78 => x79 | x79 => x7a | x7a => x7b | x7b => x7c | x7c => x7d | x7d => x7e | x7e => x7f | x7f => x80
  | x80 => x81 | x81 => x82 | x82 => x83 | x83 => x84 | x84 => x85 | x85 => x86 | x86 => x87 | x87 => x88
  | x88 => x89 | x89 => x8a | x8a => x8b | x8b => x8c | x8c => x8d | x8d => x8e | x8e => x8f | x8f => x90
  | x90 => x91 | x91 => x92 | x92 => x93 | x93 => x94 | x94 => x95 | x95 => x96 | x96 => x97 | x97 => x98
  | x98 => x99 | x99 => x9a | x9a => x9b | x9b => x9c | x9c => x9d | x9d => x9e | x9e => x9f | x9f => xa0
  | xa0 => xa1 | xa1 => xa2 | xa2 => xa3 | xa3 => xa4 | xa4 => xa5 | xa5 => xa6 | xa6 => xa7 | xa7 => xa8
  | xa8 => xa9 | xa9 => xaa | xaa => xab | xab => xac | xac => xad | xad => xae | xae => xaf | xaf => xb0
  | xb0 => xb1 | xb1 => xb2 | xb2 => xb3 | xb3 => xb4 | xb4 => xb5 | xb5 => xb6 | xb6 => xb7 | xb7 => xb8
  | xb8 => xb9 | xb9 => xba | xba => xbb | xbb => xbc | xbc => xbd | xbd => xbe | xbe => xbf | xbf => xc0
  | xc0 => xc1 | xc1 => xc2 | xc2 => xc3 | xc3 => xc4 | xc4 => xc5 | xc5 => xc6 | xc6 => xc7 | xc7 => xc8
  | xc8 => xc9 | xc9 => xca | xca => xcb | xcb => xcc | xcc => xcd | xcd => xce | xce => xcf | xcf => xd0
  | xd0 => xd1 | xd1 => xd2 | xd2 => xd3 | xd3 => xd4 | xd4 => xd5 | xd5 => xd6 | xd6 => xd7 | xd7 => xd8
  | xd8 => xd9 | xd9 => xda | xda => xdb | xdb => xdc | xdc => xdd | xdd => xde | xde => xdf | xdf => xe0
  | xe0 => xe1 | xe1 => xe2 | xe2 => xe3 | xe3 => xe4 | xe4 => xe5 | xe5 => xe6 | xe6 => xe7 | xe7 => xe8
  | xe8 => xe9 | xe9 => xea | xea => xeb | xeb => xec | xec => xed | xed => xee | xee => xef | xef => xf0
  | xf0 => xf1 | xf1 => xf2 | xf2 => xf3 | xf3 => xf4 | xf4 => xf5 | xf5 => xf6 | xf6 => xf7 | xf7 => xf8
  | xf8 => xf9 | xf9 => xfa | xfa => xfb | xfb => xfc | xfc => xfd | xfd => xfe | xfe => xff | xff => x00
  end.

Definition byte_pred (b : byte) : byte :=
  match b with
	| x00 => xff | x01 => x00 | x02 => x01 | x03 => x02 | x04 => x03 | x05 => x04 | x06 => x05 | x07 => x06
  | x08 => x07 | x09 => x08 | x0a => x09 | x0b => x0a | x0c => x0b | x0d => x0c | x0e => x0d | x0f => x0e
  | x10 => x0f | x11 => x10 | x12 => x11 | x13 => x12 | x14 => x13 | x15 => x14 | x16 => x15 | x17 => x16
  | x18 => x17 | x19 => x18 | x1a => x19 | x1b => x1a | x1c => x1b | x1d => x1c | x1e => x1d | x1f => x1e
  | x20 => x1f | x21 => x20 | x22 => x21 | x23 => x22 | x24 => x23 | x25 => x24 | x26 => x25 | x27 => x26
  | x28 => x27 | x29 => x28 | x2a => x29 | x2b => x2a | x2c => x2b | x2d => x2c | x2e => x2d | x2f => x2e
  | x30 => x2f | x31 => x30 | x32 => x31 | x33 => x32 | x34 => x33 | x35 => x34 | x36 => x35 | x37 => x36
  | x38 => x37 | x39 => x38 | x3a => x39 | x3b => x3a | x3c => x3b | x3d => x3c | x3e => x3d | x3f => x3e
  | x40 => x3f | x41 => x40 | x42 => x41 | x43 => x42 | x44 => x43 | x45 => x44 | x46 => x45 | x47 => x46
  | x48 => x47 | x49 => x48 | x4a => x49 | x4b => x4a | x4c => x4b | x4d => x4c | x4e => x4d | x4f => x4e
  | x50 => x4f | x51 => x50 | x52 => x51 | x53 => x52 | x54 => x53 | x55 => x54 | x56 => x55 | x57 => x56
  | x58 => x57 | x59 => x58 | x5a => x59 | x5b => x5a | x5c => x5b | x5d => x5c | x5e => x5d | x5f => x5e
  | x60 => x5f | x61 => x60 | x62 => x61 | x63 => x62 | x64 => x63 | x65 => x64 | x66 => x65 | x67 => x66
  | x68 => x67 | x69 => x68 | x6a => x69 | x6b => x6a | x6c => x6b | x6d => x6c | x6e => x6d | x6f => x6e
  | x70 => x6f | x71 => x70 | x72 => x71 | x73 => x72 | x74 => x73 | x75 => x74 | x76 => x75 | x77 => x76
  | x78 => x77 | x79 => x78 | x7a => x79 | x7b => x7a | x7c => x7b | x7d => x7c | x7e => x7d | x7f => x7e
  | x80 => x7f | x81 => x80 | x82 => x81 | x83 => x82 | x84 => x83 | x85 => x84 | x86 => x85 | x87 => x86
  | x88 => x87 | x89 => x88 | x8a => x89 | x8b => x8a | x8c => x8b | x8d => x8c | x8e => x8d | x8f => x8e
  | x90 => x8f | x91 => x90 | x92 => x91 | x93 => x92 | x94 => x93 | x95 => x94 | x96 => x95 | x97 => x96
  | x98 => x97 | x99 => x98 | x9a => x99 | x9b => x9a | x9c => x9b | x9d => x9c | x9e => x9d | x9f => x9e
  | xa0 => x9f | xa1 => xa0 | xa2 => xa1 | xa3 => xa2 | xa4 => xa3 | xa5 => xa4 | xa6 => xa5 | xa7 => xa6
  | xa8 => xa7 | xa9 => xa8 | xaa => xa9 | xab => xaa | xac => xab | xad => xac | xae => xad | xaf => xae
  | xb0 => xaf | xb1 => xb0 | xb2 => xb1 | xb3 => xb2 | xb4 => xb3 | xb5 => xb4 | xb6 => xb5 | xb7 => xb6
  | xb8 => xb7 | xb9 => xb8 | xba => xb9 | xbb => xba | xbc => xbb | xbd => xbc | xbe => xbd | xbf => xbe
  | xc0 => xbf | xc1 => xc0 | xc2 => xc1 | xc3 => xc2 | xc4 => xc3 | xc5 => xc4 | xc6 => xc5 | xc7 => xc6
  | xc8 => xc7 | xc9 => xc8 | xca => xc9 | xcb => xca | xcc => xcb | xcd => xcc | xce => xcd | xcf => xce
  | xd0 => xcf | xd1 => xd0 | xd2 => xd1 | xd3 => xd2 | xd4 => xd3 | xd5 => xd4 | xd6 => xd5 | xd7 => xd6
  | xd8 => xd7 | xd9 => xd8 | xda => xd9 | xdb => xda | xdc => xdb | xdd => xdc | xde => xdd | xdf => xde
  | xe0 => xdf | xe1 => xe0 | xe2 => xe1 | xe3 => xe2 | xe4 => xe3 | xe5 => xe4 | xe6 => xe5 | xe7 => xe6
  | xe8 => xe7 | xe9 => xe8 | xea => xe9 | xeb => xea | xec => xeb | xed => xec | xee => xed | xef => xee
  | xf0 => xef | xf1 => xf0 | xf2 => xf1 | xf3 => xf2 | xf4 => xf3 | xf5 => xf4 | xf6 => xf5 | xf7 => xf6
  | xf8 => xf7 | xf9 => xf8 | xfa => xf9 | xfb => xfa | xfc => xfb | xfd => xfc | xfe => xfd | xff => xfe
  end.

Definition byte_neg (b : byte) : byte :=
  match b with
	| x00 => xff | x01 => xfe | x02 => xfd | x03 => xfc | x04 => xfb | x05 => xfa | x06 => xf9 | x07 => xf8
  | x08 => xf7 | x09 => xf6 | x0a => xf5 | x0b => xf4 | x0c => xf3 | x0d => xf2 | x0e => xf1 | x0f => xf0
  | x10 => xef | x11 => xee | x12 => xed | x13 => xec | x14 => xeb | x15 => xea | x16 => xe9 | x17 => xe8
  | x18 => xe7 | x19 => xe6 | x1a => xe5 | x1b => xe4 | x1c => xe3 | x1d => xe2 | x1e => xe1 | x1f => xe0
  | x20 => xdf | x21 => xde | x22 => xdd | x23 => xdc | x24 => xdb | x25 => xda | x26 => xd9 | x27 => xd8
  | x28 => xd7 | x29 => xd6 | x2a => xd5 | x2b => xd4 | x2c => xd3 | x2d => xd2 | x2e => xd1 | x2f => xd0
  | x30 => xcf | x31 => xce | x32 => xcd | x33 => xcc | x34 => xcb | x35 => xca | x36 => xc9 | x37 => xc8
  | x38 => xc7 | x39 => xc6 | x3a => xc5 | x3b => xc4 | x3c => xc3 | x3d => xc2 | x3e => xc1 | x3f => xc0
  | x40 => xbf | x41 => xbe | x42 => xbd | x43 => xbc | x44 => xbb | x45 => xba | x46 => xb9 | x47 => xb8
  | x48 => xb7 | x49 => xb6 | x4a => xb5 | x4b => xb4 | x4c => xb3 | x4d => xb2 | x4e => xb1 | x4f => xb0
  | x50 => xaf | x51 => xae | x52 => xad | x53 => xac | x54 => xab | x55 => xaa | x56 => xa9 | x57 => xa8
  | x58 => xa7 | x59 => xa6 | x5a => xa5 | x5b => xa4 | x5c => xa3 | x5d => xa2 | x5e => xa1 | x5f => xa0
  | x60 => x9f | x61 => x9e | x62 => x9d | x63 => x9c | x64 => x9b | x65 => x9a | x66 => x99 | x67 => x98
  | x68 => x97 | x69 => x96 | x6a => x95 | x6b => x94 | x6c => x93 | x6d => x92 | x6e => x91 | x6f => x90
  | x70 => x8f | x71 => x8e | x72 => x8d | x73 => x8c | x74 => x8b | x75 => x8a | x76 => x89 | x77 => x88
  | x78 => x87 | x79 => x86 | x7a => x85 | x7b => x84 | x7c => x83 | x7d => x82 | x7e => x81 | x7f => x80
  | x80 => x7f | x81 => x7e | x82 => x7d | x83 => x7c | x84 => x7b | x85 => x7a | x86 => x79 | x87 => x78
  | x88 => x77 | x89 => x76 | x8a => x75 | x8b => x74 | x8c => x73 | x8d => x72 | x8e => x71 | x8f => x70
  | x90 => x6f | x91 => x6e | x92 => x6d | x93 => x6c | x94 => x6b | x95 => x6a | x96 => x69 | x97 => x68
  | x98 => x67 | x99 => x66 | x9a => x65 | x9b => x64 | x9c => x63 | x9d => x62 | x9e => x61 | x9f => x60
  | xa0 => x5f | xa1 => x5e | xa2 => x5d | xa3 => x5c | xa4 => x5b | xa5 => x5a | xa6 => x59 | xa7 => x58
  | xa8 => x57 | xa9 => x56 | xaa => x55 | xab => x54 | xac => x53 | xad => x52 | xae => x51 | xaf => x50
  | xb0 => x4f | xb1 => x4e | xb2 => x4d | xb3 => x4c | xb4 => x4b | xb5 => x4a | xb6 => x49 | xb7 => x48
  | xb8 => x47 | xb9 => x46 | xba => x45 | xbb => x44 | xbc => x43 | xbd => x42 | xbe => x41 | xbf => x40
  | xc0 => x3f | xc1 => x3e | xc2 => x3d | xc3 => x3c | xc4 => x3b | xc5 => x3a | xc6 => x39 | xc7 => x38
  | xc8 => x37 | xc9 => x36 | xca => x35 | xcb => x34 | xcc => x33 | xcd => x32 | xce => x31 | xcf => x30
  | xd0 => x2f | xd1 => x2e | xd2 => x2d | xd3 => x2c | xd4 => x2b | xd5 => x2a | xd6 => x29 | xd7 => x28
  | xd8 => x27 | xd9 => x26 | xda => x25 | xdb => x24 | xdc => x23 | xdd => x22 | xde => x21 | xdf => x20
  | xe0 => x1f | xe1 => x1e | xe2 => x1d | xe3 => x1c | xe4 => x1b | xe5 => x1a | xe6 => x19 | xe7 => x18
  | xe8 => x17 | xe9 => x16 | xea => x15 | xeb => x14 | xec => x13 | xed => x12 | xee => x11 | xef => x10
  | xf0 => x0f | xf1 => x0e | xf2 => x0d | xf3 => x0c | xf4 => x0b | xf5 => x0a | xf6 => x09 | xf7 => x08
  | xf8 => x07 | xf9 => x06 | xfa => x05 | xfb => x04 | xfc => x03 | xfd => x02 | xfe => x01 | xff => x00
  end.

Theorem byte_succ_pred : forall b,
  byte_pred (byte_succ b) = b.
Proof. induction b; reflexivity. Qed.

Theorem byte_pred_succ : forall b,
  byte_succ (byte_pred b) = b.
Proof. induction b; reflexivity. Qed.

Theorem byte_neg_involutive : forall b,
  byte_neg (byte_neg b) = b.
Proof. induction b; reflexivity. Qed.
