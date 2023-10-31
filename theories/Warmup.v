From Coq Require Import Ascii.
From Coq Require Import String.

From Evidence Require Import Definitions.

Example is_sub_ex : is_substring "hi" "machine".
Proof.
  simpl.
  right.
  right.
  right.
  now left.
Qed.

Example found_at_x : is_found_at "hi" "machine" (Some 3).
Proof.
  now simpl.
Qed.

Fact is_prefix_empty: forall s, is_prefix "" s.
Proof.
  reflexivity.
Qed.

Fact is_sub_empty : forall s: string, is_substring "" s.
Proof.
  now induction s.
Qed.

Fact is_found_empty : forall s, is_found_at "" s (Some 0).
Proof.
  now induction s.
Qed.
