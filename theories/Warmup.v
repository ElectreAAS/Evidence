From Coq Require Import Ascii.
From Coq Require Import String.

From Evidence Require Import
  Definitions
  Utils.

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

Fact is_sub_at_empty : forall s, is_sub_at "" s 0.
Proof.
  intros.
  apply is_prefix_empty.
Qed.
 
Fact is_sub_at_refl : forall s i, i = 0 <-> is_sub_at s s i.
Proof.
  split; intros.
  - subst.
    apply is_prefix_refl.
  - destruct i; try reflexivity.
    rewrite is_sub_at_body in H.
    repeat destruct H as [? H].
    apply string_len_eq in H0.
    simpl in H0.
    rewrite append_len,
            append_len,
            H1,
            PeanoNat.Nat.add_assoc,
            (add_comm i),
            plus_n_Sm,
            <- PeanoNat.Nat.add_assoc,
            (add_comm i)
      in H0.
    now apply add_eq_zero in H0.
Qed.

Fact new_empty : forall h, sub_new "" h 0.
Proof.
  intros.
  unfold sub_new, smallest_such, is_at.
  split.
  - now exists EmptyString, h.
  - intros.
    apply le_0_n.
Qed.

Fact new_empty2 : forall h i, sub_new "" h i -> i = 0.
Proof.
  intros.
  unfold sub_new, smallest_such, is_at in H.
  destruct H as [[pre [post [H1 H2]]] H3].
  apply PeanoNat.Nat.le_0_r, H3.
  now exists EmptyString, h.
Qed.

Fact new_ex : sub_new "hi" "machine" 3.
Proof.
  unfold sub_new, smallest_such, is_at.
  split.
  - now exists "mac"%string, "ne"%string.
  - intros.
    destruct H as [pre [post [H1 H2]]].
    rewrite <- H2.
    destruct pre; [discriminate | ].
    destruct pre; [discriminate | ].
    destruct pre; [discriminate | ].
    destruct pre; [reflexivity | ].
    simpl.
    repeat apply le_n_S.
    apply le_0_n.
Qed.

Fact new_refl : forall s i , sub_new s s i <-> i = 0.
Proof.
  unfold sub_new, smallest_such, is_at.
  split; try split; intros.
  - apply PeanoNat.Nat.le_0_r, H.
    exists EmptyString, EmptyString.
    now rewrite append_empty.
  - exists EmptyString, EmptyString.
    now rewrite append_empty.
  - intros.
    rewrite H.
    apply le_0_n.
Qed.

Lemma new_next : forall n c h i, sub_new n (String c h) (S i) -> sub_new n h i.
Proof.
  unfold sub_new, smallest_such, is_at.
  intros.
  destruct H as [[pre [post [H1 H2]]] H3].
  destruct pre; [discriminate | ].
  split.
  - exists pre, post.
    split.
    + simpl in H1.
      now apply string_eq in H1.
    + simpl in H2.
      now apply PeanoNat.Nat.succ_inj.
  - intros.
    destruct H as [pre_2 [post_2 [G1 G2]]].
    apply le_S_n, H3.
    exists (String a pre_2), post_2.
    split.
    + simpl in H1.
      apply string_eq in H1 as [].
      now apply string_eq.
    + now rewrite <- G2.
Qed.
