From Coq Require Import Ascii.
From Coq Require Import String.

From Evidence Require Import
     Definitions
     Utils
     Warmup.

Lemma is_sub_S_h : forall n h, is_substring n h ->
                   forall c, is_substring n (String c h).
Proof.
  induction n; intros; simpl; tauto.
Qed.

Lemma is_sub_P_n : forall n h c, is_substring (String c n) h ->
                   is_substring n h.
Proof.
  induction h; intros; induction H.
  - induction H; subst.
    simpl.
    induction n; [reflexivity | ].
    right.
    rewrite sub_body.
    now induction h; [inversion H0 | left].
  - apply IHh in H.
    now apply is_sub_S_h.
Qed.

Lemma is_sub_both : forall n h c,
                      is_substring (String c n) (String c h)
                   -> is_substring n h.
Proof.
  intros.
  rewrite sub_body in H.
  induction H.
  - induction H.
    rewrite sub_body.
    destruct n; [reflexivity | ].
    now destruct h; [inversion H0 | left].
  - now apply is_sub_P_n with c.
Qed.

Theorem longer_sub : forall n h, is_substring n h -> length n <= length h.
Proof.
  induction n, h; intros;
    simpl;
    try apply le_0_n.
  - inversion H.
  - apply le_n_S.
    apply IHn.
    induction H.
    + rewrite prefix_body in H.
      destruct H; subst.
      rewrite sub_body.
      destruct n; [tauto | ].
      now destruct h; [inversion H0 | left].
    + now apply is_sub_P_n in H.
Qed.

Theorem prefix_eq : forall n h, is_prefix n h <-> prefix n h = true.
Proof.
  induction n, h; split; intros; try easy.
  - simpl in H.
    destruct H; subst.
    simpl.
    now induction (ascii_dec a0 a0); [apply IHn | contradiction].
  - simpl in H.
    induction (ascii_dec a a0).
    + subst.
      simpl.
      now apply IHn in H.
    + inversion H.
Qed.

Theorem prefix_eq_not : forall n h, ~ is_prefix n h <-> prefix n h = false.
Proof.
  unfold not.
  induction n, h; split; intros; simpl in *; try easy.
  - induction (ascii_dec a a0).
    + apply IHn.
      intro.
      now apply H.
    + reflexivity.
  - destruct H0; subst.
    induction (ascii_dec a0 a0).
    + now apply IHn in H.
    + contradiction.
Qed.

Theorem prefix_append : forall s post, is_prefix s (s ++ post).
Proof.
  now induction s.
Qed.

Lemma prefix_append2 : forall s post, prefix s (s ++ post) = true.
 intros.
 apply prefix_eq, prefix_append.
Qed.

Lemma prefix_s : forall c s1 s2, is_prefix s1 s2 <-> is_prefix (String c s1) (String c s2).
Proof.
  now simpl.
Qed.

Theorem sub_eq : forall n h, is_substring n h <-> exists i, substring i (length n) h = n.
Proof.
  induction h; split; intros;
  try apply is_sub_empty.
  - induction n, H.
    now exists 0.
  - now induction n, H, x.
  - induction n.
    + now exists 0.
    + induction H.
      * destruct H; subst.
        exists 0.
        now apply prefix_correct, prefix_eq.
      * apply IHh in H.
        destruct H.
        now exists (S x).
  - induction n, H, x; try apply is_sub_empty.
    + apply prefix_correct, prefix_eq in H.
      simpl.
      now left.
    + simpl.
      right.
      apply IHh.
      now exists x.
Qed.

Theorem prefix_longer : forall s1 s2, is_prefix s1 s2 -> length s1 <= length s2.
Proof.
  induction s1, s2; intros.
  - reflexivity.
  - apply le_0_n.
  - destruct H.
  - destruct H.
    simpl.
    apply le_n_S, IHs1, H0.
Qed.

Theorem longer_sub_at : forall n h i, is_sub_at n h i -> i + length n <= length h.
Proof.
  induction i; intros.
  - simpl in H.
    now apply prefix_longer.
  - repeat destruct H as [? H].
    rewrite H0.
    simpl.
    apply le_n_S.
    rewrite append_len,
            append_len,
            H1,
            PeanoNat.Nat.add_assoc.
    apply le_add.
Qed.

Theorem mirror_prefix : forall s1 s2, is_prefix s1 s2 -> is_prefix s2 s1 -> s1 = s2.
Proof.
  induction s1, s2; intros.
  - reflexivity.
  - inversion H0.
  - inversion H.
  - apply string_eq.
    destruct H, H0.
    split.
    assumption.
    now apply IHs1.
Qed.

Theorem mirror_sub_at : forall s1 s2 i j, is_sub_at s1 s2 i ->
                                          is_sub_at s2 s1 j ->
                          s1 = s2 /\ i = j /\ i = 0.
Proof.
  intros.
  destruct i, j.
  - now split; [ apply mirror_prefix | ].
  - simpl in H.
    apply prefix_longer in H as H_false.
    contradict H_false.
    apply PeanoNat.Nat.lt_nge.
    repeat destruct H0 as [? H0].
    rewrite H1.
    simpl.
    repeat rewrite append_len.
    rewrite PeanoNat.Nat.add_assoc.
    rewrite (add_comm (length x0)).
    rewrite <- PeanoNat.Nat.add_assoc.
    rewrite <- plus_Sn_m.
    apply le_add.
  - simpl in H0.
    apply prefix_longer in H0 as H_false.
    contradict H_false.
    apply PeanoNat.Nat.lt_nge.
    repeat destruct H as [? H].
    rewrite H1.
    simpl.
    repeat rewrite append_len.
    rewrite PeanoNat.Nat.add_assoc.
    rewrite (add_comm (length x0)).
    rewrite <- PeanoNat.Nat.add_assoc.
    rewrite <- plus_Sn_m.
    apply le_add.
  - repeat destruct H as [? H].
    repeat destruct H0 as [? H0].
    apply string_len_eq in H1.
    contradict H1.
    rewrite H3.
    simpl.
    rewrite append_len.
    simpl.
    repeat rewrite append_len.
    (* such boring *)
    rewrite add_comm.
    rewrite PeanoNat.Nat.add_assoc.
    rewrite (add_comm (length x3)).
    rewrite <- PeanoNat.Nat.add_assoc.
    rewrite <- PeanoNat.Nat.add_assoc.
    rewrite <- plus_Sn_m.
    rewrite <- plus_Sn_m.
    rewrite plus_n_Sm.
    rewrite <- PeanoNat.Nat.add_assoc.
    rewrite plus_Sn_m.
    rewrite add_comm.
    apply PeanoNat.Nat.succ_add_discr.
    (* wow *)
Qed.

Lemma sub_at_s_i : forall needle haystack c i, is_sub_at needle (String c haystack) (S i) ->
                                               is_sub_at needle haystack i.
Proof.
  intros.
  repeat destruct H as [? H].
  apply string_eq in H0 as [].
  now rewrite H2.
Qed.

Theorem new_prefix : forall needle haystack, is_prefix needle haystack <-> sub_new needle haystack 0.
Proof.
  induction needle, haystack; split; intros.
  - apply new_empty.
  - reflexivity.
  - apply new_empty.
  - reflexivity.
  - inversion H.
  - unfold sub_new, smallest_such, is_at in H.
    destruct H as [[pre [post [H1 H2]]] H3].
    destruct pre; discriminate.
  - destruct H as [eq H]; subst.
    apply IHneedle in H.
    destruct H as [[pre [post [H1 H2]]] H3].
    destruct pre; [ | discriminate].
    clear H2. simpl in H1.
    unfold sub_new, smallest_such, is_at.
    split.
    + exists EmptyString, post.
      simpl.
      rewrite string_eq.
      easy.
    + intros.
      apply le_0_n.
  - destruct H as [[pre [post [H1 H2]]] H3].
    destruct pre; [ | discriminate].
    simpl in *.
    apply string_eq in H1 as []; subst.
    split; [reflexivity | apply prefix_append].
Qed.

Theorem new_mirror : forall s1 s2 i j, sub_new s1 s2 i -> sub_new s2 s1 j ->
  s1 = s2 /\ i = j /\ i = 0.
Proof.
  unfold sub_new, smallest_such, is_at.
  intros.
  destruct H as [[pre_1 [post_1 [H1 H2]]] H3].
  destruct H0 as [[pre_2 [post_2 [G1 G2]]] G3].
  rewrite H1 in G1.
  simpl in *.
  destruct pre_1, pre_2, post_1, post_2.
  1: (* correct case *)
    subst.
    now rewrite append_empty.
  (* all other cases are impossible *)
  all: contradict G1; clear;
       repeat rewrite append_empty;
       repeat rewrite append_assoc;
       try apply (string_neq_S_pre, string_neq_S_post, string_neq_S_pp).
  all: repeat rewrite append_S_assoc;
       rewrite <- append_assoc;
       apply (string_neq_S_pre, string_neq_S_post, string_neq_S_pp).
Qed.

Theorem new_at_index : forall needle haystack i,
        sub_new needle haystack i <-> index 0 needle haystack = Some i.
Proof.
  induction haystack; split; intros.
  - destruct H as [[pre [post [H1 H2]]] _].
    symmetry in H1.
    repeat apply append_null in H1 as [? H1].
    now subst.
  - destruct needle; [ | discriminate].
    inversion H.
    apply new_empty.
  - destruct needle; [apply new_empty2 in H; now rewrite H | ].
    destruct i.
    + destruct H as [[pre [post [H1 H2]]] _].
      destruct pre; [ | discriminate]. clear H2.
      simpl in *.
      apply string_eq in H1 as [].
      subst a0.
      destruct (ascii_dec a a); [ | contradiction].
      now rewrite H0, prefix_append2.
    + apply new_next in H as H1.
      apply IHhaystack in H1. clear IHhaystack.
      simpl.
      rewrite H1. clear H1.
      destruct (ascii_dec a0 a); [subst a0 | reflexivity].
      case_eq (prefix needle haystack); intro; [ | reflexivity].
      destruct H as [_ G3].
      pose proof (G3 0) as G3.
      apply PeanoNat.Nat.nle_succ_0 with i in G3; [contradiction | clear G3].
      apply new_prefix.
      apply prefix_s, prefix_eq, H0.
  - destruct needle; [injection H; intros; subst; apply new_empty | ].
    simpl in H.
    destruct (ascii_dec a0 a).
    1:   subst a.
    1:   case_eq (prefix needle haystack); intros H'; rewrite H' in H.
    1: { inversion H; subst.
         apply new_prefix, prefix_s, prefix_eq, H'. }
    all: case_eq (index 0 (String a0 needle) haystack); intros; rewrite H0 in H; [ | discriminate].
    all: inversion H; subst; clear H.
    all: apply IHhaystack in H0 as [[pre [post [H2 H3]]] H4].
    all: split.
    1:   exists (String a0 pre).
    3:   exists (String a pre).
    1,3: exists post.
    1,2: simpl in *; now rewrite H2, H3.
    all: intros.
    all: destruct H as [pre_2 [post_2 [H5 H6]]].
    all: destruct pre_2; simpl in H5; apply string_eq in H5 as [].
    1: { rewrite H0 in H'.
         apply prefix_eq_not in H'.
         contradict H'.
         apply prefix_append. }
    2:   congruence.
    all: destruct j; [discriminate | ].
    all: simpl in H6.
    all: apply eq_add_S in H6.
    all: pose proof (H4 j) as H4.
    all: apply le_n_S, H4.
    all: now exists pre_2, post_2.
Qed.
