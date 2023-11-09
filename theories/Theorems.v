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
    induction n; try reflexivity.
    right.
    rewrite sub_body.
    induction h; try inversion H0.
    now left.
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
    destruct n; try reflexivity.
    destruct h; try inversion H0.
    now left.
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
      destruct n; try reflexivity.
      destruct h; try inversion H0.
      now left.
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
  induction n, h; split; intros; try easy.
  - simpl in H.
    contradiction.
  - simpl in H.
    contradiction.
  - simpl in *.
    induction (ascii_dec a a0).
    + apply IHn.
      intro.
      now apply H.
    + reflexivity.
  - destruct H0; subst.
    simpl in H.
    induction (ascii_dec a0 a0).
    + now apply IHn in H.
    + contradiction.
Qed.

Theorem prefix_append : forall s post, prefix s (s ++ post) = true.
Proof.
  induction s; intros.
  - simpl.
    now rewrite <- prefix_eq, prefix_body.
  - rewrite <- prefix_eq.
    simpl.
    split.
    + reflexivity.
    + now rewrite prefix_eq.
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
Admitted.

(*
  induction needle, haystack, i; split; intros.
  - reflexivity.
  - simpl.
    now exists EmptyString.
  - destruct H as [pre [post [H1 [H2 H3]]]].
    apply string_len_eq in H2.
    now rewrite append_len, H1 in H2.
  - discriminate.
  - reflexivity.
  - now exists (String a haystack).
  - apply is_sub_at_empty in H.
  destruct H as [pre [post [H1 [H2 H3]]]].
    apply string_len_eq in H2.
    rewrite append_len, H1 in H2.
    simpl in H2.
    unfold not in H3.
    destruct H3.
    rewrite is_sub_at_body.
    destruct i.
    now exists (String a haystack).
    simpl.
    eexists.
    eexists.


(*   
  split.
  - intros.
    rewrite is_sub_at_body in H.
    destruct i.
    + destruct H as [post H].
      destruct haystack, needle; try (reflexivity || discriminate).
      simpl in H.
      apply string_eq in H as [eq H]; subst.
      simpl.
      destruct (ascii_dec a0 a0); try contradiction.
      now rewrite prefix_append.
    + induction haystack.
      * destruct H as [pre [post [H1 [H2 H3]]]].
        unfold not in H3.
        apply string_len_eq in H2.
        now rewrite append_len, H1 in H2.
      * destruct H as [pre [post [H1 [H2 H3]]]].
        unfold not in H3. *)
*)