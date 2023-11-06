From Coq Require Import Ascii.
From Coq Require Import String.

From Evidence Require Import
     Definitions
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

Theorem longer_sub_at : forall n h i, is_sub_at n h i -> i + length n <= length h.
Proof.
  intros.
  rewrite is_sub_at_body in H.
  destruct i.
  - destruct H as [post H].
    now rewrite H,
                append_len,
                le_add.
  - destruct H as [pre [post [H1 [H2 H3]]]].
    rewrite H2,
            append_len,
            H1,
            append_len,
            PeanoNat.Nat.add_assoc.
    apply le_add.
Qed.

Theorem mirror_sub_at : forall s1 s2 i j, is_sub_at s1 s2 i ->
                                          is_sub_at s2 s1 j ->
                          s1 = s2 /\ i = j /\ i = 0.
Proof.
  intros.
  rewrite is_sub_at_body in H, H0.
  destruct i, j.
  - destruct H as [post_1 H1].
    destruct H0 as [post_2 H2].
    rewrite H1, append_assoc in H2.
    apply append_eq_empty, append_null in H2 as [H2 _]; subst.
    now rewrite append_empty.
  - destruct H as [post_1 H1].
    destruct H0 as [pre_2 [post_2 [H2 [H3 H4]]]].
    apply string_len_eq in H3.
    rewrite H1,
            append_assoc,
            append_len,
            append_len,
            H2,
            add_sym,
            <- PeanoNat.Nat.add_assoc,
            (add_sym _ (S j))
      in H3.
    now apply neq_add in H3.
  - destruct H as [pre_1 [post_1 [H2 [H3 H4]]]].
    destruct H0 as [post_2 H1].
    apply string_len_eq in H3.
    rewrite H1,
            append_assoc,
            append_len,
            append_len,
            append_len,
            H2,
            add_sym,
            <- PeanoNat.Nat.add_assoc,
            (add_sym _ (S i))
      in H3.
    now apply neq_add in H3.
  - destruct H as [pre_1 [post_1 [H1 [H2 H3]]]].
    destruct H0 as [pre_2 [post_2 [G1 [G2 G3]]]].
    apply string_len_eq in G2.
    rewrite H2,
            append_len,
            append_len,
            append_len,
            append_len,
            H1,
            G1,
            add_sym,
            PeanoNat.Nat.add_assoc,
            (add_sym (S i)),
            <- PeanoNat.Nat.add_assoc,
            <- PeanoNat.Nat.add_assoc,
            <- PeanoNat.Nat.add_assoc
      in G2.
    now apply neq_add in G2.
Qed.
