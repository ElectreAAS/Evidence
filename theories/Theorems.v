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
  induction n; induction h; intros;
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

Theorem found_prop_eq : forall n h p, is_found_at n h p <-> is_found_opt n h = p.
Proof.
  split.

Admitted.

Theorem sub_found_eq : forall n h, is_substring n h <-> exists i, is_found_at n h (Some i).
Proof.
  induction h; split; intros.
  - induction n, H.
    now exists 0.
  - induction n, H.
    + easy.
    + inversion H.
  - induction n, H.
  (* TODO *)
Abort.
