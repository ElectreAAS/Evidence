From Coq Require Import Ascii.
From Coq Require Import String.

From Evidence Require Import Definitions.

Lemma is_sub_S_h : forall n h, is_substring n h ->
                   forall c, is_substring n (String c h).
Proof.
  intros.
  simpl.
  now right.
Qed.

Lemma is_sub_P_n : forall n h c, is_substring (String c n) h ->
                   is_substring n h.
Proof.
  induction h; intros; [easy | induction H].
  - simpl in *.
    destruct H; subst.
    right.
    rewrite sub_body.
    now destruct h; [induction n | left].
  - apply is_sub_S_h.
    now apply IHh in H.
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
    now destruct h; [induction n | left].
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
      now induction h; [induction n | left].
    + now apply is_sub_P_n in H.
Qed.
