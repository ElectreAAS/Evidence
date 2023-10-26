(* begin hide *)
From Coq Require Export String.
From Coq Require Export Ascii.

From Evidence Require Import Definitions.
(* end hide *)


Lemma prefix_body: forall s1 s2, prefix s1 s2 =
  match s1 with
  | EmptyString => true
  | String a s1' => match s2 with
    | EmptyString => false
    | String b s2' => if Ascii.ascii_dec a b then prefix s1' s2' else false
    end
  end.
Proof.
  intros.
  unfold prefix.
  now destruct s1; destruct s2.
Qed.

Example is_prefix_empty: forall s, prefix "" s = true.
Proof.
  apply prefix_body.
Qed.

Lemma is_sub_body: forall needle haystack,
  is_substring needle haystack =
  (prefix needle haystack = true \/
    match haystack with
    | EmptyString => False
    | String _ h' => is_substring needle h'
    end).
Proof.
  unfold is_substring.
  now destruct needle; destruct haystack.
Qed.

Example is_sub_trivial : forall s: string, is_substring EmptyString s.
Proof.
  intros.
  rewrite is_sub_body; left.
  now rewrite prefix_body.
Qed.

Example is_sub_foo : is_substring "hi" "machine".
Proof.
  simpl.
  right.
  right.
  right.
  now left.
Qed.

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
  induction h; intros.
  - rewrite is_sub_body in H.
    destruct H; inversion H.
  - induction (ascii_dec c a).
    + subst a.
      rewrite is_sub_body in H.
      induction H.
      * rewrite is_sub_body.
        right.
        rewrite is_sub_body.
        left.
        rewrite prefix_body in H.
        now induction (ascii_dec c c).
      * apply IHh in H.
        now apply is_sub_S_h.
    + rewrite is_sub_body in H.
      induction H.
      * rewrite prefix_body in H.
        now induction (ascii_dec c a).
      * apply IHh in H.
        now apply is_sub_S_h.
Qed.

Lemma is_sub_both : forall n h c,
                      is_substring (String c n) (String c h)
                   -> is_substring n h.
Proof.
  intros.
  rewrite is_sub_body in H.
  induction H.
  - rewrite is_sub_body.
    left.
    rewrite prefix_body in H.
    now induction (ascii_dec c c).
  - now apply (is_sub_P_n _ _ c).
Qed.

Theorem longer_sub : forall n h, is_substring n h -> length n <= length h.
Proof.
  induction n; induction h; intros;
    simpl;
    try apply le_0_n.
  - induction H; inversion H.
  - apply le_n_S.
    apply IHn.
    induction H.
    + rewrite prefix_body in H.
      induction (ascii_dec a a0).
      * rewrite is_sub_body.
        now left.
      * inversion H.
    + now apply is_sub_P_n in H.
Qed.

Example found_at_x : is_found_at "hi" "machine" = Some 3.
Proof.
  reflexivity.
Qed.