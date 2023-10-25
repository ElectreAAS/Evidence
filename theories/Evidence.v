From Coq Require Export String.
From Coq Require Export Ascii.

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
  destruct s1; destruct s2; reflexivity.
Qed.

Definition is_prefix (tested big_one : string) :=
  prefix tested big_one = true.

Example is_prefix_empty: forall s, is_prefix "" s.
Proof.
  apply prefix_body.
Qed.

Fixpoint is_substring (needle haystack : string) : Prop :=
  is_prefix needle haystack \/
  match haystack with
  | EmptyString => False
  | String _ h' => is_substring needle h'
  end.

Lemma is_sub_body: forall needle haystack,
  is_substring needle haystack =
  (is_prefix needle haystack \/
    match haystack with
    | EmptyString => False
    | String _ h' => is_substring needle h'
    end).
Proof.
  unfold is_substring.
  destruct needle; destruct haystack; reflexivity.
Qed.

Example is_sub_trivial : forall s: string, is_substring EmptyString s.
Proof.
  intros.
  rewrite is_sub_body; left.
  unfold is_prefix.
  rewrite prefix_body.
  reflexivity.
Qed.

Example is_sub_foo : is_substring "hi" "machine".
Proof.
  rewrite is_sub_body; right.
  rewrite is_sub_body; right.
  rewrite is_sub_body; right.
  rewrite is_sub_body; left.
  reflexivity.
Qed.

Lemma is_sub_S_h : forall n h, is_substring n h ->
                   forall c, is_substring n (String c h).
Proof.
  intros.
  simpl.
  right.
  assumption.
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
        unfold is_prefix in H.
        rewrite prefix_body in H.
        induction (ascii_dec c c).
        -- assumption.
        -- contradiction.
      * apply IHh in H.
        apply is_sub_S_h.
        assumption.
    + rewrite is_sub_body in H.
      induction H.
      * unfold is_prefix in H.
        rewrite prefix_body in H.
        induction (ascii_dec c a).
        -- contradiction.
        -- inversion H.
      * apply IHh in H.
        apply is_sub_S_h.
        assumption.
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
    unfold is_prefix in H.
    rewrite prefix_body in H.
    induction (ascii_dec c c).
    + assumption.
    + contradiction.
  - apply (is_sub_P_n _ _ c).
    assumption.
Qed.

Theorem longer_sub : forall n h, is_substring n h -> length n <= length h.
Proof.
  induction n; induction h; intros; simpl; try reflexivity.
  - apply le_0_n.
  - induction H; inversion H.
  - apply le_n_S.
    apply IHn.
    induction H.
    + unfold is_prefix in H.
      rewrite prefix_body in H.
      induction (ascii_dec a a0).
      * subst a0.
        rewrite is_sub_body.
        left.
        assumption.
      * inversion H.
    + apply is_sub_P_n in H.
      assumption.
Qed.

