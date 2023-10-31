From Coq Require Export String.
From Coq Require Export Ascii.

From Evidence Require Import Definitions.


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

Lemma prefix_S : forall s1 s2, prefix s1 s2 = true ->
                 forall c, prefix (String c s1) (String c s2) = true.
Proof.
  intros.
  rewrite prefix_body.
  induction (ascii_dec c c); easy.
Qed.

Lemma prefix_P : forall s1 s2 c1 c2, prefix (String c1 s1) (String c2 s2) = true -> c1 = c2 /\ prefix s1 s2 = true.
Proof.
  intros.
  rewrite prefix_body in H.
  induction (ascii_dec c1 c2); easy.
Qed.

Lemma is_sub_empty : forall s: string, is_substring EmptyString s.
Proof.
  induction s; simpl; auto.
Qed.

Theorem found_bounded : forall n h i, found_2 n h (Some i) ->
                        i <= length h.
Proof.
  induction n, h, i; intros; try now apply le_0_n.
  - now rewrite found_body_2 in H.
  - rewrite found_body_2 in H.
  induction (prefix n h).
  - destruct H as [j [H1 H2]].
    now inversion H1; subst.
  - destruct h.
    + inversion H.
    +
Admitted.

Theorem opt_Some_eq : forall {A : Type} (x y : A), Some x = Some y <-> x = y.
Proof.
  split;
  intros;
  now inversion H.
Qed.

Lemma found_empty : forall h i, is_found_at EmptyString h (Some i) ->
                    i <= length h.
Proof.
  induction h; intros.
  - simpl in *.
    destruct H as [j [H1 H2]].
    
      rewrite found_body in H.
  - simpl.
    now exists i.
Qed.

Example is_sub_foo : is_substring "hi" "machine".
Proof.
  simpl.
  right.
  right.
  right.
  now left.
Qed.

Example found_at_x : is_found_at "hi" "machine" (Some 3).
Proof.
  simpl.
  repeat eexists.
Qed.

Lemma is_sub_S_h : forall n h, is_substring n h ->
                   forall c, is_substring n (String c h).
Proof.
  intros.
  simpl.
  now right.
Qed.

Lemma found_S_n : forall n h c i, is_found_at (String c n) h (Some i) ->
                  is_found_at n h (Some (S i)).
Proof.
  induction n, h; intros; try easy.
  - apply found_empty.

Lemma found_S_h : forall n h i, is_found_at n h (Some i) ->
                  forall c, is_found_at n (String c h) (Some (S i)).
Proof.
  intros.
  induction n, h; intros.
  - simpl.
    now exists (S i).
  - simpl.
    now exists (S i).
  - inversion H.
  - admit.
Admitted.
  

Lemma is_sub_P_n : forall n h c, is_substring (String c n) h ->
                   is_substring n h.
Proof.
  induction h; try easy.
  intros.
  induction H.
  - apply prefix_P in H.
    destruct H; subst.
    rewrite is_sub_body.
    right.
    rewrite is_sub_body.
    destruct h.
    + rewrite prefix_body in H0.
      now induction n.
    + now left.
  - eapply is_sub_S_h, IHh, H.
Qed.

Lemma is_sub_both : forall n h c1 c2,
                      is_substring (String c1 n) (String c2 h)
                   -> is_substring n h.
Proof.
  induction h; intros.
  - rewrite is_sub_body.
    rewrite is_sub_body in H.
    destruct H.
    + apply prefix_P in H.
      now induction n.
    + now induction n.
  - rewrite is_sub_body in H.
    destruct H.
    + apply prefix_P in H as [_ H].
      rewrite is_sub_body.
      now left.
    + now apply is_sub_P_n with c1.
Qed.

Theorem longer_sub : forall n h, is_substring n h -> length n <= length h.
Proof.
  induction n; induction h; intros;
    simpl;
    try apply le_0_n.
  - inversion H.
  - apply le_n_S.
    apply IHn.
    now apply is_sub_both in H.
Qed.



Theorem sub_found_eq : forall h n, is_substring n h <-> exists i, is_found_at n h (Some i).
Proof.
  split;
  intros.
  - rewrite is_sub_body in H.
    induction h.
    + exists 0.
      now subst.
    + destruct H.
      * exists 0.
        rewrite found_body.
        now rewrite H.
      * rewrite <- is_sub_body in IHh.
        apply IHh in H as I.
        destruct I as [i I].
        simpl.
        induction n.
        -- now exists 0.
        -- destruct IHn.
           ++ now apply is_sub_P_n with a0.
           ++ intros.
              
        rewrite found_body.
        symmetry.
        
        
        

        
      
      
  eexists.
    rewrite found_body.
    induction (prefix n h).
    + reflexivity.
    + 





  induction h; split; intros.
  - exists 0.
    inversion H; subst.
    now simpl.
  - simpl in *.
    induction H.
    now destruct n.
  - destruct IHh with n as [H_left H_right].
    
    rewrite found_body.
    induction (prefix n (String a h)).
    + trivial.
    + induction h.
      * inversion H.
      * admit.
  -
    simpl.
    induction (ascii_dec a a0); subst.
    + induction (prefix n h).
      * now exists 0.
      * 
  apply is_sub_both in H.

    apply IHn.
   