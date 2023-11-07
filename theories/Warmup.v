From Coq Require Import Ascii.
From Coq Require Import String.

From Evidence Require Import Definitions.

Lemma eq_le : forall n m, n = m -> n <= m.
Proof.
  intros.
  now rewrite H.
Qed.

Lemma le_add : forall n m, n <= n + m.
Proof.
  induction m.
  - now rewrite PeanoNat.Nat.add_0_r.
  - rewrite <- plus_n_Sm.
    now apply le_S.
Qed.

Lemma add_sym : forall n m, n + m = m + n.
Proof.
  induction m.
  - easy.
  - rewrite <- plus_n_Sm.
    now rewrite IHm.
Qed.

Lemma neq_add : forall n m, n = n + m -> m = 0.
Proof.
  induction n.
  - easy.
  - intros.
    simpl in H.
    apply eq_add_S in H.
    now apply IHn in H.
Qed.

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

Lemma append_empty : forall s, (s ++ "")%string = s.
Proof.  
  induction s.
  - reflexivity.
  - simpl.
    now rewrite IHs.
Qed.

Lemma append_assoc : forall s1 s2 s3, ((s1 ++ s2) ++ s3 = s1 ++ (s2 ++ s3))%string.
Proof.
  induction s1; intros.
  - easy.
  - simpl.
    now rewrite IHs1.
Qed.

Fact string_eq : forall c1 c2 s1 s2, String c1 s1 = String c2 s2 <-> c1 = c2 /\ s1 = s2.
Proof.
  split; intros.
  - split; simple congruence.
  - destruct H.
    now subst.
Qed.

Fact string_neq_S : forall c s, s <> String c s.
Proof.
  induction s.
  - discriminate.
  - rewrite string_eq.
    now intros []; subst.
Qed.

Fact string_len_eq : forall s1 s2, s1 = s2 -> length s1 = length s2.
Proof.
  intros.
  now rewrite H.
Qed.

Fact string_len_neq : forall s1 s2, length s1 <> length s2 -> s1 <> s2.
Proof.
  unfold not.
  intros.
  now rewrite H0 in H.
Qed.

Fact append_eq_empty : forall s1 s2, (s1 = s1 ++ s2 -> s2 = "")%string.
Proof.
  induction s1; intros.
  - easy.
  - simpl in H.
    apply string_eq in H as [_ H].
    apply IHs1, H.
Qed.

Fact append_null : forall s1 s2, (s1 ++ s2 = "" <-> s1 = "" /\ s2 = "")%string.
Proof.
  now induction s1.
Qed.

Fact append_len : forall s1 s2, length (s1 ++ s2)%string = length s1 + length s2.
Proof.
  induction s1; intros.
  - easy.
  - simpl.
    now rewrite IHs1.
Qed.

Fact string_neq_S_pre : forall c pre s, s <> String c (pre ++ s).
Proof.
  intros.
  apply string_len_neq.
  simpl.
  rewrite append_len.
  now apply PeanoNat.Nat.succ_add_discr.
Qed.

Fact string_neq_S_post : forall c post s, s <> String c (s ++ post).
Proof.
  intros.
  apply string_len_neq.
  simpl.
  rewrite append_len.
  rewrite add_sym.
  now apply PeanoNat.Nat.succ_add_discr.
Qed.

Fact string_neq_S_pp : forall c pre post s, s <> String c (pre ++ s ++ post).
Proof.
  intros.
  apply string_len_neq.
  simpl.
  repeat rewrite append_len.
  rewrite add_sym.
  rewrite <- PeanoNat.Nat.add_assoc.
  rewrite add_sym.
  now apply PeanoNat.Nat.succ_add_discr.
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
            (add_sym i),
            plus_n_Sm,
            <- PeanoNat.Nat.add_assoc,
            (add_sym i)
      in H0.
    now apply neq_add in H0.
Qed.
