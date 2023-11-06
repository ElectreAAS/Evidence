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

Fact string_neq : forall c s, s <> String c s.
Proof.
  induction s.
  - discriminate.
  - rewrite string_eq.
    now intros [H1 H2]; subst.
Qed.

Fact string_len_eq : forall s1 s2, s1 = s2 -> length s1 = length s2.
Proof.
  intros.
  now rewrite H.
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

