From Coq Require Import Ascii.
From Coq Require Import String.

Fact le_zero : forall n, n <= 0 <-> n = 0.
Proof.
  apply PeanoNat.Nat.le_0_r.
Qed.

Lemma eq_le : forall n m, n = m -> n <= m.
Proof.
  intros.
  now rewrite H.
Qed.

Lemma le_add : forall n m, n <= n + m.
Proof.
  apply PeanoNat.Nat.le_add_r.
Qed.

Lemma add_comm : forall n m, n + m = m + n.
Proof.
  apply PeanoNat.Nat.add_comm.
Qed.

Lemma add_eq_zero : forall n m, n = n + m -> m = 0.
Proof.
  intros.
  symmetry in H.
  apply PeanoNat.Nat.add_sub_eq_l in H.
  now rewrite PeanoNat.Nat.sub_diag in H.
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

Lemma append_S_assoc : forall s1 s2 c, String c (s1 ++ s2) = (String c s1 ++ s2)%string.
Proof.
  reflexivity.
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

Fact string_neq_S_post : forall c post s, s <> (s ++ String c post)%string.
Proof.
  intros.
  apply string_len_neq.
  rewrite append_len.
  rewrite add_comm.
  now apply PeanoNat.Nat.succ_add_discr.
Qed.

Fact string_neq_S_pp : forall c pre post s, s <> String c (pre ++ s ++ post).
Proof.
  intros.
  apply string_len_neq.
  simpl.
  repeat rewrite append_len.
  rewrite add_comm.
  rewrite <- PeanoNat.Nat.add_assoc.
  rewrite add_comm.
  now apply PeanoNat.Nat.succ_add_discr.
Qed.
