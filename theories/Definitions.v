From Coq Require Import Ascii.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import String.

Fixpoint is_prefix s1 s2 :=
  match s1, s2 with
  | EmptyString, _ => True
  | _, EmptyString => False
  | String c1 s1', String c2 s2' => c1 = c2 /\ is_prefix s1' s2'
  end.

Theorem is_prefix_refl : forall s, is_prefix s s. now induction s. Qed.

Theorem is_prefix_trans : forall s1 s2 s3, is_prefix s1 s2 ->
                          is_prefix s2 s3 -> is_prefix s1 s3.
Proof.
  induction s1, s2, s3; try easy.
  intros.
  simpl in *.
  destruct H, H0; subst.
  split.
  - reflexivity.
  - now apply IHs1 with s2.
Qed.

Add Relation String.string is_prefix
  reflexivity  proved by is_prefix_refl
  transitivity proved by is_prefix_trans
as Prefix.

Lemma prefix_body : forall s1 s2, is_prefix s1 s2 =
  match s1, s2 with
  | EmptyString, _ => True
  | _, EmptyString => False
  | String c1 s1', String c2 s2' => c1 = c2 /\ is_prefix s1' s2'
  end.
Proof.
  now destruct s1, s2.
Qed.

Fixpoint is_sub_at needle haystack i :=
  match i with
  | 0 => exists post, haystack = (needle ++ post)%string
  | S j => exists pre post,
    length pre = i /\
    haystack = (pre ++ needle ++ post)%string /\
    ~ is_sub_at needle haystack j
  end.

Lemma is_sub_at_body : forall needle haystack i, is_sub_at needle haystack i =
  match i with
  | 0 => exists post, haystack = (needle ++ post)%string
  | S j => exists pre post,
    length pre = i /\
    haystack = (pre ++ needle ++ post)%string /\
    ~ is_sub_at needle haystack j
  end.
Proof.
  now destruct needle, haystack, i.
Qed.

Fixpoint is_substring needle haystack :=
  match needle, haystack with
  | EmptyString, _ => True
  | _, EmptyString => False
  | _, String _ h' => is_prefix needle haystack \/
                      is_substring needle h'
  end.

Theorem is_substring_refl : forall s, is_substring s s.
Proof.
  induction s.
  - easy.
  - simpl.
    now left.
Qed.

Add Relation String.string is_substring
  reflexivity proved by is_substring_refl
as Substring.

Lemma sub_body : forall needle haystack, is_substring needle haystack =
  match needle, haystack with
  | EmptyString, _ => True
  | _, EmptyString => False
  | _, String _ h' => is_prefix needle haystack \/
                      is_substring needle h'
  end.
Proof.
  now destruct needle, haystack.
Qed.

Fixpoint is_found_at needle haystack pos :=
  match needle, haystack, pos with
  | EmptyString, _, Some 0 => True
  | EmptyString, _, _ => False
  | _, EmptyString, None => True
  | _, EmptyString, _ => False
  | _, _, Some 0 => is_prefix needle haystack
  | _, String _ h', None => (~ is_prefix needle haystack) /\
                             is_found_at needle h' None
  | _, String _ h', Some (S i) =>
    (~ is_prefix needle haystack) /\
    is_found_at needle h' (Some i)
  end.

Lemma found_body : forall needle haystack pos, is_found_at needle haystack pos =
  match needle, haystack, pos with
  | EmptyString, _, Some 0 => True
  | EmptyString, _, _ => False
  | _, EmptyString, None => True
  | _, EmptyString, _ => False
  | _, _, Some 0 => is_prefix needle haystack
  | _, String _ h', None => (~ is_prefix needle haystack) /\
                             is_found_at needle h' None
  | _, String _ h', Some (S i) =>
    (~ is_prefix needle haystack) /\
    is_found_at needle h' (Some i)
  end.
Proof.
  now destruct needle, haystack.
Qed.

Fixpoint is_found_opt needle haystack :=
  match needle, haystack with
  | EmptyString, _ => Some 0
  | _, EmptyString => None
  | _, String _ h' =>
      if prefix needle haystack then Some 0 else
        match is_found_opt needle h' with
        | None => None
        | Some i => Some (S i)
        end
  end.

Lemma found_opt_body : forall needle haystack, is_found_opt needle haystack =
  match needle, haystack with
  | EmptyString, _ => Some 0
  | _, EmptyString => None
  | _, String _ h' =>
      if prefix needle haystack then Some 0 else
        match is_found_opt needle h' with
        | None => None
        | Some i => Some (S i)
        end
  end.
Proof.
  now destruct needle, haystack.
Qed.
