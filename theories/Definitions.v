From Coq Require Import
    Ascii
    Classes.RelationClasses
    (* Extraction *)
    Nat
    String
.

Local Open Scope string_scope.

Definition smallest_such i P := P i /\ forall j, P j -> i <= j.

Definition is_at needle haystack i := exists pre post,
    haystack = (pre ++ needle ++ post) /\
    length pre = i.

Definition sub_new needle haystack i := smallest_such i (is_at needle haystack).

Fixpoint is_prefix s1 s2 :=
  match s1, s2 with
  | "", _ => True
  | _, "" => False
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
  | "", _ => True
  | _, "" => False
  | String c1 s1', String c2 s2' => c1 = c2 /\ is_prefix s1' s2'
  end.
Proof.
  now destruct s1, s2.
Qed.

Fixpoint is_sub_at needle haystack i :=
  match i with
  | 0 => is_prefix needle haystack
  | S j => exists c pre post,
             let h := (pre ++ needle ++ post) in
             haystack = String c h /\
             length pre = j /\
             is_sub_at needle h j
  end.

Lemma is_sub_at_body : forall needle haystack i, is_sub_at needle haystack i =
  match i with
  | 0 => is_prefix needle haystack
  | S j => exists c pre post,
             let h := (pre ++ needle ++ post) in
             haystack = String c h /\
             length pre = j /\
             is_sub_at needle h j
  end.
Proof.
  now destruct needle, haystack, i.
Qed.

Fixpoint is_substring needle haystack :=
  match needle, haystack with
  | "", _ => True
  | _, "" => False
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
  | "", _ => True
  | _, "" => False
  | _, String _ h' => is_prefix needle haystack \/
                      is_substring needle h'
  end.
Proof.
  now destruct needle, haystack.
Qed.

Fixpoint is_found_at needle haystack pos :=
  match needle, haystack, pos with
  | "", _, Some 0 => True
  | "", _, _ => False
  | _, "", None => True
  | _, "", _ => False
  | _, _, Some 0 => is_prefix needle haystack
  | _, String _ h', None => (~ is_prefix needle haystack) /\
                             is_found_at needle h' None
  | _, String _ h', Some (S i) =>
    (~ is_prefix needle haystack) /\
    is_found_at needle h' (Some i)
  end.

Lemma found_body : forall needle haystack pos, is_found_at needle haystack pos =
  match needle, haystack, pos with
  | "", _, Some 0 => True
  | "", _, _ => False
  | _, "", None => True
  | _, "", _ => False
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
  | "", _ => Some 0
  | _, "" => None
  | _, String _ h' =>
      if prefix needle haystack then Some 0 else
        match is_found_opt needle h' with
        | None => None
        | Some i => Some (S i)
        end
  end.

Lemma found_opt_body : forall needle haystack, is_found_opt needle haystack =
  match needle, haystack with
  | "", _ => Some 0
  | _, "" => None
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

(* 
Theorem gget s n (p: n < length s): ascii.
Proof.
  generalize dependent n.
  induction s; intros.
  - contradict p.
    apply PeanoNat.Nat.nlt_0_r.
  - induction n.
    + exact a.
    + apply (IHs n).
      apply PeanoNat.Nat.succ_lt_mono.
      assumption.
Defined.

Lemma foo1: forall x y n,
  x <= n -> x = S y -> y < n.
  intros.
  rewrite H0 in H.
  now apply PeanoNat.Nat.le_succ_l in H.
Qed.
Arguments foo1 {_ _ _ _ _}. *)

Fixpoint gget2 str i default :=
  match str, i with
  | "", _ => default
  | String c _, 0 => c
  | String _ s, S i => gget2 s i default
  end.

Fact get_body : forall str i default, gget2 str i default =
  match str, i with
  | "", _ => default
  | String c _, 0 => c
  | String _ s, S i => gget2 s i default
  end.
now destruct str.
Qed.

Fact get_no_default : forall str i d1 d2, i < length str -> gget2 str i d1 = gget2 str i d2.
Proof.
  induction str; intros.
  - simpl in H.
    now apply PeanoNat.Nat.nlt_0_r in H.
  - simpl.
    destruct i.
    reflexivity.
    apply IHstr.
    simpl in H.
    now apply PeanoNat.Nat.succ_lt_mono.
Qed.

Fixpoint inner needle haystack xi y :=
  let n := length needle in
  let h := length haystack in
  match y with
  | 0 => true
  | S y' =>
    let yi := n - y in
    if (xi + yi <? h)%nat then
      if (gget2 needle yi "z" =? gget2 haystack (xi + yi) "z")%char then
        inner needle haystack xi y'
      else false
    else false
  end
.

Fact inner_body : forall needle haystack xi y, inner needle haystack xi y =
  let n := length needle in
  let h := length haystack in
  match y with
  | 0 => true
  | S y' =>
    let yi := n - y in
    if (xi + yi <? h)%nat then
      if (gget2 needle yi "z" =? gget2 haystack (xi + yi) "z")%char then
        inner needle haystack xi y'
      else false
    else false
  end
.
now destruct y.
Qed.

Fixpoint loop needle haystack x :=
  let n := length needle in
  let h := length haystack in
  match x with
  | 0 => None
  | S x' => 
    let xi := h - x in
    if (h <? xi + n)%nat then None else
    if inner needle haystack xi n then Some xi else loop needle haystack x'
  end
.

Fact loop_body : forall needle haystack x, loop needle haystack x =
  let n := length needle in
  let h := length haystack in
  match x with
  | 0 => None
  | S x' => 
    let xi := h - x in
    if (h <? xi + n)%nat then None else
    if inner needle haystack xi n then Some xi else loop needle haystack x'
  end
.
now destruct x.
Qed.

Theorem naive (needle haystack: string) : option nat.
Proof.
  pose (n := length needle).
  induction needle.
    exact (Some 0).
  pose (h := length haystack).
  case_eq (h <? n)%nat; intros.
  - exact None.
  - exact (loop (String a needle) haystack h).
Defined.
