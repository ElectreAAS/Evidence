From Coq Require Import String.
From Coq Require Import Ascii.

Inductive prefix_1 : string -> string -> Prop :=
| P1_Empty : forall s2, prefix_1 "" s2
| P1_S : forall s1 s2, prefix_1 s1 s2 -> forall c, prefix_1 (String c s1) (String c s2)
.

Inductive prefix_2 : string -> string -> Prop :=
| P2_Empty : forall s2, prefix_2 "" s2
| P2_S : forall s1 s2 c, prefix_2 (String c s1) (String c s2) -> prefix_2 s1 s2
.


Inductive sub_1 : string -> string -> Prop :=
| S1 : forall pre post s1, sub_1 s1 (pre ++ s1 ++ post)%string
.

Inductive sub_2 : string -> string -> Prop :=
| S2_Prefix : forall n h, prefix_1 n h -> sub_2 n h
| S2_pN : forall n h c, sub_2 (String c n) h -> sub_2 n h
.

Inductive sub_3 : string -> string -> Prop :=
| S3_Prefix : forall n h, prefix_1 n h -> sub_3 n h
| S3_sH : forall n h, sub_3 n h -> forall c, sub_3 n (String c h)
.

Inductive sub_4 : string -> string -> Prop :=
| S4 : forall s1 s2 pre post, s2 = (pre ++ s1 ++ post)%string -> sub_4 s1 s2
.

Fixpoint sub_5 s1 s2 :=
  match s1, s2 with
  | EmptyString, _ => true
  | _, EmptyString => false
  | _, String _ s2' => (prefix s1 s2 || sub_5 s1 s2')%bool
  end.

Fixpoint sub_6 s1 s2 :=
  match s1, s2 with
  | EmptyString, _ => True
  | _, EmptyString => False
  | _, String _ s2' => prefix s1 s2 = true \/ sub_6 s1 s2'
  end.

Fixpoint sub_7 s1 s2 :=
  match s2 with
  | EmptyString => s1 = EmptyString
  | String _ s2' => prefix s1 s2 = true \/ sub_7 s1 s2'
  end.

Fixpoint sub_optimized (s1 s2 : string) :=
  (* Needs to be extractable to OCaml *) True
.

Theorem correct : forall s1 s2, sub_optimized s1 s2 <-> sub_? s1 s2.
Proof.
Admitted.


Fixpoint is_substring needle haystack :=
  match haystack with
  | EmptyString => needle = EmptyString
  | String _ h =>
    prefix needle haystack = true \/
    is_substring needle h
  end.

Lemma is_sub_body : forall needle haystack, is_substring needle haystack =
  match haystack with
  | EmptyString => needle = EmptyString
  | String _ h =>
    prefix needle haystack = true \/
    is_substring needle h
  end.
Proof.
  now destruct needle, haystack.
Qed.

Fixpoint is_found_at needle haystack pos :=
  if prefix needle haystack then
    exists i, pos = Some i /\ i <= length haystack
  else
    match haystack with
    | EmptyString => pos = None
    | String _ h => exists i, pos = Some (S i) /\ is_found_at needle h (Some i)
    end.


Lemma found_body : forall needle haystack pos, is_found_at needle haystack pos =
  if prefix needle haystack then
    exists i, pos = Some i /\ i <= length haystack
  else
    match haystack with
    | EmptyString => pos = None
    | String _ h => exists i, pos = Some (S i) /\ is_found_at needle h (Some i)
    end.
Proof.
  now destruct needle, haystack.
Qed.

Fixpoint found_2 needle haystack pos :=
  match pos with
  | Some 0 => prefix needle haystack = true
  | Some (S i) =>
    match haystack with
    | EmptyString => False
    | String _ h => found_2 needle h (Some i)
    end
  | None =>
    match haystack with
    | EmptyString => True
    | String _ h => found_2 needle h None
    end
  end.

Lemma found_body_2 : forall needle haystack pos, found_2 needle haystack pos =
  match pos with
  | Some 0 => prefix needle haystack = true
  | Some (S i) =>
    match haystack with
    | EmptyString => False
    | String _ h => found_2 needle h (Some i)
    end
  | None =>
    match haystack with
    | EmptyString => True
    | String _ h => found_2 needle h None
    end
  end.
Proof.
  now destruct needle, haystack.
Qed.
