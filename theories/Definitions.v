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
| S1 : forall pre post needle, sub_1 needle (pre ++ needle ++ post)%string
.

Inductive sub_2 : string -> string -> Prop :=
| S2_Prefix : forall needle haystack, prefix_1 needle haystack -> sub_2 needle haystack
| S2_pN : forall needle haystack c, sub_2 (String c needle) haystack -> sub_2 needle haystack
.

Inductive sub_3 : string -> string -> Prop :=
| S3_Prefix : forall needle haystack, prefix_1 needle haystack -> sub_3 needle haystack
| S3_sH : forall needle haystack, sub_3 needle haystack -> forall c, sub_3 needle (String c haystack)
.

Inductive sub_4 : string -> string -> Prop :=
| S4 : forall needle haystack pre post, haystack = (pre ++ needle ++ post)%string -> sub_4 needle haystack
.

Fixpoint sub_5 needle haystack :=
  match needle, haystack with
  | EmptyString, _ => true
  | _, EmptyString => false
  | _, String _ haystack' => (prefix needle haystack || sub_5 needle haystack')%bool
  end.

Fixpoint sub_6 needle haystack :=
  match needle, haystack with
  | EmptyString, _ => True
  | _, EmptyString => False
  | _, String _ haystack' => prefix needle haystack = true \/ sub_6 needle haystack'
  end.

Fixpoint sub_7 needle haystack :=
  match haystack with
  | EmptyString => needle = EmptyString
  | String _ haystack' => prefix needle haystack = true \/ sub_7 needle haystack'
  end.

Fixpoint sub_optimized (needle haystack : string) :=
  (* Needs to be extractable to OCaml *) True
.

Theorem correct : forall needle haystack, sub_optimized needle haystack <-> sub_? needle haystack.
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
