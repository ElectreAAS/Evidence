From Coq Require Export String.
From Coq Require Export Ascii.

Fixpoint is_substring needle haystack :=
  prefix needle haystack = true \/
  match haystack with
  | EmptyString => False
  | String _ h' => is_substring needle h'
  end.

Fixpoint is_found_loop pos needle haystack :=
  match haystack with
  | EmptyString => None
  | String _ h' =>
    if prefix needle haystack then
      Some pos
    else
      is_found_loop (S pos) needle h'
  end.

Definition is_found_at := is_found_loop 0.
