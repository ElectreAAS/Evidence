From Coq Require Export String.

Definition is_empty_str (s: string) :=
  s = EmptyString.
