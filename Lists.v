Require Export Induction.

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Check (pair 3 5).