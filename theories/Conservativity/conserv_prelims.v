Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Ensembles.

Require Import im_syntax.

Section diamond_free.

Fixpoint diam_free φ : Prop :=
match φ with
| # p => True
| ⊥ => True
| ψ ∧ χ => diam_free ψ /\ diam_free χ
| ψ ∨ χ => diam_free ψ /\ diam_free χ
| ψ --> χ => diam_free ψ /\ diam_free χ
| ☐ ψ => diam_free ψ
| ⬦ ψ => False
end.


End diamond_free.