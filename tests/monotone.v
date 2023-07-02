Require Import iris.unstable.algebra.monotone.

Section test_mra_over_ofe.
  Context {A : ofe} {R : relation A}.
  Implicit Types a b : A.
  Implicit Types x y : mra R.

  Context `{!Reflexive R} {Has : AntiSymm (≡) R}.
  Lemma test a b : principal R a ≡ principal R b → a ≡ b.
  Proof.
    Fail by intros ?%(inj _).
    by intros ?%(inj (R := equiv) _).
  Qed.
End test_mra_over_ofe.
