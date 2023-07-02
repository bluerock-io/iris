Require Import iris.unstable.algebra.monotone.

Section test_mra_over_ofe.
  Context {A : ofe} {R : relation A}.
  Implicit Types a b : A.
  Implicit Types x y : mra R.

  Context `{!Reflexive R} {Has : AntiSymm (≡) R}.
  Lemma test a b : principal R a ≡ principal R b → a ≡ b.
  Proof.
    by intros ?%(inj _).
  Qed.

  Lemma principal_ne
         `{!∀ n, Proper ((dist n) ==> (dist n) ==> iff) R} :
    NonExpansive (principal R).
  Proof. apply _. Abort.

  Lemma principal_inj_instance :
    Inj (≡) (≡) (principal R).
  Proof. apply _. Abort.

  (* Also questionable. *)
  Instance principal_injN' n :
    Inj (dist n) (dist n) (principal R).
  Proof. apply principal_injN. Abort.
End test_mra_over_ofe.
