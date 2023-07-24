From stdpp Require Import propset gmap strings.
From iris.unstable.algebra Require Import monotone.

Unset Mangle Names.

Notation gset_mra K:= (mra (⊆@{gset K})).

(* Check if we indeed get [=], i.e., the right [Inj] instance is used. *)
Check "mra_test_eq".
Lemma mra_test_eq X Y : principal X ≡@{gset_mra nat} principal Y → X = Y.
Proof. intros ?%(inj _). Show. done. Qed.

Notation propset_mra K := (mra (⊆@{propset K})).

Lemma mra_test_equiv X Y : principal X ≡@{propset_mra nat} principal Y → X ≡ Y.
Proof. intros ?%(inj _). done. Qed.
