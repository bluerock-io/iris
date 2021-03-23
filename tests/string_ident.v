From iris.proofmode Require Import string_ident.
From Coq Require Import Strings.String.
From stdpp Require Import base.
Open Scope string.

(* these tests should test name generation directly, which Mangle Names
interferes with *)
Unset Mangle Names.

Lemma test_basic_ident : ∀ (n:nat), n = n.
Proof.
  let x := string_to_ident "n" in
  intros x.
  exact (eq_refl n).
Qed.

Lemma test_in_scope (n:nat) : n = n.
Proof.
  let x := string_to_ident "n" in exact (eq_refl n).
Qed.

Check "test_invalid_ident".
Lemma test_invalid_ident : True.
Proof.
  Fail let x := string_to_ident "has a space" in
       idtac x.
Abort.

Check "test_not_string".
Lemma test_not_string : True.
Proof.
  Fail let x := string_to_ident 4 in
       idtac x.
Abort.

Check "test_not_literal".
Lemma test_not_literal (s:string) : True.
Proof.
  Fail let x := string_to_ident s in
       idtac x.
Abort.
