From iris.bi Require Import bi plainly big_op.

(** See https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/610 *)
Lemma test_impl_persistent_1 `{!BiPlainly PROP, !BiPersistentlyImplPlainly PROP} :
  Persistent (PROP:=PROP) (True → True).
Proof. apply _. Qed.
Lemma test_impl_persistent_2 `{!BiPlainly PROP, !BiPersistentlyImplPlainly PROP} :
  Persistent (PROP:=PROP) (True → True → True).
Proof. apply _. Qed.

(* Test that the right scopes are used. *)
Lemma test_bi_scope {PROP : bi} : True.
Proof.
  (* [<affine> True] is implicitly in %I scope. *)
  pose proof (bi.wand_iff_refl (PROP:=PROP) (<affine> True)).
Abort.

(** Some basic tests to make sure patterns work in big ops. *)
Definition big_sepM_pattern_value
    {PROP : bi} (m : gmap nat (nat * nat)) : PROP :=
  [∗ map] '(x,y) ∈ m, ⌜ 10 = x ⌝.

Definition big_sepM_pattern_value_tt
    {PROP : bi} (m : gmap nat ()) : PROP :=
  [∗ map] '() ∈ m, True.

Definition big_sepM_pattern_key
    {PROP : bi} (m : gmap (nat * nat) nat) : PROP :=
  [∗ map] '(k,_) ↦ _ ∈ m, ⌜ 10 = k ⌝.

Definition big_sepM_pattern_both
    {PROP : bi} (m : gmap (nat * nat) (nat * nat)) : PROP :=
  [∗ map] '(k,_) ↦ '(_,y) ∈ m, ⌜ k = y ⌝.

Definition big_sepM_cast {PROP : bi} (m : gmap nat nat) : PROP :=
  [∗ map] (x:nat) ∈ m, ⌜ 10%Z = x ⌝.

Definition big_sepM2_pattern {PROP : bi} (m1 m2 : gmap nat (nat * nat)) : PROP :=
  [∗ map] '(x,_);'(_,y) ∈ m1;m2, ⌜ x = y ⌝.