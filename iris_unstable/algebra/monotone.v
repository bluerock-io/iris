(** This file is still experimental. See its tracking issue
https://gitlab.mpi-sws.org/iris/iris/-/issues/414 for details on remaining
issues before stabilization. *)

From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates.
From iris.prelude Require Import options.

(** Given a preorder [R] on a type [A] we construct the "monotone" resource
algebra [mra R] and an injection [principal : A → mra R] such that:

   [R x y] iff [principal x ≼ principal y]

Here, [≼] is the extension order of the [mra R] resource algebra. This is
exactly what the lemma [principal_included] shows.

This resource algebra is useful for reasoning about monotonicity. See the
following paper for more details:

  Reasoning About Monotonicity in Separation Logic
  Amin Timany and Lars Birkedal
  in Certified Programs and Proofs (CPP) 2021
*)

Record mra {A} (R : relation A) := { mra_car : list A }.
Definition principal {A} (R : relation A) (a : A) : mra R :=
  {| mra_car := [a] |}.
Global Arguments mra_car {_ _} _.

Section mra.
  Context {A} {R : relation A}.
  Implicit Types a b : A.
  Implicit Types x y : mra R.

  Local Definition below (a : A) (x : mra R) := ∃ b, b ∈ mra_car x ∧ R a b.

  Local Lemma below_principal a b : below a (principal R b) ↔ R a b.
  Proof. set_solver. Qed.

  (* OFE *)
  Local Instance mra_equiv : Equiv (mra R) := λ x y,
    ∀ a, below a x ↔ below a y.

  Local Instance mra_equiv_equiv : Equivalence mra_equiv.
  Proof. unfold mra_equiv; split; intros ?; naive_solver. Qed.

  Canonical Structure mraO := discreteO (mra R).

  (* CMRA *)
  Local Instance mra_valid : Valid (mra R) := λ x, True.
  Local Instance mra_validN : ValidN (mra R) := λ n x, True.
  Local Program Instance mra_op : Op (mra R) := λ x y,
    {| mra_car := mra_car x ++ mra_car y |}.
  Local Instance mra_pcore : PCore (mra R) := Some.

  Lemma mra_cmra_mixin : CmraMixin (mra R).
  Proof.
    apply discrete_cmra_mixin; first apply _.
    apply ra_total_mixin; try done.
    - (* [Proper] of [op] *) intros x y z Hyz a. specialize (Hyz a). set_solver.
    - (* [Proper] of [core] *) apply _.
    - (* [Assoc] *) intros x y z a. set_solver.
    - (* [Comm] *) intros x y a. set_solver.
    - (* [core x ⋅ x ≡ x] *) intros x a. set_solver.
  Qed.

  Canonical Structure mraR : cmra := Cmra (mra R) mra_cmra_mixin.

  Global Instance mra_cmra_total : CmraTotal mraR.
  Proof. rewrite /CmraTotal; eauto. Qed.
  Global Instance mra_core_id x : CoreId x.
  Proof. by constructor. Qed.

  Global Instance mra_cmra_discrete : CmraDiscrete mraR.
  Proof. split; last done. intros ? ?; done. Qed.

  Local Instance mra_unit : Unit (mra R) := {| mra_car := [] |}.
  Lemma auth_ucmra_mixin : UcmraMixin (mra R).
  Proof. split; done. Qed.

  Canonical Structure mraUR := Ucmra (mra R) auth_ucmra_mixin.

  (* Laws *)
  Lemma mra_idemp x : x ⋅ x ≡ x.
  Proof. intros a. set_solver. Qed.

  Lemma mra_included x y : x ≼ y ↔ y ≡ x ⋅ y.
  Proof.
    split; [|by intros ?; exists y].
    intros [z ->]; rewrite assoc mra_idemp; done.
  Qed.

  Lemma principal_R_op `{!Transitive R} a b :
    R a b →
    principal R a ⋅ principal R b ≡ principal R b.
  Proof. intros Hab c. set_solver. Qed.

  Lemma principal_included `{!PreOrder R} a b :
    principal R a ≼ principal R b ↔ R a b.
  Proof.
    split.
    - move=> [z Hz]. specialize (Hz a). set_solver.
    - intros ?; exists (principal R b). by rewrite principal_R_op.
  Qed.

  Lemma mra_local_update_grow `{!Transitive R} a x b:
    R a b →
    (principal R a, x) ~l~> (principal R b, principal R b).
  Proof.
    intros Hana. apply local_update_unital_discrete=> z _ Habz.
    split; first done. intros c. specialize (Habz c). set_solver.
  Qed.

  Lemma mra_local_update_get_frag `{!PreOrder R} a b:
    R b a →
    (principal R a, ε) ~l~> (principal R a, principal R b).
  Proof.
    intros Hana. apply local_update_unital_discrete=> z _.
    rewrite left_id. intros <-. split; first done.
    apply mra_included; by apply principal_included.
  Qed.
End mra.

Global Arguments mraO {_} _.
Global Arguments mraR {_} _.
Global Arguments mraUR {_} _.

(** If [R] is a partial order, relative to a reflexive relation [S] on the
carrier [A], then [principal R] is proper and injective. The theory for
arbitrary relations [S] is overly general, so we do not declare the results
as instances. Below we provide instances for [S] being [=] and [≡]. *)
Section mra_over_rel.
  Context {A} {R : relation A} (S : relation A).
  Implicit Types a b : A.
  Implicit Types x y : mra R.

  Lemma principal_rel_proper :
    Reflexive S →
    Proper (S ==> S ==> iff) R →
    Proper (S ==> (≡)) (principal R).
  Proof. intros ? HR a1 a2 Ha b. rewrite !below_principal. by apply HR. Qed.

  Lemma principal_rel_inj :
    Reflexive R →
    AntiSymm S R →
    Inj S (≡) (principal R).
  Proof.
    intros ?? a b Hab. move: (Hab a) (Hab b). rewrite !below_principal.
    intros. apply (anti_symm R); naive_solver.
  Qed.
End mra_over_rel.

Global Instance principal_inj {A} {R : relation A} :
  Reflexive R →
  AntiSymm (=) R →
  Inj (=) (≡) (principal R) | 0. (* Lower cost than [principal_inj] *)
Proof. intros. by apply (principal_rel_inj (=)). Qed.

Global Instance principal_proper `{Equiv A} {R : relation A} :
  Reflexive (≡@{A}) →
  Proper ((≡) ==> (≡) ==> iff) R →
  Proper ((≡) ==> (≡)) (principal R).
Proof. intros. by apply (principal_rel_proper (≡)). Qed.

Global Instance principal_equiv_inj `{Equiv A} {R : relation A} :
  Reflexive R →
  AntiSymm (≡) R →
  Inj (≡) (≡) (principal R) | 1.
Proof. intros. by apply (principal_rel_inj (≡)). Qed.
