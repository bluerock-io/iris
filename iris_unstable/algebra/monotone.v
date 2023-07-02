(** This file is still experimental. See its tracking issue
https://gitlab.mpi-sws.org/iris/iris/-/issues/414 for details on remaining
issues before stabilization. *)

From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates.
From iris.prelude Require Import options.

Local Arguments pcore _ _ !_ /.
Local Arguments cmra_pcore _ !_ /.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments cmra_validN _ _ !_ /.
Local Arguments cmra_valid _  !_ /.

(* Given a preorder relation R on a type A we construct a resource algebra mra R
   and an injection principal : A -> mra R such that:
   [R x y] iff [principal x ≼ principal y]
   where ≼ is the extension order of mra R resource algebra. This is exactly
   what the lemma [principal_included] shows.

   This resource algebra is useful for reasoning about monotonicity.
   See the following paper for more details:

   Reasoning About Monotonicity in Separation Logic
   Amin Timany and Lars Birkedal
   in Certified Programs and Proofs (CPP) 2021
*)

Definition mra {A : Type} (R : relation A) : Type := list A.
Definition principal {A : Type} (R : relation A) (a : A) : mra R := [a].

(* OFE *)
Section ofe.
  Context {A : Type} {R : relation A}.
  Implicit Types a b : A.
  Implicit Types x y : mra R.

  Local Definition below (a : A) (x : mra R) := ∃ b, b ∈ x ∧ R a b.

  Local Lemma below_app a x y : below a (x ++ y) ↔ below a x ∨ below a y.
  Proof. set_solver. Qed.

  Local Lemma below_principal a b : below a (principal R b) ↔ R a b.
  Proof. set_solver. Qed.

  Local Instance mra_equiv : Equiv (mra R) :=
    λ x y, ∀ a, below a x ↔ below a y.

  Local Instance mra_equiv_equiv : Equivalence mra_equiv.
  Proof. unfold mra_equiv; split; intros ?; naive_solver. Qed.

  Canonical Structure mraO := discreteO (mra R).
End ofe.

Global Arguments mraO [_] _.

(* CMRA *)
Section cmra.
  Context {A : Type} {R : relation A}.
  Implicit Types a b : A.
  Implicit Types x y : mra R.

  Local Instance mra_valid : Valid (mra R) := λ x, True.
  Local Instance mra_validN : ValidN (mra R) := λ n x, True.
  Local Program Instance mra_op : Op (mra R) := λ x y, x ++ y.
  Local Instance mra_pcore : PCore (mra R) := Some.

  Lemma mra_cmra_mixin : CmraMixin (mra R).
  Proof.
    apply discrete_cmra_mixin; first apply _.
    apply ra_total_mixin.
    - eauto.
    - intros ??? Heq a; by rewrite !below_app (Heq a).
    - intros ?; done.
    - done.
    - intros ????; rewrite !below_app; by intuition.
    - intros ???; rewrite !below_app; by intuition.
    - rewrite /core /pcore /=; intros ??; rewrite below_app; by intuition.
    - done.
    - intros ? ? [? ?]; eexists _; done.
    - done.
  Qed.

  Canonical Structure mraR : cmra := Cmra (mra R) mra_cmra_mixin.

  Global Instance mra_cmra_total : CmraTotal mraR.
  Proof. rewrite /CmraTotal; eauto. Qed.
  Global Instance mra_core_id (x : mra R) : CoreId x.
  Proof. by constructor. Qed.

  Global Instance mra_cmra_discrete : CmraDiscrete mraR.
  Proof. split; last done. intros ? ?; done. Qed.

  Local Instance mra_unit : Unit (mra R) := @nil A.
  Lemma auth_ucmra_mixin : UcmraMixin (mra R).
  Proof. split; done. Qed.

  Canonical Structure mraUR := Ucmra (mra R) auth_ucmra_mixin.

  Lemma mra_idemp (x : mra R) : x ⋅ x ≡ x.
  Proof. intros a; rewrite below_app; naive_solver. Qed.

  Lemma mra_included (x y : mra R) : x ≼ y ↔ y ≡ x ⋅ y.
  Proof.
    split; [|by intros ?; exists y].
    intros [z ->]; rewrite assoc mra_idemp; done.
  Qed.

  Lemma principal_R_op_base `{!Transitive R} x y :
    (∀ b, b ∈ y → ∃ c, c ∈ x ∧ R b c) → y ⋅ x ≡ x.
  Proof.
    intros HR. split; rewrite /op /mra_op below_app; [|by intuition].
    intros [(c & (d & Hd1 & Hd2)%HR & Hc2)|]; [|done].
    exists d; split; [|transitivity c]; done.
  Qed.

  Lemma principal_R_op `{!Transitive R} a b :
    R a b → principal R a ⋅ principal R b ≡ principal R b.
  Proof.
    intros; apply principal_R_op_base; intros c; rewrite /principal.
    set_solver.
  Qed.

  Lemma principal_op_R' a b x :
    R a a → principal R a ⋅ x ≡ principal R b → R a b.
  Proof. move=> Ha /(_ a) HR. set_solver. Qed.

  Lemma principal_op_R `{!Reflexive R} a b x :
    principal R a ⋅ x ≡ principal R b → R a b.
  Proof. by apply principal_op_R'. Qed.

  Lemma principal_included `{!PreOrder R} a b :
    principal R a ≼ principal R b ↔ R a b.
  Proof.
    split.
    - move=> [z Hz]. by eapply principal_op_R.
    - intros ?; exists (principal R b). by rewrite principal_R_op.
  Qed.

  (* Useful? *)
  Lemma principal_includedN `{!PreOrder R} n a b :
    principal R a ≼{n} principal R b ↔ R a b.
  Proof. by rewrite -principal_included -cmra_discrete_included_iff. Qed.

  Lemma mra_local_update_grow `{!Transitive R} a x b:
    R a b →
    (principal R a, x) ~l~> (principal R b, principal R b).
  Proof.
    intros Hana Hanb.
    apply local_update_unital_discrete.
    intros z _ Habz.
    split; first done.
    intros w. specialize (Habz w).
    set_solver.
  Qed.

  Lemma mra_local_update_get_frag `{!PreOrder R} a b:
    R b a →
    (principal R a, ε) ~l~> (principal R a, principal R b).
  Proof.
    intros Hana.
    apply local_update_unital_discrete.
    intros z _; rewrite left_id; intros <-.
    split; first done.
    apply mra_included; by apply principal_included.
  Qed.

End cmra.

Global Arguments mraR {_} _.
Global Arguments mraUR {_} _.

(**
If [R] is a partial order, relative to a setoid [S] on the carrier [A],
then [principal R] is proper and injective.

The following theory generalizes over an arbitrary setoid [S] and necessary properties,
but is overly general, so we encapsulate the instances in an opt-in module.
*)
Module mra_over_rel.
Section mra_over_rel.
  Context {A : Type} {R : relation A}.
  Implicit Types a b : A.
  Implicit Types x y : mra R.
  Implicit Type (S : relation A).

  #[export] Instance principal_rel_proper S
         `{!Proper (S ==> S ==> iff) R} `{!Reflexive S} :
    Proper (S ==> (≡)) (principal R).
  Proof. intros a1 a2 Ha; split; rewrite ->!below_principal, !Ha; done. Qed.

  Lemma principal_inj_related a b :
    principal R a ≡ principal R b → R a a → R a b.
  Proof. move=> /(_ a). set_solver. Qed.

  Lemma principal_inj_general S a b :
    principal R a ≡ principal R b →
    R a a → R b b → (R a b → R b a → S a b) → S a b.
  Proof. intros ??? Has; apply Has; apply principal_inj_related; auto. Qed.

  #[export] Instance principal_inj {S} `{!Reflexive R} `{!AntiSymm S R} :
    Inj S (≡) (principal R).
  Proof. intros ???. apply principal_inj_general => //. apply: anti_symm. Qed.
End mra_over_rel.
End mra_over_rel.

(* Specialize [mra_over_rel] to equality. Only [principal_inj] seems generally useful. *)
Global Instance principal_inj `{R : relation A} `{!Reflexive R} `{!AntiSymm (=) R} :
  Inj (=) (≡) (principal R) := mra_over_rel.principal_inj.

(* Might be useful if the type of elements is an OFE. *)
Section mra_over_ofe.
  Context {A : ofe} {R : relation A}.
  Implicit Types a b : A.
  Implicit Types x y : mra R.

  Import mra_over_rel.

  Global Instance principal_proper
         `{!∀ n, Proper ((dist n) ==> (dist n) ==> iff) R} :
    Proper ((≡) ==> (≡)) (principal R) := ne_proper _.

  (* TODO: Useful? Clients should rather call equiv_dist. *)
  Lemma principal_injN `{!Reflexive R} {Has : AntiSymm (≡) R} n :
    Inj (dist n) (≡) (principal R).
  Proof. intros x y Hxy%(inj _). by apply equiv_dist. Qed.
End mra_over_ofe.
