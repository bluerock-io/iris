From iris.proofmode Require Import proofmode.
From iris.bi Require Import internal_eq.
From iris.algebra Require Import cmra csum excl agree.
From iris.prelude Require Import options.


(** Derived [≼] connective on [cmra] elements. This can be defined on
    any [bi] that has internal equality [≡]. It corresponds to the
    step-indexed [≼{n}] connective in the [uPred] model. *)
Definition internal_included `{!BiInternalEq PROP} {A : cmra} (a b : A) : PROP
  := ∃ c, b ≡ a ⋅ c.
Global Arguments internal_included {_ _ _} _ _ : simpl never.
Global Instance: Params (@internal_included) 3 := {}.
Global Typeclasses Opaque internal_included.

Infix "≼" := internal_included : bi_scope.


Section internal_included_laws.
  Context `{!BiInternalEq PROP}.
  Implicit Type A B : cmra.

  (* Force implicit argument PROP *)
  Notation "P ⊢ Q" := (P ⊢@{PROP} Q).
  Notation "P ⊣⊢ Q" := (P ⊣⊢@{PROP} Q).

  (** Propers *)
  Global Instance internal_included_nonexpansive A :
    NonExpansive2 (internal_included (PROP := PROP) (A := A)).
  Proof. solve_proper. Qed.
  Global Instance internal_included_proper A :
    Proper ((≡) ==> (≡) ==> (⊣⊢)) (internal_included (PROP := PROP) (A := A)).
  Proof. solve_proper. Qed.

  (** Proofmode support *)
  Global Instance into_pure_internal_included {A} (a b : A) `{!Discrete b} :
    @IntoPure PROP (a ≼ b) (a ≼ b).
  Proof. rewrite /IntoPure /internal_included. eauto. Qed.

  Global Instance from_pure_internal_included {A} (a b : A) :
    @FromPure PROP false (a ≼ b) (a ≼ b).
  Proof. rewrite /FromPure /= /internal_included. eauto. Qed.

  Global Instance into_exist_internal_included {A} (a b : A) :
    IntoExist (PROP := PROP) (a ≼ b) (λ c, b ≡ a ⋅ c)%I (λ x, x).
  Proof. by rewrite /IntoExist. Qed.

  Global Instance from_exist_internal_included {A} (a b : A) :
    FromExist (PROP := PROP) (a ≼ b) (λ c, b ≡ a ⋅ c)%I.
  Proof. by rewrite /FromExist. Qed.

  Global Instance internal_included_persistent {A} (a b : A) :
    Persistent (PROP := PROP) (a ≼ b).
  Proof. rewrite /internal_included. apply _. Qed.

  Global Instance internal_included_absorbing {A} (a b : A) :
    Absorbing (PROP := PROP) (a ≼ b).
  Proof. rewrite /internal_included. apply _. Qed.

  (** Simplification lemmas *)
  Lemma f_homom_includedI {A B} (x y : A) (f : A → B) `{!NonExpansive f} :
    (* This is a slightly weaker condition than being a [CmraMorphism] *)
    (∀ c, f x ⋅ f c ≡ f (x ⋅ c)) →
    (x ≼ y ⊢ f x ≼ f y).
  Proof.
    intros f_homom. iDestruct 1 as (z) "Hz".
    iExists (f z). rewrite f_homom.
    by iApply f_equivI.
  Qed.

  Lemma prod_includedI {A B} (x y : A * B) :
    x ≼ y ⊣⊢ (x.1 ≼ y.1) ∧ (x.2 ≼ y.2).
  Proof.
    destruct x as [x1 x2]; destruct y as [y1 y2]; simpl; apply (anti_symm _).
    - apply bi.exist_elim => [[z1 z2]]. rewrite -pair_op prod_equivI /=.
      apply bi.and_mono; by eapply bi.exist_intro'.
    - iIntros "[[%z1 Hz1] [%z2 Hz2]]". iExists (z1, z2).
      rewrite -pair_op prod_equivI /=. eauto.
  Qed.

  Lemma option_includedI {A} (mx my : option A) :
    mx ≼ my ⊣⊢ match mx, my with
               | Some x, Some y => (x ≼ y) ∨ (x ≡ y)
               | None, _ => True
               | Some x, None => False
               end.
  Proof.
    apply (anti_symm _); last first.
    - destruct mx as [x|]; last (change None with (ε : option A); eauto).
      destruct my as [y|]; last eauto.
      iDestruct 1 as "[[%z H]|H]"; iRewrite "H".
      * iApply f_homom_includedI; eauto.
      * by iExists None.
    - destruct mx as [x|]; last eauto.
      iDestruct 1 as (c) "He". rewrite Some_op_opM option_equivI.
      destruct my as [y|]; last eauto.
      iRewrite "He". destruct c; simpl; eauto.
  Qed.

  Lemma csum_includedI {A B} (sx sy : csum A B) :
    sx ≼ sy ⊣⊢ match sx, sy with
               | Cinl x, Cinl y => x ≼ y
               | Cinr x, Cinr y => x ≼ y
               | _, CsumBot => True
               | _, _ => False
               end.
  Proof.
    apply (anti_symm _); last first.
    - destruct sx as [x|x|]; destruct sy as [y|y|]; eauto;
      eapply f_homom_includedI; eauto; apply _.
    - iDestruct 1 as (c) "Hc". rewrite csum_equivI.
      destruct sx; destruct sy; destruct c; eauto; by iExists _.
  Qed.

  Lemma excl_includedI {O : ofe} (x y : excl O) :
    x ≼ y ⊣⊢ match y with
             | ExclBot => True
             |  _ => False
             end.
  Proof.
    apply (anti_symm _).
    - iIntros "[%z Hz]". iStopProof.
      apply (internal_eq_rewrite' (x ⋅ z) y (λ y',
               match y' with
               | ExclBot => True
               | _ => False
               end)%I); [solve_proper|apply internal_eq_sym|].
      destruct x; destruct z; eauto.
    - destruct y; eauto.
  Qed.

  Lemma agree_includedI {O : ofe} (x y : agree O) : x ≼ y ⊣⊢ y ≡ x ⋅ y.
  Proof.
    apply (anti_symm _); last (iIntros "H"; by iExists _).
    iIntros "[%c Hc]". iRewrite "Hc". by rewrite assoc agree_idemp.
  Qed.
End internal_included_laws.