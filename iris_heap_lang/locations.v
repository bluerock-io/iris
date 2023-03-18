From stdpp Require Import countable numbers gmap.
From iris.prelude Require Export prelude.
From iris.prelude Require Import options.

Record loc := Loc { loc_car : Z }.

Add Printing Constructor loc.

Module Loc.
  Local Open Scope Z_scope.

  Lemma eq_spec l1 l2 : l1 = l2 ↔ loc_car l1 = loc_car l2.
  Proof. destruct l1, l2; naive_solver. Qed.

  Global Instance eq_dec : EqDecision loc.
  Proof. solve_decision. Defined.

  Global Instance inhabited : Inhabited loc := populate {|loc_car := 0 |}.

  Global Instance countable : Countable loc.
  Proof. by apply (inj_countable' loc_car Loc); intros []. Defined.

  Global Program Instance infinite : Infinite loc :=
    inj_infinite (λ p, {| loc_car := p |}) (λ l, Some (loc_car l)) _.
  Next Obligation. done. Qed.

  Definition add (l : loc) (off : Z) : loc :=
    {| loc_car := loc_car l + off|}.

  Module Import notations.
    Notation "l +ₗ off" :=
      (add l off) (at level 50, left associativity) : stdpp_scope.
  End notations.

  Lemma add_assoc l i j : l +ₗ i +ₗ j = l +ₗ (i + j).
  Proof. rewrite eq_spec /=. lia. Qed.

  Lemma add_0 l : l +ₗ 0 = l.
  Proof. rewrite eq_spec /=; lia. Qed.

  Global Instance add_inj l : Inj eq eq (add l).
  Proof. intros x1 x2. rewrite eq_spec /=. lia. Qed.

  Definition fresh (ls : gset loc) : loc :=
    {| loc_car := set_fold (λ k r, (1 + loc_car k) `max` r) 1 ls |}.

  Lemma fresh_fresh ls i : 0 ≤ i → fresh ls +ₗ i ∉ ls.
  Proof.
    intros Hi. cut (∀ l, l ∈ ls → loc_car l < loc_car (fresh ls) + i).
    { intros help Hf%help. simpl in *. lia. }
    apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → (loc_car l < r + i)));
      set_solver by eauto with lia.
  Qed.

  Global Opaque fresh.
End Loc.

Export Loc.notations.
