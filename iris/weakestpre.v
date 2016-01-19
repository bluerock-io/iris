Require Export iris.pviewshifts.
Require Import iris.wsat.
Local Hint Extern 10 (_ ≤ _) => omega.
Local Hint Extern 100 (@eq coPset _ _) => eassumption || solve_elem_of.
Local Hint Extern 100 (_ ∉ _) => solve_elem_of.
Local Hint Extern 10 (✓{_} _) =>
  repeat match goal with H : wsat _ _ _ _ |- _ => apply wsat_valid in H end;
  solve_validN.

Record wp_go {Σ} (E : coPset) (Q Qfork : iexpr Σ → nat → res' Σ → Prop)
    (k : nat) (rf : res' Σ) (e1 : iexpr Σ) (σ1 : istate Σ) := {
  wf_safe : reducible e1 σ1;
  wp_step e2 σ2 ef :
    prim_step e1 σ1 e2 σ2 ef →
    ∃ r2 r2',
      wsat k E σ2 (r2 ⋅ r2' ⋅ rf) ∧
      Q e2 k r2 ∧
      ∀ e', ef = Some e' → Qfork e' k r2'
}.
CoInductive wp_pre {Σ} (E : coPset)
     (Q : ival Σ → iProp Σ) : iexpr Σ → nat → res' Σ → Prop :=
  | wp_pre_0 e r : wp_pre E Q e 0 r
  | wp_pre_value n r v : Q v n r → wp_pre E Q (of_val v) n r
  | wp_pre_step n r1 e1 :
     to_val e1 = None →
     (∀ rf k Ef σ1,
       1 < k < n → E ∩ Ef = ∅ →
       wsat (S k) (E ∪ Ef) σ1 (r1 ⋅ rf) →
       wp_go (E ∪ Ef) (wp_pre E Q)
                      (wp_pre coPset_all (λ _, True%I)) k rf e1 σ1) →
     wp_pre E Q e1 n r1.
Program Definition wp {Σ} (E : coPset) (e : iexpr Σ)
  (Q : ival Σ → iProp Σ) : iProp Σ := {| uPred_holds := wp_pre E Q e |}.
Next Obligation.
  intros Σ E e Q r1 r2 n Hwp Hr.
  destruct Hwp as [| |n r1 e2 ? Hgo]; constructor; rewrite -?Hr; auto.
  intros rf k Ef σ1 ?; rewrite -(dist_le _ _ _ _ Hr); naive_solver.
Qed.
Next Obligation. constructor. Qed.
Next Obligation.
  intros Σ E e Q r1 r2 n1; revert Q E e r1 r2.
  induction n1 as [n1 IH] using lt_wf_ind; intros Q E e r1 r1' n2.
  destruct 1 as [| |n1 r1 e1 ? Hgo].
  * rewrite Nat.le_0_r; intros ? -> ?; constructor.
  * constructor; eauto using uPred_weaken.
  * intros [rf' Hr] ??; constructor; [done|intros rf k Ef σ1 ???].
    destruct (Hgo (rf' ⋅ rf) k Ef σ1) as [Hsafe Hstep];
      rewrite ?(associative _) -?Hr; auto; constructor; [done|].
    intros e2 σ2 ef ?; destruct (Hstep e2 σ2 ef) as (r2&r2'&?&?&?); auto.
    exists r2, (r2' ⋅ rf'); split_ands; eauto 10 using (IH k), @ra_included_l.
    by rewrite -!(associative _) (associative _ r2).
Qed.
Instance: Params (@wp) 3.

Section wp.
Context {Σ : iParam}.
Implicit Types P : iProp Σ.
Implicit Types Q : ival Σ → iProp Σ.
Implicit Types v : ival Σ.
Implicit Types e : iexpr Σ.
Transparent uPred_holds.

Lemma wp_weaken E1 E2 e Q1 Q2 r n n' :
  E1 ⊆ E2 → (∀ v r n', n' ≤ n → ✓{n'} r → Q1 v n' r → Q2 v n' r) →
  n' ≤ n → ✓{n'} r → wp E1 e Q1 n' r → wp E2 e Q2 n' r.
Proof.
  intros HE HQ; revert e r; induction n' as [n' IH] using lt_wf_ind; intros e r.
  destruct 3 as [| |n' r e1 ? Hgo]; constructor; eauto.
  intros rf k Ef σ1 ???.
  assert (E2 ∪ Ef = E1 ∪ (E2 ∖ E1 ∪ Ef)) as HE'.
  { by rewrite (associative_L _) -union_difference_L. }
  destruct (Hgo rf k ((E2 ∖ E1) ∪ Ef) σ1) as [Hsafe Hstep]; rewrite -?HE'; auto.
  split; [done|intros e2 σ2 ef ?].
  destruct (Hstep e2 σ2 ef) as (r2&r2'&?&?&?); auto.
  exists r2, r2'; split_ands; [rewrite HE'|eapply IH|]; eauto.
Qed.
Global Instance wp_ne E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp E e).
Proof. by intros Q Q' HQ; split; apply wp_weaken with n; try apply HQ. Qed.
Global Instance wp_proper E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp E e).
Proof.
  by intros Q Q' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.

Lemma wp_value E Q v : Q v ⊑ wp E (of_val v) Q.
Proof. by constructor. Qed.
Lemma wp_mono E e Q1 Q2 : (∀ v, Q1 v ⊑ Q2 v) → wp E e Q1 ⊑ wp E e Q2.
Proof. by intros HQ r n ?; apply wp_weaken with n; intros; try apply HQ. Qed.
Lemma wp_pvs E e Q : pvs E E (wp E e Q) ⊑ wp E e (λ v, pvs E E (Q v)).
Proof.
  intros r [|n] ?; [done|]; intros Hvs.
  destruct (to_val e) as [v|] eqn:He; [apply of_to_val in He; subst|].
  { constructor; eapply pvs_mono, Hvs; auto; clear.
    intros r n ?; inversion 1 as [| |??? He]; simplify_equality; auto.
    by rewrite ?to_of_val in He. }
  constructor; [done|intros rf k Ef σ1 ???].
  destruct (Hvs rf (S k) Ef σ1) as (r'&Hwp&?); auto.
  inversion Hwp as [| |???? Hgo]; subst; [by rewrite to_of_val in He|].
  destruct (Hgo rf k Ef σ1) as [Hsafe Hstep]; auto.
  split; [done|intros e2 σ2 ef ?].
  destruct (Hstep e2 σ2 ef) as (r2&r2'&?&Hwp'&?); auto.
  exists r2, r2'; split_ands; auto.
  eapply wp_mono, Hwp'; auto using pvs_intro.
Qed.
Lemma wp_atomic E1 E2 e Q :
  E2 ⊆ E1 → atomic e → pvs E1 E2 (wp E2 e (λ v, pvs E2 E1 (Q v))) ⊑ wp E1 e Q.
Proof.
  intros ? He r n ? Hvs; constructor; eauto using atomic_not_value.
  intros rf k Ef σ1 ???.
  destruct (Hvs rf (S k) Ef σ1) as (r'&Hwp&?); auto.
  inversion Hwp as [| |???? Hgo]; subst; [by destruct (atomic_of_val v)|].
  destruct (Hgo rf k Ef σ1) as [Hsafe Hstep]; clear Hgo; auto.
  split; [done|intros e2 σ2 ef ?].
  destruct (Hstep e2 σ2 ef) as (r2&r2'&?&Hwp'&?); clear Hsafe Hstep; auto.
  destruct Hwp' as [|k r2 v Hvs'|k r2 e2 Hgo];
    [lia| |destruct (atomic_step e σ1 e2 σ2 ef); naive_solver].
  destruct (Hvs' (r2' ⋅ rf) k Ef σ2) as (r3&[]); rewrite ?(associative _); auto.
  by exists r3, r2'; split_ands; [rewrite -(associative _)|constructor|].
Qed.
Lemma wp_mask_weaken E1 E2 e Q : E1 ⊆ E2 → wp E1 e Q ⊑ wp E2 e Q.
Proof. by intros HE r n ?; apply wp_weaken with n. Qed.
Lemma wp_frame_r E e Q R : (wp E e Q ★ R) ⊑ wp E e (λ v, Q v ★ R).
Proof.
  intros r' n Hvalid (r&rR&Hr&Hwp&?); revert Hvalid.
  rewrite Hr; clear Hr; revert e r Hwp.
  induction n as [n IH] using lt_wf_ind; intros e r1.
  destruct 1 as [| |n r e ? Hgo]; constructor; [exists r, rR; eauto|auto|].
  intros rf k Ef σ1 ???; destruct (Hgo (rR⋅rf) k Ef σ1) as [Hsafe Hstep]; auto.
  { by rewrite (associative _). }
  split; [done|intros e2 σ2 ef ?].
  destruct (Hstep e2 σ2 ef) as (r2&r2'&?&?&?); auto.
  exists (r2 ⋅ rR), r2'; split_ands; auto.
  * by rewrite -(associative _ r2)
      (commutative _ rR) !(associative _) -(associative _ _ rR).
  * apply IH; eauto using uPred_weaken.
Qed.
Lemma wp_frame_later_r E e Q R :
  to_val e = None → (wp E e Q ★ ▷ R) ⊑ wp E e (λ v, Q v ★ R).
Proof.
  intros He r' n Hvalid (r&rR&Hr&Hwp&?); revert Hvalid; rewrite Hr; clear Hr.
  destruct Hwp as [| |[|n] r e ? Hgo]; [done|by rewrite to_of_val in He|done| ].
  constructor; [done|intros rf k Ef σ1 ???].
  destruct (Hgo (rR⋅rf) k Ef σ1) as [Hsafe Hstep];rewrite ?(associative _);auto.
  split; [done|intros e2 σ2 ef ?].
  destruct (Hstep e2 σ2 ef) as (r2&r2'&?&?&?); auto.
  exists (r2 ⋅ rR), r2'; split_ands; auto.
  * by rewrite -(associative _ r2)
      (commutative _ rR) !(associative _) -(associative _ _ rR).
  * apply wp_frame_r; [auto|exists r2, rR; split_ands; auto].
    eapply uPred_weaken with rR n; eauto.
Qed.
Lemma wp_bind `(HK : is_ctx K) E e Q :
  wp E e (λ v, wp E (K (of_val v)) Q) ⊑ wp E (K e) Q.
Proof.
  intros r n; revert e r; induction n as [n IH] using lt_wf_ind; intros e r ?.
  destruct 1 as [| |n r e ? Hgo]; [| |constructor]; auto using is_ctx_value.
  intros rf k Ef σ1 ???; destruct (Hgo rf k Ef σ1) as [Hsafe Hstep]; auto.
  split.
  { destruct Hsafe as (e2&σ2&ef&?).
    by exists (K e2), σ2, ef; apply is_ctx_step_preserved. }
  intros e2 σ2 ef ?.
  destruct (is_ctx_step _ HK e σ1 e2 σ2 ef) as (e2'&->&?); auto.
  destruct (Hstep e2' σ2 ef) as (r2&r2'&?&?&?); auto.
  exists r2, r2'; split_ands; try eapply IH; eauto.
Qed.

(* Derived rules *)
Import uPred.
Global Instance wp_mono' E e :
  Proper (pointwise_relation _ (⊑) ==> (⊑)) (wp E e).
Proof. by intros Q Q' ?; apply wp_mono. Qed.
Lemma wp_frame_l E e Q R : (R ★ wp E e Q) ⊑ wp E e (λ v, R ★ Q v).
Proof. setoid_rewrite (commutative _ R); apply wp_frame_r. Qed.
Lemma wp_frame_later_l E e Q R :
  to_val e = None → (▷ R ★ wp E e Q) ⊑ wp E e (λ v, R ★ Q v).
Proof.
  rewrite (commutative _ (▷ R)%I); setoid_rewrite (commutative _ R).
  apply wp_frame_later_r.
Qed.
Lemma wp_always_l E e Q R `{!AlwaysStable R} :
  (R ∧ wp E e Q) ⊑ wp E e (λ v, R ∧ Q v).
Proof. by setoid_rewrite (always_and_sep_l' _ _); rewrite wp_frame_l. Qed.
Lemma wp_always_r E e Q R `{!AlwaysStable R} :
  (wp E e Q ∧ R) ⊑ wp E e (λ v, Q v ∧ R).
Proof. by setoid_rewrite (always_and_sep_r' _ _); rewrite wp_frame_r. Qed.
Lemma wp_impl_l E e Q1 Q2 : ((□ ∀ v, Q1 v → Q2 v) ∧ wp E e Q1) ⊑ wp E e Q2.
Proof.
  rewrite wp_always_l; apply wp_mono=> v.
  by rewrite always_elim (forall_elim _ v) impl_elim_l.
Qed.
Lemma wp_impl_r E e Q1 Q2 : (wp E e Q1 ∧ □ ∀ v, Q1 v → Q2 v) ⊑ wp E e Q2.
Proof. by rewrite (commutative _) wp_impl_l. Qed.
End wp.
