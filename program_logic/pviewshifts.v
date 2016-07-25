From iris.prelude Require Export coPset.
From iris.algebra Require Export upred_big_op updates.
From iris.program_logic Require Export model.
From iris.program_logic Require Import ownership wsat.
Local Hint Extern 10 (_ ≤ _) => omega.
Local Hint Extern 100 (_ ⊥ _) => set_solver.
Local Hint Extern 100 (_ ∉ _) => set_solver.
Local Hint Extern 10 (✓{_} _) =>
  repeat match goal with
  | H : wsat _ _ _ _ |- _ => apply wsat_valid in H; last omega
  end; solve_validN.

Program Definition pvs_def {Λ Σ} (E1 E2 : coPset) (P : iProp Λ Σ) : iProp Λ Σ :=
  {| uPred_holds n r1 := ∀ k Ef σ rf,
       0 < k ≤ n → E1 ∪ E2 ⊥ Ef →
       wsat k (E1 ∪ Ef) σ (r1 ⋅ rf) →
       ∃ r2, P k r2 ∧ wsat k (E2 ∪ Ef) σ (r2 ⋅ rf) |}.
Next Obligation.
  intros Λ Σ E1 E2 P n r1 r2 HP [r3 Hr2] k Ef σ rf ??.
  rewrite (dist_le _ _ _ _ Hr2); last lia. intros Hws.
  destruct (HP k Ef σ (r3 ⋅ rf)) as (r'&?&Hws'); rewrite ?(assoc op); auto.
  exists (r' ⋅ r3); rewrite -assoc; split; last done.
  apply uPred_mono with r'; eauto using cmra_includedN_l.
Qed.
Next Obligation. naive_solver. Qed.

Definition pvs_aux : { x | x = @pvs_def }. by eexists. Qed.
Definition pvs := proj1_sig pvs_aux.
Definition pvs_eq : @pvs = @pvs_def := proj2_sig pvs_aux.

Arguments pvs {_ _} _ _ _%I.
Instance: Params (@pvs) 4.

Notation "|={ E1 , E2 }=> Q" := (pvs E1 E2 Q%I)
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "|={ E1 , E2 }=>  Q") : uPred_scope.
Notation "|={ E }=> Q" := (pvs E E Q%I)
  (at level 99, E at level 50, Q at level 200,
   format "|={ E }=>  Q") : uPred_scope.
Notation "|==> Q" := (pvs ⊤ ⊤ Q%I)
  (at level 99, Q at level 200, format "|==>  Q") : uPred_scope.

Notation "P ={ E1 , E2 }=> Q" := (P ⊢ |={E1,E2}=> Q)
  (at level 99, E1, E2 at level 50, Q at level 200, only parsing) : C_scope.
Notation "P ={ E }=> Q" := (P ⊢ |={E}=> Q)
  (at level 99, E at level 50, Q at level 200, only parsing) : C_scope.

Notation "P ={ E1 , E2 }=★ Q" := (P -★ |={E1,E2}=> Q)%I
  (at level 99, E1,E2 at level 50, Q at level 200,
   format "P  ={ E1 , E2 }=★  Q") : uPred_scope.
Notation "P ={ E }=★ Q" := (P ={E,E}=★ Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "P  ={ E }=★  Q") : uPred_scope.

Section pvs.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types P Q : iProp Λ Σ.
Implicit Types m : iGst Λ Σ.

Lemma pvs_zero E1 E2 P r : pvs_def E1 E2 P 0 r.
Proof. intros ?????. exfalso. omega. Qed.

Global Instance pvs_ne E1 E2 n : Proper (dist n ==> dist n) (@pvs Λ Σ E1 E2).
Proof.
  rewrite pvs_eq.
  intros P Q HPQ; split=> n' r1 ??; simpl; split; intros HP k Ef σ rf ???;
    destruct (HP k Ef σ rf) as (r2&?&?); auto;
    exists r2; split_and?; auto; apply HPQ; eauto.
Qed.
Global Instance pvs_proper E1 E2 : Proper ((≡) ==> (≡)) (@pvs Λ Σ E1 E2).
Proof. apply ne_proper, _. Qed.

Lemma pvs_intro E P : P ={E}=> P.
Proof.
  rewrite pvs_eq. split=> n r ? HP k Ef σ rf ???; exists r; split; last done.
  apply uPred_closed with n; eauto.
Qed.
Lemma pvs_mono E1 E2 P Q : (P ⊢ Q) → (|={E1,E2}=> P) ={E1,E2}=> Q.
Proof.
  rewrite pvs_eq. intros HPQ; split=> n r ? HP k Ef σ rf ???.
  destruct (HP k Ef σ rf) as (r2&?&?); eauto.
  exists r2; eauto using uPred_in_entails.
Qed.
Lemma pvs_timeless E P : TimelessP P → ▷ P ={E}=> P.
Proof.
  rewrite pvs_eq uPred.timelessP_spec=> HP.
  uPred.unseal; split=>-[|n] r ? HP' k Ef σ rf ???; first lia.
  exists r; split; last done.
  apply HP, uPred_closed with n; eauto using cmra_validN_le.
Qed.
Lemma pvs_trans E1 E2 E3 P :
  E2 ⊆ E1 ∪ E3 → (|={E1,E2}=> |={E2,E3}=> P) ={E1,E3}=> P.
Proof.
  rewrite pvs_eq. intros ?; split=> n r1 ? HP1 k Ef σ rf ???.
  destruct (HP1 k Ef σ rf) as (r2&HP2&?); auto.
Qed.
Lemma pvs_mask_frame E1 E2 Ef P :
  Ef ⊥ E1 ∪ E2 → (|={E1,E2}=> P) ={E1 ∪ Ef,E2 ∪ Ef}=> P.
Proof.
  rewrite pvs_eq. intros ?; split=> n r ? HP k Ef' σ rf ???.
  destruct (HP k (Ef∪Ef') σ rf) as (r'&?&?); rewrite ?(assoc_L _); eauto.
  by exists r'; rewrite -(assoc_L _).
Qed.
Lemma pvs_frame_r E1 E2 P Q : (|={E1,E2}=> P) ★ Q ={E1,E2}=> P ★ Q.
Proof.
  rewrite pvs_eq. uPred.unseal; split; intros n r ? (r1&r2&Hr&HP&?) k Ef σ rf ???.
  destruct (HP k Ef σ (r2 ⋅ rf)) as (r'&?&?); eauto.
  { by rewrite assoc -(dist_le _ _ _ _ Hr); last lia. }
  exists (r' ⋅ r2); split; last by rewrite -assoc.
  exists r', r2; split_and?; auto. apply uPred_closed with n; auto.
Qed.
Lemma pvs_openI i P : ownI i P ={{[i]},∅}=> ▷ P.
Proof.
  rewrite pvs_eq. uPred.unseal; split=> -[|n] r ? Hinv [|k] Ef σ rf ???; try lia.
  apply ownI_spec in Hinv; last auto.
  destruct (wsat_open k Ef σ (r ⋅ rf) i P) as (rP&?&?); auto.
  { rewrite lookup_wld_op_l ?Hinv; eauto; apply dist_le with (S n); eauto. }
  exists (rP ⋅ r); split; last by rewrite (left_id_L _ _) -assoc.
  eapply uPred_mono with rP; eauto using cmra_includedN_l.
Qed.
Lemma pvs_closeI i P : ownI i P ∧ ▷ P ={∅,{[i]}}=> True.
Proof.
  rewrite pvs_eq.
  uPred.unseal; split=> -[|n] r ? [? HP] [|k] Ef σ rf ? HE ?; try lia.
  exists ∅; split; [done|].
  rewrite left_id; apply wsat_close with P r.
  - apply ownI_spec, uPred_closed with (S n); auto.
  - set_solver +HE.
  - by rewrite -(left_id_L ∅ (∪) Ef).
  - apply uPred_closed with n; auto.
Qed.
Lemma pvs_ownG_updateP E m (P : iGst Λ Σ → Prop) :
  m ~~>: P → ownG m ={E}=> ∃ m', ■ P m' ∧ ownG m'.
Proof.
  rewrite pvs_eq. intros Hup.
  uPred.unseal; split=> -[|n] r ? /ownG_spec Hinv [|k] Ef σ rf ???; try lia.
  destruct (wsat_update_gst k (E ∪ Ef) σ r rf m P) as (m'&?&?); eauto.
  { apply cmra_includedN_le with (S n); auto. }
  by exists (update_gst m' r); split; [exists m'; split; [|apply ownG_spec]|].
Qed.
Lemma pvs_allocI E P : ¬set_finite E → ▷ P ={E}=> ∃ i, ■ (i ∈ E) ∧ ownI i P.
Proof.
  rewrite pvs_eq. intros ?; rewrite /ownI; uPred.unseal.
  split=> -[|n] r ? HP [|k] Ef σ rf ???; try lia.
  destruct (wsat_alloc k E Ef σ rf P r) as (i&?&?&?); auto.
  { apply uPred_closed with n; eauto. }
  exists (Res {[ i := to_agree (Next (iProp_unfold P)) ]} ∅ ∅).
  split; [|done]. by exists i; split; rewrite /uPred_holds /=.
Qed.

(** * Derived rules *)
Import uPred.
Global Instance pvs_mono' E1 E2 : Proper ((⊢) ==> (⊢)) (@pvs Λ Σ E1 E2).
Proof. intros P Q; apply pvs_mono. Qed.
Global Instance pvs_flip_mono' E1 E2 :
  Proper (flip (⊢) ==> flip (⊢)) (@pvs Λ Σ E1 E2).
Proof. intros P Q; apply pvs_mono. Qed.
Lemma pvs_trans' E P : (|={E}=> |={E}=> P) ={E}=> P.
Proof. apply pvs_trans; set_solver. Qed.
Lemma pvs_strip_pvs E P Q : (P ={E}=> Q) → (|={E}=> P) ={E}=> Q.
Proof. move=>->. by rewrite pvs_trans'. Qed.
Lemma pvs_frame_l E1 E2 P Q : (P ★ |={E1,E2}=> Q) ={E1,E2}=> P ★ Q.
Proof. rewrite !(comm _ P); apply pvs_frame_r. Qed.
Lemma pvs_always_l E1 E2 P Q `{!PersistentP P} :
  P ∧ (|={E1,E2}=> Q) ={E1,E2}=> P ∧ Q.
Proof. by rewrite !always_and_sep_l pvs_frame_l. Qed.
Lemma pvs_always_r E1 E2 P Q `{!PersistentP Q} :
  (|={E1,E2}=> P) ∧ Q ={E1,E2}=> P ∧ Q.
Proof. by rewrite !always_and_sep_r pvs_frame_r. Qed.
Lemma pvs_impl_l E1 E2 P Q : □ (P → Q) ∧ (|={E1,E2}=> P) ={E1,E2}=> Q.
Proof. by rewrite pvs_always_l always_elim impl_elim_l. Qed.
Lemma pvs_impl_r E1 E2 P Q : (|={E1,E2}=> P) ∧ □ (P → Q) ={E1,E2}=> Q.
Proof. by rewrite comm pvs_impl_l. Qed.
Lemma pvs_wand_l E1 E2 P Q : (P -★ Q) ★ (|={E1,E2}=> P) ={E1,E2}=> Q.
Proof. by rewrite pvs_frame_l wand_elim_l. Qed.
Lemma pvs_wand_r E1 E2 P Q : (|={E1,E2}=> P) ★ (P -★ Q) ={E1,E2}=> Q.
Proof. by rewrite pvs_frame_r wand_elim_r. Qed.
Lemma pvs_sep E P Q : (|={E}=> P) ★ (|={E}=> Q) ={E}=> P ★ Q.
Proof. rewrite pvs_frame_r pvs_frame_l pvs_trans //. set_solver. Qed.
Lemma pvs_big_sepM `{Countable K} {A} E (Φ : K → A → iProp Λ Σ) (m : gmap K A) :
  ([★ map] k↦x ∈ m, |={E}=> Φ k x) ={E}=> [★ map] k↦x ∈ m, Φ k x.
Proof.
  rewrite /uPred_big_sepM.
  induction (map_to_list m) as [|[i x] l IH]; csimpl; auto using pvs_intro.
  by rewrite IH pvs_sep.
Qed.
Lemma pvs_big_sepS `{Countable A} E (Φ : A → iProp Λ Σ) X :
  ([★ set] x ∈ X, |={E}=> Φ x) ={E}=> [★ set] x ∈ X, Φ x.
Proof.
  rewrite /uPred_big_sepS.
  induction (elements X) as [|x l IH]; csimpl; csimpl; auto using pvs_intro.
  by rewrite IH pvs_sep.
Qed.

Lemma pvs_mask_frame' E1 E1' E2 E2' P :
  E1' ⊆ E1 → E2' ⊆ E2 → E1 ∖ E1' = E2 ∖ E2' → (|={E1',E2'}=> P) ={E1,E2}=> P.
Proof.
  intros HE1 HE2 HEE.
  rewrite (pvs_mask_frame _ _ (E1 ∖ E1')); last set_solver.
  by rewrite {2}HEE -!union_difference_L.
Qed.
Lemma pvs_openI' E i P : i ∈ E → ownI i P ={E, E ∖ {[i]}}=> ▷ P.
Proof. intros. etrans. apply pvs_openI. apply pvs_mask_frame'; set_solver. Qed.
Lemma pvs_closeI' E i P : i ∈ E → (ownI i P ∧ ▷ P) ={E ∖ {[i]}, E}=> True.
Proof. intros. etrans. apply pvs_closeI. apply pvs_mask_frame'; set_solver. Qed.

Lemma pvs_mask_frame_mono E1 E1' E2 E2' P Q :
  E1' ⊆ E1 → E2' ⊆ E2 → E1 ∖ E1' = E2 ∖ E2' →
  (P ⊢ Q) → (|={E1',E2'}=> P) ={E1,E2}=> Q.
Proof. intros HE1 HE2 HEE ->. by apply pvs_mask_frame'. Qed.

(** It should be possible to give a stronger version of this rule
   that does not force the conclusion view shift to have twice the
   same mask. However, even expressing the side-conditions on the
   mask becomes really ugly then, and we have not found an instance
   where that would be useful. *)
Lemma pvs_trans3 E1 E2 Q :
  E2 ⊆ E1 → (|={E1,E2}=> |={E2}=> |={E2,E1}=> Q) ={E1}=> Q.
Proof. intros HE. rewrite !pvs_trans; set_solver. Qed.

Lemma pvs_mask_weaken E1 E2 P : E1 ⊆ E2 → (|={E1}=> P) ={E2}=> P.
Proof. auto using pvs_mask_frame'. Qed.

Lemma pvs_ownG_update E m m' : m ~~> m' → ownG m ={E}=> ownG m'.
Proof.
  intros; rewrite (pvs_ownG_updateP E _ (m' =)); last by apply cmra_update_updateP.
  by apply pvs_mono, uPred.exist_elim=> m''; apply uPred.pure_elim_l=> ->.
Qed.
End pvs.

(** * Frame Shift Assertions. *)
(* Yes, the name is horrible...
   Frame Shift Assertions take a mask and a predicate over some type (that's
   their "postcondition"). They support weakening the mask, framing resources
   into the postcondition, and composition witn mask-changing view shifts. *)
Notation FSA Λ Σ A := (coPset → (A → iProp Λ Σ) → iProp Λ Σ).
Class FrameShiftAssertion {Λ Σ A} (fsaV : Prop) (fsa : FSA Λ Σ A) := {
  fsa_mask_frame_mono E1 E2 Φ Ψ :
    E1 ⊆ E2 → (∀ a, Φ a ⊢ Ψ a) → fsa E1 Φ ⊢ fsa E2 Ψ;
  fsa_trans3 E Φ : (|={E}=> fsa E (λ a, |={E}=> Φ a)) ⊢ fsa E Φ;
  fsa_open_close E1 E2 Φ :
    fsaV → E2 ⊆ E1 → (|={E1,E2}=> fsa E2 (λ a, |={E2,E1}=> Φ a)) ⊢ fsa E1 Φ;
  fsa_frame_r E P Φ : (fsa E Φ ★ P) ⊢ fsa E (λ a, Φ a ★ P)
}.

(* Used to solve side-conditions related to [fsaV] *)
Create HintDb fsaV.

Section fsa.
Context {Λ Σ A} (fsa : FSA Λ Σ A) `{!FrameShiftAssertion fsaV fsa}.
Implicit Types Φ Ψ : A → iProp Λ Σ.
Import uPred.

Lemma fsa_mono E Φ Ψ : (∀ a, Φ a ⊢ Ψ a) → fsa E Φ ⊢ fsa E Ψ.
Proof. apply fsa_mask_frame_mono; auto. Qed.
Lemma fsa_mask_weaken E1 E2 Φ : E1 ⊆ E2 → fsa E1 Φ ⊢ fsa E2 Φ.
Proof. intros. apply fsa_mask_frame_mono; auto. Qed.
Lemma fsa_frame_l E P Φ : P ★ fsa E Φ ⊢ fsa E (λ a, P ★ Φ a).
Proof. rewrite comm fsa_frame_r. apply fsa_mono=>a. by rewrite comm. Qed.
Lemma fsa_strip_pvs E P Φ : (P ⊢ fsa E Φ) → (|={E}=> P) ⊢ fsa E Φ.
Proof.
  move=>->. rewrite -{2}fsa_trans3.
  apply pvs_mono, fsa_mono=>a; apply pvs_intro.
Qed.
Lemma fsa_pvs_fsa E Φ : (|={E}=> fsa E Φ) ⊣⊢ fsa E Φ.
Proof. apply (anti_symm (⊢)); [by apply fsa_strip_pvs|apply pvs_intro]. Qed.
Lemma pvs_fsa_fsa E Φ : fsa E (λ a, |={E}=> Φ a) ⊣⊢ fsa E Φ.
Proof.
  apply (anti_symm (⊢)); [|apply fsa_mono=> a; apply pvs_intro].
  by rewrite (pvs_intro E (fsa E _)) fsa_trans3.
Qed.
Lemma fsa_mono_pvs E Φ Ψ : (∀ a, Φ a ={E}=> Ψ a) → fsa E Φ ⊢ fsa E Ψ.
Proof. intros. rewrite -[fsa E Ψ]fsa_trans3 -pvs_intro. by apply fsa_mono. Qed.
Lemma fsa_wand_l E Φ Ψ : (∀ a, Φ a -★ Ψ a) ★ fsa E Φ ⊢ fsa E Ψ.
Proof.
  rewrite fsa_frame_l. apply fsa_mono=> a.
  by rewrite (forall_elim a) wand_elim_l.
Qed.
Lemma fsa_wand_r E Φ Ψ : fsa E Φ ★ (∀ a, Φ a -★ Ψ a) ⊢ fsa E Ψ.
Proof. by rewrite (comm _ (fsa _ _)) fsa_wand_l. Qed.
End fsa.

Definition pvs_fsa {Λ Σ} : FSA Λ Σ () := λ E Φ, (|={E}=> Φ ())%I.
Arguments pvs_fsa _ _ _ _/.

Instance pvs_fsa_prf {Λ Σ} : FrameShiftAssertion True (@pvs_fsa Λ Σ).
Proof.
  rewrite /pvs_fsa.
  split; auto using pvs_mask_frame_mono, pvs_trans3, pvs_frame_r.
Qed.
