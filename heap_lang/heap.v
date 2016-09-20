From iris.heap_lang Require Export lifting.
From iris.algebra Require Import auth gmap frac dec_agree.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership.
From iris.proofmode Require Import tactics.
Import uPred.
(* TODO: The entire construction could be generalized to arbitrary languages that have
   a finmap as their state. Or maybe even beyond "as their state", i.e. arbitrary
   predicates over finmaps instead of just ownP. *)

Definition heapN : namespace := nroot .@ "heap".
Definition heapUR : ucmraT := gmapUR loc (prodR fracR (dec_agreeR val)).

(** The CMRA we need. *)
Class heapG Σ := HeapG {
  heapG_iris_inG :> irisG heap_lang Σ;
  heap_inG :> inG Σ (authR heapUR);
  heap_name : gname
}.
(** The Functor we need. *)
Definition to_heap : state → heapUR := fmap (λ v, (1%Qp, DecAgree v)).

Section definitions.
  Context `{heapG Σ}.

  Definition heap_mapsto_def (l : loc) (q : Qp) (v: val) : iProp Σ :=
    own heap_name (◯ {[ l := (q, DecAgree v) ]}).
  Definition heap_mapsto_aux : { x | x = @heap_mapsto_def }. by eexists. Qed.
  Definition heap_mapsto := proj1_sig heap_mapsto_aux.
  Definition heap_mapsto_eq : @heap_mapsto = @heap_mapsto_def :=
    proj2_sig heap_mapsto_aux.

  Definition heap_inv : iProp Σ := (∃ σ, ownP σ ★ own heap_name (● to_heap σ))%I.
  Definition heap_ctx : iProp Σ := inv heapN heap_inv.
End definitions.

Typeclasses Opaque heap_ctx heap_mapsto.
Instance: Params (@heap_inv) 2.

Notation "l ↦{ q } v" := (heap_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : uPred_scope.
Notation "l ↦ v" := (heap_mapsto l 1 v) (at level 20) : uPred_scope.

Section heap.
  Context {Σ : gFunctors}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types h g : heapUR.

  (** Conversion to heaps and back *)
  Lemma to_heap_valid σ : ✓ to_heap σ.
  Proof. intros l. rewrite lookup_fmap. by case (σ !! l). Qed.
  Lemma lookup_to_heap_None σ l : σ !! l = None → to_heap σ !! l = None.
  Proof. by rewrite /to_heap lookup_fmap=> ->. Qed.
  Lemma heap_singleton_included σ l q v :
    {[l := (q, DecAgree v)]} ≼ to_heap σ → σ !! l = Some v.
  Proof.
    rewrite singleton_included=> -[[q' av] [/leibniz_equiv_iff Hl Hqv]].
    move: Hl. rewrite /to_heap lookup_fmap fmap_Some=> -[v' [Hl [??]]]; subst.
    by move: Hqv=> /Some_pair_included_total_2 [_ /DecAgree_included ->].
  Qed.
  Lemma heap_singleton_included' σ l q v :
    {[l := (q, DecAgree v)]} ≼ to_heap σ → to_heap σ !! l = Some (1%Qp,DecAgree v).
  Proof.
    intros Hl%heap_singleton_included. by rewrite /to_heap lookup_fmap Hl.
  Qed.
  Lemma to_heap_insert l v σ :
    to_heap (<[l:=v]> σ) = <[l:=(1%Qp, DecAgree v)]> (to_heap σ).
  Proof. by rewrite /to_heap fmap_insert. Qed.

  Context `{heapG Σ}.

  (** General properties of mapsto *)
  Global Instance heap_ctx_persistent : PersistentP heap_ctx.
  Proof. rewrite /heap_ctx. apply _. Qed.
  Global Instance heap_mapsto_timeless l q v : TimelessP (l ↦{q} v).
  Proof. rewrite heap_mapsto_eq /heap_mapsto_def. apply _. Qed.

  Lemma heap_mapsto_op_eq l q1 q2 v : l ↦{q1} v ★ l ↦{q2} v ⊣⊢ l ↦{q1+q2} v.
  Proof.
    by rewrite heap_mapsto_eq
      -own_op -auth_frag_op op_singleton pair_op dec_agree_idemp.
  Qed.

  Lemma heap_mapsto_op l q1 q2 v1 v2 :
    l ↦{q1} v1 ★ l ↦{q2} v2 ⊣⊢ v1 = v2 ∧ l ↦{q1+q2} v1.
  Proof.
    destruct (decide (v1 = v2)) as [->|].
    { by rewrite heap_mapsto_op_eq pure_equiv // left_id. }
    apply (anti_symm (⊢)); last by apply pure_elim_l.
    rewrite heap_mapsto_eq -own_op -auth_frag_op own_valid discrete_valid.
    eapply pure_elim; [done|]=> /auth_own_valid /=.
    rewrite op_singleton pair_op dec_agree_ne // singleton_valid. by intros [].
  Qed.

  Lemma heap_mapsto_op_1 l q1 q2 v1 v2 :
    l ↦{q1} v1 ★ l ↦{q2} v2 ⊢ v1 = v2 ∧ l ↦{q1+q2} v1.
  Proof. by rewrite heap_mapsto_op. Qed.

  Lemma heap_mapsto_op_half l q v1 v2 :
    l ↦{q/2} v1 ★ l ↦{q/2} v2 ⊣⊢ v1 = v2 ∧ l ↦{q} v1.
  Proof. by rewrite heap_mapsto_op Qp_div_2. Qed.

  Lemma heap_mapsto_op_half_1 l q v1 v2 :
    l ↦{q/2} v1 ★ l ↦{q/2} v2 ⊢ v1 = v2 ∧ l ↦{q} v1.
  Proof. by rewrite heap_mapsto_op_half. Qed.

  (** Weakest precondition *)
  Lemma wp_alloc E e v Φ :
    to_val e = Some v → nclose heapN ⊆ E →
    heap_ctx ★ ▷ (∀ l, l ↦ v ={E}=★ Φ (LitV (LitLoc l))) ⊢ WP Alloc e @ E {{ Φ }}.
  Proof.
    iIntros (<-%of_to_val ?) "[#Hinv HΦ]". rewrite /heap_ctx.
    iInv heapN as (σ) ">[Hσ Hh] " "Hclose".
    iApply wp_alloc_pst. iFrame "Hσ". iNext. iIntros (l) "[% Hσ] !==>".
    iVs (own_update with "Hh") as "[Hh H]".
    { apply auth_update_alloc,
        (alloc_singleton_local_update _ l (1%Qp,DecAgree v));
        by auto using lookup_to_heap_None. }
    iVs ("Hclose" with "[Hσ Hh]") as "_".
    { iNext. iExists (<[l:=v]> σ). rewrite to_heap_insert. by iFrame. }
    iApply "HΦ". by rewrite heap_mapsto_eq /heap_mapsto_def.
  Qed.

  Lemma wp_load E l q v Φ :
    nclose heapN ⊆ E →
    heap_ctx ★ ▷ l ↦{q} v ★ ▷ (l ↦{q} v ={E}=★ Φ v)
    ⊢ WP Load (Lit (LitLoc l)) @ E {{ Φ }}.
  Proof.
    iIntros (?) "[#Hinv [>Hl HΦ]]".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iInv heapN as (σ) ">[Hσ Hh] " "Hclose".
    iDestruct (own_valid_2 with "[$Hh $Hl]") as %[??]%auth_valid_discrete_2.
    iApply (wp_load_pst _ σ); first eauto using heap_singleton_included.
    iIntros "{$Hσ} !> Hσ !==>". iVs ("Hclose" with "[Hσ Hh]") as "_".
    { iNext. iExists σ. by iFrame. }
    by iApply "HΦ".
  Qed.

  Lemma wp_store E l v' e v Φ :
    to_val e = Some v → nclose heapN ⊆ E →
    heap_ctx ★ ▷ l ↦ v' ★ ▷ (l ↦ v ={E}=★ Φ (LitV LitUnit))
    ⊢ WP Store (Lit (LitLoc l)) e @ E {{ Φ }}.
  Proof.
    iIntros (<-%of_to_val ?) "[#Hinv [>Hl HΦ]]".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iInv heapN as (σ) ">[Hσ Hh] " "Hclose".
    iDestruct (own_valid_2 with "[$Hh $Hl]") as %[??]%auth_valid_discrete_2.
    iApply (wp_store_pst _ σ); first eauto using heap_singleton_included.
    iIntros "{$Hσ} !> Hσ !==>".
    iVs (own_update_2 with "[$Hh $Hl]") as "[Hh Hl]".
    { eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (1%Qp, DecAgree v)); last done.
      by eapply heap_singleton_included'. }
    iVs ("Hclose" with "[Hσ Hh]") as "_".
    { iNext. iExists (<[l:=v]>σ). rewrite to_heap_insert. iFrame. }
    by iApply "HΦ".
  Qed.

  Lemma wp_cas_fail E l q v' e1 v1 e2 v2 Φ :
    to_val e1 = Some v1 → to_val e2 = Some v2 → v' ≠ v1 → nclose heapN ⊆ E →
    heap_ctx ★ ▷ l ↦{q} v' ★ ▷ (l ↦{q} v' ={E}=★ Φ (LitV (LitBool false)))
    ⊢ WP CAS (Lit (LitLoc l)) e1 e2 @ E {{ Φ }}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val ??) "[#Hinv [>Hl HΦ]]".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iInv heapN as (σ) ">[Hσ Hh] " "Hclose".
    iDestruct (own_valid_2 with "[$Hh $Hl]") as %[??]%auth_valid_discrete_2.
    iApply (wp_cas_fail_pst _ σ); [eauto using heap_singleton_included|done|].
    iIntros "{$Hσ} !> Hσ !==>". iVs ("Hclose" with "[Hσ Hh]") as "_".
    { iNext. iExists σ. by iFrame. }
    by iApply "HΦ".
  Qed.

  Lemma wp_cas_suc E l e1 v1 e2 v2 Φ :
    to_val e1 = Some v1 → to_val e2 = Some v2 → nclose heapN ⊆ E →
    heap_ctx ★ ▷ l ↦ v1 ★ ▷ (l ↦ v2 ={E}=★ Φ (LitV (LitBool true)))
    ⊢ WP CAS (Lit (LitLoc l)) e1 e2 @ E {{ Φ }}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val ?) "[#Hinv [>Hl HΦ]]".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iInv heapN as (σ) ">[Hσ Hh] " "Hclose".
    iDestruct (own_valid_2 with "[$Hh $Hl]") as %[??]%auth_valid_discrete_2.
    iApply (wp_cas_suc_pst _ σ); first eauto using heap_singleton_included.
    iIntros "{$Hσ} !> Hσ !==>".
    iVs (own_update_2 with "[$Hh $Hl]") as "[Hh Hl]".
    { eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (1%Qp, DecAgree v2)); last done.
      by eapply heap_singleton_included'. }
    iVs ("Hclose" with "[Hσ Hh]") as "_".
    { iNext. iExists (<[l:=v2]>σ). rewrite to_heap_insert. iFrame. }
    by iApply "HΦ".
  Qed.
End heap.
