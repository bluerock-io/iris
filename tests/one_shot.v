From iris.algebra Require Import dec_agree csum.
From iris.program_logic Require Import hoare.
From iris.heap_lang Require Import assert proofmode notation.
From iris.proofmode Require Import invariants ghost_ownership.
Import uPred.

Definition one_shot_example : val := λ: <>,
  let: "x" := ref NONE in (
  (* tryset *) (λ: "n",
    CAS "x" NONE (SOME "n")),
  (* check  *) (λ: <>,
    let: "y" := !"x" in λ: <>,
    match: "y" with
      NONE => #()
    | SOME "n" =>
       match: !"x" with
         NONE => assert: #false
       | SOME "m" => assert: "n" = "m"
       end
    end)).
Global Opaque one_shot_example.

Definition one_shotR := csumR (exclR unitC) (dec_agreeR Z).
Definition Pending : one_shotR := (Cinl (Excl ()) : one_shotR).
Definition Shot (n : Z) : one_shotR := (Cinr (DecAgree n) : one_shotR).

Class one_shotG Σ := one_shot_inG :> inG heap_lang Σ one_shotR.
Definition one_shotGF : gFunctorList := [GFunctor (constRF one_shotR)].
Instance inGF_one_shotG Σ : inGFs heap_lang Σ one_shotGF → one_shotG Σ.
Proof. intros [? _]; apply: inGF_inG. Qed.

Section proof.
Context `{!heapG Σ, !one_shotG Σ} (N : namespace) (HN : heapN ⊥ N).
Local Notation iProp := (iPropG heap_lang Σ).

Definition one_shot_inv (γ : gname) (l : loc) : iProp :=
  (l ↦ NONEV ★ own γ Pending ∨ ∃ n : Z, l ↦ SOMEV #n ★ own γ (Shot n))%I.

Lemma wp_one_shot (Φ : val → iProp) :
  heap_ctx ★ (∀ f1 f2 : val,
    (∀ n : Z, □ WP f1 #n {{ w, w = #true ∨ w = #false }}) ★
    □ WP f2 #() {{ g, □ WP g #() {{ _, True }} }} -★ Φ (f1,f2)%V)
  ⊢ WP one_shot_example #() {{ Φ }}.
Proof.
  iIntros "[#? Hf] /=".
  rewrite /one_shot_example. wp_seq. wp_alloc l as "Hl". wp_let.
  iPvs (own_alloc Pending) as (γ) "Hγ"; first done.
  iPvs (inv_alloc N _ (one_shot_inv γ l) with "[Hl Hγ]") as "#HN"; first done.
  { iNext. iLeft. by iSplitL "Hl". }
  iPvsIntro. iApply "Hf"; iSplit.
  - iIntros (n) "!". wp_let.
    iInv> N as "[[Hl Hγ]|H]"; last iDestruct "H" as (m) "[Hl Hγ]".
    + wp_cas_suc. iSplitL; [|by iLeft].
      iPvs (own_update with "Hγ") as "Hγ".
      { by apply cmra_update_exclusive with (y:=Shot n). }
      iPvsIntro; iRight; iExists n; by iSplitL "Hl".
    + wp_cas_fail. rewrite /one_shot_inv; eauto 10.
  - iIntros "!". wp_seq. wp_focus (! _)%E. iInv> N as "Hγ".
    iAssert (∃ v, l ↦ v ★ ((v = NONEV ★ own γ Pending) ∨
       ∃ n : Z, v = SOMEV #n ★ own γ (Shot n)))%I with "[-]" as "Hv".
    { iDestruct "Hγ" as "[[Hl Hγ]|Hl]"; last iDestruct "Hl" as (m) "[Hl Hγ]".
      + iExists NONEV. iFrame. eauto.
      + iExists (SOMEV #m). iFrame. eauto. }
    iDestruct "Hv" as (v) "[Hl Hv]". wp_load; iPvsIntro.
    iAssert (one_shot_inv γ l ★ (v = NONEV ∨ ∃ n : Z,
      v = SOMEV #n ★ own γ (Shot n)))%I with "[-]" as "[$ #Hv]".
    { iDestruct "Hv" as "[[% ?]|Hv]"; last iDestruct "Hv" as (m) "[% ?]"; subst.
      + iSplit. iLeft; by iSplitL "Hl". eauto.
      + iSplit. iRight; iExists m; by iSplitL "Hl". eauto. }
    wp_let. iPvsIntro. iIntros "!". wp_seq.
    iDestruct "Hv" as "[%|Hv]"; last iDestruct "Hv" as (m) "[% Hγ']"; subst.
    { by wp_match. }
    wp_match. wp_focus (! _)%E.
    iInv> N as "[[Hl Hγ]|Hinv]"; last iDestruct "Hinv" as (m') "[Hl Hγ]".
    { iCombine "Hγ" "Hγ'" as "Hγ". by iDestruct (own_valid with "Hγ") as %?. }
    wp_load; iPvsIntro.
    iCombine "Hγ" "Hγ'" as "Hγ".
    iDestruct (own_valid with "#Hγ") as %[=->]%dec_agree_op_inv.
    iSplitL "Hl"; [iRight; by eauto|].
    wp_match. iApply wp_assert. wp_op=>?; simplify_eq/=; eauto.
Qed.

Lemma hoare_one_shot (Φ : val → iProp) :
  heap_ctx ⊢ {{ True }} one_shot_example #()
    {{ ff,
      (∀ n : Z, {{ True }} Fst ff #n {{ w, w = #true ∨ w = #false }}) ★
      {{ True }} Snd ff #() {{ g, {{ True }} g #() {{ _, True }} }}
    }}.
Proof.
  iIntros "#? ! _". iApply wp_one_shot. iSplit; first done.
  iIntros (f1 f2) "[#Hf1 #Hf2]"; iSplit.
  - iIntros (n) "! _". wp_proj. iApply "Hf1".
  - iIntros "! _". wp_proj.
    iApply wp_wand_l; iFrame "Hf2". by iIntros (v) "#? ! _".
Qed.
End proof.
