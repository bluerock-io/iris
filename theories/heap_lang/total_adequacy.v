From iris.program_logic Require Export total_adequacy.
From iris.heap_lang Require Export adequacy.
From iris.heap_lang Require Import proofmode notation.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Definition heap_total Σ `{heapPreG Σ} s e σ φ :
  (∀ `{heapG Σ}, WP e @ s; ⊤ [{ v, ⌜φ v⌝ }]%I) →
  sn erased_step ([e], σ).
Proof.
  intros Hwp; eapply (twp_total _ _); iIntros (?) "".
  iMod (gen_heap_init σ.(heap)) as (?) "Hh".
  iMod (proph_map_init [] σ.(used_proph)) as (?) "Hp".
  iModIntro.
  iExists (fun σ κs => (gen_heap_ctx σ.(heap) ∗ proph_map_ctx κs σ.(used_proph))%I). iFrame.
  iApply (Hwp (HeapG _ _ _ _)).
Qed.
