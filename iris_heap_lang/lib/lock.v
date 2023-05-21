From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import primitive_laws notation.
From iris.prelude Require Import options.

(** A general interface for a lock.
All parameters are implicit, since it is expected that there is only one
[heapGS_gen] in scope that could possibly apply. *)
Class lock `{!heapGS_gen hlc Σ} := Lock {
  (** * Operations *)
  newlock : val;
  acquire : val;
  release : val;
  (** * Predicates *)
  (** [name] is used to associate locked with [is_lock] *)
  name : Type;
  (** No namespace [N] parameter because we only expose program specs, which
  anyway have the full mask. *)
  is_lock (γ: name) (lock: val) (R: iProp Σ) : iProp Σ;
  locked (γ: name) : iProp Σ;
  (** * General properties of the predicates *)
  is_lock_ne γ lk :> Contractive (is_lock γ lk);
  is_lock_persistent γ lk R :> Persistent (is_lock γ lk R);
  is_lock_iff γ lk R1 R2 :
    is_lock γ lk R1 -∗ ▷ □ (R1 ↔ R2) -∗ is_lock γ lk R2;
  locked_timeless γ :> Timeless (locked γ);
  locked_exclusive γ : locked γ -∗ locked γ -∗ False;
  (** * Program specs *)
  newlock_spec (R : iProp Σ) :
    {{{ R }}} newlock #() {{{ lk γ, RET lk; is_lock γ lk R }}};
  acquire_spec γ lk R :
    {{{ is_lock γ lk R }}} acquire lk {{{ RET #(); locked γ ∗ R }}};
  release_spec γ lk R :
    {{{ is_lock γ lk R ∗ locked γ ∗ R }}} release lk {{{ RET #(); True }}}
}.
Global Hint Mode lock + + + : typeclass_instances.

Global Instance is_lock_proper hlc Σ `{!heapGS_gen hlc Σ} (L : lock) γ lk :
  Proper ((≡) ==> (≡)) (L.(is_lock) γ lk) := ne_proper _.
