From iris.base_logic.lib Require Export invariants.
From iris.bi.lib Require Export fractional.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

(** A general interface for a reader-writer lock.

All parameters are implicit, since it is expected that there is only one
[heapGS_gen] in scope that could possibly apply.

Only one instance of this class should ever be in scope. To write a library that
is generic over the lock, just add a [`{rwlock}] implicit parameter. To use a
particular lock instance, use [Local Existing Instance <rwlock instance>].

When writing an instance of this class, please take care not to shadow the class
projections (e.g., either use [Local Definition newlock] or avoid the name
 [newlock] altogether), and do not register an instance -- just make it a
[Definition] that others can register later. *)
Class rwlock `{!heapGS_gen hlc Σ} := RwLock {
  (** * Operations *)
  newlock : val;
  acquire_reader : val;
  release_reader : val;
  acquire_writer : val;
  release_writer : val;
  (** * Predicates *)
  (** [lock_name] is used to associate [reader_locked] and [writer_locked] with
  [is_rw_lock] *)
  lock_name : Type;
  (** No namespace [N] parameter because we only expose program specs, which
  anyway have the full mask. *)
  is_rw_lock (γ : lock_name) (lock : val) (Φ : Qp → iProp Σ) : iProp Σ;
  reader_locked (γ : lock_name) (q : Qp) : iProp Σ;
  writer_locked (γ : lock_name) : iProp Σ;
  (** * General properties of the predicates *)
  is_rw_lock_persistent γ lk Φ :> Persistent (is_rw_lock γ lk Φ);
  is_rw_lock_iff γ lk Φ Ψ :
    is_rw_lock γ lk Φ -∗ ▷ □ (∀ q, Φ q ∗-∗ Ψ q) -∗ is_rw_lock γ lk Ψ;
  reader_locked_timeless γ q :> Timeless (reader_locked γ q);
  writer_locked_timeless γ :> Timeless (writer_locked γ);
  writer_locked_exclusive γ : writer_locked γ -∗ writer_locked γ -∗ False;
  writer_locked_not_reader_locked γ q : writer_locked γ -∗ reader_locked γ q -∗ False;
  (** * Program specs *)
  newlock_spec (Φ : Qp → iProp Σ) `{!AsFractional P Φ 1} :
    {{{ P }}}
      newlock #()
    {{{ lk γ, RET lk; is_rw_lock γ lk Φ }}};
  acquire_reader_spec γ lk Φ :
    {{{ is_rw_lock γ lk Φ }}}
      acquire_reader lk
    {{{ q, RET #(); reader_locked γ q ∗ Φ q }}};
  release_reader_spec γ lk Φ q :
    {{{ is_rw_lock γ lk Φ ∗ reader_locked γ q ∗ Φ q }}}
      release_reader lk
    {{{ RET #(); True }}};
  acquire_writer_spec γ lk Φ :
    {{{ is_rw_lock γ lk Φ }}}
      acquire_writer lk
    {{{ RET #(); writer_locked γ ∗ Φ 1%Qp }}};
  release_writer_spec γ lk Φ :
    {{{ is_rw_lock γ lk Φ ∗ writer_locked γ ∗ Φ 1%Qp }}}
      release_writer lk
    {{{ RET #(); True }}};
}.
Global Hint Mode rwlock + + + : typeclass_instances.

Global Instance is_rw_lock_contractive `{!heapGS_gen hlc Σ, !rwlock} γ lk :
  ∀ n, Proper (pointwise_relation _ (dist_later n) ==> dist n) (is_rw_lock γ lk).
Proof.
  intros n Φ1 Φ2 HΦ.
  set (Φ1' := λne (q : leibnizO Qp), Φ1 q).
  set (Φ2' := λne (q : leibnizO Qp), Φ2 q).
  assert (Next Φ1' ≡{n}≡ Next Φ2') as HΦ'.
  { constructor => m ? q /=. specialize (HΦ q). by eapply dist_later_dist_lt. }
  clear HΦ. revert n HΦ'. eapply (uPred.internal_eq_entails (M:=iResUR Σ)).
  rewrite later_equivI. iIntros "#HΦ". iApply prop_ext. iModIntro.
  iSplit; iIntros "H"; iApply (is_rw_lock_iff with "H"); iIntros "!> !> %q".
  all: rewrite ofe_morO_equivI; iSpecialize ("HΦ" $! q).
  all: change (Φ1 q) with (Φ1' q); change (Φ2 q) with (Φ2' q).
  all: iRewrite "HΦ"; auto.
Qed.

Global Instance is_rw_lock_proper `{!heapGS_gen hlc Σ, !rwlock} γ lk :
  Proper (pointwise_relation _ (≡) ==> (≡)) (is_rw_lock γ lk).
Proof.
  intros Φ1 Φ2 HΦ.
  apply equiv_dist=>n. apply is_rw_lock_contractive=>q.
  constructor=>m _. move: (HΦ q) => /equiv_dist. auto.
Qed.
