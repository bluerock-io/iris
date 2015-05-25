Require Import Ssreflect.ssreflect Ssreflect.ssrfun Omega.
Require Import SPred PreoMet RA CMRA Axioms.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope ra_scope.
Local Open Scope predom_scope.

Section Agreement.
  (* This is more complex than above, and it does not require a decidable equality. However, it needs
     a metric. It also comes with a CMRA. *)
  Context {T} `{T_ty : Setoid T} {mT: metric T}.
  Local Open Scope ra_scope.
  Local Open Scope nat.

  Implicit Types (v: SPred).

  Definition vChain v: Type := forall n, v n -> T.
  Program Definition cvChain {v} (ts: vChain v): Prop :=
    forall n i (HLe: n <= i) (v: v i), ts i _ = n = ts n _.
  Next Obligation.
    eapply dpred; eassumption.
  Qed.
  
  CoInductive ra_agree : Type :=
  ag_inj (v: SPred) (ts: vChain v) (tsx: cvChain ts).

  Global Instance ra_agree_unit : RA_unit ra_agree := fun x => x.
  Global Program Instance cmra_agree_valid : CMRA_valid _ :=
    fun x => match x with
             | ag_inj valid _ _ => valid
             end.
  Global Instance ra_agree_valid : RA_valid _ := compose valid_sp cmra_agree_valid.

  Local Ltac ra_ag_pi := match goal with
                           [H: dist ?n (?ts1 ?pv11) (?ts2 ?pv21) |- dist ?n (?ts1 ?pv12) (?ts2 ?pv22) ] =>
                           (* Also try with less rewrites, as some of the pvs apeparing in the goal may be existentials. *)
                           first [rewrite_pi pv12 pv11; rewrite_pi pv22 pv21; eexact H |
                                  rewrite_pi pv22 pv21; eexact H | rewrite_pi pv12 pv11; eexact H]
                         end.


  Program Definition ra_ag_compinj_valid {v1 v2} (ts1: vChain v1) (ts2: vChain v2) (ts1x: cvChain ts1) (ts2x: cvChain ts2): SPred :=
    mkSPred (fun n => exists (pv1: v1 n) (pv2: v2 n), ts1 _ pv1 = n = ts2 _ pv2) _ _.
  (* This has to be n-bounded equality for the operation to be non-expansive: A full equality at all step-indices here would become a proof obligation that we have to show based on just n-equality of our arguments. *)
  Next Obligation.
    do 2 eexists. exact:dist_bound.
  Grab Existential Variables.
  { exact: bpred. }
  { exact: bpred. }
  Qed.
  Next Obligation.
    intros n m ? (pv1 & pv2 & EQ). do 2 eexists.
    transitivity (ts2 n pv2); last by eapply ts2x.
    transitivity (ts1 n pv1); first by (symmetry; eapply ts1x).
    eapply mono_dist; eassumption.
  Qed.

  Program Definition ra_ag_compinj_ts {v1 v2} (ts1: vChain v1) (ts2: vChain v2) (ts1x: cvChain ts1) (ts2x: cvChain ts2):
    vChain (ra_ag_compinj_valid ts1 ts2 ts1x ts2x) :=
    fun n pv => ts1 n _.

  Lemma ra_ag_compinj_tsx {v1 v2} (ts1: vChain v1) (ts2: vChain v2) (ts1x: cvChain ts1) (ts2x: cvChain ts2):
    cvChain (ra_ag_compinj_ts ts1 ts2 ts1x ts2x).
  Proof.
    move=> n i HLe [pv1 [pv2 EQ]]. unfold ra_ag_compinj_ts.
    transitivity (ts1 i pv1); first by f_equiv. (* RJ: I have no idea why this works... *)
    move/(_ _ _ HLe pv1):(ts1x)=>ts1x'. ra_ag_pi.
  Qed.

  Global Instance ra_ag_op : RA_op _ :=
    fun x y => match x, y with
               | ag_inj v1 ts1 ts1x, ag_inj v2 ts2 ts2x =>
                 ag_inj (ra_ag_compinj_valid ts1 ts2 ts1x ts2x) (ra_ag_compinj_ts ts1 ts2 ts1x ts2x)
                        (ra_ag_compinj_tsx ts1 ts2 ts1x ts2x)

               end.
  Program Definition ra_ag_inj (t: T): ra_agree :=
    ag_inj top_sp (fun _ _ => t) (fun _ _ _ _ => _).
  Next Obligation.
    eapply dist_refl. reflexivity.
  Qed.
  
  Lemma ra_ag_inj_valid t:
    ra_agree_valid (ra_ag_inj t).
  Proof.
    intros n. exact I.
  Qed.

  Definition ra_agree_eq (x y: ra_agree): Prop :=
    match x, y with
    | ag_inj v1 ts1 _, ag_inj v2 ts2 _ => v1 == v2 /\ (forall n pv1 pv2, ts1 n pv1 = n = ts2 n pv2)
    (* The equality on the ts looks way too strong. However,
       thanks to PI, this is actally the same as
       "if both are valid, then pv1 and pv2 agree somewhere". *)
    (* Also, only the n-valid elements have to be only n-equal. Otherwise,
       commutativity breaks: n-valid here means that the arguments were
       n-equal. *)
    end.

  Local Ltac ra_ag_destr := repeat (match goal with [ x : ra_agree |- _ ] => destruct x end).
  (*Local Ltac ra_ag_auto := first [by firstorder | split; [by firstorder|intros n pv1 pv2; pi pv1 pv2; by firstorder ]].*)

  Global Instance ra_agree_eq_equiv : Equivalence ra_agree_eq.
  Proof.
    split; repeat intro; ra_ag_destr; try (exact I || contradiction); [| |]. (* 3 goals left. *)
    - split; first reflexivity. intros. rewrite_pi pv1 pv2. reflexivity.
    - destruct H. split; intros; by symmetry.
    - destruct H, H0.
      split; first (etransitivity; now eauto).
      intro; etransitivity; [now eapply H1 | now eapply H2].
  Grab Existential Variables.
  { rewrite -H. assumption. }
  Qed.
  Global Instance ra_agree_type : Setoid ra_agree := mkType ra_agree_eq.

  Lemma ra_ag_dupl (x y: ra_agree):
    x · x == x.
  Proof.
    ra_ag_destr. split.
    - split; simpl; first by firstorder.
      move=>pv. exists pv pv. now firstorder.
    - move=>n ? ?. unfold ra_ag_compinj_ts. pi.
  Qed.
  
  Global Instance ra_agree_res : RA ra_agree.
  Proof.
    split; repeat intro.
    - ra_ag_destr; [].
      destruct H as (HeqV1 & HeqT1), H0 as (HeqV2 & HeqT2).
      split.
      + split; intros (pv1 & pv2 & Heq).
        * move:(pv1)(pv2)=>pv1' pv2'. rewrite ->HeqV1 in pv1'. rewrite ->HeqV2 in pv2'. exists pv1' pv2'.
          rewrite <-HeqT1, <-HeqT2. eapply Heq; eassumption.
        * move:(pv1)(pv2)=>pv1' pv2'. rewrite <-HeqV1 in pv1'. rewrite <-HeqV2 in pv2'. exists pv1' pv2'.
          rewrite ->HeqT1, ->HeqT2. eapply Heq; eassumption.
      + intros n pv1 pv2. by apply: HeqT1.
    - ra_ag_destr; []. simpl. unfold ra_ag_compinj_ts in *. split.
      + intros n. split.
        * intros [pv1 [[pv2 [pv3 EQ']] EQ]]. hnf. 
          assert (pv4: (ra_ag_compinj_valid ts1 ts0 tsx1 tsx0) n).
          { hnf. exists pv1 pv2. ra_ag_pi. }
          exists pv4 pv3. rewrite <-EQ'. ra_ag_pi.
        * intros [[pv1 [pv2 EQ']] [pv3 EQ]]. hnf. unfold ra_ag_compinj_ts in *.
          assert (pv4: (ra_ag_compinj_valid ts0 ts tsx0 tsx) n).
          { hnf. exists pv2 pv3. rewrite <-EQ'. ra_ag_pi. }
          exists pv1 pv4. ra_ag_pi.
      + intros n pv1 pv2. f_equiv. by eapply ProofIrrelevance.
    - ra_ag_destr. unfold ra_op, ra_ag_op. unfold ra_ag_compinj_ts in *. split.
      + split; intros (pv1 & pv2 & Heq); do 2 eexists; symmetry; eassumption.
      + intros n [pv1 [pv2 EQ]] [pv3 [pv4 EQ']]. unfold ra_ag_compinj_ts in *. ra_ag_pi.
    - eapply ra_ag_dupl. assumption.
    - ra_ag_destr; unfold ra_valid, ra_agree_valid in *; firstorder.
    - exists t'. reflexivity.
    - ra_ag_destr; unfold ra_valid, ra_agree_valid in *. split; first reflexivity.
      move=>n ? ?. apply equivR. f_equiv. by eapply ProofIrrelevance.
    - ra_ag_destr; unfold ra_valid, ra_agree_valid in *; firstorder.
    - ra_ag_destr; [].
      destruct (H n) as [Hn _]. assumption.
  Qed.

  Lemma ra_ag_pord (x y: ra_agree):
    x ⊑ y <-> x · y == y.
  Proof.
    split.
    - move=>[z EQ]. ra_ag_destr; destruct EQ as [EQv EQts]; split.
      +  unfold ra_ag_compinj_ts in *; split.
        * intros (pv1 & pv2 & EQt). assumption.
        * intros pv0. hnf. move:(pv0). rewrite -{1}EQv. move=>[pv1 [pv2 EQ']].
          exists pv2 pv0. erewrite <-EQts. symmetry. ra_ag_pi.
      + unfold ra_ag_compinj_ts in *; move=>n [pv1 [pv2 EQ]] pv3. ra_ag_pi.
    - intros EQ. exists y. rewrite comm. assumption.
  Grab Existential Variables.
  { do 2 eexists. eassumption. }
  Qed.

  (* We also have a metric *)
  Definition ra_agree_dist n :=
    match n with
    | O => fun _ _ => True
    | S _ => fun x y => match x, y with
                        | ag_inj v1 ts1 _, ag_inj v2 ts2 _ =>
                          v1 = n = v2 /\ (forall n' pv1 pv2, n' <= n -> ts1 n' pv1 = n' = ts2 n' pv2)
                        end
    end.

  Global Program Instance ra_agree_metric : metric ra_agree := mkMetr ra_agree_dist.
  Next Obligation.
    repeat intro. destruct n as [|n]; first by auto.
    ra_ag_destr. destruct H as [EQv1 EQts1], H0 as [EQv2 EQts2]. split; move=>[EQv EQts]; split.
    - rewrite -EQv1 -EQv2. assumption.
    - move=> n' pv1 pv2 HLe. etransitivity; first (symmetry; by eapply EQts1).
      etransitivity; last (by eapply EQts2). by eapply EQts.
    - rewrite EQv1 EQv2. assumption.
    - move=> n' pv1 pv2 HLe. etransitivity; first (by eapply EQts1).
      etransitivity; last (symmetry; by eapply EQts2). now eauto.
  Grab Existential Variables.
  { by rewrite -EQv2. }
  { by rewrite -EQv1. }
  { by rewrite EQv2. }
  { by rewrite EQv1. }
  Qed.
  Next Obligation.
    split.
    - intros Hall. ra_ag_destr.
      split.
      + eapply dist_refl. move=> [|n]; first by apply: dist_bound. destruct (Hall (S n)) as [EQ _].
        assumption.
      + intros n pv1 pv2. specialize (Hall (S n)). destruct n as [|n]; first by apply: dist_bound.
        now firstorder.
    - repeat intro. destruct n as [|n]; first by auto. ra_ag_destr; now firstorder.
  Qed.
  Next Obligation.
    repeat intro. destruct n as [|n]; first by auto.
    ra_ag_destr; try firstorder; [].
    - symmetry. now eauto.
  Qed.
  Next Obligation.
    repeat intro. destruct n as [|n]; first by auto.
    ra_ag_destr.
    destruct H as [EQv1 EQts1], H0 as [EQv2 EQts2].
    split; first now firstorder. intros.
    etransitivity; first by eapply EQts1. by eapply EQts2.
  Grab Existential Variables.
  { apply EQv1; first omega. assumption. }
  Qed.
  Next Obligation.
    repeat intro. destruct n as [|n]; first by auto.
    ra_ag_destr. destruct H as [EQv EQts]. split.
    - move=>n' HLe. eapply EQv. omega.
    - move=>n'' pv1 pv2 HLe. eapply EQts. omega.
  Qed.

  Global Instance ra_ag_op_dist n:
    Proper (dist n ==> dist n ==> dist n) ra_ag_op.
  Proof.
    move=>a1 aa2 EQa b1 b2 EQb. destruct n as [|n]; first by apply: dist_bound.
    ra_ag_destr; try firstorder; []. destruct EQa as [EQv1 EQts1], EQb as [EQv2 EQts2]. split.
    - move=>n' HLe. split; move=>[pv1 [pv2 EQ]]; do 2 eexists.
      + etransitivity; first by (symmetry; eapply EQts1; omega).
        etransitivity; last by (eapply EQts2; omega). eassumption.
      + etransitivity; first by (eapply EQts1; omega).
        etransitivity; last by (symmetry; eapply EQts2; omega). eassumption.
    - unfold ra_ag_compinj_ts in *. move=>n' [pv1 [pv2 EQ]] [pv3 [pv4 EQ']] HLe.
      eapply EQts1. omega.
  Grab Existential Variables.
  { apply EQv2; assumption. }
  { apply EQv1; assumption. }
  { apply EQv2; assumption. }
  { apply EQv1; assumption. }
  Qed.

  Global Instance ra_ag_inj_dist n:
    Proper (dist n ==> dist n) ra_ag_inj.
  Proof.
    move=>t1 t2 EQt. destruct n as [|n]; first by apply: dist_bound.
    simpl. rewrite -/dist. split.
    - move=>? _. reflexivity.
    - move=>m _ _ Hle. eapply mono_dist, EQt. omega.
  Qed.

  Lemma ra_ag_prod_dist x y n:
    cmra_valid (x · y) n ->
    x · y = n = x.
  Proof.
    move=>Hval.  destruct n as [|n]; first exact: dist_bound.
    unfold cmra_valid in Hval. ra_ag_destr. simpl in Hval.
    destruct Hval as [pv1 [pv2 Heq]].
    split.
    - move=>m Hle /=. split.
      + move=>_. eapply dpred, pv1. omega.
      + move=>_.
        assert (pv0: v0 m) by (eapply dpred, pv1; omega).
        assert (pv: v m) by (eapply dpred, pv2; omega).
        exists pv0 pv. assert (m <= S n) by omega.
        etransitivity; last (etransitivity; first (eapply mono_dist, Heq; omega)).
        * symmetry. etransitivity; first now eapply tsx0. pi.
        * etransitivity; first now eapply tsx. pi.
    - move=>m pvcomp pv3 Hle. unfold ra_ag_compinj_ts. pi.
  Qed.

  Program Definition ra_ag_vchain (σ: chain ra_agree) {σc: cchain σ} : chain SPred :=
    fun i => match σ (S i) with
             | ag_inj v' _ _ => v'
             end.

  Instance ra_ag_vchain_c (σ: chain ra_agree) {σc: cchain σ} : cchain (ra_ag_vchain σ).
  Proof.
    intros n j m HLe1 HLe2. destruct n as [|n]; first by apply: dist_bound. unfold ra_ag_vchain.
    ddes (σ (S j)) at 1 3 as [v1 ts1 tsx1] deqn:EQ1.
    ddes (σ (S m)) at 1 3 as [v2 ts2 tsx2] deqn:EQ2.
    cchain_eleq σ at (S j) (S m) lvl:(S n); move=>[EQv _].
    assumption.
  Qed.

  Lemma ra_ag_vchain_compl_n (σ: chain ra_agree) {σc: cchain σ} n:
    compl (ra_ag_vchain σ) n ->
    forall m k, m <= n -> k >= n -> ra_ag_vchain σ k m.
  Proof.
    move=>pv m k HLe HLe'.
    assert (HTv := conv_cauchy (ra_ag_vchain σ) (S n) _ (le_refl _)).
    apply HTv in pv; last by omega.
    clear HTv. move:pv. unfold ra_ag_vchain.
    ddes (σ (S (S n))) at 1 3 as [v1 ts1 tsx1] deqn:EQ1.
    ddes (σ (S k)) at 1 3 as [v2 ts2 tsx2] deqn:EQ2=>pv.
    cchain_eleq σ at (S (S n)) (S k) lvl:(S m); move=>[EQv _].
    apply EQv; first omega. eapply dpred; eassumption.
  Qed.

  Lemma ra_ag_vchain_ucompl_n (σ: chain ra_agree) {σc: cchain σ} n:
    ra_ag_vchain σ (S n) n ->
    compl (ra_ag_vchain σ) n.
  Proof.
    move=>pv.
    assert (HTv := conv_cauchy (ra_ag_vchain σ) (S n) _ (le_refl _)).
    apply HTv in pv; last by omega. assumption.
  Qed.

  Lemma ra_ag_vchain_n (σ: chain ra_agree) {σc: cchain σ} n m:
    ra_ag_vchain σ n m -> forall v' ts' tsx', σ (S n) = ag_inj v' ts' tsx' -> v' m.
  Proof.
    move=>pv v' ts' tsx' EQ. move:pv EQ.
    unfold ra_ag_vchain.
    ddes (σ (S n)) at 1 3 as [vSn tsSn tsxSSn] deqn:EQSSn.
    move=>pv EQ. rewrite EQ in EQSSn. injection EQSSn=>{EQSSn EQ}EQ. destruct EQ.
    move=><-. assumption.
  Qed.

  Program Definition ra_ag_tsdiag_n (σ : chain ra_agree) {σc : cchain σ} n {pv: compl (ra_ag_vchain σ) n}: T :=
    match σ (S n) with
    | ag_inj v' ts' tsx' => ts' n _
    end.
  Next Obligation.
    unfold ra_ag_vchain in pv. move: pv.
    ddes (σ (S n)) at 1 3 as [vSSn tsSSn tsxSSn] deqn:EQ; move=>pv.
    injection Heq_anonymous=>_ ->. assumption.
  Qed.

  Program Definition ra_ag_compl (σ : chain ra_agree) {σc : cchain σ} :=
    ag_inj (compl (ra_ag_vchain σ))
           (fun n pv => ra_ag_tsdiag_n σ n (pv:=pv)) _.
  Next Obligation.
    move=>n i HLe pv. simpl. rewrite -/dist.    
    assert (pvc: compl (ra_ag_vchain σ) i) by assumption.
    destruct n as [|n]; first by apply: dist_bound.
    unfold ra_ag_tsdiag_n.
    ddes (σ (S i)) at 1 3 as [vSi tsSi tsxSi] deqn:EQSi.
    ddes (σ (S (S n))) at 1 3 as [vSSn tsSSn tsxSSn] deqn:EQSSn.
    cchain_eleq σ at (S i) (S (S n)) lvl:(S (S n)); move=>[EQv EQts].
    assert (pv': vSi i).
    { move:pvc. move/ra_ag_vchain_compl_n. case/(_ i i _ _)/Wrap; [omega|].
      move/ra_ag_vchain_n=>H. eapply H. symmetry. eassumption. }
    etransitivity; last first.
    { eapply EQts. omega. }
    move:(tsxSi (S n) i). move/(_ _ pv')=>EQ.
    etransitivity; last eassumption. pi.
  Qed.

  Global Program Instance ra_ag_cmt : cmetric ra_agree := mkCMetr ra_ag_compl.
  Next Obligation.
    intros [| n]; [now intros; apply dist_bound | unfold ra_ag_compl].
    intros i HLe. destruct (σ i) as [vi] eqn: EQi; split.
    - assert (HT:=conv_cauchy (ra_ag_vchain σ)).
      rewrite (HT (S n)). unfold ra_ag_vchain.
      ddes (σ (S i)) at 1 3 as [vSi tsSi tsxSi] deqn:EQSi.
      cchain_eleq σ at (S i) i lvl: (S n); move=>[EQv _]. assumption.
    - move=>j pv1 pv2 HLej.
      destruct j as [|j]; first by apply: dist_bound.
      unfold ra_ag_tsdiag_n.
      ddes (σ (S (S j))) at 1 3 as [vSSj tsSSj tsxSSj] deqn:EQSSj.
      cchain_eleq σ at (S (S j)) i lvl: (S j); move=>[EQv EQts].
      eapply EQts. omega.
  Qed.

  (* And we have a pcmType, too! *)
  Global Instance ra_ag_pcm: pcmType ra_agree.
  Proof.
    split. repeat intro. eapply ra_ag_pord. unfold compl, ra_ag_cmt, ra_ag_compl.
    assert (HT: forall n pv1 pv2, ra_ag_tsdiag_n σ (pv:=pv1) n = n = ra_ag_tsdiag_n ρ (pv:=pv2) n).
    { move=>n pv1 pv2. destruct n as [|n]; first by apply: dist_bound.
      unfold ra_ag_tsdiag_n.
      ddes (σ (S (S n))) at 1 3 as [vσn tsσn tsxσn] deqn:EQσn.
      ddes (ρ (S (S n))) at 1 3 as [vρn tsρn tsxρn] deqn:EQρn.
      specialize (H (S (S n))). rewrite ->ra_ag_pord in H.
      rewrite <-EQσn, <-EQρn in H. destruct H as [EQv EQts].
      erewrite <-EQts. unfold ra_ag_compinj_ts. pi.
    }
    split.
    - move=>n. split; first by (intros (pv1 & pv2 & _); tauto).
      simpl. move=>pv. move:(pv). rewrite {1}/ra_ag_vchain. simpl.
      ddes (ρ (S n)) at 1 3 as [vρn tsρn tsxρn] deqn:EQρn.
      move=>pvρ.
      assert (pvσ: (ra_ag_vchain σ n) n).
      { unfold ra_ag_vchain.
        ddes (σ (S n)) at 1 3 as [vσn tsσn tsxσn] deqn:EQσn.
        specialize (H (S n)). rewrite ->ra_ag_pord, <-EQρn, <-EQσn in H.
        destruct H as [EQv _]. rewrite <-EQv in pvρ. destruct pvρ as [pv1 _]. assumption. }
      do 2 eexists. etransitivity; last (etransitivity; first by eapply HT).
      + eapply dist_refl. reflexivity.
      + eapply dist_refl. reflexivity.
    - intros n (pv1 & pv2 & EQ) pv3.
      now eapply HT.
  Grab Existential Variables.
  { eapply ra_ag_vchain_ucompl_n. eapply spredNE, pvσ.
    eapply (chain_cauchy (ra_ag_vchain σ)); first apply _; omega. }
  { assumption. }
  { apply EQv. eapply ra_ag_vchain_n.
    - eapply ra_ag_vchain_compl_n with (m:=S n) (k:=S n); first (by eexact pv2); omega.
    - symmetry. eassumption. }
  Qed.

  (* And finally, be ready for the CMRA *)
  Global Instance ra_ag_cmra : CMRA ra_agree.
  Proof.
    split.
    - now apply _.
    - by move=>[|n] t1 t2 EQt. 
    - move=>n t1 t2 EQt. destruct n as [|n]; first exact: dist_bound.
      ra_ag_destr; now firstorder.
    - move=>t. reflexivity.
    - move=> t1 t2. ra_ag_destr.
      move=>n [pv _]. exact pv.
  Qed.

  (* Provide a way to get an n-approximation of the element out of an n-valid agreement. *)
  Program Definition ra_ag_unInj x n {HVal: cmra_valid x n}: T :=
    match x with
    | ag_inj v ts _ => (ts n _)
    end.

  Lemma ra_ag_unInj_dist x y n {HVal1: cmra_valid x n} {HVal2: cmra_valid y n}: (* The function is dependent, hence no "Proper" can be registered *)
    x = n = y -> ra_ag_unInj x n (HVal:=HVal1) = n = ra_ag_unInj y n (HVal:=HVal2).
  Proof.
    move=>EQ. destruct n as [|n]; first exact: dist_bound.
    ra_ag_destr; now firstorder.
  Qed.

  Lemma ra_ag_unInj_move x n1 n2 (Hle: n1 <= n2) {HVal1: cmra_valid x n1} {HVal2: cmra_valid x n2}:
    ra_ag_unInj x n1 (HVal:=HVal1) = n1 = ra_ag_unInj x n2 (HVal:=HVal2).
  Proof.
    ra_ag_destr.
    rewrite /ra_ag_unInj. symmetry.
    etransitivity; last (etransitivity; first eapply (tsx n1 n2)); pi.
  Grab Existential Variables.
  { exact HVal2. }
  Qed.

  Lemma ra_ag_inj_unInj x n {HVal: cmra_valid x n} t:
    ra_ag_inj t ⊑ x -> ra_ag_unInj x n (HVal:=HVal) = n = t.
  Proof.
    rewrite ra_ag_pord. destruct x as [v ts tsx]=>Heq.
    unfold ra_ag_inj in Heq. destruct Heq as [EQv EQts]. unfold ra_ag_unInj.
    destruct n as [|n]; first exact: dist_bound. simpl. symmetry. eapply EQts.
  Grab Existential Variables.
  { rewrite EQv. apply HVal. }
  Qed.
  
  (* Provide a way to get the full T out of the agreement again. We don't need this, but I proved it before
     I realized. *)
  (* For this, we need a complete metric! *)
  Context {cmT: cmetric T}.

  Program Definition ra_ag_tschain v (ts: vChain v) (tsx: cvChain ts) {HVal: ↓(ag_inj v ts tsx)}: chain T :=
    fun i => ts i _.

  Instance ra_ag_tschain_c v (ts: vChain v) (tsx: cvChain ts) {HVal: ↓(ag_inj v ts tsx)} : cchain (ra_ag_tschain v ts tsx (HVal:=HVal)).
  Proof.
    intros n j m HLe1 HLe2. destruct n as [|n]; first by apply: dist_bound. unfold ra_ag_tschain.
    etransitivity; first by eapply (tsx (S n)).
    symmetry. etransitivity; first by eapply (tsx (S n)).
    apply equivR. f_equiv. eapply ProofIrrelevance.
  Qed.

  Program Definition ra_ag_unInjFull x {HVal: ↓x}: T :=
    match x with
    | ag_inj v ts tsx => compl (ra_ag_tschain v ts tsx (HVal:=_))
    end.

  Lemma ra_ag_unInjFull_dist x y {HVal1: ↓x} {HVal2: ↓y} n: (* The function is dependent, hence no "Proper" can be registered *)
    x = n = y -> ra_ag_unInjFull x (HVal:=HVal1) = n = ra_ag_unInjFull y (HVal:=HVal2).
  Proof.
    move=>EQ. destruct n as [|n]; first exact: dist_bound.
    destruct x as [xv xts xtsx].
    destruct y as [yv yts ytsx].
    destruct EQ as [_ EQts]. unfold ra_valid, ra_agree_valid in HVal1. unfold ra_valid, ra_agree_valid in HVal2.
    simpl. eapply umet_complete_extn. unfold ra_ag_tschain.
    eapply EQts. reflexivity.
  Qed.

  (* Correctness of the embedding (and of the entire construction, really - together with the duplicability shown above) *)
  Lemma ra_ag_inj_unInjFull x {HVal: ↓x} t:
    ra_ag_inj t ⊑ x -> ra_ag_unInjFull x (HVal:=HVal) == t.
  Proof.
    rewrite ra_ag_pord. destruct x as [v ts tsx]=>Heq.
    unfold ra_ag_inj in Heq. destruct Heq as [EQv EQts]. simpl. rewrite <-(umet_complete_const t).
    apply umet_complete_ext=>i. unfold ra_ag_tschain. unfold ra_ag_compinj_ts in EQts. symmetry.
    eapply EQts. rewrite EQv. apply HVal.
  Qed.

End Agreement.
Arguments ra_agree T {_ _} : clear implicits.

Section AgreementMap.
  Context {T U: Type} `{cmT: cmetric T} `{cmU: cmetric U}.
  Local Open Scope pumet_scope.

  Program Definition ra_agree_map (f: T -n> U): ra_agree T -m> ra_agree U :=
    m[(fun x => match x with
                | ag_inj v ts tsx => ag_inj v (fun n => compose f (ts n)) _
                end)].
  Next Obligation.
    move=>n i HLe pv. simpl. eapply met_morph_nonexp. specialize (tsx n i HLe pv).
    rewrite tsx.
    eapply dist_refl. f_equiv. by eapply ProofIrrelevance.
  Qed.
  Next Obligation.
    move=> x y EQxy.
    destruct n as [|n]; first by apply: dist_bound.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end); try (contradiction EQxy || reflexivity); [].
    destruct EQxy as [Hv Hts]. split; first assumption.
    move=>n' pv1 pv2 HLe. specialize (Hts n' pv1 pv2 HLe). unfold compose. rewrite Hts. reflexivity.
  Qed.
  Next Obligation.
    move=>x y EQxy. apply ra_ag_pord. apply ra_ag_pord in EQxy.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end); try (contradiction EQxy || reflexivity); [].
    destruct EQxy as [EQv EQts]. split; first split.
    - intros (pv1 & pv2 & _). assumption.
    - move=>pv. move/EQv:(pv)=>[pv1 [pv2 EQ]]. exists pv1 pv2. unfold compose. rewrite EQ. reflexivity.
    - unfold compose. intros n [pv1 [pv2 EQ]] pv3. unfold ra_ag_compinj_ts. eapply met_morph_nonexp.  rewrite -EQts /ra_ag_compinj_ts. f_equiv. by eapply ProofIrrelevance.
  Grab Existential Variables.
  { rewrite EQv. assumption. }
  Qed.

  Global Instance ra_agree_map_resp: Proper (equiv ==> equiv) ra_agree_map.
  Proof.
    move=> x1 x2 EQx y.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end).
    split; first reflexivity.
    move=>n pv1 pv2. rewrite EQx. unfold compose. repeat f_equiv. eapply ProofIrrelevance.
  Qed.
  Global Instance ra_agree_map_dist n: Proper (dist n ==> dist n) ra_agree_map.
  Proof.
    move=> x1 x2 EQx y.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end).
    destruct n as [|n]; first by apply: dist_bound.
    split; first reflexivity.
    move=>n' pv1 pv2 HLe. rewrite /compose. eapply mono_dist; last first.
    - rewrite EQx. repeat f_equiv. eapply ProofIrrelevance.
    - omega.
  Qed.
End AgreementMap.

Section AgreementMapComp.
  Local Open Scope pumet_scope.
  Context {T: Type} `{cmT: cmetric T}.

  Lemma ra_agree_map_id:
    ra_agree_map (umid T) == (pid (ra_agree T)).
  Proof.
    intros x.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end).
    simpl. split; first reflexivity.
    intros n pv1 pv2. repeat f_equiv. eapply ProofIrrelevance.
  Qed.
  
  Context {U V: Type} `{cmU: cmetric U} `{cmV: cmetric V}.

  Lemma ra_agree_map_comp (f: T -n> U) (g: U -n> V): 
    (ra_agree_map g) ∘ (ra_agree_map f) == ra_agree_map (g <M< f).
  Proof.
    intros x.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end).
    simpl. split; first reflexivity.
    intros n pv1 pv2. repeat f_equiv. eapply ProofIrrelevance.
  Qed.
End AgreementMapComp.
