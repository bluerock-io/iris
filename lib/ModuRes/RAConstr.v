Require Import Ssreflect.ssreflect Ssreflect.ssrfun Omega.
Require Import PreoMet RA.

Local Open Scope ra_scope.
Local Open Scope predom_scope.

Set Bullet Behavior "Strict Subproofs".

(** These constructions are only for RA, so their equality is also defined locally. *)

(** The exclusive RA. *)
Section Exclusive.
  Context {T: Type} {eqT : Setoid T}.

  Inductive ex: Type :=
  | ex_own: T -> ex
  | ex_unit: ex
  | ex_bot: ex.

  Implicit Types (r s : ex) (t : T).

  Definition ex_eq r s: Prop :=
    match r, s with
      | ex_own t1, ex_own t2 => t1 == t2
      | ex_unit, ex_unit => True
      | ex_bot, ex_bot => True
      | _, _ => False
    end.

  Global Instance ra_equiv_ex : Equivalence ex_eq.
  Proof.
    split.
    - intros [t| |]; simpl; now auto.
    - intros [t1| |] [t2| |]; simpl; now auto.
    - intros [t1| |] [t2| |] [t3| |]; simpl; try now auto.
      + intros ? ?. etransitivity; eassumption.
  Qed.

  Global Program Instance ra_type_ex : Setoid ex :=
    mkType ex_eq.

  Global Instance ex_own_compat : Proper (equiv ==> equiv) ex_own.
  Proof. by move=> t1 t2 EQt. Qed.

  Global Instance ra_unit_ex : RA_unit _ := ex_unit.
  Global Instance ra_op_ex : RA_op _ :=
    fun r s =>
      match r, s with
        | ex_own _, ex_unit => r
        | ex_unit, ex_own _ => s
        | ex_unit, ex_unit   => ex_unit
        | _, _               => ex_bot
      end.
  Global Instance ra_valid_ex : RA_valid _ :=
    fun r => match r with
               | ex_bot => False
               | _      => True
             end.

  Global Instance ra_ex : RA ex.
  Proof.
    split.
    - intros [t1| |] [t2| |] Heqt [t'1| |] [t'2| |] Heqt'; simpl; now auto.
    - intros [s1| |] [s2| |] [s3| |]; reflexivity.
    - intros [s1| |] [s2| |]; reflexivity.
    - intros [s1| |]; reflexivity.
    - intros [t1| |] [t2| |] Heqt; unfold ra_valid; simpl in *; now auto.
    - reflexivity.
    - intros [t1| |] [t2| |]; unfold ra_valid; simpl; now auto.
  Qed.

  Lemma ra_sep_ex {t r} : ↓ex_own t · r -> r == 1.
  Proof. by case: r. Qed.

  Lemma ra_fps_ex_any t {r} (Hr : ↓r) : ex_own t ⇝ r.
  Proof. by move=> f /ra_sep_ex ->; rewrite ra_op_unit2. Qed.

  Lemma ra_fps_ex t t' : ex_own t ⇝ ex_own t'.
  Proof. exact: ra_fps_ex_any. Qed.

  Global Instance ra_can_ex : Cancellative ra_ex.
  Proof.
    case=>[t ||] a b Hv HEq.
    - by rewrite (ra_sep_ex Hv); move: Hv; rewrite -HEq=> /ra_sep_ex->; reflexivity.
    - by move: HEq; rewrite 2!ra_op_unit.
    - by exfalso.
  Qed.
End Exclusive.
Arguments ex T : clear implicits.


Section ExTests.
  Context {T : Type} {eqT : Setoid T}.
  Implicit Types (t : T).

  Goal forall t1 t2, t1 == t2 -> ex_own t1 == ex_own t2.
  Proof. move=> t1 t2 ->. reflexivity. Qed.

  Context {U} `{raU : RA U}.
  Implicit Types (u : U).
  
  Goal forall t1 t2 u, t1 == t2 -> (ex_own t1,u) ⊑ (ex_own t2,u).
  Proof. move=> t1 t2 u ->. reflexivity. Qed.

  Goal forall t u1 u2, u1 == u2 -> (ex_own t,u1) == (ex_own t,u2).
  Proof. move=> t u1 u2 ->. reflexivity. Qed.
End ExTests.

(** The authoritative RA. *)
Section Authoritative.
  Context {T} `{raT : RA T}.

  CoInductive auth := Auth of ex T * T.

  Implicit Types (x : ex T) (g t u : T) (r s : auth).

  Let auth_eq r s : Prop :=
    match r, s with
    | Auth p, Auth p' => p == p'
    end.

  Global Instance ra_equiv_auth : Equivalence auth_eq.
  Proof.
    split.
    - by move=> [p]; rewrite/auth_eq; reflexivity.
    - by move=> [p] [p']; rewrite/auth_eq; symmetry.
    - by move=> [p1] [p2] [p3]; rewrite/auth_eq; transitivity p2.
  Qed.
  Global Instance ra_type_auth : Setoid auth := mkType auth_eq.

  Section Compat.
    Variable R : relation (ex T * T).

    Let RA : relation auth := fun r1 r2 =>
      match r1, r2 with Auth p1, Auth p2 => R p1 p2 end.

    Global Instance auth_compat : Proper(R ==> RA) Auth.
    Proof. by move=> p1 p2 Rp. Qed.
  End Compat.

  Global Instance ra_unit_auth : RA_unit auth := Auth(ex_unit, 1).

  Global Instance ra_op_auth : RA_op auth := fun r s =>
    match r, s with Auth(x, t), Auth(x', t') => Auth(x·x', t·t') end.

  Global Instance ra_valid_auth : RA_valid auth := fun r =>
    match r with
    | Auth(ex_unit, t) => ↓t
    | Auth(ex_own g, t) => ↓g /\ ↓t /\ t ⊑ g
    | Auth(ex_bot, _) => False
    end.

  Global Instance ra_auth : RA auth.
  Proof.
    split.
    - move=> [[x1 t1]] [[x1' t1']] [/= Hx1 Ht1] [[x2 t2]] [[x2' t2']] [/= Hx2 Ht2].
      by rewrite Hx1 Ht1 Hx2 Ht2; split; reflexivity.
    - by move=> [[x1 t1]] [[x2 t2]] [[x3 t3]] /=; split; rewrite assoc; reflexivity.
    - by move=> [[x1 t1]] [[x2 t2]] /=; split; rewrite comm; reflexivity.
    - by move=> [[x t]] /=; split; rewrite ra_op_unit; reflexivity.
    - move=> [[x t]] [[x' t']] [/= Hx Ht].
      rewrite/ra_valid/ra_valid_auth.
      move: Hx; case: x=>[g||]; case: x'=>[g'||] => //= Hg.
      + by rewrite Ht Hg.
      + by rewrite Ht.
    - rewrite/ra_unit/ra_unit_auth/ra_valid/ra_valid_auth; exact: ra_valid_unit.
    - move=> [[x t]] [[x' t']]. rewrite /ra_op/ra_op_auth/ra_valid/ra_valid_auth.
      case: x=>[g||]; case: x'=>[g'||] //=.
      + move=>[Hg [Htv [t'' Ht]]]; split; [done | split; [exact: ra_op_valid Htv |]].
        exists (t'' · t'); by rewrite -assoc [t' · _]comm.
      + move=>[_ [Htv _]]; exact: ra_op_valid Htv.
      + exact: ra_op_valid.
  Qed.

  Lemma ra_sep_auth {t u x u'} :
    ↓Auth(ex_own t, u) · Auth(x, u') -> ↓t /\ x == 1 /\ ↓u · u' /\ u · u' ⊑ t.
  Proof.
    case: x=>[g||]; [done | | done].
    rewrite {1}/ra_valid/ra_valid_auth {1}/ra_op/ra_op_auth.
    by move=> [Ht [HSep HLe]].
  Qed.

  Definition auth_side_cond t u t' : Prop :=
    ↓t · u -> forall tf, t · tf ⊑ t · u -> t' · tf ⊑ t' · u.

  Lemma ra_fps_auth {t u t'} (SIDE : auth_side_cond t u t') (Hu' : ↓t' · u) :
    Auth(ex_own(t · u), t) ⇝ Auth(ex_own(t' · u), t').
  Proof.
    move=> [[xf tf]] /ra_sep_auth [Htu [Hxf [Htf HLe]]].
    rewrite/ra_valid/ra_valid_auth [Auth _ · _]/ra_op/ra_op_auth.
    move: Hxf; case: xf=>[g||] H; [done| clear H |done].	(* i.e., "rewrite Hxf" despite the match. *)
    rewrite {1}/ra_op/ra_op_ex.
    split; first done.
    set LE' := _ ⊑ _; suff HLe': LE'.
    { split; last done; move: Hu'; move: HLe'=>[t'' <-]. exact: ra_op_valid2. }
    exact: SIDE.
  Qed.

  Lemma ra_fps_auth_canc {HC : Cancellative raT} t {u t'} (Hu' : ↓t' · u) :
    Auth(ex_own(t · u), t) ⇝ Auth(ex_own(t' · u), t').
  Proof.
    apply: ra_fps_auth Hu'.
    move=> Hu tf HLe.
    apply: (ra_op_mono (prefl t')).
    exact: ra_cancel_ord HLe.
  Qed.

  Definition ra_local_action (act : T -=> T) : Prop :=
    forall t tf, ↓act t -> ↓t · tf -> act(t · tf) == act t · tf.

  Lemma ra_fps_auth_local {act t u} (HL : ra_local_action act) (Hu' : ↓act t · u) :
    Auth(ex_own(t · u), t) ⇝ Auth(ex_own(act t · u), act t).
  Proof.
    apply: ra_fps_auth (Hu').
    move/(_ t _ (ra_op_valid Hu')): HL => HL {Hu'}.
    move=> Hu tf [w HEq]; exists w.
    move: HEq; rewrite comm -assoc => HEq; rewrite comm -assoc.
    rewrite -(HL _ Hu).
    move: Hu; rewrite -HEq => Hu; rewrite -(HL _ Hu).
    by reflexivity.
  Qed.
End Authoritative.
Arguments auth : clear implicits.
(*
Notation "• g" := (Auth (ex_own g,1)) (at level 48) : ra_scope.
Notation "∘ t" := (Auth (1,t)) (at level 48) : ra_scope.
*)

Section AuthTests.
  Context {T : Type} `{raT : RA T}.
  Implicit Types (x : ex T) (t : T).
  
  Goal forall x t1 t2, t1 == t2 -> Auth(x,t1) == Auth(x,t2).
  Proof. move=> x t1 t2 EQt. rewrite EQt. reflexivity. Qed.

  Goal forall x1 x2 t, x1 == x2 -> Auth(x1,t) == Auth(x2,t).
  Proof. move=> x1 x2 t EQx. rewrite EQx. reflexivity. Qed.
End AuthTests.


Section DecAgreement.
  Context T `{T_ty : Setoid T} (eq_dec : forall x y, {x == y} + {x =/= y}).
  Local Open Scope ra_scope.

  Inductive ra_dagree : Type :=
    | dag_bottom
    | dag_unit
    | dag_inj (t : T).

  Global Instance ra_unit_dagree : RA_unit _ := dag_unit.
  Global Instance ra_valid_dag : RA_valid _ :=
           fun x => match x with dag_bottom => False | _ => True end.
  Global Instance ra_op_dag : RA_op _ :=
    fun x y => match x, y with
               | dag_inj t1, dag_inj t2 =>
                   if eq_dec t1 t2 is left _ then dag_inj t1 else dag_bottom
               | dag_bottom , y => dag_bottom
               | x , dag_bottom => dag_bottom
               | dag_unit, y => y
               | x, dag_unit => x
             end.

  Definition ra_eq_dag (x y: ra_dagree): Prop :=
    match x,y with
      | dag_inj t1, dag_inj t2 => t1 == t2
      | x, y => x = y
    end.


  Global Instance ra_equivalence_agree : Equivalence ra_eq_dag.
  Proof.
    split; intro; intros; destruct x; try (destruct y; try destruct z); simpl; try reflexivity;
    simpl in *; try inversion H; try inversion H0; try rewrite <- H; try rewrite <- H0; try firstorder.
  Qed.
  Global Instance ra_type_dagree : Setoid ra_dagree := mkType ra_eq_dag.
  Global Instance res_dagree : RA ra_dagree.
  Proof.
    split; repeat intro.
    - repeat (match goal with [ x : ra_dagree |- _ ] => destruct x end);
      simpl in *; try reflexivity; try rewrite H; try rewrite H0; try reflexivity;
      try inversion H; try inversion H0; compute;
      destruct (eq_dec t2 t0), (eq_dec t1 t); simpl; auto; exfalso;
      [ rewrite <- H, -> e in c | rewrite -> H, -> e in c; symmetry in c]; contradiction.
    - repeat (match goal with [ x : ra_dagree |- _ ] => destruct x end);
      simpl in *; auto; try reflexivity; compute; try destruct (eq_dec _ _); 
      try reflexivity;
      destruct (eq_dec t0 t), (eq_dec t1 t0), (eq_dec t1 t); simpl; auto; 
      try reflexivity;
      try (rewrite <- e in c; contradiction); now exfalso; eauto.
    - destruct t1, t2; try reflexivity; compute; destruct (eq_dec t0 t), (eq_dec t t0);
      try reflexivity; auto; try contradiction; symmetry in e; contradiction.
    - destruct t; reflexivity.
    - destruct x, y; simpl; firstorder; now inversion H.
    - now constructor.
    - destruct t1, t2; try contradiction; now constructor.
  Qed.

End DecAgreement.

Section Agreement.
  (* This is more complex than above, and it does not require a decidable equality.
     I also comes with support for pcmType. *)
  Context T `{T_ty : Setoid T}.
  Local Open Scope ra_scope.

  Inductive ra_agree : Type :=
  | ag_inj (valid: Prop) (ts: valid -> T)
  | ag_unit.

  Global Instance ra_agree_unit : RA_unit _ := ag_unit.
  Global Instance ra_agree_valid : RA_valid _ :=
           fun x => match x with ag_unit => True | ag_inj valid _ => valid end.
  Global Instance ra_dag_op : RA_op _ :=
    fun x y => match x, y with
               | ag_inj v1 ts1, ag_inj v2 ts2 =>
                 ag_inj (exists v1 v2, ts1 v1 == ts2 v2) (fun t => ts1 match t with ex_intro vp1 _ => vp1 end)
                        (* We need an "exists v1" here, to be able to access ts1 *)
               | ag_unit, y => y
               | x, ag_unit => x
               end.
  Definition ra_ag_inj (t: T): ra_agree := ag_inj True (fun _ => t).

  Definition ra_agree_eq (x y: ra_agree): Prop :=
    match x, y with
    | ag_inj v1 ts1, ag_inj v2 ts2 => v1 == v2 /\ (forall pv1 pv2, ts1 pv1 == ts2 pv2)
                                      (* The equality on the ts looks way too strong. However,
                                         thanks to PI, this is actally the same as
                                         "if both are valid, then pv1 and pv2 agree somewhere". *)
    | ag_unit, ag_unit => True
    | _, _ => False
    end.

  Local Ltac ra_ag_destr := repeat (match goal with [ x : ra_agree |- _ ] => destruct x end).

  (* Land of dragons starts here *)
  Axiom ProofIrrelevance: forall (P: Prop) (p q: P), p = q.
  Ltac pi p q := erewrite (ProofIrrelevance _ p q).

  Local Ltac ra_ag_auto := first [by firstorder | split; [by firstorder|intros pv1 pv2; pi pv1 pv2; by firstorder ]].
  
  Global Instance ra_agree_eq_equiv : Equivalence ra_agree_eq.
  Proof.
    split; repeat intro; ra_ag_destr; try (exact I || contradiction); [| |]. (* 3 goals left. *)
    - split; first reflexivity. intros. pi pv1 pv2. reflexivity.
    - destruct H. split; intros; by symmetry.
    - destruct H, H0.
      split; first (etransitivity; now eauto).
      intro; etransitivity; [now eapply H1 | now eapply H2].
  Grab Existential Variables.
  { rewrite -H. assumption. }
  Qed.
  Global Instance ra_agree_type : Setoid ra_agree := mkType ra_agree_eq.
  Global Instance ra_agree_res : RA ra_agree.
  Proof.
    split; repeat intro.
    - ra_ag_destr; try ra_ag_auto; [].
      destruct H as (HeqV1 & HeqT1), H0 as (HeqV2 & HeqT2).
      split.
      + split; intros (pv1 & pv2 & Heq); do 2 eexists.
        * rewrite <-HeqT1, <-HeqT2. eassumption.
        * rewrite ->HeqT1, ->HeqT2. eassumption.
      + intros (pv11 & pv12 & Heqp1) (pv21 & pv22 & Heqp2).
        by apply: HeqT1.
    - ra_ag_destr; try ra_ag_auto; []. split.
      + split.
        * intros [pv1 [[pv2 [pv3 Heq1] Heq2]]]. do 2 eexists.
          transitivity (ts0 pv2); last eassumption.
          erewrite (ProofIrrelevance _ _ pv1). assumption.
        * intros [[pv1 [pv2 Heq1]] [pv3 Heq2]]. do 2 eexists.
          erewrite (ProofIrrelevance _ _ pv2). eassumption.
      + intros (pv11 & pv12 & Heqp1) (pv21 & pv22 & Heqp2).
        f_equiv. by eapply ProofIrrelevance.
    - ra_ag_destr; try ra_ag_auto; []. split.
      + split; intros (pv1 & pv2 & Heq); do 2 eexists; symmetry; eassumption.
      + intros (pv11 & pv12 & Heqp1) (pv21 & pv22 & Heqp2).
        pi pv21 pv12. assumption.
    - ra_ag_destr; reflexivity.
    - ra_ag_destr; unfold ra_valid, ra_agree_valid in *; firstorder.
    - firstorder.
    - ra_ag_destr; firstorder.
  Grab Existential Variables.
  { do 2 eexists. transitivity (ts1 pv1); last eassumption. symmetry. eassumption. }
  { do 2 eexists. eassumption. }
  { simpl in *. tauto. }
  { simpl in *. tauto. }
  { simpl in *. tauto. }
  { simpl in *. tauto. }
  Qed.

  Lemma ra_ag_pord (x y: ra_agree):
    x ⊑ y <-> x · y == y.
  Proof.
    split.
    - move=>[z EQ]. ra_ag_destr; try ra_ag_auto; [].
      destruct EQ as [EQv EQts]. split.
      + split.
        * intros (pv1 & pv2 & EQt). assumption.
        * erewrite <-EQv. intros (pv1 & pv2 & EQt). do 2 eexists. erewrite <-EQt. erewrite <-EQts. f_equiv. by eapply ProofIrrelevance.
      + move=>[pv1 [pv2 EQt]] pv3. pi pv3 pv2. assumption.
    - intros EQ. exists y. rewrite comm. assumption.
  Grab Existential Variables.
  { do 2 eexists. eassumption. }
  { rewrite <-EQv. do 2 eexists. eassumption. }
  Qed.

  (* We also have a metric *)
  Context {mT: metric T}.

  Definition ra_agree_dist n :=
    match n with
    | O => fun _ _ => True
    | S n => fun x y => match x, y with
                        | ag_inj v1 t1, ag_inj v2 t2 => v1 == v2 /\ (forall pv1 pv2, t1 pv1 = S n = t2 pv2)
                        | ag_unit, ag_unit => True
                        | _, _ => False
                        end
    end.

  Global Program Instance ra_agree_metric : metric ra_agree := mkMetr ra_agree_dist.
  Next Obligation.
    repeat intro. destruct n as [|n]; first by auto.
    ra_ag_destr; try firstorder.
    - etransitivity; first (symmetry; eapply dist_refl; now eauto).
      etransitivity; last (eapply dist_refl; now eauto). now eauto.
    - etransitivity; first (eapply dist_refl; now eauto).
      etransitivity; last (symmetry; eapply dist_refl; now eauto). now eauto.
  Grab Existential Variables.
  { tauto. }
  { tauto. }
  { tauto. }
  { tauto. }
  Qed.
  Next Obligation.
    repeat intro. split.
    - intros Hall. ra_ag_destr; last exact I; try (specialize (Hall (S O)); now firstorder); [].
      split.
      + specialize (Hall (S O)); now firstorder.
      + intros pv1 pv2. eapply dist_refl. intro. specialize (Hall n). destruct n as [|n]; first by apply: dist_bound.
        firstorder.
    - repeat intro. destruct n as [|n]; first by auto. ra_ag_destr; try firstorder.
      + eapply dist_refl. now eauto.
  Qed.
  Next Obligation.
    repeat intro. destruct n as [|n]; first by auto.
    ra_ag_destr; try firstorder; [].
    - symmetry. now eauto.
  Qed.
  Next Obligation.
    repeat intro. destruct n as [|n]; first by auto.
    ra_ag_destr; try firstorder; [].
    etransitivity; now eauto.
  Grab Existential Variables.
  { tauto. }
  Qed.
  Next Obligation.
    repeat intro. destruct n as [|n]; first by auto.
    ra_ag_destr; try firstorder; [].
    eapply dist_mono. eapply H0.
  Qed.

  (* And a complete metric! *)
  Context {cmT: cmetric T}.

  Program Definition unInj (σ : chain ra_agree) {σc : cchain σ} {v ts} (HNE : σ (S O) = ag_inj v ts) (pv: v): chain T :=
    fun i => match σ (S i) with
             | ag_unit => False_rect _ _
             | ag_inj v' ts' => ts' _
             end.
  Next Obligation.
    specialize (σc (S O) (S O) (S i)); rewrite <- Heq_anonymous in σc.
    destruct (σ (S O)) as [ v' ts' |].
    - apply σc; omega.
    - discriminate.
  Qed.
  Next Obligation.
    cut (σ (S O) = (S 0) = σ (S i)).
    { move=> EQ. rewrite ->HNE, <-Heq_anonymous in EQ. destruct EQ as [EQ _]. rewrite -EQ. assumption. }
    eapply σc; omega.
  Qed.

  Instance unInj_c (σ : chain ra_agree) {σc : cchain σ} {v ts} (HNE : σ (S O) = ag_inj v ts) pv :
    cchain (unInj σ HNE pv).
  Proof.
    intros [| k] n m HLE1 HLE2; [now apply dist_bound |]; unfold unInj.
    generalize (@eq_refl _ (σ (S n))); pattern (σ (S n)) at 1 3.
    destruct (σ (S n)) as [v1 ts1 |]; simpl; intros EQn.
    - generalize (@eq_refl _ (σ (S m))); pattern (σ (S m)) at 1 3.
      destruct (σ (S m)) as [v2 ts2 |]; simpl; intros EQm.
      + pose (σc' := σc (S k) (S n) (S m)); rewrite <- EQm, <- EQn in σc'.
        apply σc'; auto with arith.
      + exfalso; specialize (σc (S O) (S O) (S m)); rewrite <- EQm in σc.
        destruct (σ (S O)) as [v2 ts2 |]; first by (contradiction σc; auto with arith).
        discriminate.
    - exfalso; specialize (σc (S O) (S O) (S n)); rewrite <- EQn in σc.
      destruct (σ (S O)) as [v2 ts2 |]; [contradiction σc; auto with arith | discriminate].
  Qed.

  Program Definition ra_ag_compl (σ : chain ra_agree) {σc : cchain σ} :=
    match σ (S O) with
      | ag_unit => ag_unit
      | ag_inj v ts => ag_inj v (fun pv => (compl (unInj (ts:=ts) σ _ pv)))
    end.

  Global Program Instance ra_ag_cmt : cmetric ra_agree := mkCMetr ra_ag_compl.
  Next Obligation.
    intros [| n]; [now intros; apply dist_bound | unfold ra_ag_compl].
    generalize (@eq_refl _ (σ (S O))) as EQ1. pattern (σ (S O)) at 1 3. destruct (σ (S O)) as [v0 ts0 |]; intros.
    - destruct (σ i) as [vi |] eqn: EQi; [split| exfalso].
      + move:(σc (S 0)). move/(_ (S 0) i _ _)/Wrap. intros H. edestruct H as [HEQ]=>{H}; first omega.
        rewrite <-EQ1, EQi in HEQ. destruct HEQ as [HEQ _]. assumption.
      + move=>pv1 pv2.
        assert (HT := conv_cauchy (unInj σ (ra_ag_compl_obligation_1 _ _ _ _ EQ1 pv1) pv1) (S n)).
        unfold dist; simpl; rewrite ->(HT i) by eauto with arith.
        unfold unInj; generalize (@eq_refl _ (σ (S i))); pattern (σ (S i)) at 1 3.
        destruct (σ (S i)) as [vsi |]; intros EQsi; clear HT; [| exfalso].
        * assert (HT : S n <= i) by eauto with arith.
          assert (σc':=σc (S n) (S i) i); rewrite ->EQi, <- EQsi in σc'.
          apply σc'; now auto with arith.
        * specialize (σc (S O) (S O) (S i)); rewrite <- EQ1, <- EQsi in σc.
          apply σc; auto with arith.
      + specialize (σc (S O) (S O) i); rewrite <- EQ1, EQi in σc.
        apply σc; auto with arith.
        rewrite <- HLe; auto with arith.
    - intros.
      destruct (σ i) as [vi tsvi |] eqn: EQi; [| reflexivity].
      specialize (σc (S O) (S O) i); rewrite <- EQ1, EQi in σc.
      apply σc; omega.
  Qed.

  (* And we have a pcmType, too! *)
  Global Instance ra_ag_pcm: pcmType ra_agree.
  Proof.
    split. repeat intro. eapply ra_ag_pord. unfold compl, ra_ag_cmt, ra_ag_compl.
    generalize (@eq_refl _ (ρ (S O))) as Hρ. pattern (ρ (S O)) at 1 3 7.
    destruct (ρ (S O)) as [ρv ρts|]; intros.
    - generalize (@eq_refl _ (σ (S O))) as Hσ. pattern (σ (S O)) at 1 3.
      destruct (σ (S O)) as [σv σts|]; intros.
      + simpl.
        assert (HT: forall pv1 pv2, compl (unInj σ (ra_ag_compl_obligation_1 σ σc σv σts Hσ pv1) pv1) ==
                                    compl (unInj ρ (ra_ag_compl_obligation_1 ρ ρc ρv ρts Hρ pv2) pv2)).
        { intros ? ?. apply umet_complete_ext=>i. assert (HLe: S O <= S i) by omega.
          unfold unInj. generalize (@eq_refl _ (ρ (S i))) as Hρi. pattern (ρ (S i)) at 1 3.
          destruct (ρ (S i)) as [ρiv ρits|]; intros; last first.
          { exfalso. specialize (ρc _ _ _ HLe (le_refl _)). rewrite <-Hρ, <-Hρi in ρc. exact ρc. }
          generalize (@eq_refl _ (σ (S i))) as Hσi. pattern (σ (S i)) at 1 3.
          destruct (σ (S i)) as [σiv σits|]; intros; last first.
          { exfalso. specialize (σc _ _ _ HLe (le_refl _)). rewrite <-Hσ, <-Hσi in σc. exact σc. }
          specialize (H (S i)). rewrite ->ra_ag_pord in H.
          rewrite <-Hρi, <-Hσi in H. destruct H as [EQv EQts].
          erewrite <-EQts. f_equiv. by eapply ProofIrrelevance.
        }
        split.
        * split; first by (intros (pv1 & pv2 & _); tauto).
          intros pv. specialize (H (S O)). rewrite ->ra_ag_pord, <-Hρ, <-Hσ in H.
          destruct H as [H _]. rewrite <-H in pv. destruct pv as (pv1 & pv2 & EQ).
          exists pv1 pv2. eapply HT.
        * intros (pv1 & pv2 & EQ) pv3. eapply HT.
      + rewrite ra_op_unit. reflexivity.
    - generalize (@eq_refl _ (σ (S O))) as Hσ. pattern (σ (S O)) at 1 3.
      destruct (σ (S O)) as [σv σts|]; intros.
      + simpl. specialize (H (S O)). rewrite ->ra_ag_pord, <-Hρ, <-Hσ in H. exact H.
      + reflexivity.
  Grab Existential Variables.
  { rewrite EQv. specialize (ρc _ _ _ HLe (le_refl _)). rewrite <-Hρ, <-Hρi in ρc.
    destruct ρc as [EQv' _]. rewrite EQv'. assumption. }
  Qed.
End Agreement.


Section IndexedProduct.
  (* I is the index type (domain), S the type of the components (codomain) *)
  Context {I : Type} {S : forall (i : I), Type}
          {tyS : forall i, Setoid (S i)}
          {uS : forall i, RA_unit (S i)}
          {opS : forall i, RA_op (S i)}
          {vS : forall i, RA_valid (S i)}
          {raS : forall i, RA (S i)}.
  Local Open Scope ra_scope.

  Definition ra_res_infprod := forall (i : I), S i.

  Implicit Type (i : I) (f g : ra_res_infprod).

  Definition ra_eq_infprod := fun f g => forall i, f i == g i.
  Global Instance ra_equiv_infprod : Equivalence ra_eq_infprod.
  Proof. split; repeat intro; [ | rewrite (H i) | rewrite -> (H i), (H0 i) ]; reflexivity. Qed.

  Global Instance ra_type_infprod : Setoid ra_res_infprod | 5 := mkType ra_eq_infprod.
  Global Instance ra_unit_infprod : RA_unit ra_res_infprod := fun i => 1.
  Global Instance ra_op_infprod : RA_op ra_res_infprod := fun f g i => f i · g i.
  Global Instance ra_valid_infprod : RA_valid ra_res_infprod := fun f => forall i, ↓ (f i).
  Global Instance ra_infprod : RA ra_res_infprod.
  Proof.
    split; repeat intro.
    - exact: ra_op_proper.
    - compute; now rewrite -> (assoc (T := S i) (t1 i) (t2 i) (t3 i)).
    - compute; now rewrite -> (comm (T :=S i) (t1 i) (t2 i)).
    - compute; now rewrite -> (ra_op_unit (RA := raS i) (t := t i)).
    - compute; intros; split; intros; by move/(_ i): H0; rewrite (H i).
    - now eapply (ra_valid_unit (RA := raS i)).
    - eapply (ra_op_valid (RA := raS i)); now eauto.
  Qed.
End IndexedProduct.


Section HomogeneousProduct.
  (* I is the index type (domain), S the type of the components (codomain) *)
  Context {I : Type} {S : Type} `{RA S}.

  Global Instance ra_homprod : RA (forall (i : I), S).
  Proof. now eapply ra_infprod; auto. Qed.
End HomogeneousProduct.
