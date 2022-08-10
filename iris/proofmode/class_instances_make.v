From iris.proofmode Require Export classes_make.
From iris.prelude Require Import options.
Import bi.

Section class_instances_make.
Context {PROP : bi}.
Implicit Types P Q R : PROP.

Global Instance make_embed_pure `{BiEmbed PROP PROP'} φ :
  KnownMakeEmbed (PROP:=PROP) ⌜φ⌝ ⌜φ⌝.
Proof. apply embed_pure. Qed.
Global Instance make_embed_emp `{BiEmbedEmp PROP PROP'} :
  KnownMakeEmbed (PROP:=PROP) emp emp.
Proof. apply embed_emp. Qed.
Global Instance make_embed_default `{BiEmbed PROP PROP'} P :
  MakeEmbed P ⎡P⎤ | 100.
Proof. by rewrite /MakeEmbed. Qed.

Global Instance make_sep_emp_l P : KnownLMakeSep emp P P.
Proof. apply left_id, _. Qed.
Global Instance make_sep_emp_r P : KnownRMakeSep P emp P.
Proof. apply right_id, _. Qed.
Global Instance make_sep_true_l P : Absorbing P → KnownLMakeSep True P P.
Proof. intros. apply True_sep, _. Qed.
Global Instance make_sep_true_r P : Absorbing P → KnownRMakeSep P True P.
Proof. intros. by rewrite /KnownRMakeSep /MakeSep sep_True. Qed.
Global Instance make_sep_default P Q : MakeSep P Q (P ∗ Q) | 100.
Proof. by rewrite /MakeSep. Qed.

Global Instance make_and_true_l P : KnownLMakeAnd True P P.
Proof. apply left_id, _. Qed.
Global Instance make_and_true_r P : KnownRMakeAnd P True P.
Proof. by rewrite /KnownRMakeAnd /MakeAnd right_id. Qed.
Global Instance make_and_emp_l P : Affine P → KnownLMakeAnd emp P P.
Proof. intros. by rewrite /KnownLMakeAnd /MakeAnd emp_and. Qed.
Global Instance make_and_emp_r P : Affine P → KnownRMakeAnd P emp P.
Proof. intros. by rewrite /KnownRMakeAnd /MakeAnd and_emp. Qed.
Global Instance make_and_default P Q : MakeAnd P Q (P ∧ Q) | 100.
Proof. by rewrite /MakeAnd. Qed.

Global Instance make_or_true_l P : KnownLMakeOr True P True.
Proof. apply left_absorb, _. Qed.
Global Instance make_or_true_r P : KnownRMakeOr P True True.
Proof. by rewrite /KnownRMakeOr /MakeOr right_absorb. Qed.
Global Instance make_or_emp_l P : Affine P → KnownLMakeOr emp P emp.
Proof. intros. by rewrite /KnownLMakeOr /MakeOr emp_or. Qed.
Global Instance make_or_emp_r P : Affine P → KnownRMakeOr P emp emp.
Proof. intros. by rewrite /KnownRMakeOr /MakeOr or_emp. Qed.
Global Instance make_or_default P Q : MakeOr P Q (P ∨ Q) | 100.
Proof. by rewrite /MakeOr. Qed.

Global Instance make_affinely_emp : @KnownMakeAffinely PROP emp emp | 0.
Proof. by rewrite /KnownMakeAffinely /MakeAffinely affinely_emp. Qed.
Global Instance make_affinely_True : @KnownMakeAffinely PROP True emp | 0.
Proof. by rewrite /KnownMakeAffinely /MakeAffinely affinely_True_emp. Qed.
Global Instance make_affinely_default P : MakeAffinely P (<affine> P) | 100.
Proof. by rewrite /MakeAffinely. Qed.

Global Instance make_intuitionistically_emp :
  @KnownMakeIntuitionistically PROP emp emp | 0.
Proof.
  by rewrite /KnownMakeIntuitionistically /MakeIntuitionistically
    intuitionistically_emp.
Qed.
Global Instance make_intuitionistically_True :
  @KnownMakeIntuitionistically PROP True emp | 0.
Proof.
  by rewrite /KnownMakeIntuitionistically /MakeIntuitionistically
    intuitionistically_True_emp.
Qed.
Global Instance make_intuitionistically_default P :
  MakeIntuitionistically P (□ P) | 100.
Proof. by rewrite /MakeIntuitionistically. Qed.

Global Instance make_absorbingly_emp : @KnownMakeAbsorbingly PROP emp True | 0.
Proof.
  by rewrite /KnownMakeAbsorbingly /MakeAbsorbingly
     -absorbingly_emp_True.
Qed.
Global Instance make_absorbingly_True : @KnownMakeAbsorbingly PROP True True | 0.
Proof. by rewrite /KnownMakeAbsorbingly /MakeAbsorbingly absorbingly_pure. Qed.
Global Instance make_absorbingly_default P : MakeAbsorbingly P (<absorb> P) | 100.
Proof. by rewrite /MakeAbsorbingly. Qed.

Global Instance make_laterN_true n : @KnownMakeLaterN PROP n True True | 0.
Proof. by rewrite /KnownMakeLaterN /MakeLaterN laterN_True. Qed.
Global Instance make_laterN_emp `{!BiAffine PROP} n :
  @KnownMakeLaterN PROP n emp emp | 0.
Proof. by rewrite /KnownMakeLaterN /MakeLaterN laterN_emp. Qed.
Global Instance make_laterN_default n P : MakeLaterN n P (▷^n P) | 100.
Proof. by rewrite /MakeLaterN. Qed.

Global Instance make_except_0_True : @KnownMakeExcept0 PROP True True.
Proof. by rewrite /KnownMakeExcept0 /MakeExcept0 except_0_True. Qed.
Global Instance make_except_0_default P : MakeExcept0 P (◇ P) | 100.
Proof. by rewrite /MakeExcept0. Qed.
End class_instances_make.
