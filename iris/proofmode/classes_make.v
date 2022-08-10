From iris.bi Require Export bi.
From iris.prelude Require Import options.

(* For each of the [MakeXxxx] class, there is a [KnownMakeXxxx]
   variant, that only succeeds if the parameter(s) is not an evar. In
   the case the parameter(s) is an evar, then [MakeXxxx] will not
   instantiate it arbitrarily.

   The reason for this is that if given an evar, these typeclasses
   would typically try to instantiate this evar with some arbitrary
   logical constructs such as emp or True. Therefore, we use a Hint
   Mode to disable all the instances that would have this behavior. *)

Class MakeEmbed {PROP PROP' : bi} `{BiEmbed PROP PROP'} (P : PROP) (Q : PROP') :=
  make_embed : ⎡P⎤ ⊣⊢ Q.
Global Arguments MakeEmbed {_ _ _} _%I _%I.
Global Hint Mode MakeEmbed + + + - - : typeclass_instances.
Class KnownMakeEmbed {PROP PROP' : bi} `{BiEmbed PROP PROP'} (P : PROP) (Q : PROP') :=
  known_make_embed :> MakeEmbed P Q.
Global Arguments KnownMakeEmbed {_ _ _} _%I _%I.
Global Hint Mode KnownMakeEmbed + + + ! - : typeclass_instances.

Class MakeSep {PROP : bi} (P Q PQ : PROP) := make_sep : P ∗ Q ⊣⊢ PQ .
Global Arguments MakeSep {_} _%I _%I _%I.
Global Hint Mode MakeSep + - - - : typeclass_instances.
Class KnownLMakeSep {PROP : bi} (P Q PQ : PROP) :=
  knownl_make_sep :> MakeSep P Q PQ.
Global Arguments KnownLMakeSep {_} _%I _%I _%I.
Global Hint Mode KnownLMakeSep + ! - - : typeclass_instances.
Class KnownRMakeSep {PROP : bi} (P Q PQ : PROP) :=
  knownr_make_sep :> MakeSep P Q PQ.
Global Arguments KnownRMakeSep {_} _%I _%I _%I.
Global Hint Mode KnownRMakeSep + - ! - : typeclass_instances.

Class MakeAnd {PROP : bi} (P Q PQ : PROP) :=  make_and_l : P ∧ Q ⊣⊢ PQ.
Global Arguments MakeAnd {_} _%I _%I _%I.
Global Hint Mode MakeAnd + - - - : typeclass_instances.
Class KnownLMakeAnd {PROP : bi} (P Q PQ : PROP) :=
  knownl_make_and :> MakeAnd P Q PQ.
Global Arguments KnownLMakeAnd {_} _%I _%I _%I.
Global Hint Mode KnownLMakeAnd + ! - - : typeclass_instances.
Class KnownRMakeAnd {PROP : bi} (P Q PQ : PROP) :=
  knownr_make_and :> MakeAnd P Q PQ.
Global Arguments KnownRMakeAnd {_} _%I _%I _%I.
Global Hint Mode KnownRMakeAnd + - ! - : typeclass_instances.

Class MakeOr {PROP : bi} (P Q PQ : PROP) := make_or_l : P ∨ Q ⊣⊢ PQ.
Global Arguments MakeOr {_} _%I _%I _%I.
Global Hint Mode MakeOr + - - - : typeclass_instances.
Class KnownLMakeOr {PROP : bi} (P Q PQ : PROP) :=
  knownl_make_or :> MakeOr P Q PQ.
Global Arguments KnownLMakeOr {_} _%I _%I _%I.
Global Hint Mode KnownLMakeOr + ! - - : typeclass_instances.
Class KnownRMakeOr {PROP : bi} (P Q PQ : PROP) := knownr_make_or :> MakeOr P Q PQ.
Global Arguments KnownRMakeOr {_} _%I _%I _%I.
Global Hint Mode KnownRMakeOr + - ! - : typeclass_instances.

Class MakeAffinely {PROP : bi} (P Q : PROP) :=
  make_affinely : <affine> P ⊣⊢ Q.
Global Arguments MakeAffinely {_} _%I _%I.
Global Hint Mode MakeAffinely + - - : typeclass_instances.
Class KnownMakeAffinely {PROP : bi} (P Q : PROP) :=
  known_make_affinely :> MakeAffinely P Q.
Global Arguments KnownMakeAffinely {_} _%I _%I.
Global Hint Mode KnownMakeAffinely + ! - : typeclass_instances.

Class MakeIntuitionistically {PROP : bi} (P Q : PROP) :=
  make_intuitionistically : □ P ⊣⊢ Q.
Global Arguments MakeIntuitionistically {_} _%I _%I.
Global Hint Mode MakeIntuitionistically + - - : typeclass_instances.
Class KnownMakeIntuitionistically {PROP : bi} (P Q : PROP) :=
  known_make_intuitionistically :> MakeIntuitionistically P Q.
Global Arguments KnownMakeIntuitionistically {_} _%I _%I.
Global Hint Mode KnownMakeIntuitionistically + ! - : typeclass_instances.

Class MakeAbsorbingly {PROP : bi} (P Q : PROP) :=
  make_absorbingly : <absorb> P ⊣⊢ Q.
Global Arguments MakeAbsorbingly {_} _%I _%I.
Global Hint Mode MakeAbsorbingly + - - : typeclass_instances.
Class KnownMakeAbsorbingly {PROP : bi} (P Q : PROP) :=
  known_make_absorbingly :> MakeAbsorbingly P Q.
Global Arguments KnownMakeAbsorbingly {_} _%I _%I.
Global Hint Mode KnownMakeAbsorbingly + ! - : typeclass_instances.

Class MakePersistently {PROP : bi} (P Q : PROP) :=
  make_persistently : <pers> P ⊣⊢ Q.
Global Arguments MakePersistently {_} _%I _%I.
Global Hint Mode MakePersistently + - - : typeclass_instances.
Class KnownMakePersistently {PROP : bi} (P Q : PROP) :=
  known_make_persistently :> MakePersistently P Q.
Global Arguments KnownMakePersistently {_} _%I _%I.
Global Hint Mode KnownMakePersistently + ! - : typeclass_instances.

Class MakeLaterN {PROP : bi} (n : nat) (P lP : PROP) :=
  make_laterN : ▷^n P ⊣⊢ lP.
Global Arguments MakeLaterN {_} _%nat _%I _%I.
Global Hint Mode MakeLaterN + + - - : typeclass_instances.
Class KnownMakeLaterN {PROP : bi} (n : nat) (P lP : PROP) :=
  known_make_laterN :> MakeLaterN n P lP.
Global Arguments KnownMakeLaterN {_} _%nat _%I _%I.
Global Hint Mode KnownMakeLaterN + + ! - : typeclass_instances.

Class MakeExcept0 {PROP : bi} (P Q : PROP) :=
  make_except_0 : ◇ P ⊣⊢ Q.
Global Arguments MakeExcept0 {_} _%I _%I.
Global Hint Mode MakeExcept0 + - - : typeclass_instances.
Class KnownMakeExcept0 {PROP : bi} (P Q : PROP) :=
  known_make_except_0 :> MakeExcept0 P Q.
Global Arguments KnownMakeExcept0 {_} _%I _%I.
Global Hint Mode KnownMakeExcept0 + ! - : typeclass_instances.
