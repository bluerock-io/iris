From iris.si_logic Require Import bi.

(** Make sure that [siProp]s are parsed in [bi_scope]. *)
Definition test : siProp := ▷ True.
Definition testI : siPropI := ▷ True.
