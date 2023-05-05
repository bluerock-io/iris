(** Coq configuration for Iris (not meant to leak to clients) *)
(* Everything here should be [Export Set], which means when this
file is *imported*, the option will only apply on the import site
but not transitively. *)
From stdpp Require Export options.

Export Set Suggest Proof Using. (* also warns about forgotten [Proof.] *)

(* We always annotate hints with locality ([Global] or [Local]). This enforces
that at least global hints are annotated. *)
Export Set Warnings "+deprecated-hint-without-locality".

(* "Fake" import to whitelist this file for the check that ensures we import
this file everywhere.
From iris.prelude Require Import options.
*)
