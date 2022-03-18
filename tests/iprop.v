(** Make sure these universe constraints do not conflict with Iris's definition
of [gFunctors]:
See [!782](https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/782) *)

From Coq Require Import Logic.Eqdep.

(** A [sigT] that is partially applied and template-polymorphic causes universe
inconsistency errors, which is why [sigT] should be avoided for the definition
of [gFunctors].

The following constructs a partially applied [sigT] that generates bad universe
constraints. This causes a universe inconsistency when [gFunctors] are
to be defined with [sigT]. *)
Definition foo :=
  eq_dep
    ((Type -> Type) -> Type)
    (sigT (A:=Type -> Type)).

From iris.base_logic Require Import iprop.
