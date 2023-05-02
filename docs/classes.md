# Type classes

This file collects conventions about the use of type classes in Iris.
The file is work in progress, so many conventions are missing and remain to be
documented.

## Order of `TCOr` arguments

We often use the `TCOr` combinator (from std++) to describe disjunctive type
class premises. For example:

```coq
Lemma sep_elim_l P Q `{!TCOr (Affine Q) (Absorbing P)} : P ∗ Q ⊢ P.
```

Type class search will only introduce `TCOr`, but never eliminate `TCOr`.
As such, to make it easy to derive other lemmas that use `TCOr`, it is important
that the arguments of `TCOr` are in a consistent order. For example:

```coq
Lemma sep_elim_r P Q `{!TCOr (Affine P) (Absorbing Q)} : P ∗ Q ⊢ Q.
Proof. by rewrite comm sep_elim_l. Qed.

Lemma sep_and P Q `{!TCOr (Affine P) (Absorbing Q), !TCOr (Affine Q) (Absorbing P)} : P ∗ Q ⊢ P ∧ Q.
Proof. apply and_intro; [apply: sep_elim_l|apply: sep_elim_r]. Qed.
```

As shown here, it is not needed to eliminate (i.e., `destruct`) the `TCOr`
because the order matches up.

**Conventions:**

- Affine before absorbing, i.e., `TCOr (Affine P) (Absorbing Q)`

## Use of `Hint Cut` to prune the search space

We often use type classes to describe classes of objects that satisfy some
property. For example, `Persistent` and `Separable` describe the BI propositions
that are persistent and separable. There is an inheritance between the two
classes, and both are closed under the usual logical connectives, resulting in
the instances:

```coq
Instance persistent_separable P : Persistent P → Separable P.
Instance and_persistent P Q : Persistent P → Persistent Q → Persistent (P ∧ Q).
Instance and_separable P1 P2 : Separable P1 → Separable P2 → Separable (P1 ∧ P2).
```

Having these instances at the same time is problematic since there might be
multiple derivations for the same goal. For example:

```
Persistent P        Persistent Q              Persistent P         Persistent Q
------------        ------------              ---------------------------------
Separable P         Separable Q                    Persistent (P ∧ Q)
        -----------------                          ------------------
        Separable (P ∧ Q)                           Separable (P ∧ Q)
```

When considering `P1 ∧ ... ∧ Pn`, the number of derivations is `O(n^2)`.
When adding an additional class, e.g., `Plain` for which we have
`Plain P → Persistent P`, the number of derivation becomes `O(n^3)`. This makes
failing searches very inefficient because the whole search needs to be explored
to conclude that the goal cannot be derived.

In the above, we see that the second derivation is redundant, so we should thus
exclude it. We do this using the following `Hint Cut` declaration:

```coq
Global Hint Cut [_* persistent_separable and_persistent] : typeclass_instances.
```

This hint says that at any point during the instance search (`_*`), if
`persistent_separable` has been applied, the next instance to be applied should
**not** be `and_persistent`.

**Warning from the Coq reference manual:** The regexp matches the entire path.
Most hints will start with a leading `_*` to match the tail of the path.

The order matters. Having a cut for `[_* and_persistent persistent_separable]`
(i.e., excluding the first derivation) would result in incompleteness. It
become impossible to derive `Separable (P ∧ Q)` from `Persistent P` and
`Separable Q`.

Note that `Separable` is not closed under `∀`, but `Persistent` is. Hence we
should **not** have a cut `[_* persistent_separable forall_persistent]`. This
cut would make it impossible to derive `Separable (∀ x, Φ x)` from
`∀ x, Persistent (Φ x)`.

**General principle:** For any "class inheritance" instance `C1_C2` from `C1` to
`C2` and "class closed under connective" instance `op_C1` for `C1` such that
`C2` also has a closedness instance `op_C2` for the same connective, we cut
`[_* C1_C2 op_C1]`.

The principle also works when having chains of inheritance instances, e.g., `C1`
to `C2` to `C3`. It is important to not add instances for the transitive
inheritances, i.e., from `C1` to `C3`.

