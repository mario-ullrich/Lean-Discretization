/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

/-!
# Palomar submissions

Root module of the `Palomar` library, which collects the submission surfaces for the
[Palomar registry](https://palomar-registry.org): one directory per registered result, each
holding a `Challenge` module (the audited statements), a `Solution` module (the proofs,
drawn from the development in `Discretization/` and `BasicResults/`), a `comparator.json`
and a `formalization.yaml`.

The `sorry`s in the `Challenge` modules are placeholders required by the submission format:
a Challenge advertises statements and imports only Mathlib, so that a reader can audit what
is claimed without reading the development. The mathematical development itself is
`sorry`-free.

A `Challenge` and its `Solution` are **separate roots**, never imported into one another or
into a common module: the Challenge repeats the definitions the statements rest on, while
the Solution receives the very same definitions through `Discretization`, so a shared
environment would see each of them twice. Comparator compiles the two against separate
environments for exactly this reason. Hence this module imports nothing, and the library is
built from the glob `Palomar.+`.

This library is deliberately absent from `defaultTargets`, so a plain `lake build` behaves
exactly as it does without it. Build these modules with `lake build Palomar`.

## Registered results

* `Palomar/BSS/`: the sparsification theorem of Batson, Spielman and Srivastava, the
  two-sided frame bound for a family whose Gram matrix is the identity and for finitely
  many vectors summing to the identity; advertising `Discretization.bss` and
  `Discretization.bss_of_sum_eq_one`.
* `Palomar/L2Discretization/`: the discretization theorem of Chkifa, Dolbeault, Krieg and
  Ullrich, for a finite second family and for a map into a separable Hilbert space, with
  the discretization of the `L₂`-norm it yields, for finite families and for a reproducing
  kernel Hilbert space; advertising `Discretization.bss_generalized`,
  `Discretization.exists_discretization`, `Discretization.Infinite.bss_generalized` and
  `Discretization.RKHS.exists_discretization`.
* `Palomar/OneSidedDiscretization/`: the `L₂` norm on a probability space bounded from below
  by the average of `n ≥ m` sample values; advertising
  `Discretization.bss_lower_equal_weights` and
  `Discretization.exists_one_sided_discretization`.
* `Palomar/KieferWolfowitz/`: the Kiefer–Wolfowitz theorem, with at most `2m² + 1` points
  for an `m`-dimensional space, on an arbitrary set and on a compact domain; advertising
  `Discretization.KieferWolfowitz.exists_optimal_design_card_le` and
  `Discretization.KieferWolfowitz.exists_optimal_design_of_compact_card_le`.
* `Palomar/UniformDiscretization/`: the uniform norm bounded by the discrete `ℓ₂` norm and
  by the largest of `n ≥ m` sample values, on an arbitrary set and on a compact domain;
  advertising `Discretization.exists_uniform_discretization_by_l2`,
  `Discretization.exists_uniform_discretization_of_compact_by_l2`,
  `Discretization.exists_uniform_discretization_by_max` and
  `Discretization.exists_uniform_discretization_of_compact_by_max`.
-/
