/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.UniformDiscretization

/-!
# Discretization of the uniform norm with `n ≥ m` points: proofs

This module is the *Solution* of a Palomar submission. Comparator checks that every
declaration named in `comparator.json` has, in this module's environment, exactly the same
name and type as its counterpart in `Palomar.UniformDiscretization.Challenge`, and that it
uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

Nothing is declared here. The advertised statements

* `Discretization.exists_uniform_discretization_by_l2`:
  `|f(y)|² ≤ (m + ε) / (1 - √((m-1)/n))² · (1/n) ∑ᵢ |f(xᵢ)|²` for `n ≥ m` points,
* `Discretization.exists_uniform_discretization_of_compact_by_l2`: the same with `ε = 0` for
  continuous functions on a compact domain,
* `Discretization.exists_uniform_discretization_by_max`: the same with `maxᵢ |f(xᵢ)|²` in
  place of the average,
* `Discretization.exists_uniform_discretization_of_compact_by_max`: that bound with `ε = 0`
  on a compact domain,

arrive through the import above, under their own names in the development, from
`Discretization/UniformDiscretization.lean`. They use only Mathlib's notions, so the
Challenge module restates no definition, which is why no wrapper is needed and why the
names Palomar records are the names the development actually uses.

The proof takes the design of the Kiefer–Wolfowitz theorem, points with weights summing to
one for which `|f(y)|² ≤ (m + ε) ∑ₖ wₖ |f(xₖ)|²`, and reads it as a probability measure on
its index set. The one-sided discretization with equal weights, the lower half of the
potential-function argument of Batson, Spielman and Srivastava in the form of Chkifa,
Dolbeault, Krieg and Ullrich, picks `n` of the design points with
`(1 - √((m-1)/n))² ∑ₖ wₖ |f(xₖ)|² ≤ (1/n) ∑ᵢ |f(xᵢ)|²`, and `√((m-1)/n) < 1` because
`n ≥ m`. The form with the maximum follows because an average is at most its largest term
(`Discretization.inv_mul_sum_le_iSup`).
-/

@[expose] public section
