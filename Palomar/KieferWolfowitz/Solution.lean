/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.KieferWolfowitz.PointCount
public import Discretization.UniformDiscretization

/-!
# The Kiefer–Wolfowitz theorem for sampling projections: proofs

This module is the *Solution* of a Palomar submission. Comparator checks that every
declaration named in `comparator.json` has, in this module's environment, exactly the same
name and type as its counterpart in `Palomar.KieferWolfowitz.Challenge`, and that it uses no
axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

Nothing is declared here. The advertised statements

* `Discretization.KieferWolfowitz.exists_design_kieferWolfowitz_card_le`:
  `|f(y)|² ≤ (m + ε) · ∑ₖ wₖ |f(xₖ)|²` for a design of at most `2m² + 1` points,
* `Discretization.KieferWolfowitz.exists_design_kieferWolfowitz_of_compact_card_le`: the
  same with the sharp constant `m` for continuous functions on a compact domain,
* `Discretization.exists_uniform_discretization`:
  `|f(y)|² ≤ (m + ε) / (1 - √((m-1)/n))² · ∑ᵢ wᵢ |f(xᵢ)|²` for `n ≥ m` points with positive
  weights,
* `Discretization.exists_uniform_discretization_of_compact`: the same with `m` in place of
  `m + ε` for continuous functions on a compact domain,

and the definition they rest on, `Discretization.KieferWolfowitz.designGram`, arrive through
the imports above, under their own names in the development: from
`Discretization/KieferWolfowitz/Design.lean`, `Discretization/KieferWolfowitz/MainTheorem.lean`,
`Discretization/KieferWolfowitz/Compact.lean`,
`Discretization/KieferWolfowitz/PointCount.lean` and
`Discretization/UniformDiscretization.lean`. The Challenge module restates exactly
those, which is why no wrapper is needed and why the names Palomar records are the names the
development actually uses.

The mathematics is the maximisation of a determinant. Among all finitely supported
probability measures one is chosen whose Gram matrix has an almost maximal determinant;
giving a further point `y` the weight `α` yields such a measure again, and the matrix
determinant lemma says exactly what that does to the determinant. Almost maximality bounds
that factor, and Bernoulli's inequality with the explicit weight `α = (t-m)/(2m(t-1))` turns
the bound into `t ≤ m + ε` for `t = a(y)* G⁻¹ a(y)`, uniformly in `y`. On a compact domain
the maximum is attained and the same argument gives `t ≤ m`. Carathéodory's theorem then
replaces any design by one with at most `2m² + 1` points and the same Gram matrix. For the
thinning to `n ≥ m` points the design is read as a probability measure on its index set, and
the lower half of the sparsification theorem picks `n` design points with
`(1 - √((m-1)/n))² • G ≤ ∑ᵢ wᵢ a(xᵢ) a(xᵢ)*`.
-/

@[expose] public section
