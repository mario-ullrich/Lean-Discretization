/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Topology.Compactness.Compact

/-!
# Discretization of the uniform norm with `n ≥ m` points: statement surface

This module is the *Challenge* of a Palomar submission: the small, auditable surface
carrying the advertised statements. It imports nothing beyond Mathlib, and every notion it
uses is Mathlib's own, so no definition is restated. The proofs live in
`Palomar.UniformDiscretization.Solution`, which supplies them from the development in
`Discretization/`; the `sorry`s below are the placeholders required by that format.

## The mathematics

Let `Ω` be an arbitrary set and let `a₁, …, a_m` be linearly independent bounded functions
on it, spanning an `m`-dimensional space `V`. The question is how many function values
control the uniform norm on `V`. The answer here is that for every `ε > 0` and every `n ≥ m`
there are points `x₁, …, xₙ ∈ Ω`, not necessarily distinct, with

  `|f(y)|² ≤ (m + ε) / (1 - √((m-1)/n))² · (1/n) ∑ᵢ |f(xᵢ)|²`

for every point `y ∈ Ω` and every `f ∈ V`: the uniform norm is dominated by the discrete
`ℓ₂` norm of the `n` sample values. This is Proposition 8 of Chkifa, Dolbeault, Krieg and
Ullrich for `p = ∞`. An average is at most its largest term, so the same points give

  `|f(y)|² ≤ (m + ε) / (1 - √((m-1)/n))² · maxᵢ |f(xᵢ)|²`.

On a compact domain and for continuous functions both hold with `ε = 0`.

For `n = 2m` one has `√((m-1)/n) < 1/√2`, so the first bound gives
`‖f‖_∞ ≤ (1 + √2) √(1 + ε/m) (∑ᵢ |f(xᵢ)|²)^{1/2}`, where Theorem 2 of Krieg, Pozharska,
Ullrich and Ullrich has the constant `42`, and the second gives
`‖f‖_∞ ≤ (2 + √2) √(m + ε) maxᵢ |f(xᵢ)|`. For `n = m` points Novak obtains a bound of the
second kind, `‖f‖_∞ ≤ (m + ε) maxᵢ |f(xᵢ)|`, from a form of Auerbach's lemma.

The proof takes a measure from the theorem of Kiefer and Wolfowitz, a finitely supported
probability measure `ϱ` with `|f(y)|² ≤ (m + ε) ∫ |f|² dϱ`, and thins it to `n` of its
points by a one-sided discretization of the `L₂(ϱ)` norm with equal weights,
`(1 - √((m-1)/n))² ∫ |f|² dϱ ≤ (1/n) ∑ᵢ |f(xᵢ)|²`.

Linear independence is stated as "`⟪c, a(y)⟫ = 0` for every `y` only for `c = 0`", the
functions of the span are `f(y) = ⟪c, a(y)⟫`, and the maximum over the `n` points is the
supremum `⨆ i` over `Fin n`. The four theorems carry the names they have in the
development, so the names Palomar records are the ones a reader will find in the proof
files.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace Discretization

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The discrete `ℓ₂` norm of the sample values -/

/-- **Discretization of the uniform norm with `n ≥ m` points, by the discrete `ℓ₂` norm.**

For linearly independent bounded functions `a₁, …, a_m` on an arbitrary set, every `ε > 0`
and every `n ≥ m` there are `n` points, not necessarily distinct, such that

`|f(y)|² ≤ (m + ε) / (1 - √((m-1)/n))² · (1/n) ∑ᵢ |f(xᵢ)|²`

for every point `y` and every function `f(y) = ⟪c, a(y)⟫` in the span.  This is
Proposition 8 of Chkifa, Dolbeault, Krieg and Ullrich for `p = ∞`. -/
theorem exists_uniform_discretization_by_l2 [Nonempty ι] (a : Ω → ι → ℂ) {C : ℝ}
    (hC : ∀ y i, ‖a y i‖ ≤ C) (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ x : Fin n → Ω, ∀ (c : ι → ℂ) (y : Ω),
      ‖star c ⬝ᵥ a y‖ ^ 2 ≤ (Fintype.card ι + ε) / (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
        * (1 / (n : ℝ) * ∑ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2) :=
  sorry

/-- **Discretization of the uniform norm with `n ≥ m` points on a compact domain, by the
discrete `ℓ₂` norm.**

For linearly independent continuous functions `a₁, …, a_m` on a compact space and every
`n ≥ m` there are `n` points, not necessarily distinct, such that

`|f(y)|² ≤ m / (1 - √((m-1)/n))² · (1/n) ∑ᵢ |f(xᵢ)|²`

for every point `y` and every `f` in the span: the bound above with `ε = 0`. -/
theorem exists_uniform_discretization_of_compact_by_l2 [Nonempty ι]
    [TopologicalSpace Ω] [CompactSpace Ω] (a : Ω → ι → ℂ)
    (hcont : ∀ i, Continuous fun y => a y i)
    (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0) {n : ℕ}
    (hmn : Fintype.card ι ≤ n) :
    ∃ x : Fin n → Ω, ∀ (c : ι → ℂ) (y : Ω),
      ‖star c ⬝ᵥ a y‖ ^ 2 ≤ Fintype.card ι / (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
        * (1 / (n : ℝ) * ∑ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2) :=
  sorry

/-! ### The largest sample value -/

/-- **The uniform norm by the largest sample value.**

For linearly independent bounded functions `a₁, …, a_m` on an arbitrary set, every `ε > 0`
and every `n ≥ m` there are `n` points, not necessarily distinct, such that

`|f(y)|² ≤ (m + ε) / (1 - √((m-1)/n))² · maxᵢ |f(xᵢ)|²`

for every point `y` and every function `f(y) = ⟪c, a(y)⟫` in the span.  For `n = 2m` this is
`‖f‖_∞ ≤ (2 + √2) √(m + ε) maxᵢ |f(xᵢ)|`. -/
theorem exists_uniform_discretization_by_max [Nonempty ι] (a : Ω → ι → ℂ) {C : ℝ}
    (hC : ∀ y i, ‖a y i‖ ≤ C) (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ x : Fin n → Ω, ∀ (c : ι → ℂ) (y : Ω),
      ‖star c ⬝ᵥ a y‖ ^ 2 ≤ (Fintype.card ι + ε) / (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
        * ⨆ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2 :=
  sorry

/-- **The uniform norm by the largest sample value on a compact domain.**

For linearly independent continuous functions `a₁, …, a_m` on a compact space and every
`n ≥ m` there are `n` points, not necessarily distinct, such that

`|f(y)|² ≤ m / (1 - √((m-1)/n))² · maxᵢ |f(xᵢ)|²`

for every point `y` and every `f` in the span: the bound above with `ε = 0`. -/
theorem exists_uniform_discretization_of_compact_by_max [Nonempty ι]
    [TopologicalSpace Ω] [CompactSpace Ω] (a : Ω → ι → ℂ)
    (hcont : ∀ i, Continuous fun y => a y i)
    (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0) {n : ℕ}
    (hmn : Fintype.card ι ≤ n) :
    ∃ x : Fin n → Ω, ∀ (c : ι → ℂ) (y : Ω),
      ‖star c ⬝ᵥ a y‖ ^ 2 ≤ Fintype.card ι / (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
        * ⨆ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2 :=
  sorry

end Discretization
