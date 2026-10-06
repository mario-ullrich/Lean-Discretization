/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# One-sided discretization of the `L₂` norm with equal weights: statement surface

This module is the *Challenge* of a Palomar submission: the small, auditable surface
carrying the advertised statements. It imports nothing beyond Mathlib, so every notion it
uses is either standard or written out here. The proofs live in
`Palomar.OneSidedDiscretization.Solution`, which supplies them from the development in
`Discretization/`; the `sorry`s below are the placeholders required by that format.

## The mathematics

Let `(Ω, μ)` be a probability space and `a = (aₖ)` a family of `m` square-integrable
functions on it with positive definite Gram matrix `I = ∫ a a* dμ`. Then for every `n ≥ m`
there are points `x₁, …, xₙ ∈ Ω`, not necessarily distinct, with

  `(1 - √((m-1)/n))² · I  ≼  (1/n) ∑ᵢ a(xᵢ) a(xᵢ)*`

in the **Loewner order** `A ≼ B ↔ (B - A)` positive semidefinite, that is

  `(1 - √((m-1)/n))² ∫ |f|² dμ  ≤  (1/n) ∑ᵢ |f(xᵢ)|²`

for every `f` in the span of the family. The `L₂` norm on an `m`-dimensional space of
functions is thus bounded from below by the plain average of `n` sample values, with an
explicit constant for every `n ≥ m` and no assumption on the space. Limonova and Temlyakov
prove such a bound for spaces satisfying a Nikol'skii-type inequality, and Bartel, Schäfer
and Ullrich for arbitrary spaces up to constants; the form here is Proposition 8 of Chkifa,
Dolbeault, Krieg and Ullrich for `p = 2`.

The proof is the lower half of the potential-function argument of Batson, Spielman and
Srivastava, with the constant `n` in place of the upper verifier. Each chosen point receives
a weight at most `1/n`, and raising every weight to `1/n` only enlarges the right-hand side.

## The definition restated here

* `Discretization.gram`: the Gram matrix `∫ a(x) a(x)* dμ(x)` of a finite family.

It is reproduced verbatim from the development, under the same name, so that Comparator
can match it against its counterpart there. The two theorems likewise carry the names they
have in the development, so the names Palomar records are the ones a reader will find in the
proof files.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

section Gram

variable {ι Ω : Type*} [MeasurableSpace Ω]

/-- The **Gram matrix** of a finite family of functions `a : Ω → ι → ℂ`, with entries
`∫ aₖ · conj aₗ dμ`.  In matrix notation this is `∫ a(x) a(x)* dμ(x)`. -/
noncomputable def gram (a : Ω → ι → ℂ) (μ : Measure Ω) : Matrix ι ι ℂ :=
  Matrix.of fun k l => ∫ x, a x k * star (a x l) ∂μ

end Gram

variable {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The lower half of the sparsification theorem with equal weights.**

Let `μ` be a probability measure and `a` a family of square-integrable functions indexed by a
finite nonempty set `ι` of `m` elements whose Gram matrix `I = ∫ a a* dμ` is positive
definite.  Then for every `n ≥ m` there are `n` points, not necessarily distinct, with

`(1 - √((m-1)/n))² • I ≤ (1/n) • ∑ᵢ a(xᵢ) a(xᵢ)*`. -/
theorem bss_lower_equal_weights [Fintype ι] [Nonempty ι] [IsProbabilityMeasure μ]
    {a : Ω → ι → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hI : (gram a μ).PosDef)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ x : Fin n → Ω, (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • gram a μ
      ≤ (1 / (n : ℝ)) • ∑ i, vecMulVec (a (x i)) (star (a (x i))) :=
  sorry

/-- **One-sided discretization of the `L₂`-norm**
(Chkifa–Dolbeault–Krieg–Ullrich, Proposition 8).

Let `μ` be a probability measure and `a` a family of square-integrable functions indexed by a
finite nonempty set `ι` of `m` elements with positive definite Gram matrix.  Then for every
`n ≥ m` there are `n` points, not necessarily distinct, with

`(1 - √((m-1)/n))² ∫ |f|² dμ ≤ (1/n) ∑ᵢ |f(xᵢ)|²`

for every function `f(y) = ⟪c, a(y)⟫` in the span. -/
theorem exists_one_sided_discretization [Fintype ι] [Nonempty ι] [IsProbabilityMeasure μ]
    {a : Ω → ι → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hI : (gram a μ).PosDef)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ x : Fin n → Ω, ∀ c : ι → ℂ,
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 * ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ
        ≤ 1 / (n : ℝ) * ∑ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2 :=
  sorry

end Discretization
