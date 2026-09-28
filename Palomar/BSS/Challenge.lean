/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The sparsification theorem of Batson, Spielman and Srivastava — statement surface

This module is the *Challenge* of a Palomar submission: the small, auditable surface
carrying the advertised statement. It imports nothing beyond Mathlib, so every notion it
uses is either standard or written out here. The proof lives in `Palomar.BSS.Solution`,
which supplies it from the development in `Discretization/`; the `sorry` below is the
placeholder required by that format.

## The mathematics

Let `a = (aₖ)` be `m` square-integrable functions on a measure space `(Ω, μ)` whose Gram
matrix `∫ a a* dμ` is the identity. Sparsification asks for a few point evaluations that
reproduce that identity up to a small distortion: for every `n ≥ m` there are `n` points
`x₁, …, xₙ` and positive weights `w₁, …, wₙ` with

  `(1 - √((m-1)/n))² · 1  ≼  ∑ᵢ wᵢ a(xᵢ) a(xᵢ)*  ≼  (1 + √((m-1)/n))² · 1`

in the **Loewner order** `A ≼ B ↔ (B - A)` positive semidefinite. Written for functions,
the same statement says that `∑ᵢ wᵢ |f(xᵢ)|²` stays within those two factors of
`∫ |f|² dμ` for every `f` in the span.

For `n = d·m` the ratio of the two constants is `((√d + 1)/(√d - 1))²`, the condition
number of the original theorem. Taking `μ` the counting measure on a finite set gives the
statement for finitely many vectors that Batson, Spielman and Srivastava prove: a
reweighted subset of `n` of the vectors is a spectral sparsifier of their sum.

The formalisation states this over an arbitrary measure space, which covers both the
finite case and families indexed by a continuum.

## The definition restated here

* `Discretization.gram` — the Gram matrix `∫ a(x) a(x)* dμ(x)` of a finite family.

It is reproduced verbatim from the development, under the same name, so that Comparator can
match it against its counterpart there. The theorem likewise carries the name it has in the
development, so the name Palomar records is the one a reader will find in the proof files.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

section Gram

variable {ι D : Type*} [MeasurableSpace D]

/-- The **Gram matrix** of a finite family of functions `a : D → ι → ℂ`, with entries
`∫ aₖ · conj aₗ dμ`.  In the notation of the paper this is `∫ a(x) a(x)* dμ(x)`. -/
noncomputable def gram (a : D → ι → ℂ) (μ : Measure D) : Matrix ι ι ℂ :=
  Matrix.of fun k l => ∫ x, a x k * star (a x l) ∂μ

end Gram

section Sparsification

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Sparsification theorem** (Batson–Spielman–Srivastava).

Let `a` be a family of square-integrable functions indexed by a finite nonempty set `ι` of
`m` elements whose Gram matrix `∫ a a* dμ` is the identity.  Then for every `n ≥ m` there
are `n` points and positive weights with

`(1 - √((m-1)/n))² • 1 ≤ ∑ wᵢ a(xᵢ) a(xᵢ)* ≤ (1 + √((m-1)/n))² • 1`

in the Loewner order.  For `n = d·m` the ratio of the two constants is
`((√d + 1)/(√d - 1))²`. -/
theorem bss [Nonempty ι] {a : Ω → ι → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ)
    (hgrama : gram a μ = 1) {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • vecMulVec (a (x i)) (star (a (x i)))
        ≤ (1 + Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ) :=
  sorry

end Sparsification

end Discretization
