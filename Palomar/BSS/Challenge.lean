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
# The sparsification theorem of Batson, Spielman and Srivastava: statement surface

This module is the *Challenge* of a Palomar submission: the small, auditable surface
carrying the advertised statements. It imports nothing beyond Mathlib, so every notion it
uses is either standard or written out here. The proofs live in `Palomar.BSS.Solution`,
which supplies them from the development in `Discretization/`; the `sorry`s below are the
placeholders required by that format.

## The mathematics

Let `(Ω, μ)` be a measure space and `a = (a_k)_{k ∈ ι}` a family of `m` square-integrable
functions whose Gram matrix `∫ a a* dμ` is the identity, that is an orthonormal family in
`L₂(μ)`. Sparsification asks for a few points of `Ω`, with weights, at which the family is
still nearly orthonormal: for every `n ≥ m` there are points `x₁, …, xₙ` and weights
`w₁, …, wₙ > 0` with

  `(1 - √((m-1)/n))² · 1  ≼  ∑ᵢ wᵢ a(xᵢ) a(xᵢ)*  ≼  (1 + √((m-1)/n))² · 1`

in the **Loewner order** `A ≼ B ↔ (B - A)` positive semidefinite.

For the counting measure on a finite set `Ω` this is the theorem for finitely many vectors:
if `v_k ∈ ℂ^m`, for `k ∈ Ω`, satisfy `∑_k v_k v_k* = 1`, then for every `n ≥ m` there are
weights `s_k ≥ 0`, at most `n` of them nonzero, with

  `(1 - √((m-1)/n))² · 1  ≼  ∑_k s_k v_k v_k*  ≼  (1 + √((m-1)/n))² · 1`.

The reweighted vectors are a spectral sparsifier of their sum.

The original theorem of Batson, Spielman and Srivastava has `√(m/n)` in place of
`√((m-1)/n)`; with `m - 1` in place of `m`, following Chkifa, Dolbeault, Krieg and Ullrich,
the statements here are slightly stronger.

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

variable {ι D : Type*} [MeasurableSpace D]

/-- The **Gram matrix** of a finite family of functions `a : D → ι → ℂ`, with entries
`∫ aₖ · conj aₗ dμ`.  In the notation of the paper this is `∫ a(x) a(x)* dμ(x)`. -/
noncomputable def gram (a : D → ι → ℂ) (μ : Measure D) : Matrix ι ι ℂ :=
  Matrix.of fun k l => ∫ x, a x k * star (a x l) ∂μ

end Gram

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Sparsification theorem** (Batson–Spielman–Srivastava).

Let `a` be a family of square-integrable functions indexed by a finite nonempty set `ι` of
`m` elements whose Gram matrix `∫ a a* dμ` is the identity.  Then for every `n ≥ m` there
are `n` points and positive weights with

`(1 - √((m-1)/n))² • 1 ≤ ∑ wᵢ a(xᵢ) a(xᵢ)* ≤ (1 + √((m-1)/n))² • 1`. -/
theorem bss [Nonempty ι] {a : Ω → ι → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ)
    (hgrama : gram a μ = 1) {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • vecMulVec (a (x i)) (star (a (x i)))
        ≤ (1 + Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ) :=
  sorry

omit [MeasurableSpace Ω] in
/-- **Sparsification theorem** (Batson–Spielman–Srivastava), for finitely many vectors.

Let `v_k ∈ ℂ^ι`, for `k` in a finite set `Ω`, be vectors with `∑ v_k v_k* = 1`, and let
`m = card ι` be the dimension.  Then for every `n ≥ m` there are weights `s_k ≥ 0`, at most
`n` of them nonzero, with

`(1 - √((m-1)/n))² • 1 ≤ ∑ s_k v_k v_k* ≤ (1 + √((m-1)/n))² • 1`. -/
theorem bss_of_sum_eq_one [Fintype Ω] [Nonempty ι] {v : Ω → ι → ℂ}
    (hv : ∑ k, vecMulVec (v k) (star (v k)) = 1) {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ s : Ω → ℝ, (∀ k, 0 ≤ s k) ∧ (Finset.univ.filter fun k => s k ≠ 0).card ≤ n ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ k, s k • vecMulVec (v k) (star (v k)) ∧
      ∑ k, s k • vecMulVec (v k) (star (v k))
        ≤ (1 + Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ) :=
  sorry

end Discretization
