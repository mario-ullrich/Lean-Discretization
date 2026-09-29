/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.Matrix.Order

/-!
# The sparsification theorem of Batson, Spielman and Srivastava — statement surface

This module is the *Challenge* of a Palomar submission: the small, auditable surface
carrying the advertised statement. It imports nothing beyond Mathlib, and every notion it
uses is Mathlib's own, so no definition is restated. The proof lives in
`Palomar.BSS.Solution`, which supplies it from the development in `Discretization/`; the
`sorry` below is the placeholder required by that format.

## The mathematics

Let `v_y ∈ ℂ^m`, for `y` in a finite set `Ω`, be vectors with `∑_y v_y v_y* = 1`.
Sparsification asks for a few of them, reweighted, whose sum stays close to the identity:
for every `n ≥ m` there are weights `s_y ≥ 0`, at most `n` of them nonzero, with

  `(1 - √((m-1)/n))² · 1  ≼  ∑_y s_y v_y v_y*  ≼  (1 + √((m-1)/n))² · 1`

in the **Loewner order** `A ≼ B ↔ (B - A)` positive semidefinite. The reweighted vectors
are a spectral sparsifier of their sum.

The original theorem of Batson, Spielman and Srivastava has `√(m/n)` in place of
`√((m-1)/n)`, so for `n = d·m` the ratio of the upper to the lower constant, the condition
number, is `((√d + 1)/(√d - 1))²`. With `m - 1` in place of `m`, following Chkifa,
Dolbeault, Krieg and Ullrich, the statement here is slightly stronger.

The theorem carries the name it has in the development, so the name Palomar records is the
one a reader will find in the proof files.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]

/-- **Sparsification theorem** (Batson–Spielman–Srivastava), for finitely many vectors.

Let `v_y ∈ ℂ^ι`, for `y` in a finite set `Ω`, be vectors with `∑ v_y v_y* = 1`, and let
`m = card ι` be the dimension.  Then for every `n ≥ m` there are weights `s_y ≥ 0`, at most
`n` of them nonzero, with

`(1 - √((m-1)/n))² • 1 ≤ ∑ s_y v_y v_y* ≤ (1 + √((m-1)/n))² • 1`

in the Loewner order.  For `n = d·m` the ratio of the two constants is at most
`((√d + 1)/(√d - 1))²`. -/
theorem bss_of_sum_eq_one [Fintype Ω] [Nonempty ι] {v : Ω → ι → ℂ}
    (hv : ∑ y, vecMulVec (v y) (star (v y)) = 1) {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ s : Ω → ℝ, (∀ y, 0 ≤ s y) ∧ (Finset.univ.filter fun y => s y ≠ 0).card ≤ n ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ y, s y • vecMulVec (v y) (star (v y)) ∧
      ∑ y, s y • vecMulVec (v y) (star (v y))
        ≤ (1 + Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ) :=
  sorry

end Discretization
