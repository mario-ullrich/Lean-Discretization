/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.BothEdgeCases

/-!
# The sparsification theorem of Batson, Spielman and Srivastava

The case of a single family, `a = b`, of `Discretization.bss_generalized_of_gram_eq_one'`.
Then the Gram matrix `J` of the second family is the identity, `Λ = 1` bounds it, and the
effective dimension `M = Tr J / Λ` is the number `m = card ι` of functions.  Both frame
constants are therefore built from the same

`r = √((m-1)/n)`,

and the one weighted sum is squeezed between them:

`(1 - r)² • 1 ≤ ∑ wᵢ a(xᵢ) a(xᵢ)* ≤ (1 + r)² • 1`.

For `n = d·m` the ratio of the two constants is `((√d + 1)/(√d - 1))²`, which is the
condition number of the original theorem.  Taking `μ` the counting measure on a finite set
gives the statement for finitely many vectors that Batson, Spielman and Srivastava prove.

The result is `Discretization.bss`.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Sparsification theorem** (Batson–Spielman–Srivastava).

Let `a` be a family of square-integrable functions indexed by a finite nonempty set `ι` of
`m` elements whose Gram matrix `∫ a a* dμ` is the identity.  Then for every `n ≥ m` there
are `n` points and positive weights with

`(1 - √((m-1)/n))² • 1 ≤ ∑ wᵢ a(xᵢ) a(xᵢ)* ≤ (1 + √((m-1)/n))² • 1`.

Both bounds come from `Discretization.bss_generalized_of_gram_eq_one'` applied to the pair
`a = b`, where the effective dimension of the second family is its size `m`. -/
theorem bss [Nonempty ι] {a : Ω → ι → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ)
    (hgrama : gram a μ = 1) {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • vecMulVec (a (x i)) (star (a (x i)))
        ≤ (1 + Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ) := by
  -- the effective dimension of the identity is the number of functions
  have htr : RCLike.re (1 : Matrix ι ι ℂ).trace / (1 : ℝ) - 1
      = (Fintype.card ι : ℝ) - 1 := by
    rw [Matrix.trace_one]
    simp
  obtain ⟨x, w, hwpos, hlow, hup⟩ :=
    bss_generalized_of_gram_eq_one' (κ := ι) (b := a) Matrix.PosDef.one one_pos
      (by rw [one_smul]) ha ha hgrama hgrama hmn
  exact ⟨x, w, hwpos, hlow, by rwa [htr, mul_one] at hup⟩

end Discretization
