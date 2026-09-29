/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.EdgeCases.BothEdgeCases

/-!
# The sparsification theorem of Batson, Spielman and Srivastava

The case of a single family, `a = b`, of `Discretization.bss_generalized_of_gram_eq_one'`.
Then the Gram matrix `J` of the second family is the identity, `Λ = 1` bounds it, and the
effective dimension `M = Tr J / Λ` is the number `m = card ι` of functions.  Both frame
constants are therefore built from the same

`r = √((m-1)/n)`,

and the one weighted sum is squeezed between them:

`(1 - r)² • 1 ≤ ∑ wᵢ a(xᵢ) a(xᵢ)* ≤ (1 + r)² • 1`.

The original theorem of Batson, Spielman and Srivastava has `√(m/n)` in place of `r`, so
for `n = d·m` the ratio of the upper to the lower constant, the condition number, is
`((√d + 1)/(√d - 1))²`.  With `m - 1` in place of `m`, following Chkifa, Dolbeault, Krieg
and Ullrich, the statement here is slightly stronger.

The result is `Discretization.bss`.  Taking `μ` the counting measure on a finite set gives
the statement for finitely many vectors that Batson, Spielman and Srivastava prove: for
vectors `v_y` with `∑ v_y v_y* = 1` there are weights `s_y ≥ 0`, at most `n` of them
nonzero, squeezed between the same two constants
(`Discretization.bss_of_sum_eq_one`).  A vector chosen several times receives the sum of
its weights (`Discretization.sum_fiberwise_smul`).
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

/-! ### Finitely many vectors -/

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] in
/-- **Merging repeated points.**  If a point is chosen several times, its weights add up:
with `s(y) = ∑_{xᵢ = y} wᵢ`, the weighted sum over the chosen points is the weighted sum
over `Ω`. -/
theorem sum_fiberwise_smul [Fintype Ω] [DecidableEq Ω] {M : Type*} [AddCommMonoid M]
    [Module ℝ M] {n : ℕ} (x : Fin n → Ω) (w : Fin n → ℝ) (R : Ω → M) :
    ∑ y, (∑ i ∈ Finset.univ.filter (fun i => x i = y), w i) • R y = ∑ i, w i • R (x i) := by
  simp_rw [Finset.sum_smul]
  rw [← Finset.sum_fiberwise Finset.univ x (fun i => w i • R (x i))]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.1 hi).2]

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] in
/-- After merging, at most `n` of the weights are nonzero: a nonzero merged weight belongs
to a point that was chosen. -/
theorem card_filter_sum_fiberwise_ne_zero_le [Fintype Ω] [DecidableEq Ω] {n : ℕ}
    (x : Fin n → Ω) (w : Fin n → ℝ) :
    (Finset.univ.filter fun y => (∑ i ∈ Finset.univ.filter (fun i => x i = y), w i) ≠ 0).card
      ≤ n := by
  have hsub : (Finset.univ.filter
      fun y => (∑ i ∈ Finset.univ.filter (fun i => x i = y), w i) ≠ 0)
      ⊆ Finset.univ.image x := by
    intro y hy
    obtain ⟨i, hi, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Finset.mem_filter.1 hy).2
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩
  calc _ ≤ (Finset.univ.image x).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := by simp

omit [MeasurableSpace Ω] in
/-- **Sparsification theorem** (Batson–Spielman–Srivastava), for finitely many vectors.

Let `v_y ∈ ℂ^ι`, for `y` in a finite set `Ω`, be vectors with `∑ v_y v_y* = 1`, and let
`m = card ι` be the dimension.  Then for every `n ≥ m` there are weights `s_y ≥ 0`, at most
`n` of them nonzero, with

`(1 - √((m-1)/n))² • 1 ≤ ∑ s_y v_y v_y* ≤ (1 + √((m-1)/n))² • 1`.

This is `Discretization.bss` for the counting measure on `Ω`, whose Gram matrix is
`∑ v_y v_y*` (`Discretization.gram_count`); a vector chosen several times receives the sum
of its weights. -/
theorem bss_of_sum_eq_one [Fintype Ω] [Nonempty ι] {v : Ω → ι → ℂ}
    (hv : ∑ y, vecMulVec (v y) (star (v y)) = 1) {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ s : Ω → ℝ, (∀ y, 0 ≤ s y) ∧ (Finset.univ.filter fun y => s y ≠ 0).card ≤ n ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ y, s y • vecMulVec (v y) (star (v y)) ∧
      ∑ y, s y • vecMulVec (v y) (star (v y))
        ≤ (1 + Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ) := by
  classical
  let _ : MeasurableSpace Ω := ⊤
  -- the counting measure turns the sum into a Gram matrix
  have hgram : gram v Measure.count = 1 := by rw [gram_count, hv]
  obtain ⟨x, w, hw, hlow, hup⟩ :=
    bss (μ := Measure.count) (fun _ => MemLp.of_discrete) hgram hmn
  -- a vector chosen several times receives the sum of its weights
  have hmerge := sum_fiberwise_smul x w (fun y => vecMulVec (v y) (star (v y)))
  exact ⟨fun y => ∑ i ∈ Finset.univ.filter (fun i => x i = y), w i,
    fun y => Finset.sum_nonneg fun i _ => (hw i).le, card_filter_sum_fiberwise_ne_zero_le x w,
    hlow.trans_eq hmerge.symm, hmerge.trans_le hup⟩

end Discretization
