/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.BothEdgeCases
import Discretization.Infinite.CardOne
import Discretization.Infinite.SmallEffectiveDim

/-!
# A single function and a small effective dimension, with a countable second family

The two edge cases of the previous files at the same time, for a second family given by a
square-integrable map `b : Ω → H`: `card ι = 1`, so that the lower potential is not needed,
and `M = Tr J / Λ ≤ 1 + 1/n`, so that the upper potential is not needed either.  Both
verifiers are constants,

`L(x) = n |a(x)|²`   and   `U(x) = n ‖b(x)‖² / Tr J`,   with   `∫ L dμ = ∫ U dμ = n`,

and a single admissible point `y`, used `n` times with the weight `w = 1 / L(y)`, does
everything.  There is no induction, and the point comes from the finite lemma
`Discretization.exists_admissible_point_of_unique_of_small_dim`, which consumes the second
family only through `U`.

With it the four cases are complete, and a case distinction on `m ≥ 2` and on `M ≥ 1 + 1/n`
assembles them into `Discretization.Infinite.bss_generalized_of_gram_eq_one'`, the theorem
for a countable second family with no side condition beyond `n ≥ m`.
-/

open MeasureTheory
open scoped InnerProductSpace ComplexOrder MatrixOrder
open InnerProductSpace
open ContinuousLinearMap

namespace Discretization

namespace Infinite

variable {ι κ Ω H : Type*} [DecidableEq ι] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] [MeasurableSpace Ω] {μ : Measure Ω}
  {e : HilbertBasis κ ℂ H} {J : H →L[ℂ] H}

/-! ### The theorem for a single function and a small effective dimension -/

/-- **Generalized sparsification theorem for a one-element first family, a small effective
dimension and a countable second family.**

For `card ι = 1` and `M = Tr J / Λ ≤ 1 + 1/n` neither potential is needed: one point, used
`n` times, makes the lower frame bound the identity `1 = (1 - √((m-1)/n))²` and leaves the
upper one to the crude estimate `b b* ≼ ‖b‖² • 1`. -/
theorem bss_generalized_of_unique_of_small_dim [Unique ι] [Nonempty κ] [Countable κ]
    (hJ : IsFiniteTracePos e J) {Λ : ℝ} (hΛ : 0 < Λ) {a : Ω → ι → ℂ} {b : Ω → H}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : MemLp b 2 μ) (hgrama : gram a μ = 1)
    (hgramb : ∀ u, RCLike.re ⟪u, J u⟫_ℂ = ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ)
    {n : ℕ} (hn : 0 < n) (hMlt : traceAlong e J / Λ ≤ 1 + 1 / (n : ℝ)) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 : Matrix ι ι ℂ) ≤ ∑ i, w i • Matrix.vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
        ≤ ((1 + Real.sqrt ((traceAlong e J / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : H →L[ℂ] H) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hT0 : 0 < traceAlong e J := hJ.traceAlong_pos
  -- one point, admissible for both constant verifiers
  obtain ⟨y, hUL, hLpos⟩ :=
    exists_admissible_point_of_unique_of_small_dim ha hgrama
      (U := fun y => (n : ℝ) / traceAlong e J * ‖b y‖ ^ 2)
      (fun y => upperVerifierConst_nonneg (div_nonneg (by positivity) hT0.le) y)
      (integrable_upperVerifierConst hb _) hn0
      (integral_upperVerifierConst hJ hb hgramb n)
  refine ⟨fun _ => y, fun _ => 1 / ((n : ℝ) * ‖a y default‖ ^ 2),
    fun _ => one_div_pos.2 hLpos, ?_, ?_⟩
  · -- the lower frame bound is an identity, each point contributing exactly `1/n`
    exact le_of_eq (sum_smul_vecMulVec_eq_one hn0 _ _
      fun _ => one_div_mul_cancel hLpos.ne').symm
  · -- the weight allowed by the constant upper verifier
    have hweight : ∀ _i : Fin n, 1 / ((n : ℝ) * ‖a y default‖ ^ 2) * ‖b y‖ ^ 2
        ≤ traceAlong e J / n := by
      intro _i
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hLpos hn0]
      have h1 := mul_le_mul_of_nonneg_left hUL hT0.le
      have h2 : traceAlong e J * ((n : ℝ) / traceAlong e J * ‖b y‖ ^ 2)
          = ‖b y‖ ^ 2 * n := by field_simp
      linarith [h2 ▸ h1]
    -- and the crude rank-one estimate
    have hTΛ : traceAlong e J
        ≤ (1 + Real.sqrt ((traceAlong e J / Λ - 1) / n)) ^ 2 * Λ :=
      le_sq_one_add_sqrt_div_mul hn0 hΛ hMlt
    exact (sum_smul_rankOne_le_smul_one hn0 (fun _ => y) _
      (fun _ => (one_div_pos.2 hLpos).le) hweight).trans
      (smul_le_smul_of_nonneg_right hTΛ zero_le_one)

/-! ### The theorem without side conditions -/

/-- **Generalized sparsification theorem for a normalized first family and a countable
second family**, with no side condition beyond `n ≥ m`.

The potential argument of `Discretization.Infinite.bss_generalized_of_gram_eq_one` needs
`m ≥ 2` and `M ≥ 1 + 1/n`.  A case distinction on those two conditions hands the remaining
cases to `Discretization.Infinite.bss_generalized_of_unique`,
`Discretization.Infinite.bss_generalized_of_small_dim` and
`Discretization.Infinite.bss_generalized_of_unique_of_small_dim`.  For `m = 1` the lower
frame constant `(1 - √((m-1)/n))²` is `1`, which is what those two theorems state. -/
theorem bss_generalized_of_gram_eq_one' [Fintype ι] [Nonempty ι] [Nonempty κ] [Countable κ]
    (hJ : IsFiniteTracePos e J) {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : J ≤ Λ • (1 : H →L[ℂ] H)) {a : Ω → ι → ℂ} {b : Ω → H}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : MemLp b 2 μ) (hgrama : gram a μ = 1)
    (hgramb : ∀ u, RCLike.re ⟪u, J u⟫_ℂ = ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ i, w i • Matrix.vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
        ≤ ((1 + Real.sqrt ((traceAlong e J / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : H →L[ℂ] H) := by
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hn : 0 < n := lt_of_lt_of_le hcard hmn
  by_cases hM : 1 + 1 / (n : ℝ) ≤ traceAlong e J / Λ
  · by_cases hm : 2 ≤ Fintype.card ι
    · exact bss_generalized_of_gram_eq_one hJ hΛ hJΛ ha hb hgrama hgramb hm hmn hM
    · -- a single function, with the effective dimension in the regular range
      have hcard1 : Fintype.card ι = 1 := by omega
      rw [sq_one_sub_sqrt_div_card_eq_one hcard1, one_smul]
      have : Unique ι := (Fintype.card_eq_one_iff_nonempty_unique.1 hcard1).some
      exact bss_generalized_of_unique hJ hΛ hJΛ ha hb hgrama hgramb hn hM
  · replace hM := (not_le.mp hM).le
    by_cases hm : 2 ≤ Fintype.card ι
    · exact bss_generalized_of_small_dim hJ hΛ ha hb hgrama hgramb hm hmn hM
    · -- a single function and a small effective dimension
      have hcard1 : Fintype.card ι = 1 := by omega
      rw [sq_one_sub_sqrt_div_card_eq_one hcard1, one_smul]
      have : Unique ι := (Fintype.card_eq_one_iff_nonempty_unique.1 hcard1).some
      exact bss_generalized_of_unique_of_small_dim hJ hΛ ha hb hgrama hgramb hn hM

end Infinite

end Discretization
