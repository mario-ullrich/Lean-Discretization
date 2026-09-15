/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.SmallEffectiveDim
import Discretization.Infinite.MainTheorem

/-!
# A small effective dimension, with a countable second family

The edge case `M = Tr J / Λ ≤ 1 + 1/n` of `Discretization.SmallEffectiveDim`, for a second
family given by a square-integrable map `b : Ω → H`.  As in finite dimension the upper
potential is not needed: a constant upper verifier does the job,

`U(x) = n ‖b(x)‖² / Tr J`,   with   `∫ U dμ = n`.

That its average is `n` is the finite-trace assumption of the paper in integral form,
`∫ ‖b‖² dμ = Tr J` (`Discretization.Infinite.integral_norm_sq_eq_traceAlong`), which is the
average of a quadratic form with `Q = 1`.

The lower half of the argument is the finite one verbatim: the induction
`Discretization.exists_points_weights_of_small_dim` consumes the second family only through
`U`, so the same lemma serves here.  The weights it produces satisfy `wᵢ U(xᵢ) ≤ 1`, that is
`wᵢ ‖b(xᵢ)‖² ≤ Tr J / n`, and summing over the `n` points with the crude bound
`b b* ≼ ‖b‖² • 1` (`ContinuousLinearMap.rankOne_le_norm_sq_smul_one`) gives

`∑ wᵢ b(xᵢ) b(xᵢ)* ≼ Tr J • 1 = M Λ • 1 ≼ (1 + s)² Λ • 1`,

the last step because `M ≤ 1 + 1/n` forces `M ≤ (1 + s)²`.  The read-off is
`Discretization.Infinite.sum_smul_rankOne_le_smul_one`, and the result is
`Discretization.Infinite.bss_generalized_of_small_dim`.
-/

open MeasureTheory
open scoped InnerProductSpace ComplexOrder MatrixOrder
open InnerProductSpace
open ContinuousLinearMap

namespace Discretization

namespace Infinite

variable {ι κ Ω H : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] [MeasurableSpace Ω] {μ : Measure Ω}
  {e : HilbertBasis κ ℂ H} {J : H →L[ℂ] H}

/-! ### The trace as an average -/

/-- **The trace of the Gram operator is the average of `‖b‖²`**, `∫ ‖b x‖² dμ(x) = Tr J`.

This is `ContinuousLinearMap.integral_re_inner_apply` with `Q = 1`, and it is the form in
which the finite-trace assumption of the paper is used here. -/
theorem integral_norm_sq_eq_traceAlong [Countable κ] (hJ : IsFiniteTracePos e J) {b : Ω → H}
    (hb : MemLp b 2 μ)
    (hgramb : ∀ u, RCLike.re ⟪u, J u⟫_ℂ = ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ) :
    ∫ x, ‖b x‖ ^ 2 ∂μ = traceAlong e J := by
  have h1 := integral_re_inner_apply e hJ.nonneg zero_le_one hJ.summableTrace hb hgramb
  rw [mul_one] at h1
  rw [← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ‖b x‖ ^ 2 = RCLike.re ⟪b x, b x⟫_ℂ
  exact (inner_self_eq_norm_sq (b x)).symm

/-! ### The constant upper verifier -/

omit [InnerProductSpace ℂ H] [CompleteSpace H] [MeasurableSpace Ω] in
/-- The constant upper verifier is nonnegative. -/
theorem upperVerifierConst_nonneg {b : Ω → H} {c : ℝ} (hc : 0 ≤ c) (y : Ω) :
    0 ≤ c * ‖b y‖ ^ 2 :=
  mul_nonneg hc (by positivity)

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- The constant upper verifier is integrable. -/
theorem integrable_upperVerifierConst {b : Ω → H} (hb : MemLp b 2 μ) (c : ℝ) :
    Integrable (fun x => c * ‖b x‖ ^ 2) μ :=
  hb.norm.integrable_sq.const_mul _

/-- The average of the constant upper verifier is `n`. -/
theorem integral_upperVerifierConst [Nonempty κ] [Countable κ] (hJ : IsFiniteTracePos e J)
    {b : Ω → H} (hb : MemLp b 2 μ)
    (hgramb : ∀ u, RCLike.re ⟪u, J u⟫_ℂ = ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ) (n : ℕ) :
    ∫ x, (n : ℝ) / traceAlong e J * ‖b x‖ ^ 2 ∂μ = n := by
  have hT0 : 0 < traceAlong e J := hJ.traceAlong_pos
  rw [integral_const_mul, integral_norm_sq_eq_traceAlong hJ hb hgramb]
  field_simp

/-! ### The crude upper frame bound -/

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] in
/-- **The upper frame bound from a bound on the weights.**  If every weight satisfies
`wᵢ ‖b(xᵢ)‖² ≤ T / n`, then the `n` rank-one operators add up to at most `T • 1`.

Each summand is below `wᵢ ‖b(xᵢ)‖² • 1` by
`ContinuousLinearMap.rankOne_le_norm_sq_smul_one`, and the `n` bounds add up to `T`.  This is
the operator counterpart of `Discretization.sum_smul_vecMulVec_le_smul_one`. -/
theorem sum_smul_rankOne_le_smul_one {T : ℝ} {n : ℕ} (hn0 : (0 : ℝ) < n) {b : Ω → H}
    (x : Fin n → Ω) (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw : ∀ i, w i * ‖b (x i)‖ ^ 2 ≤ T / n) :
    ∑ i, w i • rankOne ℂ (b (x i)) (b (x i)) ≤ T • (1 : H →L[ℂ] H) := by
  have hstep : ∀ i : Fin n, w i • rankOne ℂ (b (x i)) (b (x i))
      ≤ (w i * ‖b (x i)‖ ^ 2) • (1 : H →L[ℂ] H) := by
    intro i
    have h1 := smul_le_smul_of_nonneg_left (rankOne_le_norm_sq_smul_one (b (x i))) (hw0 i)
    rwa [smul_smul] at h1
  have hsum : ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
      ≤ (∑ i, w i * ‖b (x i)‖ ^ 2) • (1 : H →L[ℂ] H) := by
    rw [Finset.sum_smul]
    exact Finset.sum_le_sum fun i _ => hstep i
  have hTsum : ∑ i : Fin n, w i * ‖b (x i)‖ ^ 2 ≤ T := by
    calc ∑ i : Fin n, w i * ‖b (x i)‖ ^ 2 ≤ ∑ _i : Fin n, T / n :=
          Finset.sum_le_sum fun i _ => hw i
      _ = T := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  exact hsum.trans (smul_le_smul_of_nonneg_right hTsum zero_le_one)

/-! ### The theorem for a small effective dimension -/

/-- **Generalized sparsification theorem for a small effective dimension and a countable
second family.**

For `M = Tr J / Λ ≤ 1 + 1/n` the upper frame bound follows from the crude estimate
`b b* ≼ ‖b‖² • 1` alone; the first family still needs `m ≥ 2`.  Together with
`Discretization.Infinite.bss_generalized_of_gram_eq_one`, which needs `M ≥ 1 + 1/n`, every
effective dimension is covered. -/
theorem bss_generalized_of_small_dim [Nonempty ι] [Nonempty κ] [Countable κ]
    (hJ : IsFiniteTracePos e J) {Λ : ℝ} (hΛ : 0 < Λ) {a : Ω → ι → ℂ} {b : Ω → H}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : MemLp b 2 μ) (hgrama : gram a μ = 1)
    (hgramb : ∀ u, RCLike.re ⟪u, J u⟫_ℂ = ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ)
    {n : ℕ} (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ n)
    (hMlt : traceAlong e J / Λ ≤ 1 + 1 / (n : ℝ)) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ i, w i • Matrix.vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
        ≤ ((1 + Real.sqrt ((traceAlong e J / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : H →L[ℂ] H) := by
  -- the parameters of the lower half of the construction
  have hn0 : (0 : ℝ) < n := by
    have h : 0 < n := lt_of_lt_of_le (by norm_num) (le_trans hm hmn)
    exact_mod_cast h
  have hn : 0 < n := by exact_mod_cast hn0
  have hT0 : 0 < traceAlong e J := hJ.traceAlong_pos
  set m : ℝ := (Fintype.card ι : ℝ) with hmdef
  have hm2 : (2 : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hm
  have hmn' : m ≤ (n : ℝ) := by rw [hmdef]; exact_mod_cast hmn
  set r : ℝ := Real.sqrt ((m - 1) / n) with hrdef
  have hr0 : 0 < r := sqrt_div_pos hn0 (by linarith)
  have hr1 : r < 1 := sqrt_div_lt_one hn0 hmn'
  have hm_eq : m = (n : ℝ) * r ^ 2 + 1 := eq_mul_sq_sqrt_div_add_one hn0 (by linarith)
  set δ : ℝ := (1 - r) / n with hδdef
  have hδ0 : 0 < δ := div_pos (by linarith) hn0
  clear_value m r
  set c₀ : ℝ := δ * m / r with hc₀def
  have hc₀0 : 0 < c₀ := div_pos (by positivity) hr0
  have hA₀ : (c₀ • (1 : Matrix ι ι ℂ)).PosDef := Matrix.PosDef.one.smul hc₀0
  clear_value δ c₀
  have hΦ₀ : lowerPotential (c₀ • (1 : Matrix ι ι ℂ)) = r / δ := by
    rw [lowerPotential_smul_one hc₀0.ne', ← hmdef, hc₀def]
    field_simp
  have h1r : (1 : ℝ) - r ≠ 0 := by linarith
  have hgap : (n : ℝ) ≤ 1 / δ - lowerPotential (c₀ • (1 : Matrix ι ι ℂ)) := by
    rw [hΦ₀, hδdef, one_div_sub_div_eq hn0 h1r]
  -- run the one-sided construction, with the constant upper verifier
  obtain ⟨x, w, hwpos, hAn, hΦn, hwk⟩ :=
    exists_points_weights_of_small_dim hA₀ hδ0 ha hgrama
      (U := fun y => (n : ℝ) / traceAlong e J * ‖b y‖ ^ 2)
      (fun y => upperVerifierConst_nonneg (div_nonneg (by positivity) hT0.le) y)
      (integrable_upperVerifierConst hb _) hn
      (integral_upperVerifierConst hJ hb hgramb n) hgap n
  refine ⟨x, w, hwpos, ?_, ?_⟩
  · -- the lower frame bound, exactly as in the main theorem
    exact lower_frame_bound hn0 hr0 h1r hm_eq hδdef hc₀def hAn (hΦ₀ ▸ hΦn)
  · -- the upper frame bound from the crude rank-one estimate
    set T : ℝ := traceAlong e J with hTdef
    have hweight : ∀ i : Fin n, w i * ‖b (x i)‖ ^ 2 ≤ T / n := by
      intro i
      have h1 := hwk i
      have h3 := mul_le_mul_of_nonneg_left h1 (div_nonneg hT0.le hn0.le)
      have h4 : T / n * (w i * ((n : ℝ) / T * ‖b (x i)‖ ^ 2)) = w i * ‖b (x i)‖ ^ 2 := by
        field_simp
      rwa [h4, mul_one] at h3
    have hTΛ : T ≤ (1 + Real.sqrt ((T / Λ - 1) / n)) ^ 2 * Λ :=
      le_sq_one_add_sqrt_div_mul hn0 hΛ hMlt
    calc ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
        ≤ T • (1 : H →L[ℂ] H) :=
          sum_smul_rankOne_le_smul_one hn0 x w (fun i => (hwpos i).le) hweight
      _ ≤ ((1 + Real.sqrt ((T / Λ - 1) / n)) ^ 2 * Λ) • (1 : H →L[ℂ] H) :=
          smul_le_smul_of_nonneg_right hTΛ zero_le_one

end Infinite

end Discretization
