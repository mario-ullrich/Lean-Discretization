/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.MainTheorem

/-!
# The case of a small effective dimension

The main theorem needs `M = Tr J / Λ ≥ 1 + 1/n`, because the initial matrix
`B₀ = (ζ Tr J / s) • 1` involves `s = √((M-1)/n)`, which is too small otherwise.  As the
paper observes, for `M < 1 + 1/n` the upper potential is not needed: the upper verifier can
be replaced by the constant

`U(x) = n ‖b(x)‖² / Tr J`,   with   `∫ U dμ = n`.

The construction then tracks only the lower matrix, and the weights it produces satisfy
`wᵢ U(xᵢ) ≤ 1`, that is `wᵢ ‖b(xᵢ)‖² ≤ Tr J / n`.  Summing over the `n` points and using the
crude bound `b b* ≼ ‖b‖² • 1` (`Matrix.vecMulVec_le_norm_sq_smul_one`) gives

`∑ wᵢ b(xᵢ) b(xᵢ)* ≼ Tr J • 1 = M Λ • 1 ≼ (1 + s)² Λ • 1`,

the last step because `M ≤ 1 + 1/n` forces `s ≤ 1/n` and hence `M = 1 + n s² ≤ 1 + s`.

The lower half of the argument is unchanged, so the lower potential machinery is reused
verbatim; only the induction is one-sided
(`Discretization.exists_points_weights_of_small_dim`).  The result is
`Discretization.bss_generalized_of_small_dim`.
-/

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### The constant upper verifier -/

omit [DecidableEq κ] in
/-- The average of the constant upper verifier is `n`. -/
theorem integral_upperVerifierConst {b : Ω → κ → ℂ}
    (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (hT : 0 < RCLike.re (gram b μ).trace) (n : ℕ) :
    ∫ x, (n : ℝ) / RCLike.re (gram b μ).trace * ∑ p, ‖b x p‖ ^ 2 ∂μ = n := by
  rw [integral_const_mul, integral_sum_norm_sq hb]
  field_simp

omit [DecidableEq κ] in
/-- The constant upper verifier is integrable. -/
theorem integrable_upperVerifierConst {b : Ω → κ → ℂ}
    (hb : ∀ k, MemLp (fun x => b x k) 2 μ) (c : ℝ) :
    Integrable (fun x => c * ∑ p, ‖b x p‖ ^ 2) μ :=
  (integrable_finsetSum _ fun p _ => integrable_norm_sq hb p).const_mul _

/-! ### The one-sided construction -/

set_option maxHeartbeats 1000000 in
omit [DecidableEq κ] in
/-- **The construction for a small effective dimension.**  Only the lower matrix is tracked;
the weights are chosen as large as the lower verifier allows, which forces
`wᵢ · U(xᵢ) ≤ 1` for the constant upper verifier `U`. -/
theorem exists_points_weights_of_small_dim [Nonempty ι] [Nonempty κ] {A₀ : Matrix ι ι ℂ}
    (hA₀ : A₀.PosDef) {δ : ℝ} (hδ : 0 < δ) {a : Ω → ι → ℂ} {b : Ω → κ → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (hgrama : gram a μ = 1) (hT : 0 < RCLike.re (gram b μ).trace) {n : ℕ} (hn : 0 < n)
    (hgap : (n : ℝ) ≤ 1 / δ - lowerPotential A₀) (k : ℕ) :
    ∃ (x : Fin k → Ω) (w : Fin k → ℝ), (∀ i, 0 < w i) ∧
      (lowerState A₀ δ a x w).PosDef ∧
      lowerPotential (lowerState A₀ δ a x w) ≤ lowerPotential A₀ ∧
      ∀ i, w i * ((n : ℝ) / RCLike.re (gram b μ).trace * ∑ p, ‖b (x i) p‖ ^ 2) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  induction k with
  | zero => exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, by simpa using hA₀, by simp,
      fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨x, w, hwpos, hAk, hΦ, hwk⟩ := ih
    -- the increment is still admissible
    have hΦpos : 0 < lowerPotential (lowerState A₀ δ a x w) := lowerPotential_pos hAk
    have hgapk : (n : ℝ) ≤ 1 / δ - lowerPotential (lowerState A₀ δ a x w) := by linarith
    have hδ' : δ < (lowerPotential (lowerState A₀ δ a x w))⁻¹ := by
      have h1 : lowerPotential (lowerState A₀ δ a x w) < 1 / δ := by linarith
      rw [inv_eq_one_div, lt_div_iff₀ hΦpos]
      calc δ * lowerPotential (lowerState A₀ δ a x w) < δ * (1 / δ) :=
            mul_lt_mul_of_pos_left h1 hδ
        _ = 1 := by field_simp
    -- the average of the lower verifier beats that of the constant upper one
    have hlt : ∫ y, (n : ℝ) / RCLike.re (gram b μ).trace * ∑ p, ‖b y p‖ ^ 2 ∂μ
        < ∫ y, lowerVerifier (lowerState A₀ δ a x w) δ (a y) ∂μ := by
      rw [integral_upperVerifierConst hb hT n]
      have h1 := integral_lowerVerifier_gt hAk hδ hδ' ha hgrama
      linarith
    obtain ⟨y, hy⟩ := exists_lt_of_integral_lt (μ := μ)
      (f := fun y => lowerVerifier (lowerState A₀ δ a x w) δ (a y))
      (g := fun y => (n : ℝ) / RCLike.re (gram b μ).trace * ∑ p, ‖b y p‖ ^ 2)
      (integrable_lowerVerifier ha) (integrable_upperVerifierConst hb _) hlt
    -- the weight allowed by the lower verifier
    have hU0 : 0 ≤ (n : ℝ) / RCLike.re (gram b μ).trace * ∑ p, ‖b y p‖ ^ 2 := by
      have h1 : 0 ≤ ∑ p, ‖b y p‖ ^ 2 := Finset.sum_nonneg fun p _ => by positivity
      have h2 : 0 ≤ (n : ℝ) / RCLike.re (gram b μ).trace := by positivity
      exact mul_nonneg h2 h1
    have hLpos : 0 < lowerVerifier (lowerState A₀ δ a x w) δ (a y) := lt_of_le_of_lt hU0 hy
    have hwnew : 0 < 1 / lowerVerifier (lowerState A₀ δ a x w) δ (a y) := one_div_pos.2 hLpos
    have hcondL : 1 / (1 / lowerVerifier (lowerState A₀ δ a x w) δ (a y))
        ≤ lowerVerifier (lowerState A₀ δ a x w) δ (a y) := by rw [one_div_one_div]
    obtain ⟨hAnew, hΦnew⟩ := lowerPotential_update_le hAk hδ hδ' (a y) hwnew hcondL
    refine ⟨Fin.snoc x y, Fin.snoc w (1 / lowerVerifier (lowerState A₀ δ a x w) δ (a y)),
      ?_, ?_, ?_, ?_⟩
    · refine Fin.lastCases ?_ ?_
      · simpa using hwnew
      · intro j; simpa using hwpos j
    · rw [lowerState_snoc]; exact hAnew
    · rw [lowerState_snoc]; exact hΦnew.trans hΦ
    · refine Fin.lastCases ?_ ?_
      · simp only [Fin.snoc_last]
        rw [div_mul_eq_mul_div, div_le_one hLpos]
        calc 1 * ((n : ℝ) / RCLike.re (gram b μ).trace * ∑ p, ‖b y p‖ ^ 2)
            = (n : ℝ) / RCLike.re (gram b μ).trace * ∑ p, ‖b y p‖ ^ 2 := one_mul _
          _ ≤ lowerVerifier (lowerState A₀ δ a x w) δ (a y) := hy.le
      · intro j; simpa using hwk j

/-! ### The theorem for a small effective dimension -/

set_option maxHeartbeats 1000000 in
/-- **Generalized sparsification theorem for a small effective dimension.**

For `M = Tr J / Λ ≤ 1 + 1/n` the upper frame bound follows from the crude estimate
`b b* ≼ ‖b‖² • 1` alone.  This removes the hypothesis `M ≥ 1 + 1/n` of
`Discretization.bss_generalized_of_gram_eq_one`; the two statements together cover every
effective dimension. -/
theorem bss_generalized_of_small_dim [Nonempty ι] [Nonempty κ]
    {J : Matrix κ κ ℂ} (hJ : J.PosDef) {Λ : ℝ} (hΛ : 0 < Λ)
    {a : Ω → ι → ℂ} {b : Ω → κ → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (hgrama : gram a μ = 1) (hgramb : gram b μ = J)
    {n : ℕ} (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ n)
    (hMlt : RCLike.re J.trace / Λ ≤ 1 + 1 / (n : ℝ)) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • vecMulVec (b (x i)) (star (b (x i)))
        ≤ ((1 + Real.sqrt ((RCLike.re J.trace / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : Matrix κ κ ℂ) := by
  -- the parameters of the lower half of the construction
  have hn2 : 2 ≤ n := le_trans hm hmn
  have hn0 : (0 : ℝ) < n := by
    have h : 0 < n := lt_of_lt_of_le (by norm_num) hn2
    exact_mod_cast h
  have hn : 0 < n := by exact_mod_cast hn0
  set m : ℝ := (Fintype.card ι : ℝ) with hmdef
  have hm2 : (2 : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hm
  have hmn' : m ≤ (n : ℝ) := by rw [hmdef]; exact_mod_cast hmn
  set r : ℝ := Real.sqrt ((m - 1) / n) with hrdef
  have hrarg : (0 : ℝ) < (m - 1) / n := div_pos (by linarith) hn0
  have hr0 : 0 < r := Real.sqrt_pos.2 hrarg
  have hr2 : r ^ 2 = (m - 1) / n := Real.sq_sqrt hrarg.le
  have hrlt1 : (m - 1) / (n : ℝ) < 1 := by rw [div_lt_one hn0]; linarith
  have hr1 : r < 1 := by nlinarith [hr2, hr0, hrlt1]
  have hm_eq : m = (n : ℝ) * r ^ 2 + 1 := by rw [hr2]; field_simp; ring
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
    rw [hΦ₀, hδdef]
    have e2 : 1 / ((1 - r) / (n : ℝ)) - r / ((1 - r) / (n : ℝ)) = (n : ℝ) := by field_simp
    rw [e2]
  -- the trace of the Gram matrix of the second family
  have hT0 : 0 < RCLike.re J.trace := (RCLike.pos_iff.mp hJ.trace_pos).1
  have hT : 0 < RCLike.re (gram b μ).trace := by rw [hgramb]; exact hT0
  -- run the one-sided construction
  obtain ⟨x, w, hwpos, hAn, hΦn, hwk⟩ :=
    exists_points_weights_of_small_dim hA₀ hδ0 ha hb hgrama hT hn hgap n
  refine ⟨x, w, hwpos, ?_, ?_⟩
  · -- the lower frame bound, exactly as in the main theorem
    have hpot : lowerPotential (lowerState (c₀ • (1 : Matrix ι ι ℂ)) δ a x w) ≤ r / δ := by
      rw [← hΦ₀]; exact hΦn
    refine le_trans (le_of_eq ?_) (lower_bound_of_state hAn hpot)
    congr 1
    rw [hc₀def, hδdef, hm_eq]
    field_simp
    ring
  · -- the upper frame bound from the crude rank-one estimate
    set T : ℝ := RCLike.re J.trace with hTdef
    have hweight : ∀ i : Fin n, w i * (∑ p, ‖b (x i) p‖ ^ 2) ≤ T / n := by
      intro i
      have h1 := hwk i
      rw [hgramb, ← hTdef] at h1
      have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ T / n)
      have h4 : T / n * (w i * ((n : ℝ) / T * ∑ p, ‖b (x i) p‖ ^ 2))
          = w i * (∑ p, ‖b (x i) p‖ ^ 2) := by
        field_simp
      rwa [h4, mul_one] at h3
    have hstep : ∀ i : Fin n, w i • vecMulVec (b (x i)) (star (b (x i)))
        ≤ (w i * (∑ p, ‖b (x i) p‖ ^ 2)) • (1 : Matrix κ κ ℂ) := by
      intro i
      have h1 := Matrix.smul_le_smul_of_nonneg (Matrix.vecMulVec_le_norm_sq_smul_one
        (b (x i))) (hwpos i).le
      rwa [smul_smul] at h1
    have hsum : ∑ i, w i • vecMulVec (b (x i)) (star (b (x i)))
        ≤ (∑ i, w i * (∑ p, ‖b (x i) p‖ ^ 2)) • (1 : Matrix κ κ ℂ) := by
      rw [Finset.sum_smul]
      exact Finset.sum_le_sum fun i _ => hstep i
    have hTsum : ∑ i : Fin n, w i * (∑ p, ‖b (x i) p‖ ^ 2) ≤ T := by
      calc ∑ i : Fin n, w i * (∑ p, ‖b (x i) p‖ ^ 2) ≤ ∑ _i : Fin n, T / n :=
            Finset.sum_le_sum fun i _ => hweight i
        _ = T := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    -- and `T ≤ (1 + s)² Λ`
    set s : ℝ := Real.sqrt ((T / Λ - 1) / n) with hsdef
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hMs : T / Λ ≤ (1 + s) ^ 2 := by
      by_cases hM1 : T / Λ ≤ 1
      · nlinarith [hs0]
      · replace hM1 := not_le.mp hM1
        have harg : (0 : ℝ) ≤ (T / Λ - 1) / n := by
          apply div_nonneg (by linarith) hn0.le
        have hs2 : s ^ 2 = (T / Λ - 1) / n := Real.sq_sqrt harg
        have h1 : (n : ℝ) * s ^ 2 = T / Λ - 1 := by rw [hs2]; field_simp
        have h2 : s ^ 2 ≤ (1 / (n : ℝ)) ^ 2 := by
          rw [hs2]
          have h3 : T / Λ - 1 ≤ 1 / (n : ℝ) := by
            rw [hTdef]; linarith [hMlt]
          calc (T / Λ - 1) / n ≤ (1 / (n : ℝ)) / n := by gcongr
            _ = (1 / (n : ℝ)) ^ 2 := by field_simp
        have h4 : s ≤ 1 / n := by nlinarith [hs0, h2, hn0]
        have h5 : (n : ℝ) * s ≤ 1 := by
          have h6 := mul_le_mul_of_nonneg_left h4 hn0.le
          rwa [mul_one_div, div_self hn0.ne'] at h6
        nlinarith [h1, h5, hs0]
    have hTΛ : T ≤ (1 + s) ^ 2 * Λ := by
      rw [div_le_iff₀ hΛ] at hMs
      linarith
    calc ∑ i, w i • vecMulVec (b (x i)) (star (b (x i)))
        ≤ (∑ i, w i * (∑ p, ‖b (x i) p‖ ^ 2)) • (1 : Matrix κ κ ℂ) := hsum
      _ ≤ ((1 + s) ^ 2 * Λ) • (1 : Matrix κ κ ℂ) :=
          Matrix.PosSemidef.one.smul_le_smul_of_le (le_trans hTsum hTΛ)

end Discretization
