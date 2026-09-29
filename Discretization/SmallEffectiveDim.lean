/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.MainTheorem

/-!
# The case of a small effective dimension

The main theorem needs `M = Tr J / Λ ≥ 1 + 1/n`, because the initial state
`B₀ = (ζ Tr J / s) • 1` involves `s = √((M-1)/n)`, which is too small otherwise.  As the
paper observes, for `M ≤ 1 + 1/n` the upper potential is not needed: a constant upper
verifier does the job,

`U(x) = n ‖b(x)‖² / Tr J`,   with   `∫ U dμ = n`.

The construction then tracks only the lower matrix, and the weights it produces satisfy
`wᵢ U(xᵢ) ≤ 1`, that is `wᵢ ‖b(xᵢ)‖² ≤ Tr J / n`.  Summing over the `n` points and using the
crude bound `b b* ≼ ‖b‖² • 1` of an upper barrier gives

`∑ wᵢ b(xᵢ) b(xᵢ)* ≼ Tr J • 1 = M Λ • 1 ≼ (1 + s)² Λ • 1`,

the last step because `M ≤ 1 + 1/n` forces `s ≤ 1/n` and hence `M = 1 + n s² ≤ 1 + s`.

The lower half of the argument is that of the main theorem; only the induction is one-sided
(`Discretization.exists_points_weights_of_small_dim`).  The read-off is
`Discretization.UpperBarrier.sum_smul_R_le_smul_one`, the theorem for every upper barrier is
`Discretization.UpperBarrier.bss_generalized_of_small_dim`, and the theorem for finite
families is `Discretization.bss_generalized_of_small_dim`.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### The one-sided construction -/

/-- **The construction for a small effective dimension.**  Only the lower matrix is tracked.

The second family enters through a single nonnegative integrable function `U` of average
`n`, which is the constant upper verifier; nothing else about it is used.  The weights are
chosen as large as the lower verifier allows, which forces `wᵢ · U(xᵢ) ≤ 1`.

Stating it for an abstract `U` is what lets the same induction serve every upper barrier,
in `Discretization.UpperBarrier.bss_generalized_of_small_dim`. -/
theorem exists_points_weights_of_small_dim [Nonempty ι] {A₀ : Matrix ι ι ℂ}
    (hA₀ : A₀.PosDef) {δ : ℝ} (hδ : 0 < δ) {a : Ω → ι → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hgrama : gram a μ = 1) {U : Ω → ℝ}
    (hU0 : ∀ y, 0 ≤ U y) (hUint : Integrable U μ) {n : ℕ} (hn : 0 < n)
    (hUavg : ∫ y, U y ∂μ = n) (hgap : (n : ℝ) ≤ 1 / δ - lowerPotential A₀) (k : ℕ) :
    ∃ (x : Fin k → Ω) (w : Fin k → ℝ), (∀ i, 0 < w i) ∧
      (lowerState A₀ δ a x w).PosDef ∧
      lowerPotential (lowerState A₀ δ a x w) ≤ lowerPotential A₀ ∧
      ∀ i, w i * U (x i) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  induction k with
  | zero => exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, by simpa using hA₀, by simp,
      fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨x, w, hwpos, hAk, hΦ, hwk⟩ := ih
    -- the increment is still admissible
    have hΦpos : 0 < lowerPotential (lowerState A₀ δ a x w) := lowerPotential_pos hAk
    have hgapk : (n : ℝ) ≤ 1 / δ - lowerPotential (lowerState A₀ δ a x w) := by linarith
    have hδ' : δ < (lowerPotential (lowerState A₀ δ a x w))⁻¹ :=
      lt_inv_of_le_one_div_sub hδ hΦpos hn0 hgapk
    -- the average of the lower verifier beats that of the constant upper one
    have hlt : ∫ y, U y ∂μ < ∫ y, lowerVerifier (lowerState A₀ δ a x w) δ (a y) ∂μ := by
      rw [hUavg]
      have h1 := integral_lowerVerifier_gt hAk hδ hδ' ha hgrama
      linarith
    obtain ⟨y, hy⟩ := exists_lt_of_integral_lt (μ := μ)
      (f := fun y => lowerVerifier (lowerState A₀ δ a x w) δ (a y)) (g := U)
      (integrable_lowerVerifier ha) hUint hlt
    -- the weight allowed by the lower verifier
    have hLpos : 0 < lowerVerifier (lowerState A₀ δ a x w) δ (a y) :=
      lt_of_le_of_lt (hU0 y) hy
    obtain ⟨hwnew, hcondL, -⟩ := weight_of_verifier_lt (hU0 y) hy
    obtain ⟨hAnew, hΦnew⟩ := lowerPotential_update_le hAk hδ hδ' (a y) hwnew hcondL
    refine ⟨Fin.snoc x y, Fin.snoc w (1 / lowerVerifier (lowerState A₀ δ a x w) δ (a y)),
      ?_, ?_, ?_, ?_⟩
    · exact forall_snoc_pos hwpos hwnew
    · rw [lowerState_snoc]; exact hAnew
    · rw [lowerState_snoc]; exact hΦnew.trans hΦ
    · refine Fin.lastCases ?_ ?_
      · simp only [Fin.snoc_last]
        rw [div_mul_eq_mul_div, div_le_one hLpos, one_mul]
        exact hy.le
      · intro j; simpa using hwk j

namespace UpperBarrier

variable {S : Type*} [AddCommGroup S] [PartialOrder S] [IsOrderedAddMonoid S] [Module ℝ S]
  [IsOrderedModule ℝ S] [One S] (U : UpperBarrier μ S)

/-! ### The constant upper verifier -/

omit [IsOrderedAddMonoid S] [IsOrderedModule ℝ S] in
/-- The constant upper verifier `n ‖b(y)‖² / Tr J` has average `n`. -/
theorem integral_div_tr_mul_sq (n : ℕ) : ∫ y, (n : ℝ) / U.tr * U.sq y ∂μ = n := by
  have hT0 := U.tr_pos
  rw [integral_const_mul, U.integral_sq]
  field_simp

omit [IsOrderedAddMonoid S] in
include U in
/-- The unit of an upper barrier is positive: `0 ≤ Ψ(1)⁻¹ • J ≤ 1`. -/
theorem one_nonneg : (0 : S) ≤ 1 := by
  have hadm := U.adm_smul_one (one_pos : (0 : ℝ) < 1)
  exact (smul_nonneg (inv_nonneg.2 (U.pot_pos hadm).le) U.J_nonneg).trans
    ((U.inv_pot_smul_le hadm).trans_eq (one_smul ℝ (1 : S)))

/-! ### The crude upper frame bound -/

/-- **The upper frame bound from a bound on the weights.**  If every weight satisfies
`wᵢ ‖b(xᵢ)‖² ≤ T / n`, then the `n` rank-one pieces add up to at most `T • 1`.

Each summand is below `wᵢ ‖b(xᵢ)‖² • 1` by the crude bound of the upper barrier, and the
`n` bounds add up to `T`. -/
theorem sum_smul_R_le_smul_one {T : ℝ} {n : ℕ} (hn0 : (0 : ℝ) < n) (x : Fin n → Ω)
    (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : ∀ i, w i * U.sq (x i) ≤ T / n) :
    ∑ i, w i • U.R (x i) ≤ T • (1 : S) := by
  have hstep : ∀ i : Fin n, w i • U.R (x i) ≤ (w i * U.sq (x i)) • (1 : S) := by
    intro i
    have h1 := smul_le_smul_of_nonneg_left (U.R_le (x i)) (hw0 i)
    rwa [smul_smul] at h1
  have hsum : ∑ i, w i • U.R (x i) ≤ (∑ i, w i * U.sq (x i)) • (1 : S) := by
    rw [Finset.sum_smul]
    exact Finset.sum_le_sum fun i _ => hstep i
  have hTsum : ∑ i : Fin n, w i * U.sq (x i) ≤ T := by
    calc ∑ i : Fin n, w i * U.sq (x i) ≤ ∑ _i : Fin n, T / n :=
          Finset.sum_le_sum fun i _ => hw i
      _ = T := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  exact hsum.trans (smul_le_smul_of_nonneg_right hTsum U.one_nonneg)

/-! ### The theorem for a small effective dimension -/

/-- **Generalized sparsification theorem for a small effective dimension and an upper
barrier.**  For `M = Tr J / Λ ≤ 1 + 1/n` the upper frame bound follows from the crude
estimate `b b* ≼ ‖b‖² • 1` alone; the first family still needs `m ≥ 2`. -/
theorem bss_generalized_of_small_dim [Nonempty ι] {Λ : ℝ} (hΛ : 0 < Λ) {a : Ω → ι → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hgrama : gram a μ = 1) {n : ℕ}
    (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ n)
    (hMlt : U.tr / Λ ≤ 1 + 1 / (n : ℝ)) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • U.R (x i) ≤ ((1 + Real.sqrt ((U.tr / Λ - 1) / n)) ^ 2 * Λ) • (1 : S) := by
  -- the parameters of the lower half of the construction
  have hn0 : (0 : ℝ) < n := by
    have h : 0 < n := lt_of_lt_of_le (by norm_num) (le_trans hm hmn)
    exact_mod_cast h
  have hn : 0 < n := by exact_mod_cast hn0
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
  -- run the one-sided construction with the constant upper verifier
  have hT0 := U.tr_pos
  obtain ⟨x, w, hwpos, hAn, hΦn, hwk⟩ :=
    exists_points_weights_of_small_dim hA₀ hδ0 ha hgrama
      (U := fun y => (n : ℝ) / U.tr * U.sq y)
      (fun y => mul_nonneg (by positivity) (U.sq_nonneg y))
      (U.integrable_sq.const_mul _) hn (U.integral_div_tr_mul_sq n) hgap n
  refine ⟨x, w, hwpos, ?_, ?_⟩
  · -- the lower frame bound, exactly as in the main theorem
    exact lower_frame_bound hn0 hr0 h1r hm_eq hδdef hc₀def hAn (hΦ₀ ▸ hΦn)
  · -- the upper frame bound from the crude rank-one estimate
    set T : ℝ := U.tr with hTdef
    have hweight : ∀ i : Fin n, w i * U.sq (x i) ≤ T / n := by
      intro i
      have h1 : w i * ((n : ℝ) / T * U.sq (x i)) ≤ 1 := hwk i
      have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ T / n)
      have h4 : T / n * (w i * ((n : ℝ) / T * U.sq (x i))) = w i * U.sq (x i) := by
        field_simp
      rwa [h4, mul_one] at h3
    have hTΛ : T ≤ (1 + Real.sqrt ((T / Λ - 1) / n)) ^ 2 * Λ :=
      le_sq_one_add_sqrt_div_mul hn0 hΛ hMlt
    calc ∑ i, w i • U.R (x i)
        ≤ T • (1 : S) := U.sum_smul_R_le_smul_one hn0 x w (fun i => (hwpos i).le) hweight
      _ ≤ ((1 + Real.sqrt ((T / Λ - 1) / n)) ^ 2 * Λ) • (1 : S) :=
          smul_le_smul_of_nonneg_right hTΛ U.one_nonneg

end UpperBarrier

/-! ### The theorem for finite families -/

variable [Fintype κ] [DecidableEq κ]

/-- **Generalized sparsification theorem for a small effective dimension.**

For `M = Tr J / Λ ≤ 1 + 1/n` the upper frame bound follows from the crude estimate
`b b* ≼ ‖b‖² • 1` alone; the first family still needs `m ≥ 2`.  Together with
`Discretization.bss_generalized_of_gram_eq_one`, which needs `M ≥ 1 + 1/n`, every effective
dimension is covered. -/
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
            • (1 : Matrix κ κ ℂ) :=
  (matrixUpperBarrier hJ hb hgramb).bss_generalized_of_small_dim hΛ ha hgrama hm hmn hMlt

end Discretization
