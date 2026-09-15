/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.CardOne
import Discretization.SmallEffectiveDim

/-!
# A single function and a small effective dimension

The two edge cases of the previous files at the same time: `card ι = 1`, so that the lower
potential is not needed, and `M = Tr J / Λ ≤ 1 + 1/n`, so that the upper potential is not
needed either.  Both verifiers are constants,

`L(x) = n |a(x)|²`   and   `U(x) = n ‖b(x)‖² / Tr J`,   with   `∫ L dμ = ∫ U dμ = n`,

and neither of them depends on the state of the construction.  A single admissible point `y`,
used `n` times with the weight `w = 1 / L(y)`, therefore does everything.  The lower frame
bound becomes the identity `∑ wᵢ |a(xᵢ)|² = 1`, and the upper one follows from `w · U(y) ≤ 1`
together with the crude estimate `b b* ≼ ‖b‖² • 1`.  There is no induction.

The two averages agree here, so the point comes from
`Discretization.exists_le_of_integral_le` and not from the strict comparison that the other
cases use.  The result is `Discretization.bss_generalized_of_unique_of_small_dim`.

With it the four cases are complete, and a case distinction on `m ≥ 2` and on
`M ≥ 1 + 1/n` assembles them into `Discretization.bss_generalized_of_gram_eq_one'`, the
theorem with no side condition beyond `n ≥ m`.
-/

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {ι κ Ω : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### One point serves for all -/

/-- **An admissible point for the two constant verifiers.**  The lower verifier
`L(x) = n |a(x)|²` has average `n`, and so does the given upper verifier `U`, so there is a
point at which `U ≤ L` and `L` is positive.

Positivity of `L(y)` is what makes the weight `1 / L(y)` finite, and it is the reason the
comparison of the averages has to carry it along.  As in
`Discretization.exists_points_weights_of_small_dim`, the second family enters only through
`U`, so the same lemma serves a finite and a countable one. -/
theorem exists_admissible_point_of_unique_of_small_dim [Unique ι] {a : Ω → ι → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hgrama : gram a μ = 1) {U : Ω → ℝ}
    (hU0 : ∀ y, 0 ≤ U y) (hUint : Integrable U μ) {n : ℕ} (hn0 : (0 : ℝ) < n)
    (hUavg : ∫ y, U y ∂μ = n) :
    ∃ y, U y ≤ (n : ℝ) * ‖a y default‖ ^ 2 ∧ 0 < (n : ℝ) * ‖a y default‖ ^ 2 := by
  have hfint : ∫ y, (n : ℝ) * ‖a y default‖ ^ 2 ∂μ = n := by
    rw [integral_const_mul, integral_norm_sq_eq_one ha hgrama, mul_one]
  refine exists_le_of_integral_le ((integrable_norm_sq ha default).const_mul _)
    hUint (fun y => by positivity) hU0 ?_ ?_
  · rw [hfint]; exact hn0
  · rw [hfint, hUavg]

/-! ### The theorem for a single function and a small effective dimension -/

/-- **Generalized sparsification theorem for a one-element first family and a small effective
dimension.**

For `card ι = 1` and `M = Tr J / Λ ≤ 1 + 1/n` neither potential is needed: one point, used
`n` times, makes the lower frame bound the identity `1 = (1 - √((m-1)/n))²` and leaves the
upper one to the crude estimate.  Together with
`Discretization.bss_generalized_of_gram_eq_one`, `Discretization.bss_generalized_of_unique`
and `Discretization.bss_generalized_of_small_dim`, every size of the first family and every
effective dimension of the second one is covered. -/
theorem bss_generalized_of_unique_of_small_dim [Unique ι] [Nonempty κ]
    {J : Matrix κ κ ℂ} (hJ : J.PosDef) {Λ : ℝ} (hΛ : 0 < Λ)
    {a : Ω → ι → ℂ} {b : Ω → κ → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (hgrama : gram a μ = 1) (hgramb : gram b μ = J)
    {n : ℕ} (hn : 0 < n) (hMlt : RCLike.re J.trace / Λ ≤ 1 + 1 / (n : ℝ)) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 : Matrix ι ι ℂ) ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • vecMulVec (b (x i)) (star (b (x i)))
        ≤ ((1 + Real.sqrt ((RCLike.re J.trace / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : Matrix κ κ ℂ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hT0 : 0 < RCLike.re J.trace := (RCLike.pos_iff.mp hJ.trace_pos).1
  have hT : 0 < RCLike.re (gram b μ).trace := by rw [hgramb]; exact hT0
  -- one point, admissible for both constant verifiers
  obtain ⟨y, hUL, hLpos⟩ :=
    exists_admissible_point_of_unique_of_small_dim ha hgrama
      (U := fun y => (n : ℝ) / RCLike.re (gram b μ).trace * ∑ p, ‖b y p‖ ^ 2)
      (fun y => upperVerifierConst_nonneg (by positivity) y)
      (integrable_upperVerifierConst hb _) hn0 (integral_upperVerifierConst hb hT n)
  rw [hgramb] at hUL
  refine ⟨fun _ => y, fun _ => 1 / ((n : ℝ) * ‖a y default‖ ^ 2),
    fun _ => one_div_pos.2 hLpos, ?_, ?_⟩
  · -- the lower frame bound is an identity, each point contributing exactly `1/n`
    exact le_of_eq (sum_smul_vecMulVec_eq_one hn0 _ _
      fun _ => one_div_mul_cancel hLpos.ne').symm
  · -- the weight allowed by the constant upper verifier
    have hweight : ∀ _i : Fin n, 1 / ((n : ℝ) * ‖a y default‖ ^ 2) * (∑ p, ‖b y p‖ ^ 2)
        ≤ RCLike.re J.trace / n := by
      intro _i
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hLpos hn0]
      have h1 := mul_le_mul_of_nonneg_left hUL hT0.le
      have h2 : RCLike.re J.trace
          * ((n : ℝ) / RCLike.re J.trace * ∑ p, ‖b y p‖ ^ 2)
          = (∑ p, ‖b y p‖ ^ 2) * n := by
        field_simp
      linarith [h2 ▸ h1]
    -- and the crude rank-one estimate
    have hTΛ : RCLike.re J.trace
        ≤ (1 + Real.sqrt ((RCLike.re J.trace / Λ - 1) / n)) ^ 2 * Λ := by
      exact le_sq_one_add_sqrt_div_mul hn0 hΛ hMlt
    exact (sum_smul_vecMulVec_le_smul_one hn0 (fun _ => y) _
      (fun _ => (one_div_pos.2 hLpos).le) hweight).trans
      (smul_le_smul_of_nonneg_right hTΛ Matrix.PosSemidef.one.nonneg)

/-! ### The theorem without side conditions -/

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] [MeasurableSpace Ω] in
/-- For a one-element first family the lower frame constant is `1`. -/
theorem sq_one_sub_sqrt_div_card_eq_one [Fintype ι] {n : ℕ} (h : Fintype.card ι = 1) :
    (1 - Real.sqrt (((Fintype.card ι : ℝ) - 1) / n)) ^ 2 = 1 := by
  rw [h]
  norm_num

/-- **Generalized sparsification theorem for a normalized first family**, with no side
condition beyond `n ≥ m`.

The potential argument of `Discretization.bss_generalized_of_gram_eq_one` needs `m ≥ 2` and
`M ≥ 1 + 1/n`.  A case distinction on those two conditions hands the remaining cases to
`Discretization.bss_generalized_of_unique`,
`Discretization.bss_generalized_of_small_dim` and
`Discretization.bss_generalized_of_unique_of_small_dim`.  For `m = 1` the lower frame
constant `(1 - √((m-1)/n))²` is `1`, which is what those two theorems state. -/
theorem bss_generalized_of_gram_eq_one' [Fintype ι] [Nonempty ι] [Nonempty κ]
    {J : Matrix κ κ ℂ} (hJ : J.PosDef) {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : J ≤ Λ • (1 : Matrix κ κ ℂ)) {a : Ω → ι → ℂ} {b : Ω → κ → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (hgrama : gram a μ = 1) (hgramb : gram b μ = J)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • vecMulVec (b (x i)) (star (b (x i)))
        ≤ ((1 + Real.sqrt ((RCLike.re J.trace / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : Matrix κ κ ℂ) := by
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hn : 0 < n := lt_of_lt_of_le hcard hmn
  by_cases hM : 1 + 1 / (n : ℝ) ≤ RCLike.re J.trace / Λ
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

end Discretization
