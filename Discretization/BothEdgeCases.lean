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
-/

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {ι κ Ω : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### One point serves for all -/

omit [DecidableEq κ] in
/-- **An admissible point for the two constant verifiers.**  The averages of
`L(x) = n |a(x)|²` and of `U(x) = n ‖b(x)‖² / Tr J` are both `n`, so there is a point at
which `U ≤ L` and `L` is positive.

Positivity of `L(y)` is what makes the weight `1 / L(y)` finite, and it is the reason the
comparison of the averages has to carry it along. -/
theorem exists_admissible_point_of_unique_of_small_dim [Unique ι] {a : Ω → ι → ℂ}
    {b : Ω → κ → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ)
    (hb : ∀ k, MemLp (fun x => b x k) 2 μ) (hgrama : gram a μ = 1)
    (hT : 0 < RCLike.re (gram b μ).trace) {n : ℕ} (hn0 : (0 : ℝ) < n) :
    ∃ y, (n : ℝ) / RCLike.re (gram b μ).trace * ∑ p, ‖b y p‖ ^ 2
        ≤ (n : ℝ) * ‖a y default‖ ^ 2 ∧ 0 < (n : ℝ) * ‖a y default‖ ^ 2 := by
  have hfint : ∫ y, (n : ℝ) * ‖a y default‖ ^ 2 ∂μ = n := by
    rw [integral_const_mul, integral_norm_sq_eq_one ha hgrama, mul_one]
  have hgint : ∫ y, (n : ℝ) / RCLike.re (gram b μ).trace * ∑ p, ‖b y p‖ ^ 2 ∂μ = n :=
    integral_upperVerifierConst hb hT n
  refine exists_le_of_integral_le ((integrable_norm_sq ha default).const_mul _)
    (integrable_upperVerifierConst hb _) (fun y => by positivity) (fun y => ?_) ?_ ?_
  · have h1 : 0 ≤ ∑ p, ‖b y p‖ ^ 2 := Finset.sum_nonneg fun p _ => by positivity
    have h2 : 0 ≤ (n : ℝ) / RCLike.re (gram b μ).trace := by positivity
    exact mul_nonneg h2 h1
  · rw [hfint]; exact hn0
  · rw [hfint, hgint]

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
    exists_admissible_point_of_unique_of_small_dim ha hb hgrama hT hn0
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
      have hMs := le_sq_one_add_sqrt_div hn0 hMlt
      rw [div_le_iff₀ hΛ] at hMs
      linarith
    exact (sum_smul_vecMulVec_le_smul_one hn0 (fun _ => y) _
      (fun _ => (one_div_pos.2 hLpos).le) hweight).trans
      (smul_le_smul_of_nonneg_right hTΛ Matrix.PosSemidef.one.nonneg)

end Discretization
