/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import BasicResults.Operator.QuadraticForm
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The Gram operator of a square-integrable map

For a square-integrable map `b : Ω → H` into a complex Hilbert space, the **Gram operator**
is the Bochner integral of the rank-one operators `b(x) b(x)*`,

`J = ∫ b(x) b(x)* dμ(x)`,

the operator counterpart of the Gram matrix `∫ a(x) a(x)* dμ(x)` of a finite family.  In Lean
`b(x) b(x)*` is `rankOne ℂ (b x) (b x)`, the operator `u ↦ ⟪b x, u⟫ b x`.  Its norm is
`‖b(x)‖²`, so the integrand is integrable exactly because `b` is square-integrable
(`ContinuousLinearMap.integrable_rankOne_self`).

The **quadratic form** of `J` is `⟪u, J u⟫ = ∫ |⟪u, b(x)⟫|² dμ(x)` for every `u`
(`ContinuousLinearMap.inner_integral_rankOne_self`); it determines `J`, and it is the form in
which the proofs use it.  The two hypotheses that the discretization theorem places on `J`
read as properties of `b`, for every operator with this quadratic form:

* `J ≤ Λ • 1` is the **Bessel-type bound** `∫ |⟪u, b(x)⟫|² dμ(x) ≤ Λ ‖u‖²` for every `u`
  (`ContinuousLinearMap.le_smul_one_iff_of_inner_eq_integral`);
* `J` is injective exactly when `b` is **nondegenerate**: the only `u` with `⟪u, b(x)⟫ = 0`
  for almost every `x` is `u = 0` (`ContinuousLinearMap.injective_iff_of_inner_eq_integral`).

Equivalently, `J = T* T` for the analysis operator `T : H → L₂(μ)`, `u ↦ ⟪b(·), u⟫`, and
`Λ` bounds `‖T‖²`; the two readings above are the ones the applications check.
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace ComplexOrder
open InnerProductSpace

namespace ContinuousLinearMap

variable {Ω H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [MeasurableSpace Ω]
  {μ : Measure Ω}

/-! ### The Bochner integral -/

/-- The map `u ↦ u u*` is continuous, as the composition of `u ↦ (⟪u, ·⟫, u)` with the
bilinear map `smulRight`. -/
theorem continuous_rankOne_self : Continuous fun u : H => rankOne ℂ u u := by
  have h1 := (ContinuousLinearMap.smulRightL ℂ H H).continuous₂
  have h2 : Continuous fun u : H => (innerSL ℂ u, u) :=
    (innerSL ℂ).continuous.prodMk continuous_id
  exact h1.comp h2

/-- **The rank-one operators `b(x) b(x)*` of a square-integrable map are integrable**: their
norm is `‖b(x)‖²`. -/
theorem integrable_rankOne_self {b : Ω → H} (hb : MemLp b 2 μ) :
    Integrable (fun x => rankOne ℂ (b x) (b x)) μ := by
  refine ((memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).1 hb).mono'
    (continuous_rankOne_self.comp_aestronglyMeasurable hb.aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [norm_rankOne, sq]

/-- **The quadratic form of the Gram operator**: for `J = ∫ b(x) b(x)* dμ(x)`,

`⟪u, J u⟫ = ∫ |⟪u, b(x)⟫|² dμ(x)`   for every `u ∈ H`.

Evaluation at `u` and the inner product with `u` are continuous linear maps, so both pass
under the integral (`ContinuousLinearMap.integral_apply`, `integral_inner`). -/
theorem inner_integral_rankOne_self [CompleteSpace H] {b : Ω → H} (hb : MemLp b 2 μ) (u : H) :
    ⟪u, (∫ x, rankOne ℂ (b x) (b x) ∂μ) u⟫_ℂ = ((∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have hi := integrable_rankOne_self hb
  rw [ContinuousLinearMap.integral_apply hi,
    ← integral_inner (hi.apply_continuousLinearMap u), ← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [rankOne_apply, inner_smul_right, ← inner_conj_symm (b x) u, RCLike.conj_mul]
  norm_cast

/-! ### Two equivalent readings of the hypotheses -/

/-- **A bound `J ≤ Λ • 1` is a Bessel-type bound.**  For an operator with the quadratic form
`⟪u, J u⟫ = ∫ |⟪u, b(x)⟫|² dμ(x)`,

`J ≤ Λ • 1`   if and only if   `∫ |⟪u, b(x)⟫|² dμ(x) ≤ Λ ‖u‖²` for every `u ∈ H`.

Both sides say that the quadratic form of `Λ • 1 - J` is nonnegative. -/
theorem le_smul_one_iff_of_inner_eq_integral {J : H →L[ℂ] H} {b : Ω → H}
    (hgram : ∀ u, ⟪u, J u⟫_ℂ = ((∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ)) {Λ : ℝ} :
    J ≤ Λ • (1 : H →L[ℂ] H) ↔ ∀ u, ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ ≤ Λ * ‖u‖ ^ 2 := by
  have hform : ∀ u, ⟪(Λ • (1 : H →L[ℂ] H) - J) u, u⟫_ℂ
      = ((Λ * ‖u‖ ^ 2 - ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := fun u => by
    have hJ : ⟪J u, u⟫_ℂ = ((∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      rw [← inner_conj_symm, hgram, Complex.conj_ofReal]
    rw [_root_.sub_apply, inner_sub_left, hJ, _root_.smul_apply, one_apply_eq_self,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, inner_self_eq_norm_sq_to_K,
      RCLike.conj_ofReal]
    norm_cast
    exact (Complex.ofReal_sub _ _).symm
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff_complex]
  refine forall_congr' fun u => ?_
  rw [hform u]
  simp only [RCLike.re_to_complex, Complex.ofReal_re, true_and, sub_nonneg]

variable [CompleteSpace H]

/-- **Injectivity of `J` is nondegeneracy of `b`.**  For a square-integrable `b` and an
operator with the quadratic form `⟪u, J u⟫ = ∫ |⟪u, b(x)⟫|² dμ(x)`, `J` is injective if and
only if the only `u` with `⟪u, b(x)⟫ = 0` for almost every `x` is `u = 0`.

The quadratic form vanishes at `u` exactly when `⟪u, b(·)⟫` vanishes almost everywhere.  If
`J u = 0` it vanishes; conversely, `J` is positive, and a positive operator whose quadratic
form vanishes at `u` annihilates `u`, because `⟪u, J u⟫ = ‖√J u‖²`. -/
theorem injective_iff_of_inner_eq_integral {J : H →L[ℂ] H} {b : Ω → H} (hb : MemLp b 2 μ)
    (hgram : ∀ u, ⟪u, J u⟫_ℂ = ((∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ)) :
    (∀ v, J v = 0 → v = 0) ↔ ∀ u, (∀ᵐ x ∂μ, ⟪u, b x⟫_ℂ = 0) → u = 0 := by
  have hre := re_inner_eq_integral hgram
  -- the average of `|⟪u, b⟫|²` vanishes exactly when `⟪u, b⟫` vanishes almost everywhere
  have hzero : ∀ u, ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ = 0 ↔ ∀ᵐ x ∂μ, ⟪u, b x⟫_ℂ = 0 := fun u => by
    rw [integral_eq_zero_iff_of_nonneg (fun x => by positivity) (integrable_norm_sq_inner hb u)]
    refine Filter.eventually_congr (ae_of_all _ fun x => ?_)
    simp
  constructor
  · intro hinj u hu
    apply hinj
    have hJ0 : 0 ≤ J := nonneg_of_inner_eq_integral hgram
    have hq : ‖CFC.sqrt J u‖ ^ 2 = 0 := by
      rw [← re_inner_apply_eq_norm_sq_sqrt hJ0, hre, (hzero u).2 hu]
    have hs : CFC.sqrt J u = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hq)
    have happ : J u = CFC.sqrt J (CFC.sqrt J u) :=
      congrArg (fun S : H →L[ℂ] H => S u) (CFC.sqrt_mul_sqrt_self J hJ0).symm
    rw [happ, hs, map_zero]
  · intro h v hv
    refine h v ((hzero v).1 ?_)
    rw [← hre, hv, inner_zero_right, map_zero]

/-- The Bessel-type reading of `J ≤ Λ • 1` for the Gram operator `J = ∫ b(x) b(x)* dμ(x)`. -/
theorem integral_rankOne_self_le_iff {b : Ω → H} (hb : MemLp b 2 μ) {Λ : ℝ} :
    ∫ x, rankOne ℂ (b x) (b x) ∂μ ≤ Λ • (1 : H →L[ℂ] H)
      ↔ ∀ u, ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ ≤ Λ * ‖u‖ ^ 2 :=
  le_smul_one_iff_of_inner_eq_integral (inner_integral_rankOne_self hb)

/-- The nondegeneracy reading of injectivity for the Gram operator
`J = ∫ b(x) b(x)* dμ(x)`. -/
theorem integral_rankOne_self_injective_iff {b : Ω → H} (hb : MemLp b 2 μ) :
    (∀ v, (∫ x, rankOne ℂ (b x) (b x) ∂μ) v = 0 → v = 0)
      ↔ ∀ u, (∀ᵐ x ∂μ, ⟪u, b x⟫_ℂ = 0) → u = 0 :=
  injective_iff_of_inner_eq_integral hb (inner_integral_rankOne_self hb)

end ContinuousLinearMap
