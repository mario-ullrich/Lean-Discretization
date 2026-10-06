/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import BasicResults.IntegralQuadraticForm
public import Discretization.KieferWolfowitz.MainTheorem
public import Discretization.KieferWolfowitz.Compact

/-!
# The Kiefer–Wolfowitz measure

The theorem is proved with the design in the form it is constructed in, a list of points
with weights.  This file packages that list as an actual measure

`ϱ = ∑ₖ wₖ · δ(xₖ)`,

so that the conclusion reads as the statement about a probability measure that it is meant
to be:

`|f(y)|² ≤ (m + ε) · ∫ |f|² dϱ`   for every `f` in the span and every point `y`.

Two facts are needed for the translation, and both require the coordinate functions to be
measurable, since a Dirac measure only sees a function through its value at one point:

* `Discretization.KieferWolfowitz.integral_designMeasure`: integration against `ϱ` is the
  weighted sum over the points;
* `Discretization.KieferWolfowitz.gram_designMeasure`: the Gram matrix of `ϱ` in the sense of
  `Discretization.gram` is the Gram matrix of the design.

The second identity is what lets the measure produced here be handed to the discretization
theorem, which asks for `Discretization.gram` of a measure.  The passage from a design to its
measure is `Discretization.KieferWolfowitz.exists_probabilityMeasure_of_design`; it gives the
theorem on an arbitrary measurable space and, with `ε = 0`, for continuous functions on a
compact space whose `σ`-algebra contains the open sets.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization.KieferWolfowitz

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

/-- **The measure of a design**, `ϱ = ∑ₖ wₖ · δ(xₖ)`. -/
noncomputable def designMeasure {n : ℕ} (x : Fin n → Ω) (w : Fin n → ℝ) : Measure Ω :=
  ∑ k, ENNReal.ofReal (w k) • Measure.dirac (x k)

/-- The measure of a design with nonnegative weights summing to one is a probability
measure. -/
theorem isProbabilityMeasure_designMeasure {n : ℕ} (x : Fin n → Ω) {w : Fin n → ℝ}
    (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) :
    IsProbabilityMeasure (designMeasure x w) := by
  constructor
  rw [designMeasure, Measure.coe_finsetSum]
  simp only [Finset.sum_apply, Measure.coe_smul, Pi.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => hw k, hw1, ENNReal.ofReal_one]

/-- **Integration against the measure of a design is the weighted sum over its points.** -/
theorem integral_designMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {n : ℕ} (x : Fin n → Ω) {w : Fin n → ℝ} (hw : ∀ k, 0 ≤ w k) {f : Ω → E}
    (hf : StronglyMeasurable f) :
    ∫ y, f y ∂(designMeasure x w) = ∑ k, w k • f (x k) := by
  rw [designMeasure, integral_finsetSum_measure fun k _ =>
    (integrable_dirac' hf (by simp [enorm_lt_top])).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_smul_measure, integral_dirac' f _ hf, ENNReal.toReal_ofReal (hw k)]

omit [Fintype ι] [DecidableEq ι] in
/-- **The Gram matrix of the measure of a design is the Gram matrix of the design.**  This is
the identity that makes the measure produced by the Kiefer–Wolfowitz theorem usable by the
discretization theorem, which is phrased with `Discretization.gram`. -/
theorem gram_designMeasure {a : Ω → ι → ℂ} (hmeas : ∀ i, Measurable fun y => a y i) {n : ℕ}
    (x : Fin n → Ω) {w : Fin n → ℝ} (hw : ∀ k, 0 ≤ w k) :
    gram a (designMeasure x w) = designGram a x w := by
  ext i j
  have hm : Measurable fun y => a y i * star (a y j) :=
    Measurable.mul (hmeas i) (Measurable.comp continuous_star.measurable (hmeas j))
  rw [gram, Matrix.of_apply, integral_designMeasure x hw (Measurable.stronglyMeasurable hm)]
  simp [designGram, Matrix.sum_apply, Matrix.vecMulVec_apply]

omit [DecidableEq ι] in
/-- **A design as a probability measure.**  If points `x₁, …, xₙ` with nonnegative weights
summing to one have a positive definite Gram matrix and satisfy
`|f(y)|² ≤ K · ∑ₖ wₖ |f(xₖ)|²` for every point `y` and every `f` in the span, then the
measure `ϱ = ∑ₖ wₖ δ(xₖ)` is a probability measure with positive definite Gram matrix and
`|f(y)|² ≤ K · ∫ |f|² dϱ`.  Measurability of the coordinate functions is what lets the
Dirac measures see them. -/
theorem exists_probabilityMeasure_of_design {a : Ω → ι → ℂ}
    (hmeas : ∀ i, Measurable fun y => a y i) {K : ℝ} {n : ℕ} (x : Fin n → Ω)
    {w : Fin n → ℝ} (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) (hpd : (designGram a x w).PosDef)
    (hbound : ∀ (c : ι → ℂ) (y : Ω),
      ‖star c ⬝ᵥ a y‖ ^ 2 ≤ K * ∑ k, w k * ‖star c ⬝ᵥ a (x k)‖ ^ 2) :
    ∃ ϱ : Measure Ω, IsProbabilityMeasure ϱ ∧ (gram a ϱ).PosDef ∧
      ∀ (c : ι → ℂ) (y : Ω), ‖star c ⬝ᵥ a y‖ ^ 2 ≤ K * ∫ z, ‖star c ⬝ᵥ a z‖ ^ 2 ∂ϱ := by
  refine ⟨designMeasure x w, isProbabilityMeasure_designMeasure x hw hw1, ?_, fun c y => ?_⟩
  · rwa [gram_designMeasure hmeas x hw]
  · have hsm : StronglyMeasurable fun z : Ω => ‖star c ⬝ᵥ a z‖ ^ 2 :=
      Measurable.stronglyMeasurable (Measurable.pow_const (Measurable.norm
        (Finset.measurable_sum _ fun i _ => Measurable.mul measurable_const (hmeas i))) 2)
    rw [integral_designMeasure x hw hsm]
    simpa using hbound c y

/-- **The Kiefer–Wolfowitz theorem, in terms of a measure.**

For linearly independent bounded measurable functions `a₁, …, a_m` on an arbitrary
measurable space and every `ε > 0` there is a finitely supported probability measure `ϱ`
whose Gram matrix is invertible and for which

`|f(y)|² ≤ (m + ε) · ∫ |f|² dϱ`

for every point `y` and every function `f(y) = ⟪c, a(y)⟫` in the span.  In words: on an
`m`-dimensional space of functions, the uniform norm is dominated by the `L₂(ϱ)` norm with
the constant `√(m+ε)`. -/
theorem exists_probabilityMeasure_kieferWolfowitz [Nonempty ι] (a : Ω → ι → ℂ) {C : ℝ}
    (hC : ∀ y i, ‖a y i‖ ≤ C) (hmeas : ∀ i, Measurable fun y => a y i)
    (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ ϱ : Measure Ω, IsProbabilityMeasure ϱ ∧ (gram a ϱ).PosDef ∧
      ∀ (c : ι → ℂ) (y : Ω),
        ‖star c ⬝ᵥ a y‖ ^ 2 ≤ (Fintype.card ι + ε) * ∫ z, ‖star c ⬝ᵥ a z‖ ^ 2 ∂ϱ := by
  obtain ⟨n, x, w, hw, hw1, hpd, hbound⟩ := exists_design_kieferWolfowitz a hC hli hε
  exact exists_probabilityMeasure_of_design hmeas x hw hw1 hpd hbound

/-- **The Kiefer–Wolfowitz theorem on a compact domain, in terms of a measure.**

For linearly independent continuous functions `a₁, …, a_m` on a compact space whose
`σ`-algebra contains the open sets there is a finitely supported probability measure `ϱ`
whose Gram matrix is invertible and for which

`|f(y)|² ≤ m · ∫ |f|² dϱ`

for every point `y` and every `f` in the span: the bound with `ε = 0`.  Continuity gives
the measurability of the coordinate functions. -/
theorem exists_probabilityMeasure_kieferWolfowitz_of_compact [Nonempty ι] [TopologicalSpace Ω]
    [CompactSpace Ω] [OpensMeasurableSpace Ω] (a : Ω → ι → ℂ)
    (hcont : ∀ i, Continuous fun y => a y i)
    (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0) :
    ∃ ϱ : Measure Ω, IsProbabilityMeasure ϱ ∧ (gram a ϱ).PosDef ∧
      ∀ (c : ι → ℂ) (y : Ω),
        ‖star c ⬝ᵥ a y‖ ^ 2 ≤ Fintype.card ι * ∫ z, ‖star c ⬝ᵥ a z‖ ^ 2 ∂ϱ := by
  obtain ⟨n, x, w, hw, hw1, hpd, hbound⟩ := exists_design_kieferWolfowitz_of_compact a hcont hli
  exact exists_probabilityMeasure_of_design (fun i => (hcont i).measurable) x hw hw1 hpd hbound

end Discretization.KieferWolfowitz
