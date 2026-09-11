/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.Iteration
import Discretization.Infinite.Averages
import Discretization.Infinite.Bounds

/-!
# The construction with an operator on the upper side

The construction of `Discretization.Iteration`, for a second family given by a
square-integrable map into a Hilbert space.  The first family stays finite, so the lower
state is the matrix

`A_k = A₀ - k δ • 1 + ∑ᵢ wᵢ a(xᵢ) a(xᵢ)*`

of the finite case, while the upper state is the operator

`B_k = B₀ + k ζ • J - ∑ᵢ wᵢ b(xᵢ) b(xᵢ)*`   (`Discretization.Infinite.upperState`).

The invariant is the same as in finite dimension: both states stay positive, the operator
one even **strictly** positive (that is, invertible), and neither potential exceeds its
initial value.  The step is `Discretization.Infinite.exists_admissible_point` followed by the
two barrier lemmas, the lower one for matrices and the upper one for operators.

The result is `Discretization.Infinite.exists_points_weights`.
-/

open MeasureTheory
open scoped InnerProductSpace ComplexOrder
open InnerProductSpace

namespace Discretization

namespace Infinite

variable {ι κ Ω H : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] [MeasurableSpace Ω] {μ : Measure Ω}
  {e : HilbertBasis κ ℂ H} {J : H →L[ℂ] H}

/-! ### The upper state -/

/-- The upper operator after the steps recorded by the points `x` and the weights `w`. -/
noncomputable def upperState (J B₀ : H →L[ℂ] H) (ζ : ℝ) (b : Ω → H) {k : ℕ}
    (x : Fin k → Ω) (w : Fin k → ℝ) : H →L[ℂ] H :=
  B₀ + ((k : ℝ) * ζ) • J - ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))

omit [CompleteSpace H] [MeasurableSpace Ω] in
/-- With no points chosen, the upper state is `B₀`. -/
@[simp]
theorem upperState_zero (J B₀ : H →L[ℂ] H) (ζ : ℝ) (b : Ω → H) (x : Fin 0 → Ω)
    (w : Fin 0 → ℝ) : upperState J B₀ ζ b x w = B₀ := by simp [upperState]

omit [CompleteSpace H] [MeasurableSpace Ω] in
/-- One step of the upper state: grow by `ζ • J` and subtract the new rank-one operator. -/
theorem upperState_snoc (J B₀ : H →L[ℂ] H) (ζ : ℝ) (b : Ω → H) {k : ℕ} (x : Fin k → Ω)
    (w : Fin k → ℝ) (y : Ω) (v : ℝ) :
    upperState J B₀ ζ b (Fin.snoc x y) (Fin.snoc w v)
      = upperState J B₀ ζ b x w + ζ • J - v • rankOne ℂ (b y) (b y) := by
  simp only [upperState, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  push_cast
  module

/-! ### The construction -/

/-- **The construction.**  Under the initial gap condition
`1/ζ + Ψ_J(B₀) ≤ 1/δ - Φ(A₀)` one can choose, for every `n`, points `x₁, …, xₙ` and positive
weights `w₁, …, wₙ` such that the lower matrix stays positive definite, the upper operator
stays strictly positive, and neither potential exceeds its initial value.

The proof is the induction of `Discretization.exists_points_weights`, with the operator
barrier lemma in the upper half. -/
theorem exists_points_weights [Nonempty ι] [Nonempty κ] [Countable κ]
    {A₀ : Matrix ι ι ℂ} (hA₀ : A₀.PosDef) (hJ : IsFiniteTracePos e J) {B₀ : H →L[ℂ] H}
    (hB₀ : IsStrictlyPositive B₀) {δ ζ : ℝ} (hδ : 0 < δ) (hζ : 0 < ζ) {a : Ω → ι → ℂ}
    {b : Ω → H} (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : MemLp b 2 μ)
    (hgrama : gram a μ = 1)
    (hgramb : ∀ u, RCLike.re ⟪u, J u⟫_ℂ = ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ)
    (hgap : 1 / ζ + upperPotential e J B₀ ≤ 1 / δ - lowerPotential A₀) (n : ℕ) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (lowerState A₀ δ a x w).PosDef ∧ IsStrictlyPositive (upperState J B₀ ζ b x w) ∧
      lowerPotential (lowerState A₀ δ a x w) ≤ lowerPotential A₀ ∧
      upperPotential e J (upperState J B₀ ζ b x w) ≤ upperPotential e J B₀ := by
  induction n with
  | zero =>
    exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, by simpa using hA₀, by simpa using hB₀,
      by simp, by simp⟩
  | succ k ih =>
    obtain ⟨x, w, hwpos, hAk, hBk, hΦ, hΨ⟩ := ih
    -- the gap is still open, so `δ` is still an admissible increment
    have hgapk : 1 / ζ + upperPotential e J (upperState J B₀ ζ b x w)
        ≤ 1 / δ - lowerPotential (lowerState A₀ δ a x w) := by linarith
    have hΨpos : 0 < upperPotential e J (upperState J B₀ ζ b x w) :=
      upperPotential_pos hJ hBk
    have hΦpos : 0 < lowerPotential (lowerState A₀ δ a x w) := lowerPotential_pos hAk
    have hcpos : 0 < 1 / ζ + upperPotential e J (upperState J B₀ ζ b x w) := by
      have hζ' : 0 < 1 / ζ := by positivity
      linarith
    have hδ' : δ < (lowerPotential (lowerState A₀ δ a x w))⁻¹ :=
      lt_inv_of_le_one_div_sub hδ hΦpos hcpos hgapk
    -- the new point, and the weight it admits
    obtain ⟨y, hy⟩ :=
      exists_admissible_point hAk hδ hδ' ha hgrama hJ hBk hζ hb hgramb hgapk
    have hU0 : 0 ≤ upperVerifier e J (upperState J B₀ ζ b x w) ζ (b y) :=
      upperVerifier_nonneg hJ hBk hζ (b y)
    have hLpos : 0 < lowerVerifier (lowerState A₀ δ a x w) δ (a y) := lt_of_le_of_lt hU0 hy
    have hwnew : 0 < 1 / lowerVerifier (lowerState A₀ δ a x w) δ (a y) := one_div_pos.2 hLpos
    have hcondL : 1 / (1 / lowerVerifier (lowerState A₀ δ a x w) δ (a y))
        ≤ lowerVerifier (lowerState A₀ δ a x w) δ (a y) := by rw [one_div_one_div]
    have hcondU : upperVerifier e J (upperState J B₀ ζ b x w) ζ (b y)
        ≤ 1 / (1 / lowerVerifier (lowerState A₀ δ a x w) δ (a y)) := by
      rw [one_div_one_div]; exact hy.le
    obtain ⟨hAnew, hΦnew⟩ := lowerPotential_update_le hAk hδ hδ' (a y) hwnew hcondL
    obtain ⟨hBnew, hΨnew⟩ := upperPotential_update_le hJ hBk hζ (b y) hwnew hcondU
    refine ⟨Fin.snoc x y, Fin.snoc w (1 / lowerVerifier (lowerState A₀ δ a x w) δ (a y)),
      ?_, ?_, ?_, ?_, ?_⟩
    · refine Fin.lastCases ?_ ?_
      · simpa using hwnew
      · intro j; simpa using hwpos j
    · rw [lowerState_snoc]; exact hAnew
    · rw [upperState_snoc]; exact hBnew
    · rw [lowerState_snoc]; exact hΦnew.trans hΦ
    · rw [upperState_snoc]; exact hΨnew.trans hΨ

end Infinite

end Discretization
