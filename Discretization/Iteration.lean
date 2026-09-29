/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.Parameters
public import Discretization.UpperBarrier

/-!
# The construction, step by step

Starting from a positive definite matrix `A₀` and an admissible upper state `B₀`, the
construction picks points `x₁, …, xₙ` and positive weights `w₁, …, wₙ` one at a time.  After
`k` steps the state is

* `Discretization.lowerState A₀ δ a x w = A₀ - k δ • 1 + ∑ wᵢ a(xᵢ) a(xᵢ)*` and
* `Discretization.UpperBarrier.upperState U B₀ ζ x w = B₀ + k ζ • J - ∑ wᵢ b(xᵢ) b(xᵢ)*`,

the second for an upper barrier `U` (`Discretization.UpperBarrier`), which is a matrix for a
finite second family and an operator for a countable one.

The **invariant** carried through the induction is that both states are admissible and that
neither potential has increased beyond its initial value.  The invariant keeps the gap
`1/δ - Φ ≥ 1/ζ + Ψ` open, which by `Discretization.UpperBarrier.exists_admissible_point`
produces the next point; the weight is the reciprocal of its lower verifier, and the barrier
lemma restores the invariant.

The result is `Discretization.UpperBarrier.exists_points_weights`.  Note that the number of
steps `n` is arbitrary: the initial gap condition alone drives the whole construction, and it
is the choice of `A₀`, `B₀`, `δ` and `ζ` in `Discretization.PotentialArgument` that ties `n` to the
frame bounds.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] {μ : Measure Ω}

/-- The lower matrix after the steps recorded by the points `x` and the weights `w`. -/
noncomputable def lowerState (A₀ : Matrix ι ι ℂ) (δ : ℝ) (a : Ω → ι → ℂ) {k : ℕ}
    (x : Fin k → Ω) (w : Fin k → ℝ) : Matrix ι ι ℂ :=
  A₀ - ((k : ℝ) * δ) • 1 + ∑ i, w i • vecMulVec (a (x i)) (star (a (x i)))

/-- Appending a positive weight to a family of positive weights keeps all of them
positive. -/
theorem forall_snoc_pos {k : ℕ} {w : Fin k → ℝ} (hw : ∀ i, 0 < w i) {v : ℝ} (hv : 0 < v) :
    ∀ i, 0 < (Fin.snoc w v : Fin (k + 1) → ℝ) i := by
  refine Fin.lastCases ?_ ?_
  · simpa using hv
  · intro j; simpa using hw j

omit [Fintype ι] [MeasurableSpace Ω] in
/-- With no points chosen, the lower state is `A₀`. -/
@[simp]
theorem lowerState_zero (A₀ : Matrix ι ι ℂ) (δ : ℝ) (a : Ω → ι → ℂ) (x : Fin 0 → Ω)
    (w : Fin 0 → ℝ) : lowerState A₀ δ a x w = A₀ := by simp [lowerState]

omit [Fintype ι] [MeasurableSpace Ω] in
/-- One step of the lower state: shrink by `δ • 1` and add the new rank-one matrix. -/
theorem lowerState_snoc (A₀ : Matrix ι ι ℂ) (δ : ℝ) (a : Ω → ι → ℂ) {k : ℕ}
    (x : Fin k → Ω) (w : Fin k → ℝ) (y : Ω) (v : ℝ) :
    lowerState A₀ δ a (Fin.snoc x y) (Fin.snoc w v)
      = lowerState A₀ δ a x w - δ • 1 + v • vecMulVec (a y) (star (a y)) := by
  simp only [lowerState, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  push_cast
  module

namespace UpperBarrier

variable {S : Type*} [AddCommGroup S] [PartialOrder S] [Module ℝ S] [One S]
  (U : UpperBarrier μ S)

/-- **The construction.**  Under the initial gap condition
`1/ζ + Ψ(B₀) ≤ 1/δ - Φ(A₀)` one can choose, for every `n`, points `x₁, …, xₙ` and positive
weights `w₁, …, wₙ` such that both states stay admissible, the lower one positive definite,
and neither potential exceeds its initial value. -/
theorem exists_points_weights [Nonempty ι] {A₀ : Matrix ι ι ℂ} (hA₀ : A₀.PosDef) {B₀ : S}
    (hB₀ : U.Adm B₀) {δ ζ : ℝ} (hδ : 0 < δ) (hζ : 0 < ζ) {a : Ω → ι → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hgrama : gram a μ = 1)
    (hgap : 1 / ζ + U.pot B₀ ≤ 1 / δ - lowerPotential A₀) (n : ℕ) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (lowerState A₀ δ a x w).PosDef ∧ U.Adm (U.upperState B₀ ζ x w) ∧
      lowerPotential (lowerState A₀ δ a x w) ≤ lowerPotential A₀ ∧
      U.pot (U.upperState B₀ ζ x w) ≤ U.pot B₀ := by
  induction n with
  | zero =>
    exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, by simpa using hA₀, by simpa using hB₀,
      by simp, by simp⟩
  | succ k ih =>
    obtain ⟨x, w, hwpos, hAk, hBk, hΦ, hΨ⟩ := ih
    -- the gap is still open, so `δ` is still an admissible increment
    have hgapk : 1 / ζ + U.pot (U.upperState B₀ ζ x w)
        ≤ 1 / δ - lowerPotential (lowerState A₀ δ a x w) := by linarith
    have hΨpos : 0 < U.pot (U.upperState B₀ ζ x w) := U.pot_pos hBk
    have hΦpos : 0 < lowerPotential (lowerState A₀ δ a x w) := lowerPotential_pos hAk
    have hcpos : 0 < 1 / ζ + U.pot (U.upperState B₀ ζ x w) := by
      have hζ' : 0 < 1 / ζ := by positivity
      linarith
    have hδ' : δ < (lowerPotential (lowerState A₀ δ a x w))⁻¹ :=
      lt_inv_of_le_one_div_sub hδ hΦpos hcpos hgapk
    -- the new point, and the weight it admits
    obtain ⟨y, hy⟩ := U.exists_admissible_point hAk hδ hδ' ha hgrama hBk hζ hgapk
    obtain ⟨hwnew, hcondL, hcondU⟩ := weight_of_verifier_lt (U.ver_nonneg hBk hζ y) hy
    obtain ⟨hAnew, hΦnew⟩ := lowerPotential_update_le hAk hδ hδ' (a y) hwnew hcondL
    obtain ⟨hBnew, hΨnew⟩ := U.update_le y hBk hζ hwnew hcondU
    refine ⟨Fin.snoc x y, Fin.snoc w (1 / lowerVerifier (lowerState A₀ δ a x w) δ (a y)),
      ?_, ?_, ?_, ?_, ?_⟩
    · exact forall_snoc_pos hwpos hwnew
    · rw [lowerState_snoc]; exact hAnew
    · rw [upperState_snoc]; exact hBnew
    · rw [lowerState_snoc]; exact hΦnew.trans hΦ
    · rw [upperState_snoc]; exact hΨnew.trans hΨ

end UpperBarrier

end Discretization
