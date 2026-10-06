/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import BasicResults.Matrix.PotentialBounds
public import Discretization.Averages

/-!
# The upper half of the construction, for matrices and operators alike

The construction carries two states: a lower matrix `A`, built from the first family, and an
upper state `B`, built from the second.  The second family may be finite, and then `B` is a
matrix, or a map into a Hilbert space, and then `B` is an operator on that space
(`Discretization/Infinite/`).  The analysis of the upper state differs between the two cases,
since every trace of an operator is a series, but the construction and the assembly of the
theorem use only a few of its properties.  A `Discretization.UpperBarrier` collects them: an
ordered real vector space `S` of states with a unit `1`, the Gram element `J ∈ S` of the
second family, its rank-one pieces `R(y) = b(y) b(y)*`, a class of admissible states, the
upper potential `Ψ`, the upper verifier `U`, the trace `Tr J` and the squared norms
`‖b(y)‖²`, subject to

* `Ψ(B) > 0` and `U_B^ζ ≥ 0` for every admissible `B` and `ζ > 0`;
* the **barrier step**: if `U_B^ζ(y) ≤ 1/w`, then `B + ζ J - w R(y)` is admissible, with
  potential at most `Ψ(B)`;
* the **average**: `U_B^ζ` is integrable, with `∫ U_B^ζ dμ < 1/ζ + Ψ(B)`;
* the **read-off**: `Ψ(B)⁻¹ J ≤ B` and `0 ≤ J`, and for `c > 0` the state `c • 1` is
  admissible with `Ψ(c • 1) = Tr J / c`, where `Tr J > 0`;
* the **crude bound** `R(y) ≤ ‖b(y)‖² • 1`, with `∫ ‖b‖² dμ = Tr J`.

This file states the definition, the upper state after `k` steps
(`Discretization.UpperBarrier.upperState`), the existence of an admissible point
(`Discretization.UpperBarrier.exists_admissible_point`), and the finite instance,
`Discretization.matrixUpperBarrier`.  The operator instance is
`Discretization.Infinite.operatorUpperBarrier`.  The construction, the potential argument and its
edge cases are then proved once for every upper barrier, in the files that follow.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

/-- **The upper half of the barrier argument**, for a second family whose states live in an
ordered real vector space `S` with a unit.  See the module docstring for the meaning of the
fields; the finite instance is `Discretization.matrixUpperBarrier`. -/
structure UpperBarrier {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (S : Type*)
    [AddCommGroup S] [PartialOrder S] [Module ℝ S] [One S] where
  /-- The Gram element of the second family. -/
  J : S
  /-- The rank-one piece `b(y) b(y)*` of the point `y`. -/
  R : Ω → S
  /-- The states the construction may pass through. -/
  Adm : S → Prop
  /-- The upper potential `Ψ_J`. -/
  pot : S → ℝ
  /-- The upper verifier: `ver B ζ y` is `U_B^ζ(b(y))`. -/
  ver : S → ℝ → Ω → ℝ
  /-- The trace of `J`. -/
  tr : ℝ
  /-- The squared norm `‖b(y)‖²`. -/
  sq : Ω → ℝ
  /-- The potential of an admissible state is positive. -/
  pot_pos : ∀ {B : S}, Adm B → 0 < pot B
  /-- The verifier of an admissible state is nonnegative. -/
  ver_nonneg : ∀ {B : S} {ζ : ℝ}, Adm B → 0 < ζ → ∀ y, 0 ≤ ver B ζ y
  /-- The verifier is integrable. -/
  integrable_ver : ∀ (B : S) (ζ : ℝ), Integrable (ver B ζ) μ
  /-- The average of the verifier stays below `1/ζ + Ψ(B)`. -/
  integral_ver_lt : ∀ {B : S} {ζ : ℝ}, Adm B → 0 < ζ → ∫ y, ver B ζ y ∂μ < 1 / ζ + pot B
  /-- The barrier step. -/
  update_le : ∀ {B : S} {ζ w : ℝ} (y : Ω), Adm B → 0 < ζ → 0 < w → ver B ζ y ≤ 1 / w →
    Adm (B + ζ • J - w • R y) ∧ pot (B + ζ • J - w • R y) ≤ pot B
  /-- The Gram element is positive. -/
  J_nonneg : 0 ≤ J
  /-- A bound on the potential is a bound on the state. -/
  inv_pot_smul_le : ∀ {B : S}, Adm B → (pot B)⁻¹ • J ≤ B
  /-- Positive multiples of the unit are admissible. -/
  adm_smul_one : ∀ {c : ℝ}, 0 < c → Adm (c • (1 : S))
  /-- The potential of a multiple of the unit. -/
  pot_smul_one : ∀ {c : ℝ}, c ≠ 0 → pot (c • (1 : S)) = tr / c
  /-- The trace of `J` is positive. -/
  tr_pos : 0 < tr
  /-- The crude bound `b(y) b(y)* ≤ ‖b(y)‖² • 1`. -/
  R_le : ∀ y, R y ≤ sq y • (1 : S)
  /-- Squared norms are nonnegative. -/
  sq_nonneg : ∀ y, 0 ≤ sq y
  /-- The squared norm is integrable. -/
  integrable_sq : Integrable sq μ
  /-- The average of the squared norm is the trace of `J`. -/
  integral_sq : ∫ y, sq y ∂μ = tr

namespace UpperBarrier

variable {Ω S : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [AddCommGroup S] [PartialOrder S]
  [Module ℝ S] [One S] (U : UpperBarrier μ S)

/-! ### The upper state -/

/-- The upper state after the steps recorded by the points `x` and the weights `w`,
`B₀ + k ζ • J - ∑ wᵢ R(xᵢ)`. -/
def upperState (B₀ : S) (ζ : ℝ) {k : ℕ} (x : Fin k → Ω) (w : Fin k → ℝ) : S :=
  B₀ + ((k : ℝ) * ζ) • U.J - ∑ i, w i • U.R (x i)

/-- With no points chosen, the upper state is `B₀`. -/
@[simp]
theorem upperState_zero (B₀ : S) (ζ : ℝ) (x : Fin 0 → Ω) (w : Fin 0 → ℝ) :
    U.upperState B₀ ζ x w = B₀ := by simp [upperState]

/-- One step of the upper state: grow by `ζ • J` and subtract the new rank-one piece. -/
theorem upperState_snoc (B₀ : S) (ζ : ℝ) {k : ℕ} (x : Fin k → Ω) (w : Fin k → ℝ) (y : Ω)
    (v : ℝ) :
    U.upperState B₀ ζ (Fin.snoc x y) (Fin.snoc w v)
      = U.upperState B₀ ζ x w + ζ • U.J - v • U.R y := by
  simp only [upperState, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  push_cast
  module

/-! ### An admissible point exists -/

/-- **An admissible point exists.**  If the gap opened by the two shifts is large enough,
`1/δ - Φ(A) ≥ 1/ζ + Ψ(B)`, then some point passes the test of both verifiers: on average the
lower verifier exceeds `1/δ - Φ(A)` (`Discretization.integral_lowerVerifier_gt`) and the upper
one stays below `1/ζ + Ψ(B)`. -/
theorem exists_admissible_point {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : Matrix ι ι ℂ} (hA : A.PosDef) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < (lowerPotential A)⁻¹)
    {a : Ω → ι → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hgrama : gram a μ = 1)
    {B : S} (hB : U.Adm B) {ζ : ℝ} (hζ : 0 < ζ)
    (hgap : 1 / ζ + U.pot B ≤ 1 / δ - lowerPotential A) :
    ∃ y, U.ver B ζ y < lowerVerifier A δ (a y) := by
  have hlow := integral_lowerVerifier_gt hA hδ hδ' ha hgrama
  have hup := U.integral_ver_lt hB hζ
  refine exists_lt_of_integral_lt (μ := μ) (f := fun y => lowerVerifier A δ (a y))
    (g := U.ver B ζ) (integrable_lowerVerifier ha) (U.integrable_ver B ζ) ?_
  linarith

end UpperBarrier

/-! ### A finite second family -/

variable {κ Ω : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] [MeasurableSpace Ω]
  {μ : Measure Ω}

/-- **The upper barrier of a finite second family.**  The states are the matrices over `κ`,
the admissible ones the positive definite matrices, and potential and verifier are those of
`Discretization.upperPotential` and `Discretization.upperVerifier`, for a family `b` whose Gram
matrix is the positive definite `J`. -/
noncomputable def matrixUpperBarrier {J : Matrix κ κ ℂ} (hJ : J.PosDef) {b : Ω → κ → ℂ}
    (hb : ∀ k, MemLp (fun x => b x k) 2 μ) (hgramb : gram b μ = J) :
    UpperBarrier μ (Matrix κ κ ℂ) where
  J := J
  R y := vecMulVec (b y) (star (b y))
  Adm B := B.PosDef
  pot := upperPotential J
  ver B ζ y := upperVerifier J B ζ (b y)
  tr := RCLike.re J.trace
  sq y := ∑ p, ‖b y p‖ ^ 2
  pot_pos hB := upperPotential_pos hJ hB
  ver_nonneg hB hζ y := upperVerifier_nonneg hJ hB hζ (b y)
  integrable_ver _ _ := integrable_upperVerifier hb
  integral_ver_lt hB hζ := integral_upperVerifier_lt hJ hB hζ hb hgramb
  update_le y hB hζ hw hcond := upperPotential_update_le hJ hB hζ (b y) hw hcond
  J_nonneg := hJ.posSemidef.nonneg
  inv_pot_smul_le hB := hB.inv_re_trace_mul_smul_le hJ
  adm_smul_one hc := Matrix.PosDef.one.smul hc
  pot_smul_one hc := upperPotential_smul_one J hc
  tr_pos := (RCLike.pos_iff.mp hJ.trace_pos).1
  R_le y := Matrix.vecMulVec_le_norm_sq_smul_one (b y)
  sq_nonneg y := Finset.sum_nonneg fun p _ => by positivity
  integrable_sq := integrable_finsetSum _ fun p _ => integrable_norm_sq hb p
  integral_sq := by
    show ∫ y, ∑ p, ‖b y p‖ ^ 2 ∂μ = RCLike.re J.trace
    rw [integral_sum_norm_sq hb, hgramb]

end Discretization
