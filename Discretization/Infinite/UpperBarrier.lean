/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.EdgeCases.BothEdgeCases
public import Discretization.Infinite.Averages
public import Discretization.Infinite.Bounds

/-!
# The operators as an upper barrier

The theorem `Discretization.bss_generalized_of_gram_eq_one'` for a second family given by a
square-integrable map `b : Ω → H` into a Hilbert space with a countable Hilbert basis `e`,
whose Gram operator `J = ∫ b(x) b(x)* dμ(x)` is injective and bounded by `Λ • 1`.  With

`m = card ι`,  `M = ∫ ‖b‖² dμ / Λ`,  `r = √((m-1)/n)`,  `s = √((M-1)/n)`,

for every `n ≥ m` there are `n` points and positive weights with

`(1 - r)² • 1 ≼ ∑ᵢ wᵢ a(xᵢ) a(xᵢ)*`  and  `∑ᵢ wᵢ b(xᵢ) b(xᵢ)* ≼ (1 + s)² Λ • 1`,

the first in the matrix order and the second in the operator order, with no side condition
beyond `n ≥ m`.

Everything but the analysis of the upper state is shared with the finite case.  The
operators on `H` form an upper barrier, `Discretization.Infinite.operatorUpperBarrier`, whose
fields are the potential, the verifier, the barrier lemma, the averages and the read-off of
the preceding files, and the theorem is
`Discretization.UpperBarrier.bss_generalized_of_gram_eq_one'` for it.  Its four cases are
those of the finite theorem: the potential argument
`Discretization.UpperBarrier.bss_generalized_of_gram_eq_one` and the three edge cases
`Discretization.UpperBarrier.bss_generalized_of_unique`,
`Discretization.UpperBarrier.bss_generalized_of_small_dim` and
`Discretization.UpperBarrier.bss_generalized_of_unique_of_small_dim`.
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace ComplexOrder MatrixOrder
open InnerProductSpace
open ContinuousLinearMap

namespace Discretization

namespace Infinite

variable {ι κ Ω H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace Ω] {μ : Measure Ω} {e : HilbertBasis κ ℂ H} {J : H →L[ℂ] H}

/-- **The upper barrier of a second family in a Hilbert space.**  The states are the bounded
operators on `H`, the admissible ones the strictly positive operators, and potential and
verifier are `Discretization.Infinite.upperPotential` and `Discretization.Infinite.upperVerifier`
along the countable Hilbert basis `e`, for a square-integrable `b` with injective Gram
operator `J = ∫ b(x) b(x)* dμ(x)`.  The trace it records is `∫ ‖b‖² dμ`, which equals the
trace of `J` along `e` (`Discretization.Infinite.integral_norm_sq_eq_traceAlong`). -/
noncomputable def operatorUpperBarrier [Nonempty κ] [Countable κ] (e : HilbertBasis κ ℂ H)
    {b : Ω → H} (hb : MemLp b 2 μ) (hJb : ∫ x, rankOne ℂ (b x) (b x) ∂μ = J)
    (hinj : ∀ v, J v = 0 → v = 0) :
    UpperBarrier μ (H →L[ℂ] H) :=
  have hJ := isFiniteTracePos_of_integral_rankOne e hb hJb hinj
  have htr := integral_norm_sq_eq_traceAlong e hb hJb
  { J := J
    R y := rankOne ℂ (b y) (b y)
    Adm B := IsStrictlyPositive B
    pot := upperPotential e J
    ver B ζ y := upperVerifier e J B ζ (b y)
    tr := ∫ y, ‖b y‖ ^ 2 ∂μ
    sq y := ‖b y‖ ^ 2
    pot_pos hB := upperPotential_pos hJ hB
    ver_nonneg hB hζ y := upperVerifier_nonneg hJ hB hζ (b y)
    integrable_ver B ζ := integrable_upperVerifier hb J B ζ
    integral_ver_lt hB hζ := integral_upperVerifier_lt hb hJb hinj hB hζ
    update_le y hB hζ hw hcond := upperPotential_update_le hJ hB hζ (b y) hw hcond
    J_nonneg := hJ.nonneg
    inv_pot_smul_le hB := inv_upperPotential_smul_le hJ hB
    adm_smul_one hc := isStrictlyPositive_smul_one hc
    pot_smul_one hc := by rw [upperPotential_smul_one hc, htr]
    tr_pos := htr ▸ hJ.traceAlong_pos
    R_le y := rankOne_le_norm_sq_smul_one (b y)
    sq_nonneg y := by positivity
    integrable_sq := (memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).1 hb
    integral_sq := rfl }

/-- **Discretization theorem for a normalized first family and a second family in a Hilbert
space with a countable Hilbert basis**, with no side condition beyond `n ≥ m`: the theorem
`Discretization.UpperBarrier.bss_generalized_of_gram_eq_one'` for the upper barrier
`Discretization.Infinite.operatorUpperBarrier`.  The Gram operator is
`J = ∫ b(x) b(x)* dμ(x)`, and the effective dimension is `M = ∫ ‖b‖² dμ / Λ`. -/
theorem bss_generalized_of_gram_eq_one' [Fintype ι] [DecidableEq ι] [Nonempty ι] [Nonempty κ]
    [Countable κ] (e : HilbertBasis κ ℂ H) {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : J ≤ Λ • (1 : H →L[ℂ] H)) (hinj : ∀ v, J v = 0 → v = 0) {a : Ω → ι → ℂ}
    {b : Ω → H} (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : MemLp b 2 μ)
    (hgrama : gram a μ = 1) (hgramb : ∫ x, rankOne ℂ (b x) (b x) ∂μ = J)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ i, w i • Matrix.vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
        ≤ ((1 + Real.sqrt (((∫ y, ‖b y‖ ^ 2 ∂μ) / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : H →L[ℂ] H) :=
  (operatorUpperBarrier e hb hgramb hinj).bss_generalized_of_gram_eq_one' hΛ hJΛ ha hgrama hmn

end Infinite

end Discretization
