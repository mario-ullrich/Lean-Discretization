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
whose Gram operator `J` is positive, injective and of finite trace along `e`, and bounded by
`Λ • 1`.  With

`m = card ι`,  `M = Tr J / Λ`,  `r = √((m-1)/n)`,  `s = √((M-1)/n)`,

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

/-- **The upper barrier of a countable second family.**  The states are the bounded operators
on `H`, the admissible ones the strictly positive operators, and potential and verifier are
`Discretization.Infinite.upperPotential` and `Discretization.Infinite.upperVerifier` along the
Hilbert basis `e`, for a square-integrable `b` whose Gram operator is `J`. -/
noncomputable def operatorUpperBarrier [Nonempty κ] [Countable κ] (hJ : IsFiniteTracePos e J)
    {b : Ω → H} (hb : MemLp b 2 μ)
    (hgramb : ∀ u, RCLike.re ⟪u, J u⟫_ℂ = ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ) :
    UpperBarrier μ (H →L[ℂ] H) where
  J := J
  R y := rankOne ℂ (b y) (b y)
  Adm B := IsStrictlyPositive B
  pot := upperPotential e J
  ver B ζ y := upperVerifier e J B ζ (b y)
  tr := traceAlong e J
  sq y := ‖b y‖ ^ 2
  pot_pos hB := upperPotential_pos hJ hB
  ver_nonneg hB hζ y := upperVerifier_nonneg hJ hB hζ (b y)
  integrable_ver B ζ := integrable_upperVerifier hb J B ζ
  integral_ver_lt hB hζ := integral_upperVerifier_lt hJ hB hζ hb hgramb
  update_le y hB hζ hw hcond := upperPotential_update_le hJ hB hζ (b y) hw hcond
  J_nonneg := hJ.nonneg
  inv_pot_smul_le hB := inv_upperPotential_smul_le hJ hB
  adm_smul_one hc := isStrictlyPositive_smul_one hc
  pot_smul_one hc := upperPotential_smul_one hc
  tr_pos := hJ.traceAlong_pos
  R_le y := rankOne_le_norm_sq_smul_one (b y)
  sq_nonneg y := by positivity
  integrable_sq := (memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).1 hb
  integral_sq := integral_norm_sq_eq_traceAlong hJ hb hgramb

/-- **Discretization theorem for a normalized first family and a countable
second family**, with no side condition beyond `n ≥ m`: the theorem
`Discretization.UpperBarrier.bss_generalized_of_gram_eq_one'` for the upper barrier
`Discretization.Infinite.operatorUpperBarrier`. -/
theorem bss_generalized_of_gram_eq_one' [Fintype ι] [DecidableEq ι] [Nonempty ι] [Nonempty κ]
    [Countable κ] (hJ : IsFiniteTracePos e J) {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : J ≤ Λ • (1 : H →L[ℂ] H)) {a : Ω → ι → ℂ} {b : Ω → H}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : MemLp b 2 μ) (hgrama : gram a μ = 1)
    (hgramb : ∀ u, RCLike.re ⟪u, J u⟫_ℂ = ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ i, w i • Matrix.vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
        ≤ ((1 + Real.sqrt ((traceAlong e J / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : H →L[ℂ] H) :=
  (operatorUpperBarrier hJ hb hgramb).bss_generalized_of_gram_eq_one' hΛ hJΛ ha hgrama hmn

end Infinite

end Discretization
