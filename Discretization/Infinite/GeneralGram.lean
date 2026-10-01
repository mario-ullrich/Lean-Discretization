/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.GeneralGram
public import Discretization.Infinite.UpperBarrier
public import BasicResults.Operator.GramOperator

/-!
# Removing the normalisation of the first family, with a second family in a Hilbert space

The first family is finite here as well, and the reduction that removes the normalisation
does not look at the second one.  It is therefore the lemma
`Discretization.bss_of_gram_eq_one` of the finite development, applied with the upper frame
bound between operators as the conclusion it carries along: replace `a` by `I^{-1/2} a`,
where `I = ∫ a a* dμ`, so that the new family is orthonormal, and conjugate the resulting
lower frame bound back by `I^{1/2}`.

In both theorems the Gram operator is the Bochner integral `J = ∫ b(x) b(x)* dμ(x)`, the
only further hypothesis on it is injectivity, and the effective dimension is
`M = ∫ ‖b‖² dμ / Λ`; positivity and the finiteness of the trace follow from the definition
(`Discretization.Infinite.isFiniteTracePos_of_integral_rankOne`).  The version for a Hilbert
space with a countable Hilbert basis is
`Discretization.Infinite.bss_generalized_of_hilbertBasis`; the basis only witnesses that the
space is separable and appears in no other place of the statement.  The headline
`Discretization.Infinite.bss_generalized` assumes separability instead and chooses a basis,
which is countable (`HilbertBasis.countable_of_separableSpace`).  This is Theorem 3 of the
paper for a second family with values in a separable Hilbert space, with no side condition
beyond `n ≥ m`.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped InnerProductSpace ComplexOrder MatrixOrder
open InnerProductSpace
open ContinuousLinearMap

namespace Discretization

namespace Infinite

variable {ι κ Ω H : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] [MeasurableSpace Ω] {μ : Measure Ω}
  {J : H →L[ℂ] H}

/-- **Discretization theorem** (Chkifa–Dolbeault–Krieg–Ullrich, Theorem 3), for a Hilbert
space with a countable Hilbert basis.

Let `a` be a family of square-integrable functions indexed by a finite nonempty set `ι` of
`m` elements with positive definite Gram matrix `I = ∫ a a* dμ`, and let `b : Ω → H` be
square-integrable with injective Gram operator `J = ∫ b(x) b(x)* dμ(x)` bounded by
`Λ • 1`, and put `M = ∫ ‖b‖² dμ / Λ`.  Then for every `n ≥ m` there are `n` points and
positive weights with

`(1 - √((m-1)/n))² • I ≤ ∑ wᵢ a(xᵢ) a(xᵢ)*`  and
`∑ wᵢ b(xᵢ) b(xᵢ)* ≼ (1 + √((M-1)/n))² Λ • 1`,

the first in the matrix order and the second in the order of operators.  The first bound is
the Loewner form of the paper's `(1 - √((m-1)/n))² λ_min(I)`.  There is no side condition:
the edge cases of `m` and of `M` are covered by
`Discretization.Infinite.bss_generalized_of_gram_eq_one'`. -/
theorem bss_generalized_of_hilbertBasis [Nonempty ι] [Nonempty κ] [Countable κ]
    (e : HilbertBasis κ ℂ H) {Λ : ℝ} (hΛ : 0 < Λ) (hJΛ : J ≤ Λ • (1 : H →L[ℂ] H))
    (hJinj : ∀ v, J v = 0 → v = 0) {a : Ω → ι → ℂ} {b : Ω → H}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : MemLp b 2 μ) (hI : (gram a μ).PosDef)
    (hgramb : ∫ x, rankOne ℂ (b x) (b x) ∂μ = J)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • gram a μ
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
        ≤ ((1 + Real.sqrt (((∫ y, ‖b y‖ ^ 2 ∂μ) / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : H →L[ℂ] H) :=
  bss_of_gram_eq_one ha hI
    (P := fun x w => ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
      ≤ ((1 + Real.sqrt (((∫ y, ‖b y‖ ^ 2 ∂μ) / Λ - 1) / n)) ^ 2 * Λ) • (1 : H →L[ℂ] H))
    fun _ ha' hgram' =>
      bss_generalized_of_gram_eq_one' e hΛ hJΛ hJinj ha' hb hgram' hgramb hmn

/-- **Discretization theorem** (Chkifa–Dolbeault–Krieg–Ullrich, Theorem 3), for a second
family with values in a separable Hilbert space, with no basis in the statement.

Let `a` be a family of square-integrable functions indexed by a finite nonempty set `ι` of
`m` elements with positive definite Gram matrix `I = ∫ a a* dμ`, and let `b : Ω → H` be
square-integrable, with values in a nonzero separable Hilbert space.  Let
`J = ∫ b(x) b(x)* dμ(x)` be its Gram operator, assume `J` injective and `J ≤ Λ • 1`, and put
`M = ∫ ‖b‖² dμ / Λ`.  Then for every `n ≥ m` there are `n` points and positive weights with

`(1 - √((m-1)/n))² • I ≤ ∑ᵢ wᵢ a(xᵢ) a(xᵢ)*`  and
`∑ᵢ wᵢ b(xᵢ) b(xᵢ)* ≼ (1 + √((M-1)/n))² Λ • 1`.

Positivity of `J` and the finiteness of its trace follow from its definition.  The two
hypotheses on `J` can be checked on `b`: `J ≤ Λ • 1` is the Bessel-type bound
`∫ |⟪u, b⟫|² dμ ≤ Λ ‖u‖²` (`ContinuousLinearMap.integral_rankOne_self_le_iff`), and
injectivity says that `⟪u, b(·)⟫ = 0` almost everywhere only for `u = 0`
(`ContinuousLinearMap.integral_rankOne_self_injective_iff`). -/
theorem bss_generalized [Nonempty ι] [TopologicalSpace.SeparableSpace H] [Nontrivial H]
    {Λ : ℝ} (hΛ : 0 < Λ) (hJΛ : J ≤ Λ • (1 : H →L[ℂ] H)) (hJinj : ∀ v, J v = 0 → v = 0)
    {a : Ω → ι → ℂ} {b : Ω → H}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : MemLp b 2 μ) (hI : (gram a μ).PosDef)
    (hgramb : ∫ x, rankOne ℂ (b x) (b x) ∂μ = J)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • gram a μ
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
        ≤ ((1 + Real.sqrt (((∫ y, ‖b y‖ ^ 2 ∂μ) / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : H →L[ℂ] H) := by
  -- a Hilbert basis, countable because `H` is separable
  obtain ⟨s, e, -⟩ := exists_hilbertBasis ℂ H
  have : Countable s := e.countable_of_separableSpace
  have : Nonempty s := e.nonempty_of_nontrivial
  exact bss_generalized_of_hilbertBasis e hΛ hJΛ hJinj ha hb hI hgramb hmn

end Infinite

end Discretization
