/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.GeneralGram
import Discretization.Infinite.BothEdgeCases

/-!
# Removing the normalisation of the first family, with a countable second family

The first family is finite here as well, and the reduction that removes the normalisation
does not look at the second one.  It is therefore the lemma
`Discretization.bss_of_gram_eq_one` of the finite development, applied with the upper frame
bound between operators as the conclusion it carries along: replace `a` by `I^{-1/2} a`,
where `I = ∫ a a* dμ`, so that the new family is orthonormal, and conjugate the resulting
lower frame bound back by `I^{1/2}`.

The result is `Discretization.Infinite.bss_generalized`, which is Theorem 3 of the paper for
a countable second family, with no side condition beyond `n ≥ m`.
-/

open Matrix MeasureTheory
open scoped InnerProductSpace ComplexOrder MatrixOrder
open InnerProductSpace
open ContinuousLinearMap

namespace Discretization

namespace Infinite

variable {ι κ Ω H : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] [MeasurableSpace Ω] {μ : Measure Ω}
  {e : HilbertBasis κ ℂ H} {J : H →L[ℂ] H}

/-- **Generalized sparsification theorem** (Chkifa–Dolbeault–Krieg–Ullrich, Theorem 3), for
a countable second family.

Let `a` be a family of square-integrable functions indexed by a finite nonempty set `ι` of
`m` elements with positive definite Gram matrix `I = ∫ a a* dμ`, and let `b : Ω → H` be
square-integrable with Gram operator `J` positive, injective and of finite trace, bounded by
`Λ • 1`, with effective dimension `M = Tr J / Λ`.  Then for every `n ≥ m` there are `n`
points and positive weights with

`(1 - √((m-1)/n))² • I ≤ ∑ wᵢ a(xᵢ) a(xᵢ)*`  and
`∑ wᵢ b(xᵢ) b(xᵢ)* ≼ (1 + √((M-1)/n))² Λ • 1`,

the first in the matrix order and the second in the order of operators.  The first bound is
the Loewner form of the paper's `(1 - √((m-1)/n))² λ_min(I)`.  There is no side condition:
the edge cases of `m` and of `M` are covered by
`Discretization.Infinite.bss_generalized_of_gram_eq_one'`. -/
theorem bss_generalized [Nonempty ι] [Nonempty κ] [Countable κ]
    (hJ : IsFiniteTracePos e J) {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : J ≤ Λ • (1 : H →L[ℂ] H)) {a : Ω → ι → ℂ} {b : Ω → H}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : MemLp b 2 μ) (hI : (gram a μ).PosDef)
    (hgramb : ∀ u, RCLike.re ⟪u, J u⟫_ℂ = ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • gram a μ
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
        ≤ ((1 + Real.sqrt ((traceAlong e J / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : H →L[ℂ] H) :=
  bss_of_gram_eq_one ha hI
    (P := fun x w => ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
      ≤ ((1 + Real.sqrt ((traceAlong e J / Λ - 1) / n)) ^ 2 * Λ) • (1 : H →L[ℂ] H))
    fun _ ha' hgram' => bss_generalized_of_gram_eq_one' hJ hΛ hJΛ ha' hb hgram' hgramb hmn

end Infinite

end Discretization
