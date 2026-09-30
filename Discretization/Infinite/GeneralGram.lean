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
# Removing the normalisation of the first family, with a countable second family

The first family is finite here as well, and the reduction that removes the normalisation
does not look at the second one.  It is therefore the lemma
`Discretization.bss_of_gram_eq_one` of the finite development, applied with the upper frame
bound between operators as the conclusion it carries along: replace `a` by `I^{-1/2} a`,
where `I = ∫ a a* dμ`, so that the new family is orthonormal, and conjugate the resulting
lower frame bound back by `I^{1/2}`.

The result along a given Hilbert basis is
`Discretization.Infinite.bss_generalized_of_hilbertBasis`.  The headline
`Discretization.Infinite.bss_generalized` has no basis in its statement.  Its Gram operator
is the Bochner integral `J = ∫ b(x) b(x)* dμ(x)`, whose quadratic form is
`⟪u, J u⟫ = ∫ |⟪u, b(x)⟫|² dμ(x)` (`ContinuousLinearMap.inner_integral_rankOne_self`).  For a
separable space the proof chooses a Hilbert basis, which is countable
(`HilbertBasis.countable_of_separableSpace`), and the quadratic form supplies what the basis
version assumes, positivity of `J` (`ContinuousLinearMap.nonneg_of_inner_eq_integral`) and the
finiteness of its trace (`ContinuousLinearMap.summable_re_inner_of_gram`), with value
`∫ ‖b‖² dμ`.  So the only hypothesis on `J` besides its definition is injectivity, and the
effective dimension is `M = ∫ ‖b‖² dμ / Λ`.  This is Theorem 3 of the paper for a second
family with values in a separable Hilbert space, with no side condition beyond `n ≥ m`.
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
theorem bss_generalized_of_hilbertBasis [Nonempty ι] [Nonempty κ] [Countable κ]
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

/-- **Generalized sparsification theorem** (Chkifa–Dolbeault–Krieg–Ullrich, Theorem 3), for
a second family with values in a separable Hilbert space, with no basis in the statement.

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
  obtain ⟨s, e0, -⟩ := exists_hilbertBasis ℂ H
  have : Countable s := e0.countable_of_separableSpace
  have : Nonempty s := e0.nonempty_of_nontrivial
  -- what the quadratic form of `J` gives along it
  have hq : ∀ u, ⟪u, J u⟫_ℂ = ((∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := fun u => by
    rw [← hgramb]
    exact inner_integral_rankOne_self hb u
  have hre := re_inner_eq_integral hq
  have hJ : IsFiniteTracePos e0 J :=
    ⟨nonneg_of_inner_eq_integral hq, summable_re_inner_of_gram e0 hb hre, hJinj⟩
  have htr : traceAlong e0 J = ∫ y, ‖b y‖ ^ 2 ∂μ :=
    (integral_norm_sq_eq_traceAlong hJ hb hre).symm
  have h := bss_generalized_of_hilbertBasis hJ hΛ hJΛ ha hb hI hre hmn
  rwa [htr] at h

end Infinite

end Discretization
