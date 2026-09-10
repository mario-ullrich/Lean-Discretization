/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.InnerProductSpace.L2Space
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# The trace of an operator along a Hilbert basis

Mathlib has no trace of an operator on an infinite-dimensional space, and no trace-class
theory.  This file builds the little that the discretization argument needs, in the most
elementary way available: given a Hilbert basis `e` of `H`, the **trace along `e`** of a
bounded operator is the sum

`traceAlong e T = ∑' k, Re ⟪e k, T (e k)⟫`,

with the convention of `tsum`, so that the definition makes sense for every `T` and carries
information exactly when the family is summable.  No basis independence is proved, and none
is needed: every statement below fixes one basis, and in the application the basis is the
standard basis of `ℓ₂`.

For a **positive** operator the sum is a sum of nonnegative terms, because

`Re ⟪x, T x⟫ = ‖√T x‖²`   (`Discretization.re_inner_apply_eq_norm_sq_sqrt`),

where `√T` is the positive square root from the continuous functional calculus, so that

`traceAlong e T = ∑' k, ‖√T (e k)‖²`

is the squared Hilbert–Schmidt norm of `√T`.  This is the form in which the trace is used:

* `Discretization.traceAlong_nonneg` — the trace of a positive operator is nonnegative;
* `Discretization.le_traceAlong_smul_one` — the **crude bound** `T ≤ Tr(T) • 1`, the operator
  analogue of `Matrix.PosSemidef.le_trace_smul_one`.  Its proof runs through Parseval and the
  Cauchy–Schwarz inequality for a single inner product, which is what makes the passage from
  the Hilbert–Schmidt norm to the operator norm elementary and, incidentally, makes basis
  independence unnecessary.

Mathlib supplies everything else: `HilbertBasis` with `HilbertBasis.hasSum_inner_mul_inner`
for Parseval, the C⋆-algebra structure of `H →L[ℂ] H`, its Loewner order
(`ContinuousLinearMap.instLoewnerPartialOrder`, with positivity `ContinuousLinearMap.IsPositive`),
and `CFC.sqrt` with `CFC.sqrt_mul_sqrt_self`.
-/

open scoped InnerProductSpace ComplexOrder

namespace Discretization

variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Parseval's identity -/

omit [CompleteSpace H] in
/-- **Parseval's identity** along a Hilbert basis: the squared norm is the sum of the squared
moduli of the coefficients. -/
theorem hasSum_norm_sq_inner (e : HilbertBasis κ ℂ H) (x : H) :
    HasSum (fun k => ‖⟪e k, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
  have h := (e.hasSum_inner_mul_inner x x).mapL (RCLike.reCLM (K := ℂ))
  simp only [RCLike.reCLM_apply] at h
  have hterm : ∀ k, RCLike.re (⟪x, e k⟫_ℂ * ⟪e k, x⟫_ℂ) = ‖⟪e k, x⟫_ℂ‖ ^ 2 := fun k => by
    rw [← inner_conj_symm, RCLike.conj_mul]
    norm_cast
  have hval : RCLike.re ⟪x, x⟫_ℂ = ‖x‖ ^ 2 := inner_self_eq_norm_sq x
  rw [← hval]
  exact h.congr_fun fun k => (hterm k).symm

omit [CompleteSpace H] in
/-- The coefficients of a vector are square-summable along a Hilbert basis. -/
theorem summable_norm_sq_inner (e : HilbertBasis κ ℂ H) (x : H) :
    Summable fun k => ‖⟪e k, x⟫_ℂ‖ ^ 2 :=
  (hasSum_norm_sq_inner e x).summable

/-! ### The trace along a basis -/

/-- The **trace of `T` along the Hilbert basis `e`**, `∑' k, Re ⟪e k, T (e k)⟫`.

For a positive operator this is the sum of a family of nonnegative numbers, hence either a
genuine finite trace or, by the convention of `tsum`, zero; every statement that uses the
value assumes the family summable. -/
noncomputable def traceAlong (e : HilbertBasis κ ℂ H) (T : H →L[ℂ] H) : ℝ :=
  ∑' k, RCLike.re ⟪e k, T (e k)⟫_ℂ

/-- The quadratic form of a positive operator is the squared norm of its square root:
`Re ⟪x, T x⟫ = ‖√T x‖²`. -/
theorem re_inner_apply_eq_norm_sq_sqrt {T : H →L[ℂ] H} (hT : 0 ≤ T) (x : H) :
    RCLike.re ⟪x, T x⟫_ℂ = ‖CFC.sqrt T x‖ ^ 2 := by
  have hsq : CFC.sqrt T * CFC.sqrt T = T := CFC.sqrt_mul_sqrt_self T hT
  have hsa : IsSelfAdjoint (CFC.sqrt T) := .of_nonneg (CFC.sqrt_nonneg T)
  have hstar : ContinuousLinearMap.adjoint (CFC.sqrt T) = CFC.sqrt T := hsa.star_eq
  have happ : T x = CFC.sqrt T (CFC.sqrt T x) :=
    congrArg (fun S : H →L[ℂ] H => S x) hsq.symm
  have hmove : ⟪x, CFC.sqrt T (CFC.sqrt T x)⟫_ℂ = ⟪CFC.sqrt T x, CFC.sqrt T x⟫_ℂ := by
    have h := ContinuousLinearMap.adjoint_inner_right (CFC.sqrt T) x (CFC.sqrt T x)
    rwa [hstar] at h
  rw [happ, hmove, inner_self_eq_norm_sq]

/-- The trace of a positive operator is the squared Hilbert–Schmidt norm of its square
root: `Tr T = ∑' k, ‖√T (e k)‖²`. -/
theorem traceAlong_eq_tsum_norm_sq_sqrt (e : HilbertBasis κ ℂ H) {T : H →L[ℂ] H}
    (hT : 0 ≤ T) : traceAlong e T = ∑' k, ‖CFC.sqrt T (e k)‖ ^ 2 :=
  tsum_congr fun k => re_inner_apply_eq_norm_sq_sqrt hT (e k)

/-- Summability of the trace of a positive operator, read through its square root. -/
theorem summable_norm_sq_sqrt_iff (e : HilbertBasis κ ℂ H) {T : H →L[ℂ] H} (hT : 0 ≤ T) :
    (Summable fun k => ‖CFC.sqrt T (e k)‖ ^ 2)
      ↔ Summable fun k => RCLike.re ⟪e k, T (e k)⟫_ℂ :=
  summable_congr fun k => (re_inner_apply_eq_norm_sq_sqrt hT (e k)).symm

omit [CompleteSpace H] in
/-- **The trace of a positive operator is nonnegative.** -/
theorem traceAlong_nonneg (e : HilbertBasis κ ℂ H) {T : H →L[ℂ] H} (hT : 0 ≤ T) :
    0 ≤ traceAlong e T :=
  tsum_nonneg fun k =>
    (ContinuousLinearMap.nonneg_iff_isPositive T |>.1 hT).re_inner_nonneg_right (e k)

/-! ### The Hilbert–Schmidt sum and adjoints

The trace of a positive operator is the squared Hilbert–Schmidt norm of its square root, and
the passage from an operator to its adjoint leaves that quantity unchanged.  This is the one
place where a double series has to be rearranged; doing it in `ℝ≥0∞`, where every sum is
defined and `ENNReal.tsum_comm` is unconditional, avoids any summability hypothesis. -/

/-- Summability of a nonnegative family, read off from its sum in `ℝ≥0∞`. -/
private theorem summable_of_tsum_ofReal_ne_top {f : κ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (h : ∑' k, ENNReal.ofReal (f k) ≠ ⊤) : Summable f := by
  have h1 : Summable fun k => (f k).toNNReal :=
    ENNReal.tsum_coe_ne_top_iff_summable.1 h
  exact (NNReal.summable_coe.2 h1).congr fun k => Real.coe_toNNReal _ (hf k)

omit [CompleteSpace H] in
/-- **Parseval's identity in `ℝ≥0∞`**, where no summability hypothesis is needed. -/
theorem tsum_ofReal_norm_sq_inner (e : HilbertBasis κ ℂ H) (x : H) :
    ∑' k, ENNReal.ofReal (‖⟪e k, x⟫_ℂ‖ ^ 2) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) (summable_norm_sq_inner e x),
    (hasSum_norm_sq_inner e x).tsum_eq]

/-- **The Hilbert–Schmidt sum of an operator equals that of its adjoint**, as an identity in
`ℝ≥0∞`.

Expanding `‖S eₖ‖²` by Parseval turns the sum into the double sum of `|⟪eⱼ, S eₖ⟫|²`, which is
symmetric in the two indices once `⟪eⱼ, S eₖ⟫` is read as `⟪S* eⱼ, eₖ⟫`.  Interchanging the
two summations is unconditional in `ℝ≥0∞`. -/
theorem tsum_ofReal_norm_sq_adjoint (e : HilbertBasis κ ℂ H) (S : H →L[ℂ] H) :
    ∑' k, ENNReal.ofReal (‖S (e k)‖ ^ 2)
      = ∑' k, ENNReal.ofReal (‖ContinuousLinearMap.adjoint S (e k)‖ ^ 2) := by
  calc ∑' k, ENNReal.ofReal (‖S (e k)‖ ^ 2)
      = ∑' k, ∑' j, ENNReal.ofReal (‖⟪e j, S (e k)⟫_ℂ‖ ^ 2) :=
        tsum_congr fun k => (tsum_ofReal_norm_sq_inner e (S (e k))).symm
    _ = ∑' j, ∑' k, ENNReal.ofReal (‖⟪e j, S (e k)⟫_ℂ‖ ^ 2) := ENNReal.tsum_comm
    _ = ∑' j, ∑' k, ENNReal.ofReal (‖⟪e k, ContinuousLinearMap.adjoint S (e j)⟫_ℂ‖ ^ 2) := by
        refine tsum_congr fun j => tsum_congr fun k => ?_
        rw [← ContinuousLinearMap.adjoint_inner_left, norm_inner_symm]
    _ = ∑' j, ENNReal.ofReal (‖ContinuousLinearMap.adjoint S (e j)‖ ^ 2) :=
        tsum_congr fun j => tsum_ofReal_norm_sq_inner e _

/-- **An operator is Hilbert–Schmidt exactly when its adjoint is.** -/
theorem summable_norm_sq_adjoint_iff (e : HilbertBasis κ ℂ H) (S : H →L[ℂ] H) :
    (Summable fun k => ‖ContinuousLinearMap.adjoint S (e k)‖ ^ 2)
      ↔ Summable fun k => ‖S (e k)‖ ^ 2 := by
  constructor <;> intro h
  · refine summable_of_tsum_ofReal_ne_top (fun k => by positivity) ?_
    rw [tsum_ofReal_norm_sq_adjoint e S]
    exact h.tsum_ofReal_ne_top
  · refine summable_of_tsum_ofReal_ne_top (fun k => by positivity) ?_
    rw [← tsum_ofReal_norm_sq_adjoint e S]
    exact h.tsum_ofReal_ne_top

/-- **The Hilbert–Schmidt norm is invariant under taking adjoints.** -/
theorem tsum_norm_sq_adjoint (e : HilbertBasis κ ℂ H) (S : H →L[ℂ] H)
    (h : Summable fun k => ‖S (e k)‖ ^ 2) :
    ∑' k, ‖ContinuousLinearMap.adjoint S (e k)‖ ^ 2 = ∑' k, ‖S (e k)‖ ^ 2 := by
  have h' : Summable fun k => ‖ContinuousLinearMap.adjoint S (e k)‖ ^ 2 :=
    (summable_norm_sq_adjoint_iff e S).2 h
  refine (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg fun k => by positivity)
    (tsum_nonneg fun k => by positivity)).1 ?_
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) h',
    ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) h,
    ← tsum_ofReal_norm_sq_adjoint e S]

/-! ### Operators with vanishing trace -/

omit [CompleteSpace H] in
/-- An operator that annihilates every vector of a Hilbert basis is zero. -/
theorem eq_zero_of_apply_basis_eq_zero (e : HilbertBasis κ ℂ H) {S : H →L[ℂ] H}
    (h : ∀ k, S (e k) = 0) : S = 0 := by
  ext x
  have hs := (e.hasSum_repr x).mapL S
  simp only [ContinuousLinearMap.map_smul, h, smul_zero] at hs
  simpa using hs.unique hasSum_zero

/-- **A positive operator with vanishing trace is zero.**

The trace is `∑ₖ ‖√T eₖ‖²`, so it vanishes only if the square root annihilates every basis
vector, hence vanishes, hence so does `T = √T √T`.  This is what makes the strict
inequalities of the potential argument strict. -/
theorem eq_zero_of_traceAlong_eq_zero (e : HilbertBasis κ ℂ H) {T : H →L[ℂ] H} (hT : 0 ≤ T)
    (hsum : Summable fun k => RCLike.re ⟪e k, T (e k)⟫_ℂ) (h0 : traceAlong e T = 0) :
    T = 0 := by
  have hsqsum : Summable fun k => ‖CFC.sqrt T (e k)‖ ^ 2 :=
    (summable_norm_sq_sqrt_iff e hT).2 hsum
  have hzero : ∀ k, ‖CFC.sqrt T (e k)‖ ^ 2 = 0 := fun k => by
    have hle : ‖CFC.sqrt T (e k)‖ ^ 2 ≤ ∑' j, ‖CFC.sqrt T (e j)‖ ^ 2 :=
      hsqsum.le_tsum k fun j _ => by positivity
    rw [← traceAlong_eq_tsum_norm_sq_sqrt e hT, h0] at hle
    have := norm_nonneg (CFC.sqrt T (e k))
    nlinarith
  have hsq0 : CFC.sqrt T = 0 :=
    eq_zero_of_apply_basis_eq_zero e fun k => by
      have := hzero k
      simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  have hsq : CFC.sqrt T * CFC.sqrt T = T := CFC.sqrt_mul_sqrt_self T hT
  rw [← hsq, hsq0, mul_zero]

/-! ### The trace of a product

The trace of a product of two positive operators is nonnegative, and this is where the
double series of the previous section is rearranged once more, now with complex terms.  The
identity behind it is

`Re Tr (P Q) = ∑ₖ Re ⟪√P eₖ, Q (√P eₖ)⟫`,

whose right-hand side is a sum of nonnegative terms as soon as `Q` is positive.  In the
language of the finite-dimensional argument this is `Tr (P Q) = Tr (√P Q √P)`. -/

omit [CompleteSpace H] in
/-- The pairing `∑ₖ ⟪S eₖ, T eₖ⟫` of two Hilbert–Schmidt operators converges absolutely. -/
theorem summable_inner_apply (e : HilbertBasis κ ℂ H) {S T : H →L[ℂ] H}
    (hS : Summable fun k => ‖S (e k)‖ ^ 2) (hT : Summable fun k => ‖T (e k)‖ ^ 2) :
    Summable fun k => ⟪S (e k), T (e k)⟫_ℂ := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    (((hS.add hT).div_const 2)))
  have h := norm_inner_le_norm (𝕜 := ℂ) (S (e k)) (T (e k))
  nlinarith [sq_nonneg (‖S (e k)‖ - ‖T (e k)‖), norm_nonneg (S (e k)), norm_nonneg (T (e k))]

/-- The double family that appears when the pairing of two Hilbert–Schmidt operators is
expanded in the basis is absolutely summable.

The majorant is `(|⟪eⱼ, S eₖ⟫|² + |⟪eⱼ, T eₖ⟫|²)/2`, which dominates the product of the two
moduli; summing it over `j` gives `(‖S eₖ‖² + ‖T eₖ‖²)/2` by Parseval, and that is summable
over `k` by hypothesis. -/
private theorem summable_uncurry_inner_mul (e : HilbertBasis κ ℂ H) {S T : H →L[ℂ] H}
    (hS : Summable fun k => ‖S (e k)‖ ^ 2) (hT : Summable fun k => ‖T (e k)‖ ^ 2) :
    Summable (Function.uncurry fun k j : κ =>
      ⟪e k, ContinuousLinearMap.adjoint S (e j)⟫_ℂ
        * ⟪ContinuousLinearMap.adjoint T (e j), e k⟫_ℂ) := by
  have hcoefS : ∀ k j : κ, ‖⟪e k, ContinuousLinearMap.adjoint S (e j)⟫_ℂ‖
      = ‖⟪e j, S (e k)⟫_ℂ‖ := fun k j => by
    rw [ContinuousLinearMap.adjoint_inner_right S (e k) (e j), norm_inner_symm]
  have hcoefT : ∀ k j : κ, ‖⟪ContinuousLinearMap.adjoint T (e j), e k⟫_ℂ‖
      = ‖⟪e j, T (e k)⟫_ℂ‖ := fun k j => by
    rw [ContinuousLinearMap.adjoint_inner_left T (e k) (e j)]
  have hmaj : Summable fun p : κ × κ =>
      (‖⟪e p.2, S (e p.1)⟫_ℂ‖ ^ 2 + ‖⟪e p.2, T (e p.1)⟫_ℂ‖ ^ 2) / 2 := by
    refine (summable_prod_of_nonneg fun p => by positivity).2 ⟨fun k => ?_, ?_⟩
    · exact ((summable_norm_sq_inner e (S (e k))).add
        (summable_norm_sq_inner e (T (e k)))).div_const 2
    · refine ((hS.add hT).div_const 2).congr fun k => ?_
      rw [tsum_div_const, Summable.tsum_add (summable_norm_sq_inner e (S (e k)))
        (summable_norm_sq_inner e (T (e k))), (hasSum_norm_sq_inner e (S (e k))).tsum_eq,
        (hasSum_norm_sq_inner e (T (e k))).tsum_eq]
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hmaj)
  rw [Function.uncurry_apply_pair, norm_mul, hcoefS p.1 p.2, hcoefT p.1 p.2]
  nlinarith [sq_nonneg (‖⟪e p.2, S (e p.1)⟫_ℂ‖ - ‖⟪e p.2, T (e p.1)⟫_ℂ‖),
    norm_nonneg ⟪e p.2, S (e p.1)⟫_ℂ, norm_nonneg ⟪e p.2, T (e p.1)⟫_ℂ]

/-- **The pairing of two Hilbert–Schmidt operators is symmetric under adjoints:**
`∑ₖ ⟪S eₖ, T eₖ⟫ = ∑ₖ ⟪T* eₖ, S* eₖ⟫`.

Both sides expand, by Parseval, into the same double series over pairs of basis vectors, and
that series converges absolutely, so the order of summation may be interchanged.  With
`S = T` this is the invariance of the Hilbert–Schmidt norm under adjoints; in general it is
the cyclicity of the trace, in the only form the potential argument needs. -/
theorem tsum_inner_apply_comm (e : HilbertBasis κ ℂ H) {S T : H →L[ℂ] H}
    (hS : Summable fun k => ‖S (e k)‖ ^ 2) (hT : Summable fun k => ‖T (e k)‖ ^ 2) :
    ∑' k, ⟪S (e k), T (e k)⟫_ℂ
      = ∑' k, ⟪ContinuousLinearMap.adjoint T (e k),
          ContinuousLinearMap.adjoint S (e k)⟫_ℂ := by
  calc ∑' k, ⟪S (e k), T (e k)⟫_ℂ
      = ∑' k, ∑' j, ⟪e k, ContinuousLinearMap.adjoint S (e j)⟫_ℂ
          * ⟪ContinuousLinearMap.adjoint T (e j), e k⟫_ℂ := by
        refine tsum_congr fun k => ?_
        rw [← e.tsum_inner_mul_inner (S (e k)) (T (e k))]
        refine tsum_congr fun j => ?_
        rw [ContinuousLinearMap.adjoint_inner_right S (e k) (e j),
          ContinuousLinearMap.adjoint_inner_left T (e k) (e j)]
    _ = ∑' j, ∑' k, ⟪e k, ContinuousLinearMap.adjoint S (e j)⟫_ℂ
          * ⟪ContinuousLinearMap.adjoint T (e j), e k⟫_ℂ :=
        Summable.tsum_comm (f := fun j k : κ =>
          ⟪e k, ContinuousLinearMap.adjoint S (e j)⟫_ℂ
            * ⟪ContinuousLinearMap.adjoint T (e j), e k⟫_ℂ)
          (summable_uncurry_inner_mul e hS hT).prod_symm
    _ = ∑' j, ⟪ContinuousLinearMap.adjoint T (e j),
          ContinuousLinearMap.adjoint S (e j)⟫_ℂ := by
        refine tsum_congr fun j => ?_
        rw [← e.tsum_inner_mul_inner (ContinuousLinearMap.adjoint T (e j))
          (ContinuousLinearMap.adjoint S (e j))]
        exact tsum_congr fun k => mul_comm _ _

/-! ### The crude bound -/

/-- **A positive operator is bounded by its trace**, in the form of a quadratic form:
`Re ⟪x, T x⟫ ≤ Tr(T) · ‖x‖²`.

Parseval expands `‖√T x‖²` into `∑ₖ |⟪√T eₖ, x⟫|²`, and the Cauchy–Schwarz inequality bounds
each term by `‖√T eₖ‖² ‖x‖²`; summing gives the trace.  Only the ordinary Cauchy–Schwarz
inequality for one inner product is used, not its version for series. -/
theorem re_inner_apply_le_traceAlong_mul (e : HilbertBasis κ ℂ H) {T : H →L[ℂ] H}
    (hT : 0 ≤ T) (hsum : Summable fun k => RCLike.re ⟪e k, T (e k)⟫_ℂ) (x : H) :
    RCLike.re ⟪x, T x⟫_ℂ ≤ traceAlong e T * ‖x‖ ^ 2 := by
  have hsa : IsSelfAdjoint (CFC.sqrt T) := .of_nonneg (CFC.sqrt_nonneg T)
  have hstar : ContinuousLinearMap.adjoint (CFC.sqrt T) = CFC.sqrt T := hsa.star_eq
  have hsqsum : Summable fun k => ‖CFC.sqrt T (e k)‖ ^ 2 :=
    (summable_norm_sq_sqrt_iff e hT).2 hsum
  have hcoef : ∀ k, ⟪e k, CFC.sqrt T x⟫_ℂ = ⟪CFC.sqrt T (e k), x⟫_ℂ := fun k => by
    rw [← hstar, ContinuousLinearMap.adjoint_inner_left, hstar]
  calc RCLike.re ⟪x, T x⟫_ℂ = ‖CFC.sqrt T x‖ ^ 2 := re_inner_apply_eq_norm_sq_sqrt hT x
    _ = ∑' k, ‖⟪CFC.sqrt T (e k), x⟫_ℂ‖ ^ 2 := by
        rw [(hasSum_norm_sq_inner e (CFC.sqrt T x)).tsum_eq.symm]
        exact tsum_congr fun k => by rw [hcoef k]
    _ ≤ ∑' k, ‖CFC.sqrt T (e k)‖ ^ 2 * ‖x‖ ^ 2 := by
        refine Summable.tsum_le_tsum (fun k => ?_) ?_ (hsqsum.mul_right _)
        · calc ‖⟪CFC.sqrt T (e k), x⟫_ℂ‖ ^ 2
              ≤ (‖CFC.sqrt T (e k)‖ * ‖x‖) ^ 2 := by
                have h := norm_inner_le_norm (𝕜 := ℂ) (CFC.sqrt T (e k)) x
                have h0 : (0 : ℝ) ≤ ‖⟪CFC.sqrt T (e k), x⟫_ℂ‖ := norm_nonneg _
                nlinarith
            _ = ‖CFC.sqrt T (e k)‖ ^ 2 * ‖x‖ ^ 2 := by ring
        · exact ((summable_norm_sq_inner e (CFC.sqrt T x)).congr
            fun k => by rw [hcoef k])
    _ = traceAlong e T * ‖x‖ ^ 2 := by
        rw [tsum_mul_right, traceAlong_eq_tsum_norm_sq_sqrt e hT]

/-- **The crude bound `T ≤ Tr(T) • 1`** for a positive operator with summable trace, the
operator analogue of `Matrix.PosSemidef.le_trace_smul_one`.

It is the only estimate of the potential argument that compares an operator with a multiple
of the identity, and it is what the edge case of a small effective dimension rests on. -/
theorem le_traceAlong_smul_one (e : HilbertBasis κ ℂ H) {T : H →L[ℂ] H} (hT : 0 ≤ T)
    (hsum : Summable fun k => RCLike.re ⟪e k, T (e k)⟫_ℂ) :
    T ≤ (traceAlong e T) • (1 : H →L[ℂ] H) := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def']
  refine ⟨?_, fun x => ?_⟩
  · exact (IsSelfAdjoint.smul (star_trivial _) (IsSelfAdjoint.one _)).sub
      ((ContinuousLinearMap.nonneg_iff_isPositive T |>.1 hT).isSelfAdjoint)
  · have h := re_inner_apply_le_traceAlong_mul e hT hsum x
    have hsymm : RCLike.re ⟪T x, x⟫_ℂ = RCLike.re ⟪x, T x⟫_ℂ :=
      inner_re_symm (𝕜 := ℂ) (T x) x
    have hval : ((traceAlong e T • (1 : H →L[ℂ] H) - T) x) = traceAlong e T • x - T x := by
      simp
    have hsmul : RCLike.re ⟪traceAlong e T • x, x⟫_ℂ = traceAlong e T * ‖x‖ ^ 2 := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_left, RCLike.smul_re,
        inner_self_eq_norm_sq]
    rw [ContinuousLinearMap.reApplyInnerSelf, hval, inner_sub_left, map_sub, hsmul]
    linarith

/-- Real parts commute with a convergent sum. -/
private theorem re_tsum {f : κ → ℂ} (hf : Summable f) :
    RCLike.re (∑' k, f k) = ∑' k, RCLike.re (f k) :=
  ((hf.hasSum.mapL (RCLike.reCLM (K := ℂ))).tsum_eq).symm

/-- **The trace of a product, symmetrized:**
`Tr (P Q) = ∑ₖ Re ⟪√P eₖ, Q (√P eₖ)⟫` for a positive `P` with summable trace and a positive
`Q`.

In the finite-dimensional notation this is `Tr (P Q) = Tr (√P Q √P)`, the cyclicity of the
trace.  The right-hand side is a sum of nonnegative terms, which is the whole point: it makes
the sign of the trace of a product visible. -/
theorem traceAlong_mul (e : HilbertBasis κ ℂ H) {P Q : H →L[ℂ] H} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hsum : Summable fun k => RCLike.re ⟪e k, P (e k)⟫_ℂ) :
    traceAlong e (P * Q) = ∑' k, RCLike.re ⟪CFC.sqrt P (e k), Q (CFC.sqrt P (e k))⟫_ℂ := by
  have hsqP : CFC.sqrt P * CFC.sqrt P = P := CFC.sqrt_mul_sqrt_self P hP
  have hstarP : ContinuousLinearMap.adjoint (CFC.sqrt P) = CFC.sqrt P :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg P)).star_eq
  have hstarQ : ContinuousLinearMap.adjoint Q = Q :=
    ((ContinuousLinearMap.nonneg_iff_isPositive Q).1 hQ).isSelfAdjoint.star_eq
  have hS : Summable fun k => ‖CFC.sqrt P (e k)‖ ^ 2 := (summable_norm_sq_sqrt_iff e hP).2 hsum
  have hSadj : Summable fun k => ‖ContinuousLinearMap.adjoint (CFC.sqrt P) (e k)‖ ^ 2 :=
    (summable_norm_sq_adjoint_iff e (CFC.sqrt P)).2 hS
  -- the adjoint of `√P Q` is `Q √P`, which is Hilbert–Schmidt because `√P` is
  have hadjT : ContinuousLinearMap.adjoint (CFC.sqrt P * Q) = Q * CFC.sqrt P := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_mul, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.star_eq_adjoint, hstarQ, hstarP]
  have hTadj : Summable fun k =>
      ‖ContinuousLinearMap.adjoint (CFC.sqrt P * Q) (e k)‖ ^ 2 := by
    simp only [hadjT]
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hS.mul_left (‖Q‖ ^ 2))
    have h : ‖Q (CFC.sqrt P (e k))‖ ≤ ‖Q‖ * ‖CFC.sqrt P (e k)‖ := Q.le_opNorm _
    have h0 : (0 : ℝ) ≤ ‖Q (CFC.sqrt P (e k))‖ := norm_nonneg _
    have h1 : (0 : ℝ) ≤ ‖Q‖ * ‖CFC.sqrt P (e k)‖ := by positivity
    calc ‖(Q * CFC.sqrt P) (e k)‖ ^ 2 = ‖Q (CFC.sqrt P (e k))‖ ^ 2 := rfl
      _ ≤ (‖Q‖ * ‖CFC.sqrt P (e k)‖) ^ 2 := by nlinarith
      _ = ‖Q‖ ^ 2 * ‖CFC.sqrt P (e k)‖ ^ 2 := by ring
  have hT : Summable fun k => ‖(CFC.sqrt P * Q) (e k)‖ ^ 2 :=
    (summable_norm_sq_adjoint_iff e (CFC.sqrt P * Q)).1 hTadj
  -- the two sides of the swap, term by term
  have hL : ∀ k, ⟪CFC.sqrt P (e k), (CFC.sqrt P * Q) (e k)⟫_ℂ = ⟪e k, (P * Q) (e k)⟫_ℂ :=
    fun k => by
      have h := ContinuousLinearMap.adjoint_inner_right (CFC.sqrt P) (e k)
        (CFC.sqrt P (Q (e k)))
      rw [hstarP] at h
      calc ⟪CFC.sqrt P (e k), (CFC.sqrt P * Q) (e k)⟫_ℂ
          = ⟪CFC.sqrt P (e k), CFC.sqrt P (Q (e k))⟫_ℂ := rfl
        _ = ⟪e k, CFC.sqrt P (CFC.sqrt P (Q (e k)))⟫_ℂ := h.symm
        _ = ⟪e k, (CFC.sqrt P * CFC.sqrt P) (Q (e k))⟫_ℂ := rfl
        _ = ⟪e k, (P * Q) (e k)⟫_ℂ := by rw [hsqP]; rfl
  have hR : ∀ k, ⟪ContinuousLinearMap.adjoint (CFC.sqrt P * Q) (e k),
      ContinuousLinearMap.adjoint (CFC.sqrt P) (e k)⟫_ℂ
        = ⟪Q (CFC.sqrt P (e k)), CFC.sqrt P (e k)⟫_ℂ := fun k => by
    rw [hadjT, hstarP]; rfl
  -- take real parts on both sides of the swap
  have hswap := tsum_inner_apply_comm e hS hT
  rw [tsum_congr hL, tsum_congr hR] at hswap
  have hsumL : Summable fun k => ⟪e k, (P * Q) (e k)⟫_ℂ :=
    ((summable_inner_apply e hS hT).congr hL)
  have hsumR : Summable fun k => ⟪Q (CFC.sqrt P (e k)), CFC.sqrt P (e k)⟫_ℂ :=
    ((summable_inner_apply e hTadj hSadj).congr hR)
  calc traceAlong e (P * Q) = RCLike.re (∑' k, ⟪e k, (P * Q) (e k)⟫_ℂ) :=
        (re_tsum hsumL).symm
    _ = RCLike.re (∑' k, ⟪Q (CFC.sqrt P (e k)), CFC.sqrt P (e k)⟫_ℂ) := by rw [hswap]
    _ = ∑' k, RCLike.re ⟪Q (CFC.sqrt P (e k)), CFC.sqrt P (e k)⟫_ℂ := re_tsum hsumR
    _ = ∑' k, RCLike.re ⟪CFC.sqrt P (e k), Q (CFC.sqrt P (e k))⟫_ℂ :=
        tsum_congr fun k => inner_re_symm (𝕜 := ℂ) _ _

/-- **The trace of a product of two positive operators is nonnegative**, the operator
analogue of `Matrix.PosSemidef.trace_mul_nonneg`. -/
theorem traceAlong_mul_nonneg (e : HilbertBasis κ ℂ H) {P Q : H →L[ℂ] H} (hP : 0 ≤ P)
    (hQ : 0 ≤ Q) (hsum : Summable fun k => RCLike.re ⟪e k, P (e k)⟫_ℂ) :
    0 ≤ traceAlong e (P * Q) := by
  rw [traceAlong_mul e hP hQ hsum]
  exact tsum_nonneg fun k =>
    ((ContinuousLinearMap.nonneg_iff_isPositive Q).1 hQ).re_inner_nonneg_right _

/-- **The trace of a product is strictly positive** when the factor of finite trace is
nonzero and the bounded factor is positive and invertible, the operator analogue of
`Matrix.PosDef.re_trace_mul_pos`.

Invertibility of `Q` is what replaces positive definiteness: it makes `√Q` injective, so a
vanishing trace would force `√P` to annihilate the whole basis. -/
theorem traceAlong_mul_pos (e : HilbertBasis κ ℂ H) {P Q : H →L[ℂ] H} (hP : 0 ≤ P)
    (hQ : 0 ≤ Q) (hQu : IsUnit Q) (hsum : Summable fun k => RCLike.re ⟪e k, P (e k)⟫_ℂ)
    (hP0 : P ≠ 0) : 0 < traceAlong e (P * Q) := by
  have hS : Summable fun k => ‖CFC.sqrt P (e k)‖ ^ 2 := (summable_norm_sq_sqrt_iff e hP).2 hsum
  -- the trace of the product is the squared Hilbert–Schmidt norm of `√Q √P`
  have hval : traceAlong e (P * Q) = ∑' k, ‖CFC.sqrt Q (CFC.sqrt P (e k))‖ ^ 2 := by
    rw [traceAlong_mul e hP hQ hsum]
    exact tsum_congr fun k => re_inner_apply_eq_norm_sq_sqrt hQ _
  have hQsum : Summable fun k => ‖CFC.sqrt Q (CFC.sqrt P (e k))‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (hS.mul_left (‖CFC.sqrt Q‖ ^ 2))
    have h := (CFC.sqrt Q).le_opNorm (CFC.sqrt P (e k))
    have h0 : (0 : ℝ) ≤ ‖CFC.sqrt Q (CFC.sqrt P (e k))‖ := norm_nonneg _
    have h1 : (0 : ℝ) ≤ ‖CFC.sqrt Q‖ * ‖CFC.sqrt P (e k)‖ := by positivity
    calc ‖CFC.sqrt Q (CFC.sqrt P (e k))‖ ^ 2 ≤ (‖CFC.sqrt Q‖ * ‖CFC.sqrt P (e k)‖) ^ 2 := by
          nlinarith
      _ = ‖CFC.sqrt Q‖ ^ 2 * ‖CFC.sqrt P (e k)‖ ^ 2 := by ring
  -- `√Q` is injective, because `Q` is a unit
  obtain ⟨u, hu⟩ := (CFC.isUnit_sqrt_iff Q hQ).2 hQu
  have hinj : ∀ y : H, CFC.sqrt Q y = 0 → y = 0 := fun y hy => by
    have h1 : ((↑u⁻¹ : H →L[ℂ] H) * (↑u : H →L[ℂ] H)) y = y := by rw [u.inv_mul]; rfl
    have h2 : (↑u : H →L[ℂ] H) y = 0 := by rw [hu]; exact hy
    calc y = ((↑u⁻¹ : H →L[ℂ] H) * (↑u : H →L[ℂ] H)) y := h1.symm
      _ = (↑u⁻¹ : H →L[ℂ] H) ((↑u : H →L[ℂ] H) y) := rfl
      _ = (↑u⁻¹ : H →L[ℂ] H) 0 := by rw [h2]
      _ = 0 := map_zero _
  -- a vanishing trace would make `√P` vanish on the basis, hence `P = 0`
  rcases eq_or_lt_of_le (traceAlong_mul_nonneg e hP hQ hsum) with h0 | h
  · refine absurd ?_ hP0
    have hzero : ∀ k, ‖CFC.sqrt Q (CFC.sqrt P (e k))‖ ^ 2 = 0 := fun k => by
      have hle : ‖CFC.sqrt Q (CFC.sqrt P (e k))‖ ^ 2
          ≤ ∑' j, ‖CFC.sqrt Q (CFC.sqrt P (e j))‖ ^ 2 :=
        hQsum.le_tsum k fun j _ => by positivity
      rw [← hval, ← h0] at hle
      have := norm_nonneg (CFC.sqrt Q (CFC.sqrt P (e k)))
      nlinarith
    have hsq0 : CFC.sqrt P = 0 :=
      eq_zero_of_apply_basis_eq_zero e fun k =>
        hinj _ (by simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (hzero k))
    have hsqP : CFC.sqrt P * CFC.sqrt P = P := CFC.sqrt_mul_sqrt_self P hP
    rw [← hsqP, hsq0, mul_zero]
  · exact h

/-! ### Linearity, and the trace of a rank-one operator -/

omit [CompleteSpace H] in
/-- The trace is additive, where both traces exist. -/
theorem traceAlong_add (e : HilbertBasis κ ℂ H) {S T : H →L[ℂ] H}
    (hS : Summable fun k => RCLike.re ⟪e k, S (e k)⟫_ℂ)
    (hT : Summable fun k => RCLike.re ⟪e k, T (e k)⟫_ℂ) :
    traceAlong e (S + T) = traceAlong e S + traceAlong e T := by
  simp only [traceAlong]
  rw [← hS.tsum_add hT]
  exact tsum_congr fun k => by
    rw [show (S + T) (e k) = S (e k) + T (e k) from rfl, inner_add_right, map_add]

omit [CompleteSpace H] in
/-- The trace is homogeneous for real scalars. -/
theorem traceAlong_smul (e : HilbertBasis κ ℂ H) (c : ℝ) (T : H →L[ℂ] H) :
    traceAlong e (c • T) = c * traceAlong e T := by
  simp only [traceAlong]
  rw [← tsum_mul_left]
  exact tsum_congr fun k => by
    rw [show (c • T) (e k) = c • T (e k) from rfl, RCLike.real_smul_eq_coe_smul (K := ℂ),
      inner_smul_real_right, RCLike.smul_re]

/-- **The pairing of a product with the basis is absolutely summable** when the first factor
is positive with summable trace and the second is positive.

This is the summability that makes `Tr (P Q)` an honest sum, and it is not a consequence of
the summability of `Tr P` alone: it rests on `√P Q` being Hilbert–Schmidt, which in turn
follows from its adjoint `Q √P` being so. -/
theorem summable_inner_apply_mul (e : HilbertBasis κ ℂ H) {P Q : H →L[ℂ] H} (hP : 0 ≤ P)
    (hQ : 0 ≤ Q) (hsum : Summable fun k => RCLike.re ⟪e k, P (e k)⟫_ℂ) :
    Summable fun k => ⟪e k, (P * Q) (e k)⟫_ℂ := by
  have hsqP : CFC.sqrt P * CFC.sqrt P = P := CFC.sqrt_mul_sqrt_self P hP
  have hstarP : ContinuousLinearMap.adjoint (CFC.sqrt P) = CFC.sqrt P :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg P)).star_eq
  have hstarQ : ContinuousLinearMap.adjoint Q = Q :=
    ((ContinuousLinearMap.nonneg_iff_isPositive Q).1 hQ).isSelfAdjoint.star_eq
  have hS : Summable fun k => ‖CFC.sqrt P (e k)‖ ^ 2 := (summable_norm_sq_sqrt_iff e hP).2 hsum
  have hadjT : ContinuousLinearMap.adjoint (CFC.sqrt P * Q) = Q * CFC.sqrt P := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_mul, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.star_eq_adjoint, hstarQ, hstarP]
  have hTadj : Summable fun k =>
      ‖ContinuousLinearMap.adjoint (CFC.sqrt P * Q) (e k)‖ ^ 2 := by
    simp only [hadjT]
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hS.mul_left (‖Q‖ ^ 2))
    have h : ‖Q (CFC.sqrt P (e k))‖ ≤ ‖Q‖ * ‖CFC.sqrt P (e k)‖ := Q.le_opNorm _
    have h0 : (0 : ℝ) ≤ ‖Q (CFC.sqrt P (e k))‖ := norm_nonneg _
    have h1 : (0 : ℝ) ≤ ‖Q‖ * ‖CFC.sqrt P (e k)‖ := by positivity
    calc ‖(Q * CFC.sqrt P) (e k)‖ ^ 2 = ‖Q (CFC.sqrt P (e k))‖ ^ 2 := rfl
      _ ≤ (‖Q‖ * ‖CFC.sqrt P (e k)‖) ^ 2 := by nlinarith
      _ = ‖Q‖ ^ 2 * ‖CFC.sqrt P (e k)‖ ^ 2 := by ring
  have hT : Summable fun k => ‖(CFC.sqrt P * Q) (e k)‖ ^ 2 :=
    (summable_norm_sq_adjoint_iff e (CFC.sqrt P * Q)).1 hTadj
  refine (summable_inner_apply e hS hT).congr fun k => ?_
  have h := ContinuousLinearMap.adjoint_inner_right (CFC.sqrt P) (e k)
    (CFC.sqrt P (Q (e k)))
  rw [hstarP] at h
  calc ⟪CFC.sqrt P (e k), (CFC.sqrt P * Q) (e k)⟫_ℂ
      = ⟪CFC.sqrt P (e k), CFC.sqrt P (Q (e k))⟫_ℂ := rfl
    _ = ⟪e k, CFC.sqrt P (CFC.sqrt P (Q (e k)))⟫_ℂ := h.symm
    _ = ⟪e k, (CFC.sqrt P * CFC.sqrt P) (Q (e k))⟫_ℂ := rfl
    _ = ⟪e k, (P * Q) (e k)⟫_ℂ := by rw [hsqP]; rfl

/-- The real form of `Discretization.summable_inner_apply_mul`: the trace of a product of a
positive operator of finite trace with a positive operator exists. -/
theorem summable_re_inner_apply_mul (e : HilbertBasis κ ℂ H) {P Q : H →L[ℂ] H} (hP : 0 ≤ P)
    (hQ : 0 ≤ Q) (hsum : Summable fun k => RCLike.re ⟪e k, P (e k)⟫_ℂ) :
    Summable fun k => RCLike.re ⟪e k, (P * Q) (e k)⟫_ℂ :=
  (summable_inner_apply_mul e hP hQ hsum).mapL (RCLike.reCLM (K := ℂ))

omit [CompleteSpace H] in
/-- **The trace against a rank-one operator is a quadratic form:**
`Tr (T · u u*) = ⟪u, T u⟫`.

This is the operator form of `Matrix.trace_mul_vecMulVec_self_star`, and it is what turns the
rank-one update of the construction into a pointwise condition on the new sampling point.  No
summability hypothesis is needed: the series is the one of Parseval's identity. -/
theorem traceAlong_mul_rankOne (e : HilbertBasis κ ℂ H) (T : H →L[ℂ] H) (u : H) :
    traceAlong e (T * InnerProductSpace.rankOne ℂ u u) = RCLike.re ⟪u, T u⟫_ℂ := by
  have hterm : ∀ k, RCLike.re ⟪e k, (T * InnerProductSpace.rankOne ℂ u u) (e k)⟫_ℂ
      = RCLike.re (⟪u, e k⟫_ℂ * ⟪e k, T u⟫_ℂ) := fun k => by
    rw [show (T * InnerProductSpace.rankOne ℂ u u) (e k) = T (⟪u, e k⟫_ℂ • u) from rfl,
      ContinuousLinearMap.map_smul, inner_smul_right]
  rw [traceAlong, tsum_congr hterm, ← re_tsum (e.summable_inner_mul_inner u (T u)),
    e.tsum_inner_mul_inner]

end Discretization
