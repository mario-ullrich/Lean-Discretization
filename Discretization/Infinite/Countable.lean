/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.Infinite.GeneralGram
public import Discretization.Infinite.NormDiscretization
public import BasicResults.Operator.GramOperator

/-!
# The countable case for a family of functions

The paper states its Theorem 3 for a second family `b = (b_k)_{k ∈ κ}` of square-integrable
functions indexed by an at most countable set, with the Gram matrix `J = (∫ b_k b_l̄ dμ)` in
place of the Gram operator.  This file proves that form from the operator form,
`Discretization.Infinite.bss_generalized`, applied to the Hilbert space `ℓ²(κ)`, which is
separable.

The hypotheses are those of the paper:

* every `b_k` is square-integrable and `∑_k ‖b_k‖²_{L₂} < ∞` (the trace of `J` is finite);
* no nonzero `c ∈ ℓ²(κ)` makes `∑_k c̄_k b_k` vanish in `L₂` (`J` is injective);
* `∫ |∑_k c̄_k b_k|² dμ ≤ Λ ‖c‖²` for every `c ∈ ℓ²(κ)` (`J ≤ Λ • 1`).

Nothing pointwise is assumed.  The finite trace gives `∑_k |b_k(x)|² < ∞` for almost every
`x` (`Discretization.Countable.ae_mem_l2`), and the theorem is first proved under the
assumption that this holds for every `x` (`Discretization.Countable.bss_generalized_of_mem_l2`).
The general case restricts the measure space to a measurable set of full measure on which
it holds; the construction then runs inside that set, so the points it chooses lie in it.
This is the formal counterpart of the remark that points chosen at random avoid any null
set with probability one.

The dictionary to the operator form: `x ↦ (b_k(x))_k` is a square-integrable map into
`ℓ²(κ)` (`Discretization.Countable.memLp_toLp`) with `∫ ‖b‖² dμ = ∑_k ‖b_k‖²`
(`Discretization.Countable.integral_norm_sq_toLp`), and its Gram operator
`J = ∫ b(x) b(x)* dμ` (`Discretization.Countable.gramOp`) is injective and bounded by
`Λ • 1` under the two quadratic-form hypotheses above.
-/

@[expose] public section

open MeasureTheory Filter Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder ENNReal lp ComplexConjugate Topology
open InnerProductSpace ContinuousLinearMap

namespace Discretization

namespace Countable

variable {κ Ω : Type*} {b : Ω → κ → ℂ}

/-! ### The family at a point, as a vector of `ℓ²` -/

/-- A sequence whose square sum is finite in `ℝ≥0∞` lies in `ℓ²`. -/
theorem mem_l2_of_tsum_ofReal_ne_top {v : κ → ℂ}
    (h : ∑' k, ENNReal.ofReal (‖v k‖ ^ 2) ≠ ⊤) : Memℓp v 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have hs := ContinuousLinearMap.summable_of_tsum_ofReal_ne_top (fun k => by positivity) h
  simpa using hs

/-- The family at the point `x`, as a vector of `ℓ²(κ)`. -/
def toLp (hbx : ∀ x, Memℓp (b x) 2) (x : Ω) : ℓ²(κ, ℂ) := ⟨b x, hbx x⟩

section Pointwise

variable (hbx : ∀ x, Memℓp (b x) 2)

@[simp]
theorem toLp_apply (x : Ω) (k : κ) : toLp hbx x k = b x k := rfl

/-- The inner product with the family at a point is the series `∑_k c̄_k b_k(x)`. -/
theorem inner_toLp (c : ℓ²(κ, ℂ)) (x : Ω) :
    ⟪c, toLp hbx x⟫_ℂ = ∑' k, conj (c k) * b x k := by
  rw [lp.inner_eq_tsum]
  simp [RCLike.inner_apply, mul_comm]

/-- The coordinates of the family at a point, along the standard basis of `ℓ²(κ)`. -/
theorem inner_basis_toLp (k : κ) (x : Ω) :
    ⟪(default : HilbertBasis κ ℂ ℓ²(κ, ℂ)) k, toLp hbx x⟫_ℂ = b x k := by
  rw [← HilbertBasis.repr_apply_apply]
  rfl

/-- The squared norm of the family at a point is its square sum. -/
theorem norm_sq_toLp (x : Ω) : ‖toLp hbx x‖ ^ 2 = ∑' k, ‖b x k‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (toLp hbx x)
  simpa using h

include hbx in
/-- The square sum at a point is summable. -/
theorem summable_norm_sq (x : Ω) : Summable fun k => ‖b x k‖ ^ 2 := by
  have h := (memℓp_gen_iff (p := 2) (by norm_num)).1 (hbx x)
  simpa using h

end Pointwise

/-! ### Square sums along the family -/

variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- The squared modulus of one member of the family, as an `ℝ≥0∞`-valued function, is almost
everywhere measurable. -/
theorem aemeasurable_ofReal_norm_sq (hb : ∀ k, MemLp (fun x => b x k) 2 μ) (k : κ) :
    AEMeasurable (fun x => ENNReal.ofReal (‖b x k‖ ^ 2)) μ :=
  ((hb k).aestronglyMeasurable.aemeasurable.norm.pow_const 2).ennreal_ofReal

variable [Countable κ]

/-- The square sum `x ↦ ∑_k |b_k(x)|²`, in `ℝ≥0∞`, is almost everywhere measurable: it is the
supremum of its finite partial sums. -/
theorem aemeasurable_tsum_ofReal_norm_sq (hb : ∀ k, MemLp (fun x => b x k) 2 μ) :
    AEMeasurable (fun x => ∑' k, ENNReal.ofReal (‖b x k‖ ^ 2)) μ := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact .iSup fun s => Finset.aemeasurable_fun_sum s fun k _ => aemeasurable_ofReal_norm_sq hb k

/-- **Tonelli for the square sum**: the integral of `∑_k |b_k|²` is `∑_k ‖b_k‖²_{L₂}`. -/
theorem lintegral_tsum_ofReal_norm_sq (hb : ∀ k, MemLp (fun x => b x k) 2 μ) :
    ∫⁻ x, ∑' k, ENNReal.ofReal (‖b x k‖ ^ 2) ∂μ
      = ∑' k, ENNReal.ofReal (∫ x, ‖b x k‖ ^ 2 ∂μ) := by
  rw [lintegral_tsum (aemeasurable_ofReal_norm_sq hb)]
  refine tsum_congr fun k => ?_
  rw [ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (hb k).aestronglyMeasurable).1 (hb k))
    (ae_of_all _ fun x => by positivity)]

/-- A finite trace makes the square sum integrable in `ℝ≥0∞`. -/
theorem lintegral_tsum_ofReal_norm_sq_ne_top (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (htr : Summable fun k => ∫ x, ‖b x k‖ ^ 2 ∂μ) :
    ∫⁻ x, ∑' k, ENNReal.ofReal (‖b x k‖ ^ 2) ∂μ ≠ ⊤ := by
  rw [lintegral_tsum_ofReal_norm_sq hb,
    ← ENNReal.ofReal_tsum_of_nonneg (fun k => integral_nonneg fun x => by positivity) htr]
  exact ENNReal.ofReal_ne_top

/-- **Almost every value of the family lies in `ℓ²`**, because the square sum has a finite
integral. -/
theorem ae_mem_l2 (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (htr : Summable fun k => ∫ x, ‖b x k‖ ^ 2 ∂μ) : ∀ᵐ x ∂μ, Memℓp (b x) 2 := by
  have h := ae_lt_top' (aemeasurable_tsum_ofReal_norm_sq hb)
    (lintegral_tsum_ofReal_norm_sq_ne_top hb htr)
  filter_upwards [h] with x hx
  exact mem_l2_of_tsum_ofReal_ne_top hx.ne

/-! ### The family as a square-integrable map into `ℓ²` -/

variable (hbx : ∀ x, Memℓp (b x) 2)

/-- The family is an almost everywhere strongly measurable map into `ℓ²(κ)`: it is the
pointwise limit of its finite partial sums `∑_{k ∈ F} b_k(x) e_k`. -/
theorem aestronglyMeasurable_toLp (hb : ∀ k, MemLp (fun x => b x k) 2 μ) :
    AEStronglyMeasurable (toLp hbx) μ := by
  classical
  refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset κ))
    (f := fun F x => ∑ k ∈ F, (lp.single 2 k (b x k) : ℓ²(κ, ℂ))) (fun F => ?_)
    (ae_of_all _ fun x => ?_)
  · refine Finset.aestronglyMeasurable_fun_sum F fun k _ => ?_
    have hsingle : (fun x => (lp.single 2 k (b x k) : ℓ²(κ, ℂ)))
        = fun x => b x k • (lp.single 2 k (1 : ℂ) : ℓ²(κ, ℂ)) := by
      funext x
      ext j
      by_cases hj : j = k
      · subst hj
        simp [lp.single_apply]
      · simp [lp.single_apply, hj]
    rw [hsingle]
    exact (hb k).aestronglyMeasurable.smul_const _
  · exact lp.hasSum_single (by norm_num) (toLp hbx x)

/-- **The family is a square-integrable map into `ℓ²(κ)`** as soon as its trace is finite. -/
theorem memLp_toLp (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (htr : Summable fun k => ∫ x, ‖b x k‖ ^ 2 ∂μ) : MemLp (toLp hbx) 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_toLp hbx hb)).2 ?_
  have hi := integrable_toReal_of_lintegral_ne_top (aemeasurable_tsum_ofReal_norm_sq hb)
    (lintegral_tsum_ofReal_norm_sq_ne_top hb htr)
  refine hi.congr (ae_of_all _ fun x => ?_)
  show (∑' k, ENNReal.ofReal (‖b x k‖ ^ 2)).toReal = ‖toLp hbx x‖ ^ 2
  rw [norm_sq_toLp, ← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
    (summable_norm_sq hbx x), ENNReal.toReal_ofReal (tsum_nonneg fun k => by positivity)]

/-! ### The space `ℓ²(κ)` -/

/-- **`ℓ²(κ)` is separable** for a countable index set: its standard basis is countable
(`HilbertBasis.separableSpace`). -/
instance : TopologicalSpace.SeparableSpace ℓ²(κ, ℂ) :=
  (default : HilbertBasis κ ℂ ℓ²(κ, ℂ)).separableSpace

omit [Countable κ] in
/-- `ℓ²(κ)` is nonzero for a nonempty index set: the vectors of its standard basis are
nonzero. -/
instance [Nonempty κ] : Nontrivial ℓ²(κ, ℂ) :=
  let e : HilbertBasis κ ℂ ℓ²(κ, ℂ) := default
  nontrivial_of_ne (e (Classical.arbitrary κ)) 0 (e.ne_zero _)

/-! ### The Gram operator -/

/-- The **Gram operator** of the family, `J = ∫ b(x) b(x)* dμ(x)` on `ℓ²(κ)`.  Its matrix
along the standard basis is the Gram matrix `(∫ b_k b̄_l dμ)`. -/
noncomputable def gramOp (hbx : ∀ x, Memℓp (b x) 2) (μ : Measure Ω) :
    ℓ²(κ, ℂ) →L[ℂ] ℓ²(κ, ℂ) :=
  ∫ x, rankOne ℂ (toLp hbx x) (toLp hbx x) ∂μ

/-- **The Gram identity**: the quadratic form of the Gram operator is the average of
`|⟪u, b(x)⟫|²`, as a complex number.  This is `ContinuousLinearMap.inner_integral_rankOne_self`
for the square-integrable map `x ↦ (b_k(x))_k` into `ℓ²(κ)`. -/
theorem inner_gramOp_self (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (htr : Summable fun k => ∫ x, ‖b x k‖ ^ 2 ∂μ) (u : ℓ²(κ, ℂ)) :
    ⟪u, gramOp hbx μ u⟫_ℂ = ((∫ x, ‖⟪u, toLp hbx x⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) :=
  inner_integral_rankOne_self (memLp_toLp hbx hb htr) u

/-- The real form of the Gram identity. -/
theorem re_inner_gramOp (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (htr : Summable fun k => ∫ x, ‖b x k‖ ^ 2 ∂μ) (u : ℓ²(κ, ℂ)) :
    RCLike.re ⟪u, gramOp hbx μ u⟫_ℂ = ∫ x, ‖⟪u, toLp hbx x⟫_ℂ‖ ^ 2 ∂μ :=
  re_inner_eq_integral (inner_gramOp_self hbx hb htr) u

/-- The diagonal of the Gram operator along the standard basis: `⟪e_k, J e_k⟫ = ‖b_k‖²`. -/
theorem re_inner_basis_gramOp (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (htr : Summable fun k => ∫ x, ‖b x k‖ ^ 2 ∂μ) (k : κ) :
    RCLike.re ⟪(default : HilbertBasis κ ℂ ℓ²(κ, ℂ)) k,
      gramOp hbx μ ((default : HilbertBasis κ ℂ ℓ²(κ, ℂ)) k)⟫_ℂ = ∫ x, ‖b x k‖ ^ 2 ∂μ := by
  rw [re_inner_gramOp hbx hb htr]
  exact integral_congr_ae (ae_of_all _ fun x => by simp only [inner_basis_toLp])

/-- **The trace of the Gram operator is `∑_k ‖b_k‖²`.** -/
theorem traceAlong_gramOp (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (htr : Summable fun k => ∫ x, ‖b x k‖ ^ 2 ∂μ) :
    traceAlong (default : HilbertBasis κ ℂ ℓ²(κ, ℂ)) (gramOp hbx μ)
      = ∑' k, ∫ x, ‖b x k‖ ^ 2 ∂μ :=
  tsum_congr fun k => re_inner_basis_gramOp hbx hb htr k

/-- **The average of `‖b‖²` is `∑_k ‖b_k‖²`**: the trace of the Gram operator, read once as
`∫ ‖b‖² dμ` (`Discretization.Infinite.integral_norm_sq_eq_traceAlong`) and once along the
standard basis (`Discretization.Countable.traceAlong_gramOp`). -/
theorem integral_norm_sq_toLp (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (htr : Summable fun k => ∫ x, ‖b x k‖ ^ 2 ∂μ) :
    ∫ x, ‖toLp hbx x‖ ^ 2 ∂μ = ∑' k, ∫ x, ‖b x k‖ ^ 2 ∂μ :=
  (Infinite.integral_norm_sq_eq_traceAlong (default : HilbertBasis κ ℂ ℓ²(κ, ℂ))
    (memLp_toLp hbx hb htr) rfl).trans (traceAlong_gramOp hbx hb htr)

omit [Countable κ] in
/-- The average of `|⟪c, b(x)⟫|²`, written with the series `∑_k c̄_k b_k(x)`. -/
theorem integral_norm_sq_inner_toLp (c : ℓ²(κ, ℂ)) :
    ∫ x, ‖⟪c, toLp hbx x⟫_ℂ‖ ^ 2 ∂μ = ∫ x, ‖∑' k, conj (c k) * b x k‖ ^ 2 ∂μ :=
  integral_congr_ae (ae_of_all _ fun x => by simp only [inner_toLp])

/-- **The Gram operator is injective** if no nonzero `c ∈ ℓ²(κ)` makes `∑_k c̄_k b_k` vanish
in `L₂`. -/
theorem gramOp_injective (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (htr : Summable fun k => ∫ x, ‖b x k‖ ^ 2 ∂μ)
    (hinj : ∀ c : ℓ²(κ, ℂ), ∫ x, ‖∑' k, conj (c k) * b x k‖ ^ 2 ∂μ = 0 → c = 0)
    (c : ℓ²(κ, ℂ)) (hc : gramOp hbx μ c = 0) : c = 0 := by
  refine hinj c ?_
  rw [← integral_norm_sq_inner_toLp hbx c, ← re_inner_gramOp hbx hb htr, hc,
    inner_zero_right, map_zero]

/-- **The Gram operator is bounded by `Λ • 1`** if its quadratic form is bounded by
`Λ ‖c‖²`: the Bessel-type reading of `J ≤ Λ • 1`
(`ContinuousLinearMap.le_smul_one_iff_of_inner_eq_integral`). -/
theorem gramOp_le (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (htr : Summable fun k => ∫ x, ‖b x k‖ ^ 2 ∂μ) {Λ : ℝ}
    (hJΛ : ∀ c : ℓ²(κ, ℂ), ∫ x, ‖∑' k, conj (c k) * b x k‖ ^ 2 ∂μ ≤ Λ * ‖c‖ ^ 2) :
    gramOp hbx μ ≤ Λ • (1 : ℓ²(κ, ℂ) →L[ℂ] ℓ²(κ, ℂ)) :=
  (le_smul_one_iff_of_inner_eq_integral (inner_gramOp_self hbx hb htr)).2 fun c => by
    rw [integral_norm_sq_inner_toLp hbx c]
    exact hJΛ c

/-! ### The theorem when every value lies in `ℓ²` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

include hbx in
/-- **Discretization theorem for a countable family, when every value lies in `ℓ²`.**

This is `Discretization.Infinite.bss_generalized` for the separable space `H = ℓ²(κ)`,
`b(x) = (b_k(x))_k` and the Gram operator of the family; the effective dimension is
`M = ∑_k ‖b_k‖²_{L₂} / Λ`, and the upper bound is read through quadratic forms. -/
theorem bss_generalized_of_mem_l2 [Nonempty ι] [Nonempty κ]
    {a : Ω → ι → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hI : (gram a μ).PosDef)
    (hb : ∀ k, MemLp (fun x => b x k) 2 μ) (htr : Summable fun k => ∫ x, ‖b x k‖ ^ 2 ∂μ)
    (hinj : ∀ c : ℓ²(κ, ℂ), ∫ x, ‖∑' k, conj (c k) * b x k‖ ^ 2 ∂μ = 0 → c = 0)
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : ∀ c : ℓ²(κ, ℂ), ∫ x, ‖∑' k, conj (c k) * b x k‖ ^ 2 ∂μ ≤ Λ * ‖c‖ ^ 2)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • gram a μ
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) ∧
      ∀ c : ℓ²(κ, ℂ), ∑ i, w i * ‖∑' k, conj (c k) * b (x i) k‖ ^ 2
        ≤ (1 + Real.sqrt (((∑' k, ∫ y, ‖b y k‖ ^ 2 ∂μ) / Λ - 1) / n)) ^ 2 * Λ * ‖c‖ ^ 2 := by
  obtain ⟨x, w, hw, hlow, hup⟩ := Infinite.bss_generalized hΛ (gramOp_le hbx hb htr hJΛ)
    (gramOp_injective hbx hb htr hinj) ha (memLp_toLp hbx hb htr) hI rfl hmn
  refine ⟨x, w, hw, hlow, fun c => ?_⟩
  rw [integral_norm_sq_toLp hbx hb htr] at hup
  simpa only [inner_toLp] using Infinite.sum_mul_norm_sq_inner_le hup c

/-! ### Restriction to a set of full measure -/

section FullMeasure

variable {S : Set Ω}

omit [Countable κ] in
/-- Integrals over a measurable set of full measure, seen as a measure space of its own, are
integrals over the whole space. -/
theorem integral_comap_val (hS : MeasurableSet S) (hae : ∀ᵐ x ∂μ, x ∈ S) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Ω → E) :
    ∫ x : S, f x ∂(μ.comap Subtype.val) = ∫ x, f x ∂μ := by
  rw [integral_subtype_comap hS, Measure.restrict_eq_self_of_ae_mem hae]

omit [Countable κ] in
/-- A function in `L_p` of the whole space is in `L_p` of a measurable set of full measure. -/
theorem memLp_comap_val (hS : MeasurableSet S) (hae : ∀ᵐ x ∂μ, x ∈ S) {E : Type*}
    [NormedAddCommGroup E] {f : Ω → E} {p : ℝ≥0∞} (hf : MemLp f p μ) :
    MemLp (fun x : S => f x) p (μ.comap Subtype.val) := by
  have h := (MeasurableEmbedding.subtype_coe hS).memLp_map_measure_iff (g := f) (p := p)
    (μ := μ.comap Subtype.val)
  rw [map_comap_subtype_coe hS, Measure.restrict_eq_self_of_ae_mem hae] at h
  exact h.1 hf

omit [Countable κ] [Fintype ι] [DecidableEq ι] in
/-- The Gram matrix does not change when the measure space is restricted to a measurable set
of full measure. -/
theorem gram_comap_val (hS : MeasurableSet S) (hae : ∀ᵐ x ∂μ, x ∈ S) (a : Ω → ι → ℂ) :
    gram (fun x : S => a x) (μ.comap Subtype.val) = gram a μ := by
  ext k l
  simp only [gram, Matrix.of_apply]
  exact integral_comap_val hS hae (fun x => a x k * star (a x l))

end FullMeasure

/-- The values of a family of finite trace lie in `ℓ²` on a measurable set of full
measure. -/
theorem exists_measurableSet_mem_l2 (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (htr : Summable fun k => ∫ x, ‖b x k‖ ^ 2 ∂μ) :
    ∃ S : Set Ω, MeasurableSet S ∧ (∀ᵐ x ∂μ, x ∈ S) ∧ ∀ x ∈ S, Memℓp (b x) 2 := by
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 (ae_mem_l2 hb htr))
  refine ⟨Nᶜ, hNm.compl, ?_, fun x hx => ?_⟩
  · rw [ae_iff]
    simpa using hN0
  · by_contra h
    exact hx (hNsub h)

/-! ### The theorem in the paper's form -/

/-- **Discretization theorem for a countable second family**
(Chkifa–Dolbeault–Krieg–Ullrich, Theorem 3), in the form of the paper.

Let `a` be a finite family of square-integrable functions with positive definite Gram matrix
`I`, and let `b = (b_k)_{k ∈ κ}` be a countable family of square-integrable functions with
`∑_k ‖b_k‖²_{L₂} < ∞`, whose Gram matrix `J` is injective on `ℓ²(κ)` (no nonzero `c` makes
`∑_k c̄_k b_k` vanish in `L₂`) and bounded by `Λ • 1` (`∫ |∑_k c̄_k b_k|² ≤ Λ ‖c‖²`).  Put
`M = ∑_k ‖b_k‖² / Λ`.  Then for every `n ≥ m` there are `n` points, at which every value of
the family lies in `ℓ²`, and positive weights with

`(1 - √((m-1)/n))² • I ≤ ∑ᵢ wᵢ a(xᵢ) a(xᵢ)*`  and
`∑ᵢ wᵢ |∑_k c̄_k b_k(xᵢ)|² ≤ (1 + √((M-1)/n))² Λ ‖c‖²`  for every `c ∈ ℓ²(κ)`.

Nothing pointwise is assumed.  The proof restricts the measure space to a measurable set of
full measure on which the values lie in `ℓ²` (`exists_measurableSet_mem_l2`) and applies
`bss_generalized_of_mem_l2` there, so the points are chosen inside that set. -/
theorem bss_generalized [Nonempty ι] [Nonempty κ]
    {a : Ω → ι → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hI : (gram a μ).PosDef)
    (hb : ∀ k, MemLp (fun x => b x k) 2 μ) (htr : Summable fun k => ∫ x, ‖b x k‖ ^ 2 ∂μ)
    (hinj : ∀ c : ℓ²(κ, ℂ), ∫ x, ‖∑' k, conj (c k) * b x k‖ ^ 2 ∂μ = 0 → c = 0)
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : ∀ c : ℓ²(κ, ℂ), ∫ x, ‖∑' k, conj (c k) * b x k‖ ^ 2 ∂μ ≤ Λ * ‖c‖ ^ 2)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧ (∀ i, Memℓp (b (x i)) 2) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • gram a μ
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) ∧
      ∀ c : ℓ²(κ, ℂ), ∑ i, w i * ‖∑' k, conj (c k) * b (x i) k‖ ^ 2
        ≤ (1 + Real.sqrt (((∑' k, ∫ y, ‖b y k‖ ^ 2 ∂μ) / Λ - 1) / n)) ^ 2 * Λ * ‖c‖ ^ 2 := by
  obtain ⟨S, hSm, hSae, hSb⟩ := exists_measurableSet_mem_l2 hb htr
  have htr' : (∑' k, ∫ y : S, ‖b y k‖ ^ 2 ∂(μ.comap Subtype.val))
      = ∑' k, ∫ y, ‖b y k‖ ^ 2 ∂μ :=
    tsum_congr fun k => integral_comap_val hSm hSae (fun y => ‖b y k‖ ^ 2)
  obtain ⟨x, w, hw, hlow, hup⟩ := bss_generalized_of_mem_l2 (μ := μ.comap Subtype.val)
    (a := fun y : S => a y) (b := fun y : S => b y) (fun y => hSb y y.2)
    (fun k => memLp_comap_val hSm hSae (ha k)) (by rwa [gram_comap_val hSm hSae])
    (fun k => memLp_comap_val hSm hSae (hb k))
    ((summable_congr fun k => integral_comap_val hSm hSae (fun y => ‖b y k‖ ^ 2)).2 htr)
    (fun c hc => hinj c
      ((integral_comap_val hSm hSae (fun y => ‖∑' k, conj (c k) * b y k‖ ^ 2)).symm.trans hc))
    hΛ (fun c => (integral_comap_val hSm hSae
      (fun y => ‖∑' k, conj (c k) * b y k‖ ^ 2)).trans_le (hJΛ c)) hmn
  refine ⟨fun i => x i, w, hw, fun i => hSb (x i) (x i).2, ?_, fun c => ?_⟩
  · rwa [gram_comap_val hSm hSae] at hlow
  · have h := hup c
    rw [htr'] at h
    exact h

/-- **Discretization of the `L₂`-norm for a countable second family**
(Chkifa–Dolbeault–Krieg–Ullrich, Corollary 4), in the form of the paper: under the
hypotheses of `Discretization.Countable.bss_generalized` with a normalized first family, its
points and weights satisfy

`(1 - √((m-1)/n))² ∫ |f|² dμ ≤ ∑ᵢ wᵢ |f(xᵢ)|²`  for every `f` in the span of `a`, and
`∑ᵢ wᵢ |∑_k c̄_k b_k(xᵢ)|² ≤ (1 + √((M-1)/n))² Λ ‖c‖²`  for every `c ∈ ℓ²(κ)`. -/
theorem exists_discretization [Nonempty ι] [Nonempty κ]
    {a : Ω → ι → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hgrama : gram a μ = 1)
    (hb : ∀ k, MemLp (fun x => b x k) 2 μ) (htr : Summable fun k => ∫ x, ‖b x k‖ ^ 2 ∂μ)
    (hinj : ∀ c : ℓ²(κ, ℂ), ∫ x, ‖∑' k, conj (c k) * b x k‖ ^ 2 ∂μ = 0 → c = 0)
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : ∀ c : ℓ²(κ, ℂ), ∫ x, ‖∑' k, conj (c k) * b x k‖ ^ 2 ∂μ ≤ Λ * ‖c‖ ^ 2)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧ (∀ i, Memℓp (b (x i)) 2) ∧
      (∀ c : ι → ℂ, (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
            * ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ
          ≤ ∑ i, w i * ‖star c ⬝ᵥ a (x i)‖ ^ 2) ∧
      ∀ c : ℓ²(κ, ℂ), ∑ i, w i * ‖∑' k, conj (c k) * b (x i) k‖ ^ 2
        ≤ (1 + Real.sqrt (((∑' k, ∫ y, ‖b y k‖ ^ 2 ∂μ) / Λ - 1) / n)) ^ 2 * Λ * ‖c‖ ^ 2 := by
  obtain ⟨x, w, hw, hmem, hlow, hup⟩ :=
    bss_generalized ha (by rw [hgrama]; exact Matrix.PosDef.one) hb htr hinj hΛ hJΛ hmn
  exact ⟨x, w, hw, hmem, mul_integral_norm_sq_le_sum ha hlow, hup⟩

end Countable

end Discretization
