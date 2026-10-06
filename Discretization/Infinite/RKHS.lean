/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.Infinite.NormDiscretization
public import BasicResults.Operator.GramOperator
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# A reproducing kernel Hilbert space as the second family

Let `H` be a Hilbert space of functions on `Ω` on which every point evaluation `f ↦ f(x)` is
continuous.  In Lean the functions are given by a linear map `φ : H →ₗ[ℂ] (Ω → ℂ)`, and
`φ f x` is the value of `f` at `x`.  By the Riesz representation theorem each point
evaluation is the inner product with a vector `kₓ ∈ H`, the **kernel section**
(`Discretization.RKHS.kernelSection`):

`⟪kₓ, f⟫ = f(x)`   for every `f ∈ H`,

and `K(x, y) = ⟪k_y, kₓ⟫ = kₓ(y)` is the reproducing kernel, so that `kₓ = K(x, ·)` and
`K(x, x) = ‖kₓ‖²`.

The map `x ↦ kₓ` is the second family `b(x) = K(x, ·)` of the discretization theorem.  Its
coefficients are the functions themselves, `|⟪g, kₓ⟫| = |g(x)|`, so every hypothesis on the
Gram operator becomes a statement about `H` and `L₂(μ)`:

* `J ≤ Λ • 1` says `∫ |g|² dμ ≤ Λ ‖g‖²` for every `g ∈ H`: `Λ` bounds the squared norm of the
  embedding `H → L₂(μ)`;
* injectivity of `J` says that this embedding is injective: a `g ∈ H` that vanishes almost
  everywhere is zero;
* the effective dimension is `M = ∫ K(x, x) dμ(x) / Λ`.

Measurability of `x ↦ kₓ` comes from that of the functions in `H`: along a countable Hilbert
basis `(e_j)` of the separable space `H`, `kₓ = ∑_j conj(e_j(x)) e_j`.

The conclusion, `Discretization.RKHS.exists_discretization`, is the discretization inequality
for the norm of `H`,

`∑ᵢ wᵢ |g(xᵢ)|² ≤ (1 + √((M-1)/n))² Λ ‖g‖²`   for every `g ∈ H`,

together with the lower bound for the finite first family.  This is Corollary 4 of
Chkifa, Dolbeault, Krieg and Ullrich in the form of its title.  No basis of `H` and no
singular value decomposition of the embedding enter the statement.
-/

@[expose] public section

open MeasureTheory Filter Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder ComplexConjugate
open InnerProductSpace ContinuousLinearMap

namespace Discretization

namespace RKHS

variable {Ω H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (φ : H →ₗ[ℂ] (Ω → ℂ)) (hφ : ∀ x, Continuous fun f => φ f x)

/-! ### Kernel sections -/

/-- The **evaluation functional** `f ↦ f(x)` at the point `x`, continuous by assumption. -/
noncomputable def evalCLM (x : Ω) : StrongDual ℂ H :=
  ⟨(LinearMap.proj x).comp φ, hφ x⟩

omit [CompleteSpace H] in
/-- The evaluation functional at `x` sends `f` to its value `f(x)`, by definition. -/
@[simp]
theorem evalCLM_apply (x : Ω) (f : H) : evalCLM φ hφ x f = φ f x := rfl

/-- The **kernel section** `kₓ = K(x, ·)`: the vector of `H` that represents evaluation at
`x`, `⟪kₓ, f⟫ = f(x)`, given by the Riesz representation theorem
(`InnerProductSpace.toDual`). -/
noncomputable def kernelSection (x : Ω) : H :=
  (InnerProductSpace.toDual ℂ H).symm (evalCLM φ hφ x)

/-- **The reproducing property**: `⟪kₓ, f⟫ = f(x)` for every `f ∈ H`. -/
theorem inner_kernelSection (x : Ω) (f : H) : ⟪kernelSection φ hφ x, f⟫_ℂ = φ f x := by
  rw [kernelSection, InnerProductSpace.toDual_symm_apply, evalCLM_apply]

/-- The coefficients of the kernel sections are the values of the function:
`|⟪f, kₓ⟫| = |f(x)|`. -/
theorem norm_inner_kernelSection (f : H) (x : Ω) :
    ‖⟪f, kernelSection φ hφ x⟫_ℂ‖ = ‖φ f x‖ := by
  rw [← inner_conj_symm, inner_kernelSection, RCLike.norm_conj]

/-- The **reproducing kernel** `K(x, y) = ⟪k_y, kₓ⟫`, the value of `kₓ` at `y`. -/
noncomputable def kernel (x y : Ω) : ℂ :=
  ⟪kernelSection φ hφ y, kernelSection φ hφ x⟫_ℂ

/-- The kernel section is a section of the kernel: `K(x, y) = kₓ(y)`. -/
theorem kernel_eq (x y : Ω) : kernel φ hφ x y = φ (kernelSection φ hφ x) y :=
  inner_kernelSection φ hφ y _

/-- On the diagonal the kernel is the squared norm of the kernel section:
`K(x, x) = ‖kₓ‖²`. -/
theorem kernel_self (x : Ω) :
    kernel φ hφ x x = ((‖kernelSection φ hφ x‖ ^ 2 : ℝ) : ℂ) := by
  rw [kernel, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-! ### Measurability -/

variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The kernel sections form a strongly measurable map** when every function of `H` is
measurable and `H` is separable.  Along a countable Hilbert basis `(e_j)`,
`kₓ = ∑_j ⟪e_j, kₓ⟫ e_j` with coefficients `⟪e_j, kₓ⟫ = conj(e_j(x))`, so `x ↦ kₓ` is the
pointwise limit of finite sums of measurable maps. -/
theorem aestronglyMeasurable_kernelSection [TopologicalSpace.SeparableSpace H]
    (hmeas : ∀ f, AEStronglyMeasurable (φ f) μ) :
    AEStronglyMeasurable (kernelSection φ hφ) μ := by
  classical
  obtain ⟨s, e, -⟩ := exists_hilbertBasis ℂ H
  have : Countable s := e.countable_of_separableSpace
  refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset s))
    (f := fun F x => ∑ j ∈ F, ⟪e j, kernelSection φ hφ x⟫_ℂ • e j) (fun F => ?_)
    (ae_of_all _ fun x => ?_)
  · refine Finset.aestronglyMeasurable_fun_sum F fun j _ => ?_
    have hc : AEStronglyMeasurable (fun x => ⟪e j, kernelSection φ hφ x⟫_ℂ) μ := by
      refine (Complex.continuous_conj.comp_aestronglyMeasurable (hmeas (e j))).congr
        (ae_of_all _ fun x => ?_)
      simp only
      rw [← inner_conj_symm, inner_kernelSection]
    exact hc.smul_const _
  · have h := e.hasSum_repr (kernelSection φ hφ x)
    simp only [HilbertBasis.repr_apply_apply] at h
    exact h

/-- **The kernel sections form a square-integrable map** when, in addition, the kernel is
integrable on the diagonal, `∫ K(x, x) dμ(x) < ∞`. -/
theorem memLp_kernelSection [TopologicalSpace.SeparableSpace H]
    (hmeas : ∀ f, AEStronglyMeasurable (φ f) μ)
    (hK : Integrable (fun x => ‖kernelSection φ hφ x‖ ^ 2) μ) :
    MemLp (kernelSection φ hφ) 2 μ :=
  (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_kernelSection φ hφ hmeas)).2 hK

/-! ### The discretization inequality -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Discretization of the `L₂`-norm with a reproducing kernel Hilbert space**
(Chkifa–Dolbeault–Krieg–Ullrich, Corollary 4).

Let `a` be a family of square-integrable functions indexed by a finite nonempty set `ι` of
`m` elements with Gram matrix `1`.  Let `H` be a nonzero separable Hilbert space of
measurable functions on `Ω` with continuous point evaluations and reproducing kernel `K`,
with `∫ K(x, x) dμ(x) < ∞`, let `Λ > 0` satisfy `∫ |g|² dμ ≤ Λ ‖g‖²` for every `g ∈ H`, and
assume that the only `g ∈ H` vanishing almost everywhere is `g = 0`.  Put
`M = ∫ K(x, x) dμ(x) / Λ`.  Then for every `n ≥ m` there are `n` points and positive weights
with

`(1 - √((m-1)/n))² ∫ |f|² dμ ≤ ∑ᵢ wᵢ |f(xᵢ)|²`  for every `f` in the span of `a`, and
`∑ᵢ wᵢ |g(xᵢ)|² ≤ (1 + √((M-1)/n))² Λ ‖g‖²`  for every `g ∈ H`.

The kernel appears through `K(x, x) = ‖kₓ‖²` (`Discretization.RKHS.kernel_self`).  This is
`Discretization.Infinite.exists_discretization` for the kernel sections `b(x) = kₓ`, whose
coefficients `⟪f, kₓ⟫` have modulus `|f(x)|`. -/
theorem exists_discretization [Nonempty ι] [TopologicalSpace.SeparableSpace H] [Nontrivial H]
    (hmeas : ∀ f, AEStronglyMeasurable (φ f) μ)
    (hK : Integrable (fun x => ‖kernelSection φ hφ x‖ ^ 2) μ)
    {Λ : ℝ} (hΛ : 0 < Λ) (hHΛ : ∀ g, ∫ x, ‖φ g x‖ ^ 2 ∂μ ≤ Λ * ‖g‖ ^ 2)
    (hinj : ∀ g, (∀ᵐ x ∂μ, φ g x = 0) → g = 0)
    {a : Ω → ι → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hgrama : gram a μ = 1)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (∀ c : ι → ℂ, (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
            * ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ
          ≤ ∑ i, w i * ‖star c ⬝ᵥ a (x i)‖ ^ 2) ∧
      (∀ g : H, ∑ i, w i * ‖φ g (x i)‖ ^ 2
          ≤ (1 + Real.sqrt (((∫ y, ‖kernelSection φ hφ y‖ ^ 2 ∂μ) / Λ - 1) / n)) ^ 2
              * Λ * ‖g‖ ^ 2) := by
  have hb := memLp_kernelSection φ hφ hmeas hK
  have hcoef := norm_inner_kernelSection φ hφ
  -- the two hypotheses on the Gram operator, read on `H`
  have hJΛ : ∫ y, rankOne ℂ (kernelSection φ hφ y) (kernelSection φ hφ y) ∂μ
      ≤ Λ • (1 : H →L[ℂ] H) :=
    (integral_rankOne_self_le_iff hb).2 fun f => by
      simp only [hcoef]
      exact hHΛ f
  have hJinj := (integral_rankOne_self_injective_iff hb).2 fun f hf =>
    hinj f (hf.mono fun y hy => norm_eq_zero.1 ((hcoef f y).symm.trans (by rw [hy, norm_zero])))
  obtain ⟨x, w, hw, hlow, hup⟩ :=
    Infinite.exists_discretization hΛ hJΛ hJinj ha hb hgrama rfl hmn
  exact ⟨x, w, hw, hlow, fun f => by simpa only [hcoef] using hup f⟩

end RKHS

end Discretization
