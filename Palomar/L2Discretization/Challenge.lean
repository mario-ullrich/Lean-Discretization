/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The discretization theorem and the discretization of the `L₂`-norm: statement surface

This module is the *Challenge* of a Palomar submission: the small, auditable surface
carrying the advertised statements. It imports nothing beyond Mathlib, so every notion it
uses is either standard or written out here. The proofs live in
`Palomar.L2Discretization.Solution`, which supplies them from the development in
`Discretization/`; the `sorry`s below are the placeholders required by that format.

## The mathematics

Let `(Ω, μ)` be a measure space, `a = (aₖ)` a finite family of `m` square-integrable functions
on it with positive definite Gram matrix `I = ∫ a a* dμ`, and `b : Ω → H` a square-integrable
map into a nonzero separable complex Hilbert space. Its **Gram operator**
`J = ∫ b(x) b(x)* dμ(x)` is a Bochner integral of rank-one operators; assume that it is
injective and that `J ≼ Λ · 1` for some `Λ > 0`, and put

  `M = ∫ ‖b‖² dμ / Λ`,

the **effective dimension** of `J` relative to `Λ`. The question is whether the integral can
be replaced by finitely many weighted point evaluations so that the first family stays a frame
from below and `b` stays a frame from above. The answer is that for every `n ≥ m` there are
`n` points `x₁, …, xₙ` and positive weights `w₁, …, wₙ` with

  `(1 - √((m-1)/n))² · I ≼ ∑ᵢ wᵢ a(xᵢ) a(xᵢ)*`   and
  `∑ᵢ wᵢ b(xᵢ) b(xᵢ)* ≼ (1 + √((M-1)/n))² Λ · 1`

in the **Loewner order** `A ≼ B ↔ (B - A)` positive semidefinite, the first between matrices
and the second between operators. What the number of points depends on is `M`, not the
dimension of `H`. That is what makes the theorem applicable to infinite-dimensional spaces,
and it is why the constants beat those obtainable from the Kadison–Singer theorem. For a
finite second family `b : Ω → ℂ^κ` with Gram matrix `J` the same holds with `M = Tr J / Λ`.

Read through quadratic forms, with the kernel sections of a reproducing kernel Hilbert space
as second family, the theorem becomes the discretization of the `L₂`-norm. Let `H` be a
nonzero separable Hilbert space of measurable functions on `Ω` on which every point
evaluation is continuous. By the Riesz representation theorem evaluation at `x` is the inner
product with a **kernel section** `kₓ ∈ H`, `⟪kₓ, g⟫ = g(x)`, and `K(x, x) = ‖kₓ‖²` is the
reproducing kernel on the diagonal. Assume `∫ K(x, x) dμ < ∞`, let `Λ` bound the squared norm
of the embedding `H → L₂(μ)`, `∫ |g|² dμ ≤ Λ ‖g‖²`, and let that embedding be injective. With
`I = 1` and `M = ∫ K(x, x) dμ / Λ` the points and weights satisfy

  `(1 - √((m-1)/n))² · ∫ |f|² dμ ≤ ∑ᵢ wᵢ |f(xᵢ)|²`   for every `f` in the span of `a`, and
  `∑ᵢ wᵢ |g(xᵢ)|² ≤ (1 + √((M-1)/n))² Λ · ‖g‖²`      for every `g ∈ H`.

For finite families the same reading gives the upper bound with the coefficient norm of `g`
in place of `‖g‖`.

Traces of the matrices appearing here are real, and real parts are taken with `RCLike.re`
wherever a real number is needed. A Hilbert space of functions on `Ω` is a Hilbert space `H`
together with a linear map `φ : H →ₗ[ℂ] (Ω → ℂ)`, `φ g x` being the value of `g` at `x`.

## The definitions restated here

* `Discretization.gram`: the Gram matrix `∫ a(x) a(x)* dμ(x)` of a finite family.
* `Discretization.RKHS.evalCLM`: the evaluation functional `g ↦ g(x)`, continuous by
  assumption.
* `Discretization.RKHS.kernelSection`: the kernel section `kₓ`, the vector that represents
  evaluation at `x`.

They are reproduced verbatim from the development, under the same names, so that Comparator
can match them against their counterparts there. The four theorems likewise carry the names
they have in the development, so the names Palomar records are the ones a reader will find in
the proof files.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped InnerProductSpace ComplexOrder MatrixOrder
open InnerProductSpace
open ContinuousLinearMap

namespace Discretization

section Gram

variable {ι D : Type*} [MeasurableSpace D]

/-- The **Gram matrix** of a finite family of functions `a : D → ι → ℂ`, with entries
`∫ aₖ · conj aₗ dμ`.  In the notation of the paper this is `∫ a(x) a(x)* dμ(x)`. -/
noncomputable def gram (a : D → ι → ℂ) (μ : Measure D) : Matrix ι ι ℂ :=
  Matrix.of fun k l => ∫ x, a x k * star (a x l) ∂μ

end Gram

end Discretization

namespace Discretization

/-! ### A finite second family -/

section Finite

variable {ι κ Ω : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [MeasurableSpace Ω]
  {μ : Measure Ω} [DecidableEq ι]

/-- **Discretization theorem** (Chkifa–Dolbeault–Krieg–Ullrich, Theorem 3), for finite
families.

Let `a` be a family of square-integrable functions indexed by a finite nonempty set `ι` of
`m` elements with positive definite Gram matrix `I = ∫ a a* dμ`, and let `b` be a second
family whose Gram matrix `J` is positive definite and bounded by `Λ • 1`, with effective
dimension `M = Tr J / Λ`.  Then for every `n ≥ m` there are `n` points and positive weights
with

`(1 - √((m-1)/n))² • I ≤ ∑ wᵢ a(xᵢ) a(xᵢ)*`  and
`∑ wᵢ b(xᵢ) b(xᵢ)* ≤ (1 + √((M-1)/n))² Λ • 1`.

The first bound is the Loewner form of the paper's `(1 - √((m-1)/n))² λ_min(I)`.  There is
no side condition beyond `n ≥ m`. -/
theorem bss_generalized [Nonempty ι] [Nonempty κ]
    {J : Matrix κ κ ℂ} (hJ : J.PosDef) {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : J ≤ Λ • (1 : Matrix κ κ ℂ)) {a : Ω → ι → ℂ} {b : Ω → κ → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (hI : (gram a μ).PosDef) (hgramb : gram b μ = J)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • gram a μ
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • vecMulVec (b (x i)) (star (b (x i)))
        ≤ ((1 + Real.sqrt ((RCLike.re J.trace / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : Matrix κ κ ℂ) :=
  sorry

/-- **Discretization of the `L₂`-norm** (Chkifa–Dolbeault–Krieg–Ullrich, Corollary 4), for
finite families.

Under the hypotheses of `Discretization.bss_generalized` with `I = 1`, the `n` points and
weights discretize the norm of every function in the span of the first family from below,

`(1 - √((m-1)/n))² · ∫ |f|² dμ ≤ ∑ wᵢ |f(xᵢ)|²`,

and bound the weighted sum for every function in the span of the second family from above,

`∑ wᵢ |g(xᵢ)|² ≤ (1 + √((M-1)/n))² Λ · ‖c‖²`,

where `c` is the coefficient vector of `g`.  If the second family is an orthonormal basis of
a reproducing kernel Hilbert space `H`, then the coefficient norm on the right is the
`H`-norm of `g`, and `Λ` bounds the squared norm of the embedding `H → L₂`. -/
theorem exists_discretization [Nonempty ι] [Nonempty κ]
    {J : Matrix κ κ ℂ} (hJ : J.PosDef) {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : J ≤ Λ • (1 : Matrix κ κ ℂ)) {a : Ω → ι → ℂ} {b : Ω → κ → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (hgrama : gram a μ = 1) (hgramb : gram b μ = J)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (∀ c : ι → ℂ, (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
            * ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ
          ≤ ∑ i, w i * ‖star c ⬝ᵥ a (x i)‖ ^ 2) ∧
      (∀ c : κ → ℂ, ∑ i, w i * ‖star c ⬝ᵥ b (x i)‖ ^ 2
          ≤ (1 + Real.sqrt ((RCLike.re J.trace / Λ - 1) / n)) ^ 2 * Λ
              * ∑ k, ‖c k‖ ^ 2) :=
  sorry

end Finite

end Discretization

namespace Discretization

namespace Infinite

/-! ### A second family with values in a Hilbert space -/

section InfiniteGeneralGram

variable {ι Ω H : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] [MeasurableSpace Ω] {μ : Measure Ω}
  {J : H →L[ℂ] H}

/-- **Discretization theorem** (Chkifa–Dolbeault–Krieg–Ullrich, Theorem 3), for a second
family with values in a separable Hilbert space.

Let `a` be a family of square-integrable functions indexed by a finite nonempty set `ι` of
`m` elements with positive definite Gram matrix `I = ∫ a a* dμ`, and let `b : Ω → H` be
square-integrable, with values in a nonzero separable Hilbert space.  Let
`J = ∫ b(x) b(x)* dμ(x)` be its Gram operator, assume `J` injective and `J ≤ Λ • 1`, and put
`M = ∫ ‖b‖² dμ / Λ`.  Then for every `n ≥ m` there are `n` points and
positive weights with

`(1 - √((m-1)/n))² • I ≤ ∑ wᵢ a(xᵢ) a(xᵢ)*`  and
`∑ wᵢ b(xᵢ) b(xᵢ)* ≼ (1 + √((M-1)/n))² Λ • 1`,

the first in the matrix order and the second in the order of operators.  The number of
points is the same as for a finite second family, because it is governed by the effective
dimension and not by the size of the family. -/
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
            • (1 : H →L[ℂ] H) :=
  sorry

end InfiniteGeneralGram

end Infinite

end Discretization

namespace Discretization

namespace RKHS

/-! ### A reproducing kernel Hilbert space as the second family -/

section RKHS

variable {Ω H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (φ : H →ₗ[ℂ] (Ω → ℂ)) (hφ : ∀ x, Continuous fun f => φ f x)

/-- The **evaluation functional** `f ↦ f(x)` at the point `x`, continuous by assumption. -/
noncomputable def evalCLM (x : Ω) : StrongDual ℂ H :=
  ⟨(LinearMap.proj x).comp φ, hφ x⟩

/-- The **kernel section** `kₓ = K(x, ·)`: the vector of `H` that represents evaluation at
`x`, `⟪kₓ, f⟫ = f(x)`, given by the Riesz representation theorem
(`InnerProductSpace.toDual`). -/
noncomputable def kernelSection (x : Ω) : H :=
  (InnerProductSpace.toDual ℂ H).symm (evalCLM φ hφ x)

variable [MeasurableSpace Ω] {μ : Measure Ω}

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

The kernel appears through `K(x, x) = ‖kₓ‖²`, the squared norm of the kernel section. -/
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
              * Λ * ‖g‖ ^ 2) :=
  sorry

end RKHS

end RKHS

end Discretization
