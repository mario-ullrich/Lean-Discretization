/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The generalized sparsification theorem — statement surface

This module is the *Challenge* of a Palomar submission: the small, auditable surface
carrying the advertised statements. It imports nothing beyond Mathlib, so every notion it
uses is either standard or written out here. The proofs live in
`Palomar.Sparsification.Solution`, which supplies them from the development in
`Discretization/`; the `sorry`s below are the placeholders required by that format.

## The mathematics

Let `(Ω, μ)` be a measure space and let two families of square-integrable functions on it be
given: a finite one `a = (aₖ)` indexed by `ι` with `m = #ι` elements, and a second one `b`.
The question is whether the integral `∫ |f|² dμ` can be replaced by a finite weighted sum
`∑ᵢ wᵢ |f(xᵢ)|²` of point evaluations, with a controlled loss in both directions: the first
family should stay a frame from below and the second a frame from above.

The answer below is that `n` points suffice for every `n ≥ m`, with the frame constants
`(1 - √((m-1)/n))²` and `(1 + √((M-1)/n))² Λ`. Here `Λ` bounds the Gram matrix `J` of the
second family, `J ≼ Λ · 1`, and

  `M = Tr J / Λ`

is its **effective dimension**. What the number of points depends on is `M`, not the number
of functions in the second family. That is what makes the theorem applicable when the second
family is infinite, and it is why the constants beat those obtainable from the
Kadison–Singer theorem. For `a = b` with both Gram matrices the identity, `M` is `m` and the
statement is the sparsification theorem of Batson, Spielman and Srivastava.

Two forms are advertised. In the first the conclusion is an inequality between matrices, in
the **Loewner order** `A ≼ B ↔ (B - A)` positive semidefinite; in the second it is read
through quadratic forms as an inequality between norms, which is the discretization
inequality for the `L₂` norm. Each comes in a version for a finite second family and one for
a countably infinite second family, where the Gram matrix `J` becomes a positive, injective
operator of finite trace on a Hilbert space `H` and the upper bound is an inequality between
operators.

Traces of the matrices appearing here are real, and real parts are taken with `RCLike.re`
wherever a real number is needed. Mathlib has no trace outside finite dimension, so the
trace of an operator is taken along a fixed Hilbert basis.

## The definitions restated here

* `Discretization.gram` — the Gram matrix `∫ a(x) a(x)* dμ(x)` of a finite family.
* `ContinuousLinearMap.traceAlong` — the trace of an operator along a Hilbert basis.
* `Discretization.Infinite.IsFiniteTracePos` — the three hypotheses on the Gram operator of
  an infinite second family: positive, of summable trace, and injective.

Each is reproduced verbatim from the development, under the same name, so that Comparator
can match it against its counterpart there. The four theorems likewise carry the names they
have in the development, so the names Palomar records are the ones a reader will find in the
proof files.
-/

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

namespace ContinuousLinearMap

variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The **trace of `T` along the Hilbert basis `e`**, `∑' k, Re ⟪e k, T (e k)⟫`.

For a positive operator the terms are nonnegative.  If their sum diverges, Lean's `∑'`
returns `0`, so every statement about the value assumes that the family is summable. -/
noncomputable def traceAlong (e : HilbertBasis κ ℂ H) (T : H →L[ℂ] H) : ℝ :=
  ∑' k, RCLike.re ⟪e k, T (e k)⟫_ℂ

end ContinuousLinearMap

namespace Discretization

namespace Infinite

variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The hypotheses carried by the Gram operator of an infinite second family: it is
**positive**, its **trace** along the basis `e` converges, and it is **injective**.

The first two say that `J` is a positive trace-class operator; the third replaces the
positive definiteness of the finite-dimensional Gram matrix.  A positive operator of finite
trace on an infinite-dimensional space is compact, so it is never bounded away from zero,
and injectivity is what the strict inequalities of the argument need. -/
structure IsFiniteTracePos (e : HilbertBasis κ ℂ H) (J : H →L[ℂ] H) : Prop where
  /-- `J` is a positive operator. -/
  nonneg : 0 ≤ J
  /-- The trace of `J` along `e` converges. -/
  summableTrace : Summable fun k => RCLike.re ⟪e k, J (e k)⟫_ℂ
  /-- `J` is injective. -/
  injective : ∀ v : H, J v = 0 → v = 0

end Infinite

end Discretization

namespace Discretization

/-! ### A finite second family -/

section Finite

variable {ι κ Ω : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [MeasurableSpace Ω]
  {μ : Measure Ω} [DecidableEq ι]

/-- **Generalized sparsification theorem** (Chkifa–Dolbeault–Krieg–Ullrich, Theorem 3), for
finite families.

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

where `c` is the coefficient vector of `g`.  If the second family is the singular basis of
the embedding of a reproducing kernel Hilbert space `H` into `L₂`, that is, an orthonormal
basis of `H` that is orthogonal in `L₂`, then the coefficient norm on the right is the
`H`-norm of `g` and `Λ` is the squared norm of the embedding. -/
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

/-! ### A countably infinite second family -/

section InfiniteGeneralGram

variable {ι κ Ω H : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] [MeasurableSpace Ω] {μ : Measure Ω}
  {e : HilbertBasis κ ℂ H} {J : H →L[ℂ] H}

/-- **Generalized sparsification theorem** (Chkifa–Dolbeault–Krieg–Ullrich, Theorem 3), for
a countable second family.

Let `a` be a family of square-integrable functions indexed by a finite nonempty set `ι` of
`m` elements with positive definite Gram matrix `I = ∫ a a* dμ`, and let `b : Ω → H` be
square-integrable with Gram operator `J`, that is `Re ⟪u, J u⟫ = ∫ |⟪u, b x⟫|² dμ` for every
`u`.  Assume `J` positive, injective and of finite trace, bounded by `Λ • 1`, and let
`M = Tr J / Λ` be its effective dimension.  Then for every `n ≥ m` there are `n` points and
positive weights with

`(1 - √((m-1)/n))² • I ≤ ∑ wᵢ a(xᵢ) a(xᵢ)*`  and
`∑ wᵢ b(xᵢ) b(xᵢ)* ≼ (1 + √((M-1)/n))² Λ • 1`,

the first in the matrix order and the second in the order of operators.  The number of
points is the same as for a finite second family, because it is governed by the effective
dimension and not by the size of the family. -/
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
  sorry

end InfiniteGeneralGram

section InfiniteNormDiscretization

variable {ι κ Ω H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {e : HilbertBasis κ ℂ H} {J : H →L[ℂ] H}

variable [Fintype ι] [DecidableEq ι] [CompleteSpace H] [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Discretization of the `L₂`-norm** (Chkifa–Dolbeault–Krieg–Ullrich, Corollary 4), for a
countable second family.

Under the hypotheses of `Discretization.Infinite.bss_generalized` with `I = 1`, the `n`
points and weights discretize the norm of every function in the span of the first family
from below,

`(1 - √((m-1)/n))² · ∫ |f|² dμ ≤ ∑ wᵢ |f(xᵢ)|²`,

and bound the weighted sum for every function in the span of the second family from above,

`∑ wᵢ |⟪u, b(xᵢ)⟫|² ≤ (1 + √((M-1)/n))² Λ · ‖u‖²`,

where a vector `u` of the Hilbert space plays the role of the coefficient vector.  What
controls the number of points is the effective dimension `M = Tr J / Λ`. -/
theorem exists_discretization [Nonempty ι] [Nonempty κ] [Countable κ]
    (hJ : IsFiniteTracePos e J) {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : J ≤ Λ • (1 : H →L[ℂ] H)) {a : Ω → ι → ℂ} {b : Ω → H}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : MemLp b 2 μ) (hgrama : gram a μ = 1)
    (hgramb : ∀ u, RCLike.re ⟪u, J u⟫_ℂ = ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (∀ c : ι → ℂ, (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
            * ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ
          ≤ ∑ i, w i * ‖star c ⬝ᵥ a (x i)‖ ^ 2) ∧
      (∀ u : H, ∑ i, w i * ‖⟪u, b (x i)⟫_ℂ‖ ^ 2
          ≤ (1 + Real.sqrt ((traceAlong e J / Λ - 1) / n)) ^ 2 * Λ * ‖u‖ ^ 2) :=
  sorry

end InfiniteNormDiscretization

end Infinite

end Discretization
