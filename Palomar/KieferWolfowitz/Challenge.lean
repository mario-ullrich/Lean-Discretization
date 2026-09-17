/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.Compactness.Compact

/-!
# The Kiefer–Wolfowitz theorem for sampling projections — statement surface

This module is the *Challenge* of a Palomar submission: the small, auditable surface
carrying the advertised statements. It imports nothing beyond Mathlib, so every notion it
uses is either standard or written out here. The proofs live in
`Palomar.KieferWolfowitz.Solution`, which supplies them from the development in
`Discretization/KieferWolfowitz/`; the `sorry`s below are the placeholders required by that
format.

## The mathematics

Let `D` be an arbitrary set and let `a₁, …, aₙ` be linearly independent bounded functions on
it, spanning an `n`-dimensional space `V`. The question is which measure to discretize: is
there a finitely supported probability measure `ϱ = ∑ₖ wₖ δ(xₖ)` for which the uniform norm
on `V` is already controlled by the `L₂(ϱ)` norm?

The answer of Kiefer and Wolfowitz is yes, with the constant `√n`, up to an arbitrarily
small loss on a general domain:

  `|f(y)|² ≤ (n + ε) · ∑ₖ wₖ |f(xₖ)|²`

for every point `y ∈ D` and every `f ∈ V`. On a compact domain and for continuous functions
the loss disappears and the constant is the sharp `√n`. In both cases at most `2n² + 1`
points are needed, by Carathéodory's theorem applied to the Gram matrices of designs.

The measure is one whose Gram matrix has an almost maximal determinant. Applying the
sparsification theorem to such a measure is how one arrives at sampling projections with few
points and small norm.

Two hypotheses are stated in the form the argument consumes. Linear independence appears as
the separating condition `∀ c, (∀ y, ⟪c, a(y)⟫ = 0) → c = 0`, which the development
identifies with `LinearIndependent ℂ`; boundedness appears as one constant `C` bounding all
the values. The design is given as points and weights rather than as a measure; the measure
form is proved in the development as well.

## The definition restated here

* `Discretization.KieferWolfowitz.designGram` — the Gram matrix
  `∑ₖ wₖ a(xₖ) a(xₖ)*` of a design.

It is reproduced verbatim from the development, under the same name, so that Comparator can
match it against its counterpart there. The two theorems likewise carry the names they have
in the development, so the names Palomar records are the ones a reader will find in the
proof files.
-/

open Matrix
open scoped ComplexOrder

namespace Discretization

namespace KieferWolfowitz

section Design

variable {Ω ι : Type*}

/-- **The Gram matrix of a design.**  For points `x₁, …, x_N` with weights `w₁, …, w_N`,

`designGram a x w = ∑ₖ wₖ · a(xₖ) a(xₖ)*`.

If the weights are nonnegative and sum to one this is the matrix of the inner products
`⟪aᵢ, aⱼ⟫` in `L₂` of the measure `∑ₖ wₖ δ(xₖ)`. -/
noncomputable def designGram (a : Ω → ι → ℂ) {N : ℕ} (x : Fin N → Ω) (w : Fin N → ℝ) :
    Matrix ι ι ℂ :=
  ∑ k, w k • vecMulVec (a (x k)) (star (a (x k)))

end Design

section Theorems

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Kiefer–Wolfowitz theorem, with the number of points bounded.**

For linearly independent bounded functions `a₁, …, a_n` on an arbitrary set and every
`ε > 0` there is a design of at most `2n² + 1` points, that is a finitely supported
probability measure `∑ₖ wₖ δ(xₖ)` with invertible Gram matrix, such that

`|f(y)|² ≤ (n + ε) · ∑ₖ wₖ |f(xₖ)|²`

for every point `y` and every function `f(y) = ⟪c, a(y)⟫` in the span.  This is
Proposition 9 of Krieg, Pozharska, Ullrich and Ullrich. -/
theorem exists_design_kieferWolfowitz_card_le [Nonempty ι] (a : Ω → ι → ℂ) {C : ℝ}
    (hC : ∀ y i, ‖a y i‖ ≤ C) (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (x : Fin N → Ω) (w : Fin N → ℝ), N ≤ 2 * Fintype.card ι ^ 2 + 1 ∧
      (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧ (designGram a x w).PosDef ∧
      ∀ (c : ι → ℂ) (y : Ω),
        ‖star c ⬝ᵥ a y‖ ^ 2 ≤ (Fintype.card ι + ε) * ∑ k, w k * ‖star c ⬝ᵥ a (x k)‖ ^ 2 :=
  sorry

/-- **The Kiefer–Wolfowitz theorem on a compact domain**, with the sharp constant and the
number of points bounded.

For linearly independent continuous functions `a₁, …, a_n` on a compact space there is a
design of at most `2n² + 1` points with

`|f(y)|² ≤ n · ∑ₖ wₖ |f(xₖ)|²`

for every point `y` and every `f` in the span: the uniform norm is dominated by the `L₂`
norm of the design with the constant `√n`, and no `ε` is lost. -/
theorem exists_design_kieferWolfowitz_of_compact_card_le [Nonempty ι] [TopologicalSpace Ω]
    [CompactSpace Ω] (a : Ω → ι → ℂ) (hcont : ∀ i, Continuous fun y => a y i)
    (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0) :
    ∃ (N : ℕ) (x : Fin N → Ω) (w : Fin N → ℝ), N ≤ 2 * Fintype.card ι ^ 2 + 1 ∧
      (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧ (designGram a x w).PosDef ∧
      ∀ (c : ι → ℂ) (y : Ω),
        ‖star c ⬝ᵥ a y‖ ^ 2 ≤ Fintype.card ι * ∑ k, w k * ‖star c ⬝ᵥ a (x k)‖ ^ 2 :=
  sorry

end Theorems

end KieferWolfowitz

end Discretization
