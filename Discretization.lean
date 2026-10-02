/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import BasicResults
public import Discretization.Parameters
public import Discretization.Potentials
public import Discretization.Barrier
public import Discretization.Averages
public import Discretization.UpperBarrier
public import Discretization.Iteration
public import Discretization.PotentialArgument
public import Discretization.EdgeCases.CardOne
public import Discretization.EdgeCases.SmallEffectiveDim
public import Discretization.EdgeCases.BothEdgeCases
public import Discretization.GeneralGram
public import Discretization.NormDiscretization
public import Discretization.BSS
public import Discretization.Infinite.Potentials
public import Discretization.Infinite.Barrier
public import Discretization.Infinite.Averages
public import Discretization.Infinite.Bounds
public import Discretization.Infinite.UpperBarrier
public import Discretization.Infinite.GeneralGram
public import Discretization.Infinite.NormDiscretization
public import Discretization.Infinite.Countable
public import Discretization.Infinite.RKHS
public import Discretization.KieferWolfowitz.MixEstimate
public import Discretization.KieferWolfowitz.Design
public import Discretization.KieferWolfowitz.NonDegenerate
public import Discretization.KieferWolfowitz.DetMax
public import Discretization.KieferWolfowitz.MainTheorem
public import Discretization.KieferWolfowitz.Measure
public import Discretization.KieferWolfowitz.ConvexHull
public import Discretization.KieferWolfowitz.Compact
public import Discretization.KieferWolfowitz.JohnDecomposition
public import Discretization.KieferWolfowitz.PointCount
public import Discretization.UniformDiscretization

/-!
# Norm discretization

Two theorems on discretizing a norm by finitely many point evaluations.

The first is the discretization theorem of Chkifa, Dolbeault, Krieg and Ullrich, a
generalization of the sparsification theorem of Batson, Spielman and Srivastava.  Given a
finite family of square-integrable functions on a measure space and a square-integrable map
`b` into a Hilbert space, one can select `n` points and positive weights so that the first
family stays a frame from below and `b` stays a frame from above, with bounds
`(1 - √((m-1)/n))²` and `(1 + √((M-1)/n))² Λ`.  Here `m` is the size of the first family,
`Λ` bounds the Gram operator `J = ∫ b(x) b(x)* dμ(x)`, and `M = Tr J / Λ` is its
**effective dimension**, not a dimension of the space.  This is what makes the upper bound
dimension-free.  A countable family `b(x) = (b_k(x))_k` and the kernel sections
`b(x) = K(x, ·)` of a reproducing kernel Hilbert space are the two cases of interest.

The argument is the potential-function argument of Batson–Spielman–Srivastava in the form
given by Chkifa, Dolbeault, Krieg and Ullrich.  Two matrices are carried along, a small one
for the lower bound and a large one for the upper bound; for a countable second family the
large one is an operator, and the two cases share everything but its analysis.  Two real
numbers, the potentials, measure how close they are to failure.  Each new sampling point is
chosen so that neither potential gets worse.

The second is the theorem of Kiefer and Wolfowitz in the form needed for sampling
projections: on an `m`-dimensional space of bounded functions on an arbitrary set, and for
every `ε > 0`, the uniform norm is dominated by the `L₂` norm of a finitely supported
probability measure with the constant `√(m+ε)`, and by `√m` if the functions are continuous
on a compact domain.  The measure is one whose Gram matrix has an almost maximal
determinant, and the whole argument consists of comparing that determinant with the
determinants obtained by giving one further point a small weight.  Thinned by the
sparsification theorem, the measure can be replaced by any `n ≥ m` points, at the price of
the factor `(1 - √((m-1)/n))⁻²`.

## Layout

The finite theory lies at the top level, with its three edge cases in
`Discretization/EdgeCases/`; `Discretization/Infinite/` holds the analysis of the upper
state for a second family in a Hilbert space and the theorems for it, and
`Discretization/KieferWolfowitz/` the second theorem, whose thinning to `n ≥ m` points is
again at the top level.

* `Discretization.Parameters`: the arithmetic of the four parameters `r`, `s`, `δ`, `ζ`
  that drive the construction.
* `Discretization.Potentials`: the two potentials `Φ(A) = Re Tr A⁻¹` and
  `Ψ_J(B) = Re Tr (J B⁻¹)`, and how the shifts `A ↦ A - δ • 1`, `B ↦ B + ζ • J` change them.
* `Discretization.Barrier`: the verifiers, which test a single point, and the barrier
  lemma.  A weight between the two verifiers keeps both potentials from increasing.
* `Discretization.Averages`: the verifiers pass the test on average.
* `Discretization.UpperBarrier`: what the construction needs to know about the upper state,
  `Discretization.UpperBarrier`, so that matrices and operators share everything else; the
  upper state after `k` steps, the existence of an admissible point, and the matrix instance
  `Discretization.matrixUpperBarrier`.
* `Discretization.Iteration`: the construction in `n` steps, with the invariant that both
  states stay admissible and neither potential exceeds its initial value.
* `Discretization.PotentialArgument`: the potential argument, under the side conditions
  `m ≥ 2` and `M ≥ 1 + 1/n`: the initial data, the read-off of the frame bounds, and the
  theorem, for every upper barrier and for finite families,
  `Discretization.bss_generalized_of_gram_eq_one`.
* `Discretization.EdgeCases.CardOne`: the edge case of a one-element first family, where
  the lower verifier becomes a constant, `Discretization.bss_generalized_of_unique`.
* `Discretization.EdgeCases.SmallEffectiveDim`: the edge case of an effective dimension
  below `1 + 1/n`, where the upper verifier becomes a constant,
  `Discretization.bss_generalized_of_small_dim`.
* `Discretization.EdgeCases.BothEdgeCases`: the two edge cases at the same time, where both
  verifiers are constants and a single point suffices,
  `Discretization.bss_generalized_of_unique_of_small_dim`.
* `Discretization.GeneralGram`: removing the normalisation of the first family, which gives
  the theorem in the form of the paper, `Discretization.bss_generalized`.
* `Discretization.NormDiscretization`: the same statement read as a discretization
  inequality for the `L₂`-norm, `Discretization.exists_discretization`.
* `Discretization.BSS`: the case of a single family, which is the sparsification theorem
  of Batson, Spielman and Srivastava, `Discretization.bss`, and its lower half for any
  positive definite Gram matrix, `Discretization.bss_lower`.
* `Discretization.Infinite.Potentials`: the upper potential `Ψ_J(B) = Tr (J B⁻¹)` for a
  positive operator `J` of finite trace.
* `Discretization.Infinite.Barrier`: the upper verifier and the barrier lemma for
  operators.
* `Discretization.Infinite.Averages`: on a separable space the Gram operator
  `J = ∫ b(x) b(x)* dμ(x)` is positive and of finite trace,
  `Discretization.Infinite.isFiniteTracePos_of_integral_rankOne`, with `∫ ‖b‖² dμ = Tr J`,
  `Discretization.Infinite.integral_norm_sq_eq_trace`; and the upper verifier passes the
  test on average.
* `Discretization.Infinite.Bounds`: a bound on the upper potential is a bound on the
  operator, `Ψ_J(B)⁻¹ • J ≼ B`.
* `Discretization.Infinite.UpperBarrier`: the operators as an upper barrier,
  `Discretization.Infinite.operatorUpperBarrier`, and with it the theorem without side
  conditions for a normalized first family and a nonzero separable Hilbert space,
  `Discretization.Infinite.bss_generalized_of_gram_eq_one'`.
* `Discretization.Infinite.GeneralGram`: removing the normalisation of the first family,
  which gives the theorem for a separable space and the Gram operator
  `J = ∫ b(x) b(x)* dμ(x)`, `Discretization.Infinite.bss_generalized`.
* `Discretization.Infinite.NormDiscretization`: the same statement read as a discretization
  inequality, `Discretization.Infinite.exists_discretization`.
* `Discretization.Infinite.Countable`: the theorem in the form of the paper, for a countable
  family `(b_k)` with `∑_k ‖b_k‖² < ∞` and its Gram matrix, deduced from the Hilbert-space
  form on `ℓ²(κ)`: `Discretization.Countable.bss_generalized`,
  `Discretization.Countable.exists_discretization`.
* `Discretization.Infinite.RKHS`: the discretization inequality for the norm of a reproducing
  kernel Hilbert space, with the kernel sections `b(x) = K(x, ·)` as second family and
  `M = ∫ K(x, x) dμ(x) / Λ`, `Discretization.RKHS.exists_discretization`.
* `Discretization.KieferWolfowitz.MixEstimate`: the one real inequality behind the
  Kiefer–Wolfowitz argument, describing how the determinant reacts to giving a new point the
  weight `α`.  No matrices occur in it.
* `Discretization.KieferWolfowitz.Design`: designs, that is finitely supported probability
  measures, and their Gram matrices `G = ∑ₖ wₖ a(xₖ) a(xₖ)*`.
* `Discretization.KieferWolfowitz.NonDegenerate`: for linearly independent functions some
  design has an invertible Gram matrix, so the determinant is somewhere positive.
* `Discretization.KieferWolfowitz.DetMax`: the maximisation of the determinant and its
  consequence `a(y)* G⁻¹ a(y) ≤ m + ε`, uniformly in `y`.
* `Discretization.KieferWolfowitz.MainTheorem`: the Kiefer–Wolfowitz theorem in terms of the
  points and weights, `Discretization.KieferWolfowitz.exists_design_kieferWolfowitz`.
* `Discretization.KieferWolfowitz.Measure`: the same statement for the measure
  `ϱ = ∑ₖ wₖ δ(xₖ)`, `Discretization.KieferWolfowitz.exists_probabilityMeasure_kieferWolfowitz`,
  together with the identity `gram a ϱ = G` that hands it to the discretization theorem.
* `Discretization.KieferWolfowitz.ConvexHull`: the Gram matrices of designs are the convex
  hull of the rank-one matrices `a(y) a(y)*`, and Carathéodory's theorem bounds the number
  of points by `2m² + 1`.
* `Discretization.KieferWolfowitz.Compact`: on a compact domain the maximum is attained and
  the constant is the sharp `√m`,
  `Discretization.KieferWolfowitz.exists_design_kieferWolfowitz_of_compact`.
* `Discretization.KieferWolfowitz.JohnDecomposition`: the Gram matrix of a design decomposes
  the identity over the design points, with weights summing to `m`.  This is John's
  decomposition of the identity, the condition dual to the Kiefer–Wolfowitz bound.
* `Discretization.KieferWolfowitz.PointCount`: the two theorems with the number of points
  bounded.
* `Discretization.UniformDiscretization`: the Kiefer–Wolfowitz design thinned by the
  sparsification theorem, which gives the uniform norm with any `n ≥ m` points,
  `Discretization.exists_uniform_discretization` and
  `Discretization.exists_uniform_discretization_of_compact`.
-/
