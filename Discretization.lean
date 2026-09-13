/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults
import Discretization.Parameters
import Discretization.Potentials
import Discretization.Barrier
import Discretization.Averages
import Discretization.Iteration
import Discretization.MainTheorem
import Discretization.GeneralGram
import Discretization.CardOne
import Discretization.SmallEffectiveDim
import Discretization.BothEdgeCases
import Discretization.NormDiscretization
import Discretization.Infinite.Potentials
import Discretization.Infinite.Barrier
import Discretization.Infinite.Averages
import Discretization.Infinite.Bounds
import Discretization.Infinite.Iteration
import Discretization.Infinite.MainTheorem
import Discretization.Infinite.NormDiscretization
import Discretization.KieferWolfowitz.MixEstimate
import Discretization.KieferWolfowitz.Design
import Discretization.KieferWolfowitz.NonDegenerate
import Discretization.KieferWolfowitz.DetMax
import Discretization.KieferWolfowitz.MainTheorem
import Discretization.KieferWolfowitz.Measure
import Discretization.KieferWolfowitz.ConvexHull
import Discretization.KieferWolfowitz.Compact
import Discretization.KieferWolfowitz.PointCount

/-!
# Constructive discretization

Two theorems on discretizing a norm by finitely many point evaluations.

The first is a generalization of the sparsification theorem of Batson, Spielman and
Srivastava.  Given two families of square-integrable functions on a measure space, one can
select `n` points and positive weights so that the first family stays a frame from below and
the second stays a frame from above, with bounds `(1 - √((m-1)/n))²` and
`(1 + √((M-1)/n))² Λ`.  Here `m` is the size of the first family, `Λ` bounds the Gram matrix
`J` of the second one, and `M = Tr J / Λ` is its **effective dimension**, not its
cardinality.  This is what makes the upper bound dimension-free, and it allows the second
family to be countably infinite.

The argument is the potential-function argument of Batson–Spielman–Srivastava in the form
given by Chkifa, Dolbeault, Krieg and Ullrich.  Two matrices are carried along, a small one
for the lower bound and a large one for the upper bound.  Two real numbers, the potentials,
measure how close they are to failure.  Each new sampling point is chosen so that neither
potential gets worse.

The second is the theorem of Kiefer and Wolfowitz in the form needed for sampling
projections: on an `n`-dimensional space of bounded functions on an arbitrary set, and for
every `ε > 0`, the uniform norm is dominated by the `L₂` norm of a finitely supported
probability measure with the constant `√(n+ε)`, and by `√n` if the functions are continuous
on a compact domain.  The measure is one whose Gram matrix has an almost maximal
determinant, and the whole argument consists of comparing that determinant with the
determinants obtained by giving one further point a small weight.

## Layout

* `Discretization.Parameters`: the arithmetic of the four parameters `r`, `s`, `δ`, `ζ`
  that drive the construction.
* `Discretization.Potentials`: the two potentials `Φ(A) = Re Tr A⁻¹` and
  `Ψ_J(B) = Re Tr (J B⁻¹)`, and how the shifts `A ↦ A - δ • 1`, `B ↦ B + ζ • J` change them.
* `Discretization.Barrier`: the verifiers, which test a single point, and the barrier
  lemma.  A weight between the two verifiers keeps both potentials from increasing.
* `Discretization.Averages`: the verifiers pass the test on average, so an admissible point
  exists.
* `Discretization.Iteration`: the construction in `n` steps, with the invariant that both
  matrices stay positive definite and neither potential exceeds its initial value.
* `Discretization.MainTheorem`: the initial data, the read-off of the frame bounds, and the
  theorem itself, `Discretization.bss_generalized_of_gram_eq_one`.
* `Discretization.GeneralGram`: removing the normalisation of the first family, which gives
  the theorem in the form of the paper, `Discretization.bss_generalized`.
* `Discretization.NormDiscretization`: the same statement read as a discretization
  inequality for the `L₂`-norm, `Discretization.exists_discretization`.
* `Discretization.CardOne`: the edge case of a one-element first family, where the lower
  verifier becomes a constant, `Discretization.bss_generalized_of_unique`.
* `Discretization.SmallEffectiveDim`: the edge case of an effective dimension below
  `1 + 1/n`, where the upper verifier becomes a constant,
  `Discretization.bss_generalized_of_small_dim`.
* `Discretization.BothEdgeCases`: the two edge cases at the same time, where both verifiers
  are constants and a single point suffices,
  `Discretization.bss_generalized_of_unique_of_small_dim`.
* `Discretization.Infinite.Potentials`: the upper potential `Ψ_J(B) = Tr (J B⁻¹)` for a
  positive operator `J` of finite trace, where the second family is indexed by a countable
  set.
* `Discretization.Infinite.Barrier`: the upper verifier and the barrier lemma for
  operators.
* `Discretization.Infinite.Averages`: the upper verifier passes the test on average, so an
  admissible point exists.
* `Discretization.Infinite.Bounds`: a bound on the upper potential is a bound on the
  operator, `Ψ_J(B)⁻¹ • J ≼ B`.
* `Discretization.Infinite.Iteration`: the construction, with a matrix on the lower side and
  an operator on the upper one.
* `Discretization.Infinite.MainTheorem`: the theorem for a countable second family,
  `Discretization.Infinite.bss_generalized_of_gram_eq_one`.
* `Discretization.Infinite.NormDiscretization`: the same statement read as a discretization
  inequality, `Discretization.Infinite.exists_discretization`.
* `Discretization.KieferWolfowitz.MixEstimate`: the one real inequality behind the
  Kiefer–Wolfowitz argument, describing how the determinant reacts to giving a new point the
  weight `α`.  No matrices occur in it.
* `Discretization.KieferWolfowitz.Design`: designs, that is finitely supported probability
  measures, and their Gram matrices `G = ∑ₖ wₖ a(xₖ) a(xₖ)*`.
* `Discretization.KieferWolfowitz.NonDegenerate`: for linearly independent functions some
  design has an invertible Gram matrix, so the determinant is somewhere positive.
* `Discretization.KieferWolfowitz.DetMax`: the maximisation of the determinant and its
  consequence `a(y)* G⁻¹ a(y) ≤ n + ε`, uniformly in `y`.
* `Discretization.KieferWolfowitz.MainTheorem`: the Kiefer–Wolfowitz theorem in terms of the
  points and weights, `Discretization.KieferWolfowitz.exists_design_kieferWolfowitz`.
* `Discretization.KieferWolfowitz.Measure`: the same statement for the measure
  `ϱ = ∑ₖ wₖ δ(xₖ)`, `Discretization.KieferWolfowitz.exists_probabilityMeasure_kieferWolfowitz`,
  together with the identity `gram a ϱ = G` that hands it to the sparsification theorem.
* `Discretization.KieferWolfowitz.ConvexHull`: the Gram matrices of designs are the convex
  hull of the rank-one matrices `a(y) a(y)*`, and Carathéodory's theorem bounds the number
  of points by `2n² + 1`.
* `Discretization.KieferWolfowitz.Compact`: on a compact domain the maximum is attained and
  the constant is the sharp `√n`,
  `Discretization.KieferWolfowitz.exists_design_kieferWolfowitz_of_compact`.
* `Discretization.KieferWolfowitz.PointCount`: the two theorems with the number of points
  bounded.
-/
