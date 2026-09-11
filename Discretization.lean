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
import Discretization.NormDiscretization
import Discretization.Infinite.Potentials
import Discretization.Infinite.Barrier
import Discretization.Infinite.Averages
import Discretization.Infinite.Bounds
import Discretization.Infinite.Iteration
import Discretization.Infinite.MainTheorem
import Discretization.Infinite.NormDiscretization

/-!
# Constructive discretization

A generalization of the sparsification theorem of Batson, Spielman and Srivastava.  Given two
families of square-integrable functions on a measure space, one can select `n` points and
positive weights so that the first family stays a frame from below and the second stays a
frame from above, with bounds `(1 - √((m-1)/n))²` and `(1 + √((M-1)/n))² Λ`.  Here `m` is
the size of the first family, `Λ` bounds the Gram matrix `J` of the second one, and
`M = Tr J / Λ` is its **effective dimension**, not its cardinality.  This is what makes the
upper bound dimension-free, and it allows the second family to be countably infinite.

The argument is the potential-function argument of Batson–Spielman–Srivastava in the form
given by Chkifa, Dolbeault, Krieg and Ullrich.  Two matrices are carried along, a small one
for the lower bound and a large one for the upper bound.  Two real numbers, the potentials,
measure how close they are to failure.  Each new sampling point is chosen so that neither
potential gets worse.

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
-/
