/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults
import Discretization.Potentials
import Discretization.Barrier
import Discretization.Averages
import Discretization.Iteration
import Discretization.MainTheorem
import Discretization.GeneralGram
import Discretization.NormDiscretization

/-!
# Constructive discretization

A generalization of the sparsification theorem of Batson, Spielman and Srivastava: given two
finite families of square-integrable functions on a measure space, one can select `n` points
and positive weights so that the first family stays a frame from below and the second stays a
frame from above, with bounds `(1 - √((m-1)/n))²` and `(1 + √((M-1)/n))² Λ`.  Here `m` is the
size of the first family, `Λ` bounds the Gram matrix `J` of the second one, and
`M = Tr J / Λ` is its **effective dimension** — not its cardinality, which is what makes the
upper bound dimension-free.

The argument is the potential-function argument of Batson–Spielman–Srivastava in the form
given by Chkifa, Dolbeault, Krieg and Ullrich.  Two matrices are carried along, a small one
for the lower bound and a large one for the upper bound; two real numbers, the potentials,
measure how close they are to failure; and each new sampling point is chosen so that neither
potential gets worse.

## Layout

* `Discretization.Potentials` — the two potentials `Φ(A) = Re Tr A⁻¹` and
  `Ψ_J(B) = Re Tr (J B⁻¹)`, and how the shifts `A ↦ A - δ • 1`, `B ↦ B + ζ • J` change them.
* `Discretization.Barrier` — the verifiers, which test a single point, and the barrier
  lemma: a weight between the two verifiers keeps both potentials from increasing.
* `Discretization.Averages` — the verifiers pass the test on average, so an admissible point
  exists.
* `Discretization.Iteration` — the construction: `n` steps, with the invariant that both
  matrices stay positive definite and neither potential exceeds its initial value.
* `Discretization.MainTheorem` — the initial data, the read-off of the frame bounds, and the
  theorem itself, `Discretization.bss_generalized_of_gram_eq_one`.
* `Discretization.GeneralGram` — removing the normalisation of the first family, which gives
  the theorem in the form of the paper, `Discretization.bss_generalized`.
* `Discretization.NormDiscretization` — the same statement read as a discretization
  inequality for the `L₂`-norm, `Discretization.exists_discretization`.
-/
