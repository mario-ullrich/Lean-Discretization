/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.GeneralGram
import Discretization.NormDiscretization
import Discretization.Infinite.GeneralGram
import Discretization.Infinite.NormDiscretization

/-!
# The generalized sparsification theorem — proofs

This module is the *Solution* of a Palomar submission. Comparator checks that every
declaration named in `comparator.json` has, in this module's environment, exactly the same
name and type as its counterpart in `Palomar.Sparsification.Challenge`, and that it uses no
axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

Nothing is declared here. The advertised statements

* `Discretization.bss_generalized` — the frame bounds
  `(1 - √((m-1)/n))² • I ≼ ∑ wᵢ a(xᵢ) a(xᵢ)*` and
  `∑ wᵢ b(xᵢ) b(xᵢ)* ≼ (1 + √((M-1)/n))² Λ • 1`, for a finite second family,
* `Discretization.exists_discretization` — the same read as a discretization inequality for
  the `L₂` norm,
* `Discretization.Infinite.bss_generalized` — the frame bounds for a countably infinite
  second family, the second one in the order of operators,
* `Discretization.Infinite.exists_discretization` — the discretization inequality in that
  case,

and the definitions they rest on — `Discretization.gram`,
`ContinuousLinearMap.traceAlong` and `Discretization.Infinite.IsFiniteTracePos` — all arrive
through the imports above, under their own names in the development: from
`BasicResults/IntegralQuadraticForm.lean`, `BasicResults/OperatorTrace.lean`,
`Discretization/Infinite/Potentials.lean`, `Discretization/GeneralGram.lean`,
`Discretization/NormDiscretization.lean`, `Discretization/Infinite/GeneralGram.lean` and
`Discretization/Infinite/NormDiscretization.lean`. The Challenge module restates exactly
those, which is why no wrapper is needed and why the names Palomar records are the names the
development actually uses.

The mathematics is the potential-function argument of Batson, Spielman and Srivastava in the
form given by Chkifa, Dolbeault, Krieg and Ullrich: two matrices are carried along, one
controlling each frame bound, and two potentials measure how close each is to failure. Each
of the `n` steps shifts both matrices, which costs an exactly computable amount of both
potentials, and the barrier lemma names the weights that spend no more than that. Averaging
the verifiers over `μ` shows that such a point exists.
-/
