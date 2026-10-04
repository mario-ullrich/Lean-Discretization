/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.OneSidedDiscretization

/-!
# One-sided discretization of the `L₂` norm with equal weights: proofs

This module is the *Solution* of a Palomar submission. Comparator checks that every
declaration named in `comparator.json` has, in this module's environment, exactly the same
name and type as its counterpart in `Palomar.OneSidedDiscretization.Challenge`, and that it
uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. The definition the
statements use, `Discretization.gram`, is not a hole: Comparator checks that it is the
same declaration, body included, in both modules.

Nothing is declared here. The advertised statements

* `Discretization.bss_lower_equal_weights`: `(1 - √((m-1)/n))² • I ≼ (1/n) ∑ᵢ a(xᵢ) a(xᵢ)*`
  on a probability space, in the Loewner order,
* `Discretization.exists_one_sided_discretization`:
  `(1 - √((m-1)/n))² ∫ |f|² dμ ≤ (1/n) ∑ᵢ |f(xᵢ)|²` for every `f` in the span,

and the definition they rest on, `Discretization.gram`, arrive through the import above,
under their own names in the development: from `Discretization/OneSidedDiscretization.lean`
and `BasicResults/IntegralQuadraticForm.lean`. The Challenge module restates exactly those,
which is why no wrapper is needed and why the names Palomar records are the names the
development actually uses.

The proof is the lower half of the potential-function argument of Batson, Spielman and
Srivastava in the form of Chkifa, Dolbeault, Krieg and Ullrich. Only the matrix for the
lower frame bound is carried along, and the upper verifier is the constant `n`, whose
average is `n` because `μ` is a probability measure. A point passes when its lower verifier
exceeds `n`, and the weight it receives, the reciprocal of that verifier, is then at most
`1/n` (`Discretization.bss_lower_le_one_div`). Raising every weight to `1/n` only enlarges
the sum, since the matrices `a(xᵢ) a(xᵢ)*` are positive semidefinite.
-/

@[expose] public section
