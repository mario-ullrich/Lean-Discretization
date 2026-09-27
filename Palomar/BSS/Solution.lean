/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.BSS

/-!
# The sparsification theorem of Batson, Spielman and Srivastava — proof

This module is the *Solution* of a Palomar submission. Comparator checks that every
declaration named in `comparator.json` has, in this module's environment, exactly the same
name and type as its counterpart in `Palomar.BSS.Challenge`, and that it uses no axioms
beyond `propext`, `Classical.choice` and `Quot.sound`.

Nothing is declared here. The advertised statement `Discretization.bss`, and the definition
it rests on, `Discretization.gram`, arrive through the import above under their own names in
the development: from `BasicResults/IntegralQuadraticForm.lean` and
`Discretization/BSS.lean`. The Challenge module restates exactly those, which is why no
wrapper is needed and why the names Palomar records are the names the development actually
uses.

The theorem is the case `a = b` of the generalized sparsification theorem
`Discretization.bss_generalized_of_gram_eq_one'`: the Gram matrix of the second family is
then the identity, `Λ = 1` bounds it, and its effective dimension `Tr J / Λ` is the number
of functions, so both frame constants are built from the same `√((m-1)/n)`.

Underneath lies the potential-function argument. Two matrices are carried along, one for
each frame bound, and two potentials measure how close each is to failure. Each of the `n`
steps shifts both matrices, which costs an exactly computable amount of both potentials,
and the barrier lemma names the weights that spend no more than that. Averaging the
verifiers over `μ` shows that such a point exists.
-/
