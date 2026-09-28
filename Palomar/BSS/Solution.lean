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

The proof is the potential-function argument of Batson, Spielman and Srivastava. Two
matrices are carried along, one for each frame bound, and two potentials measure how close
each is to failure. Each of the `n` steps shifts both matrices, which costs an exactly
computable amount of both potentials, and the barrier lemma names the weights that spend no
more than that. Averaging the verifiers over `μ` shows that such a point exists. The
development in `Discretization/` runs this argument in the form of Chkifa, Dolbeault, Krieg
and Ullrich, which allows a second family; `Discretization/BSS.lean` reads off the statement
for a single family.
-/
