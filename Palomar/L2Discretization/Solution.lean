/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.GeneralGram
public import Discretization.NormDiscretization
public import Discretization.Infinite.GeneralGram
public import Discretization.Infinite.RKHS

/-!
# The discretization theorem and the discretization of the `L₂`-norm: proofs

This module is the *Solution* of a Palomar submission. Comparator checks that every
declaration named in `comparator.json` has, in this module's environment, exactly the same
name and type as its counterpart in `Palomar.L2Discretization.Challenge`, and that it uses no
axioms beyond `propext`, `Classical.choice` and `Quot.sound`. The definitions the
statements use, `Discretization.gram`, `Discretization.RKHS.evalCLM` and
`Discretization.RKHS.kernelSection`, are not holes: Comparator checks that each is the
same declaration, body included, in both modules.

Nothing is declared here. The advertised statements

* `Discretization.bss_generalized`: the frame bounds
  `(1 - √((m-1)/n))² • I ≼ ∑ wᵢ a(xᵢ) a(xᵢ)*` and
  `∑ wᵢ b(xᵢ) b(xᵢ)* ≼ (1 + √((M-1)/n))² Λ • 1`, for a finite second family, from
  `Discretization/GeneralGram.lean`,
* `Discretization.exists_discretization`: the same read as a discretization inequality for
  the `L₂` norm, from `Discretization/NormDiscretization.lean`,
* `Discretization.Infinite.bss_generalized`: the frame bounds for a second family with
  values in a separable Hilbert space, the second one in the order of operators, from
  `Discretization/Infinite/GeneralGram.lean`,
* `Discretization.RKHS.exists_discretization`: the discretization of the `L₂`-norm from
  below and of the norm of a reproducing kernel Hilbert space from above, from
  `Discretization/Infinite/RKHS.lean`,

and the definitions they rest on, `Discretization.gram` from
`BasicResults/IntegralQuadraticForm.lean` and `Discretization.RKHS.evalCLM`,
`Discretization.RKHS.kernelSection` from `Discretization/Infinite/RKHS.lean`, all arrive
through the imports above under their own names in the development. The Challenge module
restates exactly those, which is why no wrapper is needed and why the names Palomar records
are the names the development actually uses.

The mathematics is the potential-function argument of Batson, Spielman and Srivastava in the
form given by Chkifa, Dolbeault, Krieg and Ullrich: two matrices, or a matrix and an
operator, are carried along, one controlling each frame bound, and two potentials measure how
close each is to failure. Each of the `n` steps shifts both, which costs an exactly
computable amount of both potentials, and the barrier lemma names the weights that spend no
more than that. Averaging the verifiers over `μ` shows that such a point exists. For the
reproducing kernel Hilbert space the second family is the map `x ↦ kₓ` to the kernel
sections, whose Gram operator is injective and bounded by `Λ • 1` exactly under the two
hypotheses on the space.
-/

@[expose] public section
