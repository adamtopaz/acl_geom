/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import AclGeom.Interpretation.Naturality
import AclGeom.Transfer.JCorrectness

/-!
# Field isomorphisms from closed-subfield lattices of perfect fields

The corrected interpreted reconstruction (the corrected counterpart of blueprint Prop
`interpreted-reconstruction`) builds a field isomorphism from a closed-subfield lattice
isomorphism through the interpreted ratio field of one Frobenius class
(`nonempty_ringEquiv_of_closedIF_orderIso`). Its two completeness inputs are supplied here by the
proved rank-five completeness of geometric `J` over the algebraic-closure pairs
(`jCompletenessACF`, with `five_le_trdeg_algebraicClosure`), and the characteristic exponents are
the canonical ones. The result needs only perfection of both fields and rank five of the source:
no relatively algebraically closed base is assumed, and none is needed for the bare existence of a
field isomorphism.

The public reconstruction theorem additionally assumes relatively algebraically closed bases and
proves that a compatible field isomorphism induces the given lattice map; this module asserts only
existence. The original literal decoder and advertised operation semantics are refuted
(`Counterexamples.GenericArithmetic`, `Counterexamples.GenericNegation`). The separate
geometric invariance assertions for the literal predicates and the correspondence of
quotient carriers by equivalence closure are proved in `Counterexamples.BlueprintTransport`.
The literal operation recipes and their invariance are proved in
`Counterexamples.BlueprintTotalGraphs`; their true raw totality and reverse components are
proved separately. `Counterexamples.RatioAddQuotient` refutes addition functionality after
any identification of nonzero representatives with the named zero adjoined, when `2 ≠ 0`.
The literal decoded construction has a recorded refutation and a proved corrected replacement.
The original formulas and proofs retain their provenance; true bypassed source statements
and the R1/R2 source-disposition work remain separate.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#8).
-/

namespace AclGeom

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K] [Field l] [Field L] [Algebra l L]

/-- **Perfect fields with isomorphic closed-subfield lattices are isomorphic** (the unconditional
existence form of the corrected interpreted reconstruction, blueprint Prop
`interpreted-reconstruction`). If `K` and `L` are perfect, `K/k` has transcendence degree at least
five and the lattices of relatively algebraically closed intermediate fields of `K/k` and `L/l` are
order isomorphic, then `K` and `L` are isomorphic fields. No relatively algebraically closed base,
completeness input or characteristic exponent is supplied by the caller. The resulting isomorphism
is not asserted to induce the given lattice map. -/
theorem nonempty_ringEquiv_of_closedIF_orderIso_of_perfectField [PerfectField K] [PerfectField L]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) (e : ClosedIF k K ≃o ClosedIF l L) :
    Nonempty (K ≃+* L) := by
  have htr' : (5 : Cardinal) ≤ Algebra.trdeg l L :=
    Cardinal.ofNat_le_lift_iff.1 <| (Cardinal.ofNat_le_lift_iff.2 htr).trans
      (lift_trdeg_le_of_orderIso e)
  have : IsAlgClosed ↥(algebraicClosure k (AlgebraicClosure K)) := IsAlgClosure.isAlgClosed k
  have : IsAlgClosed ↥(algebraicClosure l (AlgebraicClosure L)) := IsAlgClosure.isAlgClosed l
  exact nonempty_ringEquiv_of_closedIF_orderIso (ringExpChar K) htr
    (jCompletenessACF (five_le_trdeg_algebraicClosure htr)) (ringExpChar L)
    (jCompletenessACF (five_le_trdeg_algebraicClosure htr')) e

end AclGeom
