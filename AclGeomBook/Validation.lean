/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import VersoManual
import AclGeom.Test.Validation
import AclGeom.Counterexamples.GenericNegation

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Validation and remaining source obligations" =>

%%%
tag := "validation"
%%%

The blueprint asks for eleven mathematical checks. Several are already public theorems;
others involve literal operation graphs whose representative choices are defective. This
chapter records the evidence and its precise scope. The entire suite is still open, as is
the complete disposition audit for the original and supplementary blueprints.

# Characteristic and Frobenius checks
%%%
tag := "validation-frobenius"
%%%

TEST-1 is covered by `frobeniusZPow_eq_one_of_eq_one`, `PerfExt.frobHom_eq_id` and
`Perfection.Induces.eq_of_p_eq_one`: in characteristic zero the integral action is the
identity, and the rank-five reconstruction fibre reduces to literal uniqueness.

For TEST-2, `Perfection.inducedIso_frobZPow` proves that every integral iterate induces the
identity on the original closed-field lattice when the base is RAC. Restriction to its
atoms gives the identity on points. In positive characteristic, distinctness requires positive
transcendence degree, with no rank-five or RAC hypothesis:

{docstring AclGeom.Perfection.frobZPow_injective}

# Rational function fields
%%%
tag := "validation-rational-function-fields"
%%%

TEST-8 applies the actual reconstruction theorem to rational function fields. Both bases
are arbitrary fields, the characteristic is unrestricted, and both chosen perfections are
arbitrary. The supporting results discharge RAC and identify the transcendence degree:

{docstring AclGeom.Test.isRAC_bot_ratFn}

{docstring AclGeom.Test.trdeg_ratFn}

The theorem derives equality of the variable counts from an order isomorphism, constructs
the compatible field isomorphism of perfections and identifies its exact Frobenius fibre:

{docstring AclGeom.reconstruction_ratFn}

# Diagram and interpretation checks
%%%
tag := "validation-interpretation"
%%%

TEST-3's seven multiplication-diagram lines and rank assertion are proved in
`Config.MulDiagramCheck`: `mulDiagram_of_indep`, the seven `mtable_line_…` lemmas and
`mtable_rank_XYA`. The literal `BlueprintJAdd` and `BlueprintJMul` coordinate graphs are
refuted in `Counterexamples.GenericArithmetic`. The corrected coupled coordinate checks
are `jAddRel_jTupleOf_iff` and `jMulRel_jTupleOf_iff` in `Interpretation.JArithSem`.
They retain their explicit class-correctness inputs.

For TEST-4, `frobEq_iff_frobenius_twist` includes both natural-number directions, and
`frobEq_iff_exists_frobeniusZPow` gives the integral-exponent formulation. The reverse
construction `frobEq_of_frobenius_twist` uses the rank-five bound. The forward completeness
interface keeps its ACF input explicit; the proved `jCompletenessACF`, with the transported
rank-five bound, supplies that input in the source setting. `frobEq_equivalence` and
`frobEqSetoid` prove the global equivalence-relation conclusion over perfect ambient fields
at rank five, supplying completeness internally and requiring neither RAC nor an infinite
base. These results do not settle
every original simultaneous-representative or interpreted-carrier claim.

For TEST-5, the literal `BlueprintRatioEq` is refuted by
`blueprintRatioEq_counterexample`. The corrected `ratioEq_iff` combines `RatioEq.div_eq`
and `ratioEq_of_div_eq`. Its converse uses a fresh `t` and the prescribed witnesses
`c₁ = s₂*t`, `c₂ = r₂*t`, with the corresponding two common products. The corrected
statement retains its explicit completeness and carrier hypotheses.

TEST-6 has a proved corrected zero-addition branch: `JNegTotalRel` on the common-denominator
numerators, `jNegTotalRel_iff`, and `ratioAddGraph_iff` identify the decoded sum with zero.
The literal negation detour and literal total-nonzero-addition claim are refuted in
`Counterexamples.GenericNegation`. Both predicates retain every auxiliary class-membership
condition. Over an infinite base at rank five, each graph admits two distinct outputs
inside one Frobenius class, with no completeness hypothesis:

{docstring AclGeom.blueprintJNeg_not_functional_on_class}

{docstring AclGeom.blueprintJAddTotalNZ_not_functional_on_class}

The explicit families are `blueprintJNeg_smul` and `blueprintJAddTotalNZ_kappa`.
Negation accepts every `j(c*x,a)` for nonzero base scalars `c`; when `2 ≠ 0`,
`blueprintJNeg_self` even makes `j(x,a)` its own negation, distinct from `j(-x,a)`.
For independent `x,y,a`, the total-addition detour accepts `j(κ*x+y,a)` for every
nonzero `κ`, giving the wrong output when `κ ≠ 1`. These inputs satisfy the original
lemma's nonvanishing-over-`acl(a)` hypotheses. The original source formulas and proof
are retained, following the counterexamples reported on
[issue #23](https://github.com/adamtopaz/acl_geom/issues/23#issuecomment-6210013012) and
[its total-addition follow-up](https://github.com/adamtopaz/acl_geom/issues/23#issuecomment-6210631348).
The corrected coupled negation/addition predicates have the proved semantics cited above.
The additional theorem `blueprintRatioEq_no_decoder` rules out the advertised literal
decoder on a fixed class, even after passage to the equivalence closure of the relation.
`BlueprintTransport` proves literal predicate invariance and the correspondence of
quotient carriers under lattice isomorphisms. It asserts no field structure on these
carriers. `BlueprintRatioEq.symm` proves the literal symmetry assertion over arbitrary
fields. `blueprintRatioEq_refl` proves fixed-class reflexivity over perfect ambient fields
at rank five, with arbitrary bases and internally supplied completeness.
`blueprintRatioEq_not_transitive` refutes transitivity over arbitrary fields at rank five,
with no completeness or perfection hypothesis. The literal relation therefore does not
define a setoid. `BlueprintTotalGraphs` transcribes both raw representative-level recipes
and proves their geometric invariance with all literal replacement witnesses. Source
totality, decoded-operation claims and the remaining provenance retain separate obligations. The bare field-isomorphism existence result is now stated
without completeness inputs as `nonempty_ringEquiv_of_closedIF_orderIso_of_perfectField`;
its bases need not be relatively algebraically closed. Remaining source provenance
obligations still require their own disposition.

# Dimension and endpoint hypotheses
%%%
tag := "validation-dimension"
%%%

TEST-7 is covered by `lift_trdeg_eq_of_orderIso` and `trdeg_eq_of_orderIso`; the point/lattice
presentation bridge transports the same dimension. `PerfExt.trdeg_eq_of_hom` also proves
invariance under field-pair arrows, including the rank-five property.

For TEST-9, the public reconstruction and fullness statements retain the source rank-five
hypothesis. Literal uniqueness is restricted to characteristic zero; positive characteristic
has the exact Frobenius fibre and uniqueness of the exponent. The lower-rank warning is
formalized in `Counterexamples.KernelRank`. The positive-transcendence-degree Frobenius
statements above concern distinctness of automorphisms and do not assert reconstruction
below rank five.

# Quotient and Hom-set checks
%%%
tag := "validation-quotient"
%%%

For TEST-10, `PerfExt.congruence_frobRel` proves representative independence of composition,
using Frobenius naturality. The quotient category and its identity laws are Mathlib's
`CategoryTheory.Quotient`; the quotient of this groupoid is a groupoid.

TEST-11 is expressed by `geomLit_map_surjective`, `geomLit_map_eq_iff` and
`geomQuot_map_bijective`. They prove the literal surjection, exact Frobenius fibres and
injectivity after quotienting. The functorial chapter displays their hypotheses and
conclusions.

# Reproducing the dependency audit
%%%
tag := "validation-dependencies"
%%%

Run `lake env python3 scripts/audit_axioms.py --output /tmp/acl_geom_axiom_audit`, choosing a
new or empty output directory. The driver builds both mathematical library roots and checks
that their imported module inventory equals the mathematical source inventory. It records
each declaration's module, visibility, kind and axiom dependencies, including generated
public declarations, and writes source hashes and logs. Selection uses declaring modules,
so declarations outside the project namespaces are included too.

The command fails for project axioms or dependencies outside `propext`, `Classical.choice`
and `Quot.sound`. A successful dependency audit certifies that scope at the recorded source
hashes; the unresolved blueprint statements above still require mathematical dispositions.
