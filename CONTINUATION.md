# Continuation guide

This document lets a fresh agent (or human) pick up the formalization
with no prior context. Read the **Current status** section first, then the
open GitHub issues, then start working.

## What this project is

A Lean 4 formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem. The mathematical source of truth is
`sources/blueprint.tex`. The library lives in `AclGeom/`, a Verso book
documenting it lives in `AclGeomBook/` (built with `lake exe book`).
Toolchain: see `lean-toolchain`. The upgrade to Lean/Mathlib v4.34.1 (Verso
v4.34.0) was committed and pushed as `8a54b54` (#20, closed). The complete
local build and rendered book pass; reproduction and measurements appear at
the end of this guide. Verso uses the compatible stable tag for the toolchain.

## Current status (2026-10-18; #5)

Guarded affine-grid extraction and Q completeness are now proved for every ACF pair,
and the multiplication converse gives ACF J completeness at transcendence degree at least
five. The product-output clause now also holds over arbitrary fields for an actual diagram
and representatives X=[x], Y=[y], V=[x/y], with no closedness, perfection or rank premise:
`MulDiagram.product_point`. Only E=[xy] reflects from the algebraic closure; the full
auxiliary table remains an ACF result. Corrected projected Q/Q′ equivalences are now proved
over arbitrary bases and perfect ambient fields at rank five, with every existential
point over K. The raw consequences remain refuted. General raw existential-witness
descent is an unresolved exploratory question, not a separately stated source theorem. The actual chart and its original-field
coordinate descent are internal. The public
`exists_reconstruction` and `reconstruction_target` now supply both completeness proofs
internally. Their only hypotheses are the two original RAC bases, source rank five, the
chosen perfections and lattice isomorphism. The exact Frobenius fibre and converse are
included. Original scheme/action algebraization and descent and true bypassed source
statements remain obligations. Point-geometry reconstruction, the automorphism exact sequence and
the rank-five literal/Frobenius-quotient functorial statements are proved. The canonical
perfection-choice equivalence and its geometry compatibility are proved too. The literal
negation and total-nonzero-addition graphs are separately refuted, with all auxiliary
class conditions, over infinite bases at rank five; their corrected coupled replacements
have proved semantics. The global Frobenius setoid is proved on geometric J-tuples over
perfect ambient fields at rank five, without RAC or an infinite base. The literal
full-carrier TOT/decoded construction has recorded refutations and a proved corrected
replacement. Addition remains nonfunctional after any identification of nonzero pairs with
the named zero adjoined when `2 ≠ 0`, independently of a decoder. Its true raw totality and
nonzero-input reverse components and geometric transport are proved. The original I6b/I6c
clauses are disposed of with their precise hypotheses and original provenance retained;
R1--R4 are proved for the actual reconstructed map, with every explicit input supplied by
its proved producer in the source setting. The full canonical tuple image is now named
`interpretedRingEquiv_jTupleOf`; it needs no RAC. Compatibility and all-point recovery
use both genuine RAC bases. The actual-H lattice equality supplies every closed-field
image and, on chosen perfections, the original-field intersection formula for that H.
The original literal RatioEq/JMul proofs retain their provenance. All eleven numbered
validation checks have their precise Lean dispositions. Literal intended-coordinate
soundness and the prescribed-witness ratio reverse are proved; literal uniqueness/forward
defects retain their refutations and corrected replacements. The complete original and
supplementary source-disposition audit and true auxiliary statements stay open. The original three-pair additive
and literal multiplicative correspondence theorems are proved without extra ambient-rank
or freshness hypotheses, including both sum constants and both nonzero exponents/constants.
Connected one-dimensional additive subgroups of the plane now have the source polynomial
classification, with primality of the canonical vanishing ideal derived from connectedness.
Connected one-dimensional torus subgroups have the source character classification, with
nonzero integer exponents and the equation of every coset. Both subgroup theorems use one
shared connectedness-to-primality proof with concrete polynomial translations or scalings.
The original two-generic proof's embedded-field assertions are checked independently in
`Test.TwoGenericSource`, including the finite normal envelope and extension of embeddings
fixing the other rational field pointwise; the algebraicity conclusion uses exchange.
The original conjugate proof route is retained. Actual equal j-tuples now have a unique
normalized common Frobenius exponent over arbitrary bases and perfect ambient fields,
without a rank bound, supplied freshness or completeness. The literal integer uniqueness
is refuted in characteristic zero, where the pair is equal and every integer works; the
normalized exponent is zero. Original statements/proofs and both downstream proof
qualifications retain their provenance (#32). The additive finite-correspondence case of
curve-coset now constructs the actual closed subgroup, its prime principal ideal, connected
coordinate spectrum, dimension one, both nonconstant projections and all three ideal/point
cosets over ACF base and ambient fields, with no caller rank/freshness/completeness input.
The general curve-coset lemma is now proved for closed irreducible curves over an ACF base,
with an actual connected one-dimensional algebraic subgroup, a closed-immersion group morphism
and all three noncommutative cosets. The commutative clause gives three left cosets of the
same subgroup. The ambient group need not be connected. The existential jointly generic
scheme-product input only requires its product to lie in the third curve; product integrality
and all restricted group operations are derived. Abstract torus and constant-coordinate
cases are permitted once the ambient group is presented as an AlgebraicGroup. Concrete
Gaⁿ, Gm, Gm² and affine group schemes now have actual operations and point coordinates.
The affine group has dimension two and an ACF connected algebraic-group package. Its
standard affine scheme action satisfies the literal ax+b formula and is faithful over every
commutative coefficient algebra in the base universe. This constructs the (8.4a) target
model; the arbitrary-action classifier and all eight original #21 items remain open.
The actual scheme/function-field bridge now derives the one-variable class for the genuine
generic stalk of an integral locally finite-type curve of dimension one over arbitrary fields.
A regular scheme action gives a contravariant field-automorphism homomorphism on base-field
points, injective for a separated scheme under the explicit point-action kernel criterion.
Both results share one internally constructed base algebra. Actual regular actions now also
act on places and preserve the global-section subalgebra. An affine integral locally finite-type
curve of dimension one has a nonempty valuation-place boundary over any field; over an ACF base
it is finite. The finite generation and one-variable hypotheses are derived internally. Every
place of an actual such curve over an ACF base is a DVR, without needing affineness. Every
connected regular action on an affine curve now fixes each boundary place and supplies an actual
fixed place internally. Order closedness comes from the actual action through uniform finite tensor
sums and algebraic dual separation, in every characteristic. An actual integral locally finite-
type group of dimension at least two acting regularly and faithfully on an integral affine
locally finite-type dimension-one curve over an ACF base now internally supplies an actual
affine chart, its parameter fraction field, coefficient point-map faithfulness and rank, and
two independent regular curve variations from the same effective coefficients. Over an
internally chosen algebraically closed constant extension K, the canonical tensor fraction
field of the actual generic-stalk k(V) is a one-variable field of genus zero. Domains and all
rank, separating-parameter and regularity inputs are internal. Finite-coefficient localization
and specialization now descend rationality from any constant extension of an ACF base. The
actual regular-affine action has genus zero and a transcendental generator over the original
base on its actual generic-stalk field (`SchemeCurveGenus`), with both one-variable instances
and descent internal. For a connected algebraic-group package of dimension at least two,
`SchemeAffinePointAction` now chooses a transcendental coordinate and an injective homomorphism
from actual k-points into `AffineTransformation k`, with the literal field-pullback formula.
The fixed boundary place, genus and faithful field action are internal. The same coordinate
and global faithful point homomorphism now have rational coefficients on an internally chosen
actual affine group chart (`SchemeAffineParameters`). The chart fraction field is finite over
the two coefficients, which form a transcendence basis, with literal specialized and actual
generic-translate formulas. Inseparability is allowed. No chart, coefficient, specialization,
rank or finiteness certificate is a caller premise. `SchemeAffineMorphism` now constructs
an actual global regular group-scheme morphism to the standard affine group from these SAME
data, injective on k-points, with actual unit/multiplication identities. Its principal-open
model and translated-open gluing are internal. No regularity, extension or morphism
certificate is a premise; no scheme monomorphism is asserted. Inseparability is allowed.
The SAME global morphism now restricts, on internally chosen nonempty group and affine-group
opens, to an actual finite surjective scheme map (`SchemeAffineParameterCover`). Its square
commutes. No dominance, algebraicity or finite-cover certificate is a premise.
`SchemeAffineCurveDiagram` now spreads the SAME generator to a regular map on an actual
nonempty curve open with its literal generic-point value, and proves the actual joint
scheme action diagram with the SAME global group morphism on a nonempty open of G times V.
No coordinate, normality or intertwining certificate is supplied. `SchemeAffineCurveCover`
now restricts the GIVEN old coordinate to an isomorphism of nonempty curve and line opens,
finite/surjective onto its target open, with the joint action diagram for the SAME t and
group morphism on this restriction. All old data are retained; remaining source finite
covers and the full classifier remain owed. Every actual group-scheme automorphism of Gm
is now identity or inversion over any field. Over an ACF base, an actual normal multiplicative
subgroup of a connected algebraic group is central as a joint scheme identity, in every
characteristic (`MultiplicativeRigidity.normal_multiplicativeGroup_conj`). The exponent,
regular conjugation lift, separating point and constancy are internal. The actual normal-Ga case now constructs a regular group character G to Gm and proves the
joint scheme conjugation diagram of (8.4b), with only the actual group, inclusion and genuine
normality as inputs (`AdditiveRigidity.normal_additiveGroup_conj`). Actual field-base Ga
automorphisms are nonzero scalar maps. The parameter group is reduced; every characteristic
is covered. Coefficient, regularity, global invertibility and character laws are internal.
Arbitrary one-dimensional normal-subgroup/isogeny classification remains owed.
Non-affine and rational-action cases, completion/points identification, the normal subgroup
and arbitrary-action classification remain open.
The tuple-locus-to-scheme-curves and jointly generic product bridge remains separate.
The earlier additive theorem has its own coordinate interface. Original group extraction and scheme/action/descent remain owed.
Read PROJECT_GOAL.md for the unchanged full endpoint and current source obligations. The historical M4a
items 1–117 remain frozen.

The precise group configuration theorem, arbitrary-small-ACF base change,
parameter descent and interalgebraicity part of the Ψ application are proved.
The actual canonical-code constructible group, stabilizer and homogeneous-space
presentations are now assembled after internally chosen two-stage generic
sampling. The full Ψ constructibility corollary constructs these data from the
actual witness, with original-base freshness and final-base rank/orbit statements.
The combined general configuration conclusion (`thm:main-informal`) now composes
the precise main theorem and canonical presentation on the same actual objects.
Its final-base rank is the rank of the input over the original base. The Ψ
constructibility corollary specializes it with its public statement unchanged.
The finite supporting audit #29 is complete; it is not a whole-source audit.
The preceding model-completeness checkpoint is a68edb2; its full local
library/book gates and peer review are recorded on #12. Exact-head CI, artifact
and existing-deployment reports are kept on the issues. The earlier actual
rank-one HW rationality checkpoint 9b2aeb8 passed exact CI38783156757, with
artifact11997275903 and existing deployment7100727066 successful at 18:18:06 UTC.
The canonical-base line example, necessity of the configuration clauses from
the actual main conclusion, and the finite-ambient representative-collapse
warning now have public proofs. Base-algebraic-closure invariance now has an
actual closed-field order isomorphism preserving carriers, points and ranks.
The affine-line proof is shared over arbitrary coefficient fields while all
five original public example statements are retained. The full translation example
now constructs actual germs and HW structure, identifies the homogeneous space
with K, and computes its pair relation, generic-point image and total action.
The zero class has no independent presentation. The full nonfaithful product-group
example now proves the literal action, all Ψ (i)–(iii) clauses, the source atom
violating (iv), and the obstruction to the precise main conclusion over any
finite independent extension. The actual five-copy construction now retains
the three-plus-two generic-copy ranks and proves rank(E)=5*rank(a) over
the original base, together with the actual main conclusion. All six old
public statements and docstrings remain unchanged projections. The
universal-domain hypothesis and remaining auxiliary obligations are retained.
Every member of the actual HW two-product group on a rank-one locus now has
an equal representative of exponent zero, in both characteristics. Its
Frobenius index is intrinsic and additive under arbitrary composition; only
the HW orbit argument uses independence. Its actual locus fraction field is
now proved to be a one-variable function field over K. The actual HW group
acts faithfully by K-algebra automorphisms, with the coordinate formula for
every rational representative of the inverse. Genus and Möbius classification are proved, as is the actual rank-two affine generator.
The original scheme/action bridge and normal-subgroup producer remain open.
The degree-only constructibility usage claim is refuted on #31 alongside
the fixed-formula source correction. Model completeness of algebraically closed
fields now constructs an actual Mathlib elementary embedding for each prescribed
field embedding and preserves every finite-arity first-order ring formula.
The proof fixes the existing parameters in its Tarski–Vaught fibre; no
universal-domain or rank hypothesis is used. Finite polynomial witness descent and independence recovery now supply the actual guarded
chart over the original ACF ambient in `Config.GuardedAffineGrid`. The original
scheme/action descent remains open. The current integration's source and
validation details are recorded at the end of this guide and on #12, #21 and #31. Full
library/book gates are required before every commit.

## Audit baseline (2026-10-07; #19, performance #18 and carryovers #24)

This section records the historical #19 audit baseline. Its bullet-point boundaries
retain that checkpoint's scope; later proofs supersede the old open-status descriptions.
Read the current status above and the coverage overview and priorities below for the
present frontier. The original diagnoses and checkpoint evidence are kept for provenance.

- **No `sorry`, `admit` or project `axiom` in the sources.** The latest CI run
  at the start of the audit was on `ee31244` (run 31712093484), cancelled after about six hours (job
  time 6h 0m 16s), and the latest
  successful run at that point was for the older `7f572e4`. Historical
  "CI green" reports are therefore not current evidence. The v4.34.1 upgrade `8a54b54` (#20) supplies fresh local
  full-build/book, hygiene and compiled-axiom evidence. Its full Lean Action CI
  run [37575646876](https://github.com/adamtopaz/acl_geom/actions/runs/37575646876)
  subsequently passed. The audit head `f6964f0` also passed the full build/book
  and deployment in run
  [37580135219](https://github.com/adamtopaz/acl_geom/actions/runs/37580135219),
  completed on 2026-10-07 at 07:16 UTC. The focused-module code checkpoint
  `31864cd` also passed full CI in run
  [37591789192](https://github.com/adamtopaz/acl_geom/actions/runs/37591789192),
  completed at 08:27 UTC. These are current CI evidence; the separate release
  workflow is not a full build.
  The later documentation-only head `842976b` also has a cancelled CI run
  (37533928699, completed 2026-10-07 03:27:14 UTC after 6h 0m 30s);
  deployment was skipped. It is not successful-build evidence.
  Build latency and memory are tracked in #18. The focused core/leaf and
  configuration-book refactor is recorded below; it preserves the audited
  mathematical targets. Paired project-clean measurements now pass, and the
  #18 acceptance evidence is recorded below.
- **The old M4 completeness target was false.** `AffineGridExtraction`
  required equality with the table witness in all 21 fields, but `Psi` sees
  the generators `A₁, A₂` (likewise `B`, `C`) only through their joins.
  Exchanging `A₁` and `A₂` preserves `Psi`, so the conditional
  `QGeom ↔ QSem` held only vacuously. Blueprint table (8.5) has the same
  imprecision. This checkpoint retains the literal-target refutation and
  corrects the interface to three joins and fifteen points (#22). The ACF
  unguarded extraction and Q completeness were subsequently refuted even over ACF pairs
  (#27); the corrected candidate requires I≠D and I≠P and remains open.
- **The M4a group-chunk chain (historical items 1–117 below) is frozen.** It
  did not converge toward a blueprint statement: no `Config/Chunk*` module is
  upstream of `AffineGrid`, `Correctness` or `Main`, and several headline
  "composition" theorems hold by construction (#19, finding A2). M4 is being
  re-planned against the corrected target (#12, #21, #22).
- **The arbitrary-field Q/Q′ consequences are false.** In the rank-five
  extension ℚ(s,t,e₁,e₂,e₃), geometric Q and Q′ can hold without K-valued
  semantic representatives. Both mathematical counterexamples were independently
  checked; both are now refuted in Lean over every characteristic-zero
  rational function field in five variables (#25), with explicit geometric
  witness reflection and a semantic square obstruction. The four-way J target is
  separate. The source withdraws the invalid projection consequence.
- **The Frobenius-class, generic-arithmetic and ratio sections need a correction.** `SumPoint` and `MulPoint` allow
  independent changes of representatives. The literal JAdd/JMul definitions
  are nonfunctional even over algebraically closed fields: they accept
  j(κx+y,a) and j(κxy,a) for κ ∈ k×, κ ≠ 1. This refutes the original
  generic-arithmetic equivalences (#23), rather than only exposing a proof gap.
  The FrobEq converse reuses one multiplier representative across three
  existential clauses without proving that choice. EH95's route supplies a
  partial-quadrangle coupling by specialization. Concurrence has an independently
  checked Lean proof in `Interpretation/FrobLinkIncidence` (five public
  declarations, standard axioms); an algebraic converse from this concurrence
  now yields exact parameter twists from supplied semantic endpoint witnesses,
  over arbitrary base fields. The two-link implication keeps semantic bridge
  completeness explicit; its canonical form uses perfect K, rank at least
  five and the still-open ACF JCompletenessACF input. The original
  common-representative calculation and unconditional bridge completeness
  remain obligations. The natural/integral FrobEq semantic equivalences and
  fixed-class description are proved under explicit perfection, rank-five and
  ACF J-completeness inputs, over any base field. The coordinate bijection
  is proved under the same explicit inputs. Corrected generic fixed-class
  arithmetic and corrected geometric ratio semantics are proved under these
  inputs. The corrected geometric ratio setoid/quotient and bijective nonzero
  decoding are proved under the same inputs. Adjoining zero yields the full
  carrier decoding equivalence. The corrected two-addition negation detour
  and corrected total nonzero addition are proved under the same inputs.
  Corrected total geometric graphs on the full ratio carrier are proved
  under the same inputs. The named transported field structure, actual decoding ring
  equivalence and geometric graph/operation characterizations are proved under the same
  inputs. Pure geometric Q/Q′/J configuration and J-locus/Frobenius-link/bridge
  transport, coupled meet/join arithmetic and corrected total/ratio transport are
  proved across arbitrary bases/universes, with no completeness or perfection input.
  Conditional class/carrier maps and graph transport are proved given the
  canonical image-base equality and explicit carrier inputs. The same geometric
  map is bundled as an actual RingEquiv and composed with both decodings.
  Canonical image-base existence and conditional field-isomorphism existence are
  also proved under explicit ACF completeness; general inducing reconstruction
  remains open (#23).
  The JAdd, JMul and full-class RatioEq refutations have an
  independently checked Lean proof in `Counterexamples/GenericArithmetic`;
  all 26 public declarations use standard axioms. They record the literal
  predicates for provenance and explicitly prove membership of every witness
  in the encoded class relation.
  EH95 Lemma 2.11 and Figures 4–5 use meets of joins of the given coordinates
  for subtraction/division, preserving the coupling lost in the blueprint's
  existential projections. `Interpretation/JArith` and `JArithSem` now prove
  the generic meet identities, Point-valued JSem bridge and derived generic
  negation/inverse/addition/multiplication over arbitrary relative fields.
  All 89 authored public declarations have standard-axiom checks. Inputs
  share a literal parameter and are independent. Geometric membership
  follows from rank-five soundness without an infinite-base binder.
  Generic fixed-class correctness and corrected ratio semantics are proved
  under explicit completeness, as is bijective nonzero quotient decoding.
  Corrected negation and nonzero addition detours and full-carrier geometric graphs
  are proved under the same inputs, with a named reducible field structure and
  actual decoding RingEquiv. Conditional carrier/graph transport is proved
  with the canonical image-base equality and carrier inputs explicit; its
  induced RingEquiv and composition with both decodings are proved.
  The canonical image base and conditional field-isomorphism endpoint are proved
  under explicit ACF completeness. Public original-field existence and the assembled lattice-form target are proved
  conditionally with both exact perfected completeness inputs explicit (#9/#10).
- **The base-ratio corollary prerequisite is complete (#5/#9, R1a/C7b).**
  `Reconstruct/Base` proves ratio algebraicity over arbitrary relative fields
  with no rank, fresh-witness, perfection, completeness or characteristic
  input. Adjoining a rational-function variable supplies freshness. The
  original ratio-in-base orientation is proved with explicit `IsRAC` for the
  base. Actual corrected conditional base recovery and Compatible assembly
  for `interpretedRingEquiv` are proved under explicit carrier/completeness
  and both RAC inputs. Corrected conditional scalar one and outside-point
  recovery for the same map are proved without RAC under its explicit
  carrier/completeness inputs. Actual inducing equality and compatible
  inducing existence for perfect fields are proved with RAC/completeness
  explicit. Original-field inducing existence through arbitrary chosen perfections
  is proved with original RAC and both perfected completeness inputs explicit.
  The public conditional target is assembled in Main. General unconditional R1/R2
  and full reconstruction remain open. The original
  source proof’s incorrect correspondence-pair ordering is reported on #5
  and preserved; the corrected formal proof uses `(u₁,u₂)` and `(b,b)`.
- **Lemma 8.4 (affine action) has no Lean statement.** #13's curve
  prerequisites are proved: places, divisors, Riemann–Roch, genus, rationality
  in genus 0, Tate residues, rigidity of regular derivations in genus ≥ 1, and
  Möbius normalization. #13's final step (P7, assembling Lemma 8.4) is absent,
  and so are the group-action model and the bridge from actions to the curve
  library (#21). No module outside `Curves`/`Tate` uses the curve library
  yet.

Current coverage overview (precise hypotheses and source obligations are in PROJECT_GOAL.md):

| Layer | Proved scope and remaining obligations |
|---|---|
| Foundations, perfection | Closure lattices, points, rank/independence transport, all-characteristic perfections and chosen-perfection naturality are proved. The public reconstruction target has the genuine RAC/source-rank-five hypotheses and supplies both ACF completeness proofs internally. Point reconstruction, automorphism variants, literal functor laws/exact fibres, the rank-five fully faithful Frobenius quotient and perfection-choice equivalence are proved. |
| Configurations | Q/Q′/J soundness, geometric transport and semantic J assembly are proved in their stated scopes. The guarded affine-grid chart and Q completeness are proved for every ACF pair, keeping both guards explicit. The multiplication converse gives rank-five ACF Q′ and J completeness. Unguarded Q and arbitrary-field Q/Q′ correctness have proved refutations (#25/#27); general existential-witness descent and the remaining original group/chunk/action obligations stay open. |
| Hard kernel | The source three-pair additive and literal multiplicative correspondence theorems, simultaneous-coset classification, j-rigidity and both connected additive/torus subgroup classifications are proved. Generic-point field freeness and numerical field degrees are proved; field-theoretic tensor components realize composite germs in an ACF ambient over an arbitrary base. The general curve-coset statement is proved with an actual connected closed algebraic subgroup. Original group/chunk/six-point and scheme/action statements remain open (#5/#12/#21); later dated checkpoints record the proved geometric and generic-extension bridges. |
| Transfer | T1–T3, point/configuration lifts and their explicit-instance reflections are proved. Four-way J descent and geometric/semantic J correctness hold over perfect ambient fields at rank five, with no RAC or infinite-base hypothesis. General existential-witness descent remains a separate obligation (#7/#25). |
| Interpretation, reconstruction, functorial | Corrected coupled interpretation semantics and the generic internal APIs under explicit carrier/completeness inputs are proved. The public reconstruction theorem discharges those completeness inputs internally. Frobenius kernel/uniqueness, public variants and perfection-choice equivalence are proved. The original two-generic embedded-field assertions have separate source validation, including the normal envelope and extension fixing the other rational field. Literal full-carrier TOT/ratio and original general interpretation/provenance obligations remain open (#8/#9/#23). |

Current priorities:

1. Advance the remaining original and supplementary source mathematics, including the
   coordinate-ring/localization bridge to geometric fiber products, packaged generic extension,
   group/chunk/six-point and original scheme/action statements (#5/#12/#21).
2. Complete the source validation/disposition ledger and the literal interpretation/provenance
   work (#8–#10/#23), retaining every refutation and justified correction (#22/#25/#27/#31).
   True bypassed source statements remain obligations; the frozen M4a history is not a new
   deliverables list.
3. Keep general witness descent and definability-in-families requirements distinct from the
   proved guarded chart, rank-five J correctness and public reconstruction. Public theorems
   supply completeness internally; reusable internal APIs may retain explicit parameters.
4. Validate every checkpoint with the full library and rendered book, strict checks and
   appropriately scoped dependency/source evidence; commit, push and verify exact-head CI.

## How work is coordinated

- **All communication with Adam happens on GitHub issues** of
  `adamtopaz/acl_geom`, and only there. Nothing else on Adam's GitHub
  account may be changed. Check for new comments from Adam at the start of
  every work session and treat them as top priority. Questions for Adam use
  the `question-for-adam` label.
- Two agents work on the project: `aclgeom.claude` and `aclgeom.codex`.
  They coordinate through chit direct messages. File ownership is divided
  explicitly before editing. In the shared checkout only one Lean/Lake build
  family runs at a time, with combined memory capped at 20 GB
  (20,000,000,000 bytes), following Adam's
  [updated instruction on #28](https://github.com/adamtopaz/acl_geom/issues/28#issuecomment-6174030382).
  This replaces the former 30 GiB available-memory stop. Older measurements
  below retain the rule in force when they were taken.
- Issue map: #1 coordination; #2–#10 milestones M0–M8; #11 M3a regularity
  brick (open, off the critical path); #12 M4a design; #13 M4b curve
  library; #14–#16 historical M4a sub-steps; #18 build performance;
  #19 audit; #20 upgrade (closed, 8a54b54); #21 Lemma 8.4 action bridge; #22 extraction
  target repair; #23 representative alignment and refuted generic arithmetic
  in §10–12; #24 foundational carryovers from #3/#4; #25 false arbitrary-field
  Q/Q′ consequences; #26 source-paper request fulfilled (PDFs outside git).
- Issue comments are posted through Adam's `gh` account. Do not append
  signature lines. When it matters which agent did the work, say so in the
  body.
- Post a progress comment on the relevant issue after each substantive push.
- Blueprint statements that the Lean route bypasses (for example the
  three-pair additive correspondence or general `E ⊗ F` regularity) remain
  tracked obligations; do not close them merely because nothing uses them.

## Hard policies

`AGENTS.md` is authoritative. In particular:

- **Never leave `sorry` or `admit` on `main`**, including WIP files.
- **Never axiomatize blueprint theorems.** Every Lean declaration must be
  kernel checked; explicitly named unproved hypotheses remain obligations.
- Use focused `lake build <module>` checks during development; never trust
  `lake env lean` alone. Run a full `lake build` before every commit.
- Keep `lake exe book` building; grow the book alongside the code.
- Never `cd` into `.lake/packages/*` — lake builds whatever package
  the cwd is in.
- Commit and push at every natural checkpoint, in small verifiable
  increments, always green (Adam's standing instruction).

## State of the library (descriptive; see #19 for the audited coverage)

### Foundations (earlier milestones)
- M0 skeleton/CI done. M1–M2: the lattice, atoms, point geometry and
  perfection isomorphism are proved. The carryovers from closed #3/#4 are
  proved for compatible cross-base transport, point/lattice round trips,
  independence/rank/trdeg transport, all-characteristic perfection existence
  and chosen-perfection naturality. The explicit `Induces` relation,
  intersection formula and compatible induced-map converse are also proved
  (#24). Full reconstruction and functorial constructions remain open
  (#8–#10). The finite
  representative calculus (Lemma 4.2) is proved in `Geometry/Representatives`;
  it is used by the arithmetic refutations. M3: `j_rigidity` and the
  correspondence theorems are proved (two-pair additive form; the general
  `E ⊗ F` regularity of #11 is open). M4: soundness and semantic J assembly
  are proved; geometric completeness remains open (#6).
  The curve theory below is M4b (#13), built as the input to blueprint
  Lemma 8.4. The lemma itself and the bridge from group actions to the
  curve library are not formalized yet (#21).

### Curve theory (`AclGeom/Curves/`, Stichtenoth-style, no schemes;
### base field algebraically closed, all places degree one)
- `Places.lean` — places are DVRs (Stichtenoth 1.1.6, self-contained).
- `Divisors.lean` — ord calculus, divisors, `deg div f = 0` support.
- `Residues.lean`, `DegreeBound.lean` — residue fields, pole-degree =
  `[F : k(f)]` (1.4.11).
- `RiemannRoch.lean` — `L(D)`, one-point decomposition, `ℓ ≤ deg + 1`.
- `Genus.lean` — defect, genus, Riemann's inequality.
- `Rational.lean` — genus 0 ⟺ rational (`genus_eq_zero_iff_exists_generator`).
- `Adeles.lean` — adele space, monomials, one-point steps, stabilized
  Riemann, 1.5.8 (`adeleSubmodule_eq_sup_of_defect_eq_genus`).
- `Specialty.lean` — index of specialty, full Riemann–Roch
  `ℓ(D) = deg D + 1 − g + i(D)`.
- `Differentials.lean` — Weil differentials, levels, proportionality
  (dim_F Ω = 1), max level exists.
- `Canonical.lean` — duality `i(D) = ℓ(W−D)`, canonical divisor with
  `deg W = 2g−2`, `ℓ(W) = g`.

### Tate residue theory
- `Tate/FinitePotent.lean` — finite-potent operators, cores, the Tate
  trace, squared-range trace calculus (symmetry, additivity,
  finite-sum additivity, traceless commutators), commensurability
  (`AlmostLE`), trace class, the abstract projection-comparison
  theorem (`tateTrace_commutator_eq_of_projection`), compatible
  projection pairs (`exists_projection_pair`), abstract trace-class
  certificates (`isTraceClass_commutator_of_comm`).
- `Curves/TateResidue.lean` — valuation-ring filtration and
  commensurability; the residue
  `P.residue f g := tateTrace [ε∘m_f, m_g]` (morally `res_P(f dg)`)
  with: trace-class certificate; **bilinearity** (`residue_add_left/
  right`, `residue_smul_left/right`, `residue_zero_left/right`);
  **R2** (`residue_eq_zero_of_mem`: vanishing for integral pairs);
  **ord-link** (`residue_inv_self : res(g⁻¹dg) = ord g` for
  `ord g ≥ 0`); **threshold** (`residue_eq_zero_of_ord_ge`:
  `res(f dg) = 0` for `ord f ≥ m+1`, `ord g ≥ −m`, char-free
  nilpotency proof); **projection independence** (`residue_eq_of_
  projection`, and `residue_eq_of_projection_filtration` for
  filtration stages); **Leibniz** (`residue_mul_right`:
  `res(x d(gh)) = res(xg dh) + res(xh dg)`); the principal-part
  decomposition (`isCompl_principalSpan`) and the **monomial table**:
  `residue_zpow_pi_base` (`res(π^c dπ) = 0`, `c ≤ −2`),
  `residue_one_right`, `residue_zpow_pi_self`
  (`res(π^{−b}d(π^b)) = b`), `residue_zpow_flip`,
  `residue_zpow_pi_zpow_eq_zero` (`res(π^a d(π^b)) = 0` for
  `a+b ≠ 0`).
- `Curves/GlobalResidue.lean` — bounded adele spaces inside the adele
  module are pairwise commensurable; adelic multiplication
  almost-stabilizes them; global trace-class; the diagonal;
  **`tateTrace_adeleSMul_commutator_eq_zero`** (global trace
  vanishes, via the triple decomposition from 1.5.8);
  the componentwise projection (`adeleProj`) acting blockwise;
  single-place inclusions (`adeleSingle`); block operators with
  vanishing cross-products; **`tateTrace_adeleProj_commutator`**
  (localization: global trace = Σ local traces); **the residue
  theorem `sum_residue_eq_zero` : `Σ_{P∈S} res_P(f dg) = 0`** for any
  finite S outside which f, g are integral; the residue functional
  `residueFunctional g : Dual k 𝔸` (`ω_g`), which kills the diagonal
  and the bounded space at level `−2·poleDivisor(g)`
  (`residueFunctional_mem_weilDifferentialsAt`) and is **nonzero at
  uniformizers** (`residueFunctional_pi_ne_zero`, value 1 on the
  single-place adele `π⁻¹`).

## Historical log: M4a finite-cover field action (items 1–117; frozen)

The numbered historical items are preserved as a record. They are **not** the
current plan. The
2026-10-06 audit (#19) found that the chain was aimed at a false target (#22)
and was not converging. Several statements described below as
"strict composition" or "cancellation" hold by construction. Re-check any
item before relying on it.

The P6 prerequisites are proved in the library: regular-derivation
rigidity, infinitesimal automorphisms, genus-zero rationality,
rational-function-field automorphisms, and Möbius normalization. P7, the
assembly of Lemma 8.4 from them, has not been done. Only the abstract
`kˣ ⋉ k` bookkeeping of the affine-action endgame exists (#21).

The current boundary is blueprint Theorem 8.2 applied to equation (8.6):

1. The rank-two `A/B/C` parameter multiplication and the rank-one
   `S/T/U` quotient are genuine presented groupoids; the induced vertex
   homomorphism has a normal categorical kernel with the expected rank-one
   fiber count.
2. Every joint parameter edge is a finite cover.  Its conjugate branches
   and deck group are normalized against one reference edge with strict
   cocycle laws, and the full finite branch/deck bundles are globally
   trivialized without collapsing their positive-dimensional base.
3. `AlgebraicClosureTransport.lean` now gives each selected finite
   correspondence a semilinear equivalence between the algebraic closures
   of its source and target curve fields.  Independent lifts are not
   declared coherent: their composition discrepancy is an explicit deck
   automorphism fixing the target curve field.
4. `Config/ChunkFieldAction.lean` instantiates this for Ψ.  Over the field
   generated by the two independent rank-two parameters, the selected
   `A` transport sends `X` to `Y`, the `B` transport sends `Y` to `Z`, and
   strict composition followed by the vertical deck defect is exactly the
   selected `C` transport.  This is the field-action form of (8.6).
5. `FiniteNormalTransport.lean` proves that semilinear algebraic-closure
   transport preserves finite normal subcovers and that every vertical
   base-fixing automorphism stabilizes such a cover.  The corrected ambient
   composition law therefore restricts exactly.
6. `Config/ChunkFiniteFieldAction.lean` chooses the Ψ source cover as the
   finite normal compositum of the selected `A` branch cover, the pullback
   of the selected `B` branch cover, and the selected composite `C` branch
   cover.  Its middle and target transports contain all three branches,
   and the deck-corrected `A · B = C` equality now holds on these
   finite-dimensional normal fields.
7. `Correspondence/AlgebraicGroup.lean` fixes the honest target of the
   algebraization step: separated finite-type group schemes over the base
   field, with the connected version geometrically integral.  It constructs
   scheme-theoretic kernels in the internal group category, proves that the
   kernel is a closed finite-type separated subgroup scheme, and proves its
   inclusion normal by identifying the kernel square with pullback along the
   unit section.
8. `Correspondence/WeilGluing.lean` begins the actual scheme-gluing layer.
   Compatible maps on open charts descend to Mathlib's explicit glued
   scheme; local finite type descends from all charts; a finite atlas of
   quasi-compact chart maps is quasi-compact; and integral charts with
   nonempty pairwise overlaps glue to an integral scheme.  These discharge
   the abstract descent and irreducibility consequences needed once the
   normalized chunk supplies its concrete transition charts.
9. `Correspondence/FiniteExtensionChart.lean` turns a finite extension of a
   finitely generated parameter field into an integral separated affine
   scheme of finite type over the ground field, with the prescribed extension
   as its fraction field.  `Config/ChunkAlgebraicChart.lean` applies this
   construction to the normalized `A/S`, `B/T`, and `C/U` scalar covers.  The
   two displayed parameter coordinates still generate their base fields and
   are algebraically independent, so these are genuine rank-two scheme charts
   rather than finite deck groups.
10. `Correspondence/BirationalGluing.lean` converts mutually inverse dominant
    partial maps into an isomorphism between explicit dense open subschemes.
    Its rational-map form applies this to inverse dominant rational maps
    between integral separated schemes.  Together with the direct
    `IsFractionRing` realization of every finite-extension chart inside its
    selected ambient cover field, this supplies the generic birational-to-open
    bridge needed by the normalized transition maps.
11. `Correspondence/PrincipalLocalization.lean` clears the finitely many
    denominators of an injective map from a finitely generated algebra to a
    fraction field.  Their nonzero product gives one explicit dense principal
    open `D(d)` and a dominant partial map from it.  The wrapper in
    `Correspondence/FiniteExtensionTransition.lean` applies this construction
    contravariantly to any field equivalence between two finite-extension
    charts.  `Config/ChunkAlgebraicTransition.lean` upgrades the normalized
    scalar-cover equivalence to a ground-field equivalence and instantiates
    the construction at all four repeated blocks `s`, `u`, `sA`, and `uB` of
    a lifted Ψ four-arrow diagram.  Thus every branch comparison used by the
    chunk now has a concrete dominant principal-open representative.
12. `Correspondence/FunctionFieldEquivalence.lean` proves the generic-point
    composition law for dominant partial and rational maps, recovers the
    induced field homomorphism, and proves that a function-field equivalence
    and its inverse give mutually inverse dominant rational maps.  Every
    finite-extension chart now carries its canonical ground-field function
    field, identified with the selected ambient cover field.
    `Correspondence/FiniteExtensionTransition.lean` conjugates an ambient
    equivalence through those identifications, spreads the resulting map over
    `Spec k`, proves both rational composites are identities, and extracts an
    explicit isomorphism between dense open chart subschemes via
    `BirationalGluing`.  `Config/ChunkAlgebraicTransition.lean` instantiates
    this dense-open isomorphism on all four normalized `s`, `u`, `sA`, and
    `uB` branch comparisons, alongside their principal-open representatives.
13. The generic-point lift through a principal open is now identified with
    the canonical localization map into the source function field.
    Consequently, the denominator-cleared finite-extension partial map is
    proved to induce exactly the conjugated ambient field equivalence, and
    its rational-map class is the canonical rational transition used by the
    dense-open isomorphism extractor.  Thus the explicit principal-open and
    function-field descriptions of every normalized transition agree.
14. Reference-normalized scalar-cover equivalences are now defined by going
    through one fixed branch.  They satisfy identity, symmetry, and strict
    transitive cocycle laws.  Conjugated finite-extension chart rational maps
    preserve transitive composition, so the normalized dense rational
    transitions inherit the strict cocycle.  Independently,
    `BirationalGluing.partialIsoGlueData` packages any dense-open partial
    isomorphism as an actual two-chart `Scheme.GlueData`; all four repeated
    blocks `s`, `u`, `sA`, and `uB` expose such normalized gluing data.
15. `WeilGluing.commonOverlapGlueData` packages an arbitrary family of open
    immersions from one fixed overlap as full scheme gluing data with literal
    identity triple cocycles.  `BirationalGluing.partialIsoFamilyGlueData`
    applies this to a finite family of partial isomorphisms from one reference
    chart: their finitely many dense source opens are intersected once, every
    partial isomorphism is restricted to that common dense source, and all
    target charts are glued simultaneously.  The reference-normalized scalar
    transitions instantiate this as `rankTwoScalarReferenceAtlasGlueData` for
    an arbitrary finite branch family on one rank-two locus, with
    `rankTwoScalarReferenceAtlas` the resulting actual scheme.  The extracted
    dense-open transitions are now proved to commute with their chart
    structure maps to `Spec k`; those maps descend to
    `rankTwoScalarReferenceAtlasToSpec`.  The full atlas is integral (for a
    nonempty branch family), locally of finite type, and quasi-compact, so the
    finite-type and irreducibility parts of the Weil construction are now
    discharged.  Separatedness remains tied to the group law rather than to
    the common-open gluing alone.
16. `GroupScheme.diagonal_isPullback_unit` identifies the diagonal of any
    group scheme over `k` as the pullback of its closed unit section along the
    difference morphism.  Hence every group scheme over the field is
    separated, and `AlgebraicGroup.ofGroupScheme` packages a locally
    finite-type, quasi-compact group scheme without a separate separatedness
    proof.  The existing finite reference-normalized scalar atlas should now
    be understood precisely as the branch-normalization input to Weil's
    theorem, not as the translation-indexed group atlas itself.
17. Equality of full rank-two/scalar graph loci now restricts to equality of
    their rank-two parameter loci.  The induced equivalences of the two base
    function fields and scalar extensions lift semilinearly to the normal
    covers, even when the displayed generic rank-two tuples are different.
    Normalizing these equivalences through one selected realization gives
    strict identity, inverse, and transitive laws, dominant rational chart
    comparisons, and dense-open isomorphisms over `Spec k`.  For the actual
    Ψ cancellation family, `psiBProjectionReferenceRationalMap` specializes
    this construction to arbitrary generic realizations of the `B/T` graph,
    all represented by one fixed positive-dimensional affine normal-cover
    model.  This is the model-comparison prerequisite for spreading the
    four-arrow difference product; it does not yet construct that product.
18. `Correspondence/CurveEquation.lean` removes the remaining scalar
    ambiguity from an irreducible finite-correspondence germ.  Its prime
    planar ideal now has a canonical lexicographically monic generator,
    proved to depend only on the ideal.  The coefficients generate an
    intrinsic intermediate field contained in every chosen field of
    definition, and the canonical equation descends nontrivially to that
    field while still vanishing on the selected generic endpoint pair.  This
    supplies faithful, scaling-independent coordinates for the next
    multiplication-graph normalization; arbitrary unnormalized generators
    cannot be used because rescaling them would change their coefficient
    fields.
19. The descended canonical equation now proves that the target is
    algebraic over the intrinsic coefficient field and the source.
    `RankEq.eq_of_le_of_not_le_point` supplies the corresponding rank-two
    lattice principle: a closed subfield of a rank-two flat which is not
    contained in any point is the whole flat.  Applying the Ψ minimality
    clauses in `Config/ChunkGermCoordinates.lean` shows that the canonical
    coefficient closures of the inverse-oriented `A` germ, the `B` germ,
    and the output `C` germ are exactly `A`, `B`, and `C`.  Thus the germ
    coefficients are faithful rank-two coordinates up to finite algebraic
    extension, rather than merely fields contained in the displayed
    parameter fields.
20. `finiteDimensional_extendScalars_adjoin_of_close_eq` turns equality of
    relative closures into the required finiteness statement for any
    finitely displayed parameter tuple.  Consequently the selected displayed
    `A`, `B`, and `C` parameter fields are finite over their intrinsic germ
    coefficient fields.  The compositum of the inverse-`A` and forward-`B`
    coefficient fields has relative closure exactly `A ⊔ B`; the entire
    displayed `A,B,C` multiplication component is finite over this intrinsic
    independent-input field.  `germMultiplicationNormalCover` is its one
    common normal closure in the ambient algebraically closed field, proved
    finite and normal over the intrinsic two-input base.
21. The canonical coefficient set is now proved finite, and its tautological
    lifts generate the whole intrinsic coefficient field.  The inverse-`A`
    and forward-`B` families combine to a finite coordinate family for their
    intrinsic compositum.  `FiniteExtensionProjection` spreads any embedding
    of finite-extension function fields to an explicit dominant
    principal-open rational map.  Applying it in
    `Config/ChunkGermChart.lean` produces honest integral affine charts for
    the selected intrinsic `A`, `B`, and `C` germs and for the common normal
    multiplication graph, together with dominant rational projections from
    that graph to all three parameter charts.
22. `Correspondence/FourArrowNormalization.lean` normalizes the complete
    four-arrow difference component over its actual eight free coordinates.
    The four multiplication/division edges prove successively that the
    selected blocks `u`, `sA`, `uB`, and `c` are algebraic over the input
    tuple `(s,e,a,b)`.  Hence the sixteen-coordinate total field is finite
    over the eight-coordinate input field and lies in one finite normal
    cover.  `FourArrowDifferenceDiagram.algebraicChart` realizes that cover
    as an integral affine chart, with dominant rational projections to the
    displayed `e`, inverse-`a`, `b`, and output-`c` rank-two block charts.
    This is the normalized relational difference-product component; it does
    not assert single-valuedness after forgetting the auxiliary `s` block.
23. The chosen sixteen-coordinate prime component now spreads over every
    independent eight-coordinate input tuple.  `exists_relocation` relocates
    all sixteen coordinates at once while fixing `(s,e,a,b)` literally; the
    four six-coordinate restrictions remain realizations of the original
    multiplication locus, and the full prime ideal is preserved.  Equal
    complete loci canonically identify their input fields and total fields,
    these equivalences commute as a finite-extension square, and they lift
    semilinearly to the concrete normal covers.  After upgrading to
    ground-field algebra equivalences, the affine charts have dominant
    rational comparisons and dense-open isomorphisms.  Normalizing all such
    comparisons through one reference component gives literal identity,
    inverse, and transitive laws on the cover equivalences and a strict
    transitive cocycle on the rational chart comparisons.  Thus the selected
    branch is now a genuine generically spread component, not one isolated
    tuple.
24. `Config/ChunkFourArrowNormalization.lean` retains the complete scalar
    information on that component.  Its twenty-eight-coordinate tuple is
    the sixteen ambient coordinates followed by the three independently
    selected scalar branches on each of the four edges.  Restriction to each
    nine-coordinate edge is literally the selected complete joint
    rank-two/scalar projection locus.  All twelve scalar coordinates are
    algebraic over their displayed rank-two blocks, hence all twenty-eight
    coordinates are algebraic over the same eight independent ambient
    inputs.  Their field is finite over that input field and lies in one
    finite normal cover with an integral affine chart.  The four displayed
    `e`, inverse-`a`, `b`, and output-`c` `B/T` branch fields embed in this
    cover, producing dominant rational projections to their raw finite
    scalar-branch charts.  The targets are intentionally not yet their
    individual normal closures, so this step records all finite branch data
    without claiming a comparison with the selected reference model.
25. `Correspondence/FiniteExtensionCompositum.lean` gives the required
    finite-basis base-change lemma: if `F ≤ E` and `N/F` is finite, adjoining
    the values of a finite `F`-basis of `N` to `E` contains all of `N` and is
    finite over `E`.  `Config/ChunkFourArrowReference.lean` iterates this
    construction for the `e`, inverse-`a`, `b`, and output-`c` `B/T` normal
    fields.  The resulting common field is still finite over the original
    eight inputs and literally contains every individual normal field.  One
    final normal closure gives an integral affine source chart with dominant
    rational projections `toNormalizedE/A/B/C`.  Composing each with
    `psiBProjectionReferenceRationalMap` yields four dominant maps
    `toReferenceE/A/B/C` to the exact same selected `(B,T)` affine normal
    model.  Thus the reference-model comparison requested after item 24 is
    now concrete; equality of the output map with the categorical
    difference product of the three input maps remains to be proved.
26. `Correspondence/FunctionFieldEquivalence.lean` now treats arbitrary
    embeddings, not only equivalences: it constructs their generic-point
    morphisms, recovers the embedding from any dominant representative, and
    proves that successive rational maps induce the literal contravariant
    composite.  `Correspondence/FiniteExtensionProjection.lean` identifies
    the denominator-cleared projection with the embedding obtained by
    conjugating its ambient field inclusion through the two canonical chart
    function-field identifications.  The scalar-chart reference transition
    exposes its exact function-field equivalence as well.  Consequently
    `ChunkFourArrowReference.lean` gives exact generic-point formulas for
    `toNormalizedE/A/B/C` and, after reference transport, for all four
    `toReferenceE/A/B/C`: each is attached to a displayed composite field
    embedding from the selected `(B,T)` function field into the common
    eight-input cover field.  The remaining comparison with the presented
    family is therefore an equality of explicit field maps, rather than an
    implicit appeal to dominance or birational equivalence.
27. The normalized intrinsic multiplication graph now carries the same
    exact generic-point data as the four-arrow reference chart.  The three
    projections in `Config/ChunkGermChart.lean` expose explicit
    contravariant function-field embeddings for inverse-`A`, input-`B`, and
    output-`C`; conjugating each through the canonical chart identifications
    recovers the literal inclusion of its displayed parameter field into the
    common normal multiplication field.  Each dominant rational projection
    is proved to induce exactly that embedding.  Thus a future descent from
    the eight-input four-arrow source to this intrinsic two-input graph can
    be stated and checked entirely as equality of concrete field maps.
28. `Correspondence/FieldEquivDiagram.lean` supplies the faithful semantic
    target that the formal presented family lacked.  Field equivalences can
    be conjugated to fixed reference charts while preserving composition,
    inverse, and equality, and a four-arrow diagram of four literal
    composition triangles satisfies the exact map identity
    `c = a ≫ e⁻¹ ≫ b`.  `Config/ChunkFiniteFieldAction.lean` now exposes the
    selected `A` and `B` restrictions separately, proves that they compose
    to the strict `AB` restriction, and corrects the independently selected
    `C` restriction by the inverse vertical deck defect.  The result is a
    literal finite-normal-cover composition triangle suitable for assembly
    into that semantic four-arrow diagram; no equality in the formal
    presented quotient is used as equality of field maps.
29. `Config/ChunkCurveRelocation.lean` lifts an arbitrary realization
    `(a,b,c)` of the rank-two Ψ multiplication locus to the actual curve
    coordinates on which its correspondence branches act.  Given one
    source generic over the six parameters, it relocates the complete
    nine-coordinate `(a,b,c,x,y,z)` selected prime locus while fixing
    `(a,b,c,x)` literally.  Restricting this single relocated component
    recovers exactly the selected `A` family locus on `(a,x,y)`, the `B`
    family locus on `(b,y,z)`, and the `C` family locus on `(c,x,z)`.
    Thus each parameter edge now has a coherent curve-coordinate
    composition triangle rather than three independently chosen family
    members.
30. `Correspondence/Family.lean` now rebuilds a generic family member of
    arbitrary parameter dimension from equality of its complete tuple
    ideal and independence of its parameter/source prefix.  Applying this
    to item 29 packages the relocated `A`, `B`, and `C` restrictions as
    genuine rank-two family members and as finite-correspondence pairs over
    the common field generated by all six parameters.  The reusable module
    `Correspondence/FiniteCompositionTriangle.lean` puts any two pairs with
    a literal shared middle on one common finite normal source/middle/target
    cover, restricts the vertical deck defect, and produces a strict
    equality `A ≫ B = C`.  Consequently every relocated Ψ parameter edge
    now carries its own literal finite-cover composition triangle.
31. `Config/ChunkCurveFourArrow.lean` instantiates item 30 on all four
    edges `s·e=u`, `sA·a=u`, `s·b=uB`, and `sA·c=uB` of an ambient
    rank-two difference diagram.  From independence of the original eight
    input coordinates it proves independence of the three successive
    tuples obtained by finite parameter replacement.  An unused ambient
    coordinate is therefore generic over each six-parameter edge, giving
    a package of four curve-coordinate realizations and four literal
    finite-normal-cover composition identities.
32. `Correspondence/FieldEquivDiagram.lean` now packages one strict
    `CompositionTriangle` and a `FourTriangleReference`: twelve explicit
    equivalences from four independently typed triangles to three reference
    fields, together with the four compatibility equations for repeated
    `s`, `sA`, `u`, and `uB` arrows.  Its constructor produces a literal
    `FieldEquiv.FourArrowDiagram`.  The Ψ-specific `ReferenceAlignment` in
    `Config/ChunkCurveFourArrow.lean` specializes this interface to the four
    finite-cover triangles from item 31 and exposes faithful right-arrow
    cancellation.  Thus the remaining obligation is exactly to construct
    the coefficient-compatible reference equivalences; arbitrary abstract
    field isomorphisms are insufficient.
33. `Config/ChunkCurveCommonSource.lean` removes the first obstruction to
    those coefficient-compatible equivalences.  It embeds the original
    ambient field `K` into the algebraic closure of `K(X)` and proves that
    the image of the formal variable is transcendental over all of `K`,
    hence generic over every embedded finite parameter tuple.  Ambient
    invariance transports the selected nine-coordinate Ψ locus and its
    algebraicity data along the embedding.  The tuple-relocation theorem can
    therefore be applied to all four parameter edges while fixing the same
    formal source literally.  The resulting four complete curve triangles
    now have a common source over the full eight-input coefficient field;
    their middle and target normal covers still have to be normalized over
    that common base.
34. `FiniteCorrespondenceFamilyMember.map` transports a generic family
    member along an ambient embedding, and `ofTupleIdealEqOnly` now recovers
    the independent parameter/source prefix directly from equality of the
    complete family locus.  The embedded restrictions from item 33 are
    therefore genuine generic members of the mapped selected A/B/C
    families.  `CommonBaseData` then rebases each branch to the field
    generated by the mapped eight-input tuple: the selected auxiliary
    parameter blocks need only be algebraic over this field.  Genericity of
    each B-source middle coordinate follows from its interalgebraicity with
    the one formal source.  Consequently all four faces now have strict
    deck-corrected finite-normal-cover composition triangles over the same
    coefficient field and with the same literal source coordinate.
35. `FiniteCoverTriangle.OnSourceCover` proves that the strict
    deck-corrected composition construction works on any caller-supplied
    finite normal source cover, not only the branch-generated cover chosen
    internally by one face.  The four facewise source covers are therefore
    joined by `FiniteNormalCover.sup` into
    `PsiCurveFourArrowCommonSourceRealizations.commonFiniteSourceCover`.
    Each original source normalization is proved to lie in this finite
    normal compositum, and all four faces are transported through it to
    literal strict composition triangles with exactly the same source
    field.  The remaining alignment problem is now confined to the four
    transported middle and target fields.
36. `Correspondence/FamilyCover.lean` packages the complete field of a
    generic family member as a finite extension of its independent
    parameter/source field.  Equality of complete family loci gives an
    `ExtensionEquiv` that sends every displayed coordinate to its matching
    coordinate, a semilinear equivalence of the concrete normal closures,
    and a deck-corrected `FiniteCoverBasedBranchEquiv` which preserves the
    literal selected branch.  The four repeated labels `s`, `sA`, `u`, and
    `uB` in the fresh-source diagram have equal complete family loci, so
    they now carry four such coefficient-aware based comparisons.  These
    comparisons currently live over their rank-two-parameter/source fields;
    they still have to be extended across the other six independent inputs
    to the common coefficient field of item 35.
37. Complete family-locus equality now also descends to equality of the
    endpoint-pair ideals over the field generated by the common literal
    parameter tuple.  The proof constructs the complete-locus function-field
    equivalence, proves generator by generator that it fixes the parameter
    field, and transports every two-variable polynomial evaluation.  Applied
    to the fresh-source four-arrow diagram, the two occurrences of each of
    `s`, `sA`, `u`, and `uB` therefore define the same selected curve relation
    over their exact rank-two parameter field.  This is the coefficient-
    faithful scalar-extension input: the remaining task is to preserve these
    four equal pair ideals while adjoining the other six independent input
    coordinates and then pass their selected normal branches to the common
    coefficient field of item 35.
38. Independent scalar extension is now proved without an irreducibility
    shortcut.  A base-field equivalence extends canonically after adjoining
    matching algebraically independent tuples, fixing every new generator.
    Consequently equal endpoint-pair ideals remain equal after adjoining an
    auxiliary tuple independent over both complete endpoint fields.  A
    separate tower lemma shows that six coordinates jointly independent from
    the parameter/source prefix stay independent after adjoining the
    algebraic family target.  The alternative independent presentations
    `(s,e,a,b)`, `(s,sA,a,b)`, `(s,u,a,b)`, and `(s,sA,a,uB)` supply the four
    required six-coordinate complements, so all four repeated curve ideals
    are now equal over full transcendence-degree-eight input fields.  For the
    repeated `s` block this field is literally the common input field from
    item 35, yielding the first exact common-base repeated-arrow equality.
    The other three full input fields have the same relative algebraic
    closure as the original input field but are not definitionally equal;
    their finite algebraic coefficient changes must still be normalized
    before transporting the selected branches to the common covers.
39. Equality of a selected two-variable curve ideal now canonically
    identifies the finite extension from the source-coordinate field to the
    complete branch field.  The comparison lifts semilinearly to the
    concrete normal closures and a deck correction makes it preserve the
    literal selected branch.  The exact common-input `s` relation from item
    38 instantiates this construction on the actual common-base
    finite-correspondence pairs, producing the first faithful selected-normal-
    cover anchor for the reference alignment.  This is stronger than an
    arbitrary equivalence between transported middle fields: it remembers
    which normal subcover and selected branch encode the repeated curve.
40. The remaining finite algebraic coefficient changes are now packaged in
    one field obtained by adjoining the actual `sA`, `u`, and `uB` blocks to
    the common eight inputs.  This extension is finite; its normal closure
    is finite and normal over the common input field and contains each of
    the three named alternative full input fields.  A generic family member
    plus an auxiliary tuple jointly independent from its parameter/source
    prefix now becomes a finite-correspondence pair over the enlarged
    coefficient field.  Applying this to both occurrences of `sA`, `u`, and
    `uB` turns their alternative-field ideal equalities into three genuine
    `FiniteCoverBasedBranchEquiv`s, each proved to preserve the literal
    selected branch.  The remaining bridge is to transport these three
    based comparisons through their embeddings into the common coefficient
    normal field and then into the simultaneous common source cover.
41. The common coefficient comparison field is now proved finite over all
    three alternative eight-input fields, not merely over the original
    common input field.  A reusable ambient-invariance lemma shows that
    equality of relative algebraic closures survives an embedding into a
    larger ambient field.  The diagram's successive interalgebraic block
    replacements therefore identify the closures of the original input
    tuple with `(s,sA,a,b)`, `(s,u,a,b)`, and `(s,sA,a,uB)` after embedding.
    Every common or replacement coefficient is algebraic over each named
    alternative field, so the explicit coefficient enlargement is finite
    over each; finiteness then ascends to its common normal closure by the
    finite-extension tower law.  Thus the next transport may take finite
    pairwise normal closures after adjoining the formal source and the
    simultaneous source cover.  No unsupported assertion that curve ideals
    remain prime after algebraic base change is used.
42. `FiniteCoefficientBranchCompositum` now performs the next pairwise
    normalization without tensoring curve ideals.  Given a finite coefficient
    extension and two finite correspondences with the same literal source,
    it successively adjoins the coefficient field, the first selected branch,
    and the second selected branch.  Each step is finite over the preceding
    field, so the joint field is finite over the source-coordinate field;
    its ambient normal closure is finite and normal and contains the
    coefficient extension and both selected branches literally.  The `sA`,
    `u`, and `uB` alternative pairs now instantiate this construction using
    the common coefficient normalization from items 40--41.  Thus each
    comparison has a concrete pairwise normal source field on which its
    branch equivalence can be extended.
43. Equality of the selected pair ideals with a literally common source now
    gives an equivalence of the two branch fields over that source, with an
    explicit theorem carrying the first displayed target to the second.
    Composing this equivalence with inclusion of the second branch into the
    pairwise normal field gives an embedding of the first branch; normality
    extends it to an automorphism of the whole joint field.  The extension is
    proved to restrict to the prescribed branch equivalence and hence to
    carry the first literal target to the second.  The `sA`, `u`, and `uB`
    comparisons now each expose such an automorphism.
44. The pairwise fields are now rebased honestly to the literal common
    coefficient/source field.  The alternative and common coefficient bases
    are not treated as nested: a finite-basis compositum first proves the
    pairwise normal field finite over the common field with the same formal
    source adjoined, and a second ambient normal closure handles the possible
    loss of normality between incomparable bases.  Its canonical model lives
    in the exact algebraic closure used by the four strict triangles, and
    both literal target branches embed in it.  The three canonical rebased
    covers are joined to the earlier simultaneous four-face source cover as
    `branchComparisonSourceCover`; all four composition triangles have been
    rebuilt with literal strict composition on this enlarged source.  The
    remaining local step is to compare the two induced transported
    middle/target embeddings inside that cover and use the canonical curve
    coefficients to prove coefficient-compatible equality, rather than only
    existence of the two branch embeddings.
45. Canonical normal closures now retain a distinguished branch: the
    literal ambient extension is first included in its concrete normal
    closure and then transported through the chosen concrete-to-canonical
    equivalence.  Returning along that equivalence recovers the literal
    inclusion.  The composition source cover now exposes its left,
    pulled-right, and direct canonical subcovers, and any larger source cover
    containing it inherits distinguished left and direct branch embeddings.
    For each of the four Ψ faces, both selected embeddings have been placed
    in `branchComparisonSourceCover`.  Thus the next comparison can refer to
    the actual selected `s`, `sA`, `u`, and `uB` branches of the four strict
    triangles, rather than merely to abstract isomorphic normal fields.  The
    generic ideal-induced generator theorems were also made explicit enough
    for clean dependency rebuilds, and the finite coefficient compositum now
    imports and instantiates its normal-cover prerequisites directly.
46. Branch-domain equivalences can now reparametrize a selected embedding,
    after which a distinguished deck automorphism aligns it with any other
    embedding in the same normal cover.  The construction anchors the
    temporary algebra structure at the first embedding, so it does not
    silently use an unrelated inclusion of the branch field.  The exact
    common-base repeated `s` ideal identifies its two literal branch fields;
    the induced automorphism of `branchComparisonSourceCover` fixes the full
    common coefficient/source field, carries the first selected `s` branch
    to the reparametrized second branch, and sends the first displayed middle
    coordinate to the second.  A rebased comparison branch can also be
    inherited by any larger canonical normal cover.  Thus the `s` coherence
    is now coefficient-faithful; the same domain comparison over the literal
    common base remains to be proved for `sA`, `u`, and `uB`.
47. The repeated `sA` coefficient comparison is now transported through an
    explicit semilinear rebase instead of an equality cast.  The raw rebased
    source presentation is identified with the literal common source, that
    equivalence is extended to the two algebraic closures, and both raw
    selected branches are identified carrier-faithfully with the literal
    branch fields of the `sA·a=u` and `sA·c=uB` common-base faces.  Transport
    by the same source/closure equivalence puts both branch embeddings in the
    named rebased cover and then in `branchComparisonSourceCover`.  The face
    source fields reduce to the same literal common-base type, so two chosen
    deck transformations now carry the actual selected `sA` face embeddings
    to these coefficient-comparison copies, with exact `smul` equations.
    Thus the closure choices for both occurrences of `sA` are aligned while
    retaining the algebraic coefficient transport.  The analogous explicit
    transports for the repeated direct `u` and `uB` branches remain next.
48. The repeated direct `u` comparison now has the same explicit semilinear
    transport and selected-branch alignment.  The strict composite pairs of
    the `s·e=u` and `sA·a=u` faces name the two literal direct branches.  A
    reusable carrier lemma shows that adjoining an equal ambient generator
    to equal intermediate-field carriers produces the same field carrier;
    this identifies both raw comparison branches with those strict direct
    branch fields.  The raw common-source equivalence and its algebraic-
    closure lift transport both embeddings into the named rebased cover and
    then into `branchComparisonSourceCover`.  Two chosen deck transformations
    carry the actual selected direct face embeddings to the transported
    comparison copies, with exact `smul` equations.  Thus `s`, `sA`, and `u`
    are now coefficient-faithfully aligned in the common source cover; only
    the symmetric direct `uB` transport remains before constructing the
    coefficient-compatible reference charts.
49. The symmetric direct `uB` transport and alignment are now complete.  The
    strict composite pairs of the `s·b=uB` and `sA·c=uB` faces identify the
    literal direct branch domains.  Their raw comparison branches are
    carried through the explicit common-source equivalence and its
    algebraic-closure lift, included in `branchComparisonSourceCover`, and
    aligned with the two actual selected face embeddings by distinguished
    deck transformations.  Both exact `smul` equations are proved over the
    full common coefficient/source field.  Consequently all four repeated
    labels `s`, `sA`, `u`, and `uB` now have coefficient-faithful selected-
    branch comparisons in one finite normal source cover.  The next step is
    to transport these four equations through the strict face triangles,
    choose coefficient-compatible middle and target reference charts, and
    instantiate the Ψ-specific `ReferenceAlignment`.
50. The alternative-base comparisons are now exposed with their correct
    semilinear source data.  Their branch automorphisms are linear over the
    alternative `sA`, `u`, and `uB` source-coordinate fields, but need not
    fix every coefficient of the literal eight-input common source field.
    The literal common source is therefore included in each pairwise normal
    field as a ground-field algebra, its image under the corresponding
    restricted automorphism is retained as an actual intermediate field,
    and an explicit algebra equivalence identifies the original source with
    that image.  A reusable scalar-fixity lemma proves that all three image
    equivalences fix the common formal curve generator while faithfully
    recording the potentially moved coefficient presentation.  Thus the
    next middle/target charts can be induced from genuine semilinear source
    charts; no false common-base deck-transformation assertion is needed.
51. The semilinear source charts have now been lifted to the chosen
    algebraic closures and restricted to the full enlarged common finite
    source cover.  Their restriction squares are explicit pointwise, and
    the formal curve generator is still carried by the corresponding
    source-image algebra map.  For branch faithfulness, each moved source
    field is also mapped back into the original common curve ambient.  It
    and the original source then form two bases of the same pairwise normal
    total field, and the actual alternative-base branch automorphism gives
    an equivalence of those nested extensions.  Lifting this complete
    extension equivalence to canonical normal closures retains both the
    source movement and the total-field automorphism; it does not replace
    the latter by an unrelated lift of the source equivalence.  The next
    local step is the target deck correction which makes this semilinear
    normal-closure equivalence preserve the literal selected total branch,
    followed by its inclusion in the simultaneous source cover.
52. The branch-faithful semilinear normal-cover comparisons are now
    complete for `sA`, `u`, and `uB`.  Finiteness of the pairwise total
    field over the literal common source is proved explicitly and
    transported across each moved-base extension square.  The resulting
    canonical normal-closure equivalence is returned to the concrete
    normal closures, then corrected by a target deck transformation.  This
    correction is packaged by the existing based finite-cover interface and
    proves that the literal selected embedding of the entire pairwise total
    field is carried to the literal selected embedding over the moved
    source image.  Thus both the coefficient movement and the actual branch
    automorphism survive normalization.  The next step is to compare these
    corrected concrete normal covers with the already embedded canonical
    rebased comparison covers, include the corrected charts in
    `branchComparisonSourceCover`, and induce the middle/target charts.
53. The source-chart layer has also been re-elaborated from source rather
    than accepted from replayed build hashes.  This exposed and repaired
    three presentation-level defects in items 50--52: inferred automorphism
    types did not retain the named normal-field algebra structures,
    dependent rewriting through `extendScalars` was unstable, and the
    finite-cover generator statements asked typeclass search to reconstruct
    an ambiguous scalar presentation.  The branch automorphisms now have
    explicit named-field types, equality-based finite-dimensional transport
    is packaged by `FiniteCover.finiteDimensional_of_eq`, and the generator
    equations use their literal algebraic-closure representatives.  A
    direct compilation of `ChunkCurveCommonSource.lean`, the full build,
    and the book generator all pass.  Keep direct compilation of a changed
    leaf module in the validation loop whenever only `.olean.hash` artifacts
    are initially present.  The mathematical next step remains the
    corrected concrete-to-canonical cover comparison from item 52.
54. The corrected concrete normal-cover comparisons now meet the canonical
    comparison covers already present in `branchComparisonSourceCover`.
    For each of `sA`, direct `u`, and direct `uB`, equality of the literal
    common source with the raw rebased source is packaged together with
    equality of the named pairwise total field as an extension
    equivalence.  Its canonical normal lift is composed with the same
    raw-to-common algebraic-closure transport used to define the rebased
    cover.  The result is an explicit ring equivalence from the canonical
    normal closure of the literal-common-source pairwise extension to the
    named rebased canonical cover already embedded in the simultaneous
    compositum.  The next local step is to record the base-compatibility of
    these three bridges, transport the selected whole-total-field branches
    through them, and include those embeddings into
    `branchComparisonSourceCover`.
55. The three concrete-to-canonical bridges are now algebra equivalences
    over the literal common source.  Equality-induced extension
    equivalences expose their canonical base map, and a reusable mapped
    normal-lift API proves that composing this base map with the chosen
    raw-to-common algebraic-closure transport is the identity.  This upgrades
    the `sA`, direct-`u`, and direct-`uB` canonical-cover ring equivalences to
    common-base algebra equivalences.  Each upgrade carries the canonical
    selected embedding of the entire pairwise total field into the named
    rebased cover and then, through the established containment, into
    `branchComparisonSourceCover`.  A generic algebra-map equation records
    that these whole-total-field embeddings fix the common source exactly.
    The next local step is to use these three coefficient-faithful total-field
    embeddings with the semilinear source-image charts and the four existing
    face-to-copy alignment equations to induce compatible middle and target
    reference charts.
56. The coefficient-faithful whole-total-field embeddings now supply
    coherent anchors for all six alternative selected face branches.  A
    carrier-transport lemma moves containments across two changes of scalar
    presentation, and the rebased first and second branches are proved to
    lie already in their original pairwise normal total field.  Restricting
    each of the three whole-total-field embeddings therefore places both
    occurrences of `sA`, both direct occurrences of `u`, and both direct
    occurrences of `uB` in `branchComparisonSourceCover` through one shared
    embedding for each repeated label.  Six chosen common-source deck
    transformations carry the actual selected face branches to these
    coherent anchors, with exact whole-branch `smul` equations.  Separately,
    a strict composition triangle now exposes the canonical middle and
    target charts induced by any source chart, and four source charts package
    into a literal four-triangle reference.  The next local step is to choose
    the four source charts so that the two anchor corrections attached to
    each face are jointly compatible; their induced middle and target charts
    can then be proved coefficient-faithful and fed to four-arrow
    cancellation.
57. The four coefficient/source charts are now chosen and the enlarged
    strict triangles have been assembled into an actual semantic
    four-triangle reference.  On the two `u` faces the source charts are the
    two coherent direct-`u` anchor corrections; on the two `uB` faces they
    are the corresponding direct-`uB` corrections.  All four are algebra
    automorphisms over the literal common coefficient/source field, so they
    fix every canonical curve coefficient even when they move a selected
    left branch to another conjugate.  The induced middle-chart restriction
    formula is proved on the entire selected `s` or `sA` branch, and the
    induced target chart is proved pointwise to recover the appropriate
    shared whole-total-field `u` or `uB` anchor.  These charts instantiate
    `FourTriangleReference.ofSourceCharts`, produce a literal semantic
    four-arrow diagram, and satisfy exact right-arrow cancellation.  The
    next local step is to apply canonical-curve-equation faithfulness to
    these restriction formulas and identify the four displayed parameter
    field embeddings occurring in the normalized reference projections.
58. Canonical-curve-equation faithfulness now survives the actual
    finite-cover charts.  A selected correspondence branch is represented
    inside its source-based branch field by explicit source and target
    elements; both satisfy the original canonical equation, and every
    coefficient-linear embedding carries them to another zero.  The strict
    finite composition cover now contains the literal selected right branch
    in its transported middle field.  Its left and deck-corrected direct
    equivalences fix the original coefficient field, and any
    coefficient-linear middle chart therefore preserves the right branch's
    equation.  All four `e`, `a`, `b`, and `c` right branches are embedded in
    their enlarged middle covers.  The induced middle and target charts are
    proved to fix the literal common coefficient field, and the two charted
    coordinates of every selected right branch are proved to satisfy its
    original canonical curve equation.  Thus semantic four-arrow
    cancellation is now coefficient-faithful on the actual selected
    branches, not only an identity of abstract cover equivalences.  The next
    local step is to combine these four equation identities with intrinsic
    germ coefficient-field faithfulness and identify the explicit
    function-field embeddings underlying `toReferenceE/A/B/C`.
59. The explicit normalized `B/T` reference cover and the semantic curve
    action now have one literal codomain.  The canonical embedding
    `K → AlgebraicClosure K(X)` maps the eight-input field exactly onto the
    common curve coefficient field and transports the finite normalized
    reference cover without changing its degree.  After base change across
    the formal curve source, its canonical normal closure is joined with
    `branchComparisonSourceCover`; the resulting finite normal cover
    contains both constructions.  An explicit coefficient-linear embedding
    from the original reference cover into this combined source sends every
    free input through the same semantic coefficient algebra map.  The four
    displayed contravariant embeddings underlying `toReferenceE/A/B/C` have
    been postcomposed with this embedding and are now literal ring maps into
    the semantic source cover.  The remaining local comparison is therefore
    an equality of maps with the same domain and codomain: identify their
    restrictions on intrinsic germ coefficients, then align the finite
    scalar branches inside the common normal cover.
60. The four explicit reference maps now have exact restrictions to the
    intrinsic selected-`B` germ coefficient field.  The selected coefficient
    field is included first in `k(B₁,B₂)` and then in the selected
    normalized `B/T` cover.  For every relocated projection `(p,x)`, the
    normalized selected-to-projection equivalence is proved semilinear over
    the canonical function-field equivalence induced by equality of the
    two parameter loci.  Consequently its restriction to an intrinsic germ
    coefficient is exactly that coefficient transported to `k(p₁,p₂)`,
    followed by the literal algebra map to the scalar normal cover.  This
    formula is pushed through the original reference cover and the combined
    semantic/reference source, and is instantiated as four named maps
    `toReferenceE/A/B/COnBGermCoefficientRingHom`.  Their simultaneous
    restriction theorem removes all chart-conjugation choices from the
    coefficient layer.  Direct leaf compilation also exposed and repaired
    an old stale-artifact defect in the preceding common-codomain theorem:
    its dependencies are now explicit and its large opaque composite is
    factored into small maps with a fast direct proof.  The next local step
    is to identify these canonical parameter transports with the
    coefficients of the four relocated right-branch curve equations, then
    align the remaining finite scalar-normal branches.
61. Canonical curve equations now transport coefficientwise across both
    operations used in the four-face comparison.  Ambiently embedding a
    family maps its parameter field, endpoint ideal, and lexicographically
    monic curve equation exactly; equality of two complete family loci then
    maps the endpoint ideal and canonical equation through the induced
    parameter-field equivalence.  These reusable results identify the
    selected `B` equation with every relocated right-branch equation.  The
    parameter equivalence obtained from each full relocated family locus is
    proved generator-by-generator to equal the normalized equivalence
    obtained from its `B/T` scalar locus.  Consequently, for every monomial
    index, all four canonical transports from item 60 send the corresponding
    intrinsic selected-`B` coefficient to the coefficient with that same
    index in the relocated `e`, `a`, `b`, or `c` right-branch equation.  The
    four formulas are packaged simultaneously.  Thus the coefficient layer
    of the normalized reference charts is now identified with the semantic
    curve layer without any choice of equation generator or parameter-field
    isomorphism.  The next local step is to align the remaining finite
    scalar-normal branches in the combined cover and use the resulting
    whole-branch equality to factor the four explicit reference maps.
62. The deck correction used to base a transported finite normal cover is
    now retained as an explicit semilinear field equivalence.  The generic
    `FiniteCoverBasedNormalEquiv` records both its base-field square and an
    exact whole-selected-branch square, and recovers the existing based
    branch-groupoid equivalence without making a second choice.  Applied to
    the complete nine-coordinate joint chunk edges, the corrected normal-
    cover equivalence sends every selected coordinate positionwise.  Four
    named equivalences based at the `s·e=u` edge therefore send its selected
    `B/T` scalar at coordinate `7` exactly to the `e`, `a`, `b`, and `c`
    scalar branches used by the normalized reference maps.  Their induced
    reference-based field transitions satisfy a strict cocycle, and the
    four-edge field-level holonomy is literally the identity.  Thus the
    scalar alignment is no longer only an equality in an abstract branch
    groupoid: it is carried by selected-branch-preserving field
    equivalences with exact coordinate formulas.  The next local step is to
    base-change these four corrected edge equivalences to the common eight-
    input/formal-source field and include their selected scalar branches in
    `referenceSemanticSourceCover`; there they can be compared pointwise
    with the four promoted `toReference` embeddings and the semantic curve
    charts from items 58--61.
63. The four complete selected edges have now been scalar-extended from
    their different six-coordinate ambient fields to the single
    sixteen-coordinate coefficient field of the four-arrow diagram.  A
    reusable `TotalBaseChangedEdge` records the literal ambient and selected
    inclusions.  Its finite-basis compositum is finite over the common
    coefficient field, contains the full selected nine-coordinate edge, and
    remains a subfield of the twenty-eight-coordinate joint field.  Hence
    all four such fields embed literally in `referenceNormalCover`, and
    their selected coordinate `7` elements are exactly the `e`, `a`, `b`,
    and `c` scalar branches already used by the explicit normalized
    projections.  Composing these inclusions with the canonical transport
    to `referenceSemanticSourceCover` places all nine coordinates of all
    four scalar-extended edges in the common formal-source normal cover and
    preserves them exactly.  No additional scalar branch has been chosen.
    The remaining half of the base-change step is to extend the four
    corrected complete-edge normal-cover equivalences across this common
    coefficient field and the formal source, using the coefficient-
    semilinear source charts.  Their coordinate-`7` formulas can then be
    compared pointwise with the promoted `toReferenceE/A/B/C` maps.
64. The normalized scalar-reference transitions now retain the based
    normal-cover correction instead of reverting to an arbitrary lift after
    strict reference normalization.  They therefore still satisfy strict
    identity, inverse, and transitive laws while also carrying the literal
    selected scalar branch to the literal selected target branch.  The
    selected normalized `B/T` chart has a named intrinsic function-field
    scalar generator, and every promoted projection sends it to the selected
    scalar in that projection's concrete normal field.  After inclusion in
    `referenceSemanticSourceCover`, the four named `toReferenceE/A/B/C`
    embeddings agree pointwise on this generator with coordinate `7` of the
    four literal scalar-extended complete edges from item 63.  The four named
    intrinsic-`B`-germ maps are also proved to be literally the restrictions
    of those promoted embeddings.  Thus both the coefficient layer and the
    distinguished finite scalar branch now meet the semantic construction in
    the same codomain.  The remaining local step is to extend this equality
    from the coefficient field plus selected scalar to the whole relevant
    branch/function-field comparison and derive the auxiliary-`s`-independent
    three-input factorization.
65. The pointwise selected-scalar comparison now extends to every element of
    the selected nonnormal `B/T` scalar extension.  Each scalar-extended
    complete edge contains its entire three-coordinate right branch
    literally, and the direct inclusion of that branch in
    `referenceNormalCover` is proved equal to the route through the complete
    edge.  Canonical total-field equivalences transport the intrinsic
    selected branch to each of the `e`, `a`, `b`, and `c` branches, while the
    based normal-cover transitions agree with those equivalences on the
    whole extension.  After promotion to `referenceSemanticSourceCover`, all
    four `toReferenceE/A/B/C` embeddings therefore restrict as ring
    homomorphisms to the corresponding literal complete-edge inclusions;
    the four equalities are packaged simultaneously.  The next local step
    is to extend this exact comparison from the nonnormal scalar extensions
    across the full selected normalized function field and the four complete
    curve-branch fields.  That whole-function-field equality should then
    identify the explicit reference embeddings with the semantic curve
    arrows and yield the auxiliary-`s`-independent three-input
    factorization.
66. The explicit comparison now extends across the entire selected
    normalized `B/T` function field.  A generic ambient ring homomorphism
    applies the based selected-to-projection normal-cover equivalence and
    then the literal inclusions into `referenceNormalCover` and
    `referenceSemanticSourceCover`.  Pulling that map back through the
    selected chart's generic-point equivalence is proved equal, as a ring
    homomorphism on every function-field element, to the promoted reference
    projection.  The equality is specialized and packaged simultaneously
    for `toReferenceE/A/B/C`; thus no normal-closure element remains outside
    the exact comparison.  The remaining half of the local step is to
    identify these four whole-field maps with the four complete semantic
    curve-branch embeddings and then apply literal four-arrow cancellation.
67. The four complete semantic right-branch maps now have the same literal
    codomain as the promoted normalized reference maps.  The reusable
    finite-cover triangle API proves that its right equivalence fixes the
    original coefficient field, and the four-triangle API gives exact
    pointwise formulas expressing every charted right arrow as the original
    complete right-arrow transport followed by its target chart.  The
    branch-comparison cover has a named literal inclusion in
    `referenceSemanticSourceCover`; composing it with the selected complete
    `e`, `a`, `b`, and `c` branch embeddings, the four middle charts, and the
    semantic right arrows yields four ring homomorphisms defined on the
    entire curve-branch fields.  The remaining comparison is now an equality
    between named maps with a common codomain: prove that their intrinsic
    parameter restrictions are the four whole normalized maps from item 66,
    then descend four-arrow cancellation to the `B` germ chart.
68. The coordinatewise comparison with the relocated right-branch equations
    is now promoted to maps on the whole intrinsic selected-`B` coefficient
    field.  A reusable extensionality theorem says that two coefficient-linear
    maps out of this field agree once they agree on every canonical curve
    coefficient.  Four named algebra homomorphisms land in the complete
    relocated `e`, `a`, `b`, and `c` family parameter fields and send each
    canonical generator to the coefficient with the same monomial index.
    The codomains are deliberately kept separate: in particular, the
    relocated `c` parameter field is algebraic over, not a literal subfield
    of, the common eight-input coefficient field.  Each promoted intrinsic
    `toReferenceE/A/B/C` map is proved on the entire field to factor through
    the corresponding relocated parameter map and then the normalized
    scalar-cover inclusion.  Thus the remaining equality with the complete
    semantic branch maps is reduced rigorously to their action on the named
    canonical coefficients; no invalid inclusion of the output parameter
    field into the common coefficient base is required.  The next local step
    is to construct those four coefficient embeddings into the complete
    right branches, identify their charted semantic images generator by
    generator with the factorizations above, and apply intrinsic-field
    extensionality before four-arrow cancellation.
69. The four relocated parameter-field maps now factor through precisely the
    intrinsic coefficient fields of their canonical curve equations.  For an
    arbitrary relocated member on the selected complete family locus, the
    ambient image of the selected germ coefficient field is proved equal to
    the field generated by the relocated equation's coefficients.  This gives
    a canonical algebra equivalence between the two intrinsic coefficient
    fields, sends every selected coefficient to the same-index relocated
    coefficient, and recovers the previous full parameter transport after the
    literal coefficient-field inclusion.  Four named equivalences and one
    simultaneous factorization theorem specialize the construction to the
    `e`, `a`, `b`, and `c` right families.  Consequently, the remaining
    semantic comparison is confined to actual curve-equation data rather than
    unrelated displayed parameter coordinates.  The next local step is to
    embed these four relocated coefficient fields in their complete branch
    fields, compare their semantic images with the normalized reference maps,
    and then use coefficient-field extensionality and four-arrow cancellation.
70. A chart-gauge audit has isolated an important boundary in the existing
    semantic comparison.  For every composition triangle, choosing both the
    middle and target charts by transport from a source chart conjugates not
    only the left and direct arrows but also the right arrow to the identity.
    This is now a proved reusable theorem, and its four-face specialization
    states explicitly that all four right arrows in
    `coefficientFourArrowDiagram` are `RingEquiv.refl`.  The diagram still
    organizes coefficient-faithful selected graph embeddings, but its abstract
    cancellation theorem alone is therefore gauge-trivial and cannot justify
    intrinsic parameter factorization.  GitHub issue #16 tracks the corrective
    construction: put the transported normalized reference cover and the four
    selected semantic branches in one coherent normal model, then choose
    non-induced middle/target charts (or equivalent graph-faithful data) whose
    restriction theorems retain the `e/a/b/c` coefficient embeddings.
71. Each relocated intrinsic curve-coefficient field now has a literal ring
    embedding in its complete selected right-branch field.  Composing the four
    coefficient equivalences from item 69 with these inclusions gives named
    whole-field embeddings of the intrinsic selected-`B` germ into the
    complete `e`, `a`, `b`, and `c` curve branches, and a simultaneous theorem
    identifies every canonical generator with the same-index relocated curve
    coefficient.  This closes the first unchecked task of issue #14.  The
    codomains intentionally remain the four original complete branches: the
    next issue-#16 step is the honest scalar extension/joint normal-cover
    comparison that places them beside the common-base semantic branches
    without assuming, especially for `c`, that the full relocated parameter
    field lies in the eight-input coefficient field.
72. The selected semantic/reference comparison now has a concrete joint
    field before canonicalization.  Starting from the transported reference
    compositum over the literal common curve source, it adjoins the two
    algebraic `c` coordinates and the source/target pair of each of the four
    selected semantic right branches.  All ten generators are proved
    algebraic over the common source, so the joint field is finite there and
    one ambient normal closure is both finite and normal.  Literal containment
    theorems place the transported normalized reference field, all four
    common-base semantic right branches, and all four original relocated
    complete right branches in that same normal field.  In particular, the
    `c` parameter presentation is handled by honest finite adjunction rather
    than a false inclusion in the original eight-input field.  This completes
    the concrete-joint-field and single-normal-closure tasks of issue #16.
    The next issue-#16 checkpoint is to expose selected whole-branch embeddings
    into this normal field, canonicalize it once, and prove that the resulting
    comparison maps preserve the four intrinsic coefficient embeddings.
73. The concrete selected semantic/reference normal field is now
    canonicalized exactly once, with an explicit algebra equivalence over the
    full common coefficient/source field.  A reusable cross-base branch
    inclusion sends a complete selected correspondence branch into any
    intermediate field containing its ambient branch carrier.  It supplies
    eight named literal inclusions—four common-base semantic right branches
    and four original relocated right branches—into the concrete normal field,
    followed by eight maps through the same canonicalization equivalence.
    The four intrinsic selected-`B` coefficient embeddings from item 71 now
    compose with those relocated whole-branch maps into one selected canonical
    cover.  A simultaneous generator theorem proves that all four still send
    every canonical germ coefficient to the corresponding literal relocated
    curve coefficient before the shared canonicalization.  This completes the
    selected-embedding/canonical-comparison task of issue #16.  The remaining
    issue-#16 work is to construct common graph-faithful source/middle/target
    charts from this selected model, prove repeated-arrow coherence, and expose
    the resulting non-vacuous four-arrow coefficient restrictions for #14.
74. The generic non-induced chart interface required by issue #16 is now
    explicit.  Given four strict composition triangles, four source charts,
    two independently selected common left arrows, and two independently
    selected common direct arrows, `FourTriangleReference.ofCommonLeftDirect`
    constructs all middle and target charts and proves the four repeated-arrow
    coherence equations.  The conjugated right arrows are computed exactly as
    `left⁻¹ ≫ direct`; unlike `ofSourceCharts`, they are not forced to be
    identities.  The next local step is to instantiate those four common
    arrows from the selected semantic/reference normal model of items 72--73
    and prove that the resulting graph restrictions recover the four named
    intrinsic coefficient embeddings.
75. The coherent semantic branch cover and the once-canonicalized selected
    semantic/reference cover now sit in one literal finite normal source,
    `selectedGraphSourceCover`, formed by a single supremum over their common
    source field.  Literal inclusions put all eight selected semantic and
    relocated whole-branch maps in this source, and the four intrinsic germ
    coefficient maps retain their exact same-index generator formulas there.
    The four charted semantic right-branch maps have also been duplicated
    with this precise codomain.  Thus the final issue-#16 chart step no longer
    involves incomparable canonical closures: it is the construction of
    non-induced charts in this one source whose charted semantic maps agree
    with the named selected graph embeddings (first on canonical
    coefficients, then on the whole intrinsic field).
76. A reusable normal-cover extension operation now promotes any prescribed
    automorphism of an embedded finite subcover to an automorphism of the
    ambient normal cover, with an exact restriction formula on the whole
    embedded field.  It extends each of the four established semantic source
    charts to `selectedGraphSourceCover`; the new charts agree there with the
    old `se`, `sAa`, `sb`, and `sAc` charts on all of
    `branchComparisonSourceCover`.  Four strict composition triangles now act
    on this one unified source.  This completes the source-chart half of the
    final issue-#16 construction without imposing any gauge-trivial target
    chart: the remaining step is to select compatible common middle and
    target charts and prove that their right arrows restrict to the named
    intrinsic `e`, `a`, `b`, and `c` coefficient embeddings.
77. The four complete normalized reference edges now enter
    `selectedGraphSourceCover` through the same transported concrete normal
    field and the same single canonicalization as the selected semantic and
    relocated branches.  Every one of their nine selected coordinates has an
    exact preservation formula in that codomain.  More strongly, the four
    promoted reference maps agree with their literal complete-edge routes on
    the entire selected nonnormal `B/T` scalar branch; composing with the
    intrinsic germ-field inclusion gives four equalities on the whole
    selected-`B` coefficient field, including the algebraic output `c` edge.
    The remaining issue-#16 comparison is therefore internal to one selected
    graph cover: identify these whole-field reference restrictions with the
    charted semantic right arrows while choosing common middle/target charts
    compatible with the already lifted source charts.
78. The normalized-reference restrictions of item 77 are now identified
    pointwise with the four named selected relocated intrinsic coefficient
    maps in `selectedGraphSourceCover`.  The proof works on an arbitrary
    element of the intrinsic germ field: the relocated coefficient-field
    factorization recovers its full relocated parameter transport, while the
    scalar-extension equivalence's base square shows that the complete-edge
    route transports the same element before the common curve embedding.
    Thus the simultaneous theorem is a whole-field equality for `e/a/b/c`,
    not a generator-only comparison, and it includes the algebraic `c`
    parameter field.  The remaining issue-#16 step is now specifically to
    choose the non-induced common middle/target charts whose semantic
    right-arrow restrictions are these already-identified maps.
79. The non-vacuity condition for the final charts is now a first-class
    semantic interface rather than prose.  A `FourArrowDiagram.RightRestriction`
    consists of one literal intrinsic coefficient embedding in the common
    middle field, its four named images in the common target field, and proofs
    that all four are restrictions of the corresponding semantic right
    arrows.  Its `mapC_factorization` theorem descends faithful four-arrow
    cancellation to that one coefficient field, retaining the inverse `e`
    arrow in the middle chart.  In particular, four unrelated maps with the
    right codomain cannot satisfy the interface merely because a source-induced
    diagram is gauge-trivial.  The remaining issue-#16 construction must now
    produce this restriction package with `mapE/mapA/mapB/mapC` equal to the
    four whole-field selected/reference maps from item 78.
80. The complete semantic right branches now share one anchor before any
    chart choice.  The finite extension generated by all selected semantic
    face coordinates contains the whole common-base `e`, `a`, `b`, and `c`
    branch fields.  Its one embedding into `selectedGraphSourceCover` uses
    the existing concrete normal model and its single canonicalization.
    Transitivity of literal intermediate-field inclusions then proves,
    simultaneously, that all four semantic graph maps are restrictions of
    this one whole-face embedding.  In particular, the remaining middle and
    target charts can be aligned against one coherent map rather than four
    independently canonicalized branch embeddings.  The next issue-#16 step
    is to transport the middle/target covers to this anchor and package their
    restrictions as the `RightRestriction` of item 79.
81. Equality of complete family loci now reaches the actual complete branch
    types used by the four semantic triangles.  A reusable bridge identifies
    the family-field presentation with `toPair.branchOverSource`, transports
    equal loci to a full branch ring equivalence, and proves that this
    equivalence restricts to the canonical parameter-field transport.  The
    mapped selected `B` family therefore supplies one common complete middle
    branch, with four full equivalences to the relocated `e`, `a`, `b`, and
    `c` branches.  A simultaneous factorization theorem proves that the one
    intrinsic germ embedding in this common branch becomes exactly the four
    named complete-branch coefficient embeddings.  The remaining issue-#16
    step is to extend these branch equivalences to compatible common finite
    normal middle/target covers, join them with the selected graph source,
    and package the resulting four restrictions as item 79's
    `RightRestriction`.
82. The common complete-branch comparison now survives canonical normal
    closure without losing its selected branch.  The family-locus API
    exposes the deck-corrected `FiniteCoverBasedNormalEquiv`, embeds the
    actual `toPair.branchOverSource` as the literal selected branch of that
    normal cover, and proves that the corrected normal equivalence restricts
    on the whole branch to `completeBranchRingEquivOfIdealEq`.  Specializing
    this once gives four normal-cover equivalences from one mapped
    selected-`B` normal cover to the relocated `e`, `a`, `b`, and `c` normal
    covers, with one simultaneous full-branch restriction theorem.  These
    covers still have their separate parameter/source bases.  The remaining
    issue-#16 step is their honest scalar extension into compatible common
    semantic middle/target covers, followed by the selected-graph join and
    item 79's `RightRestriction`.
83. Finite-basis scalar extension now packages the branch-preserving normal
    cover needed by that next step.  Given a finite field `N/F` and a larger
    base `F ≤ E` in one algebraically closed ambient field, the concrete
    compositum has a finite normal closure over `E` and a canonical finite
    normal-cover model.  The original `N` remains literally contained in the
    ambient normal field, and its named map to the canonical cover factors
    through the literal compositum inclusion and the canonical selected
    normal-closure embedding.  Thus rebasing one of the four separately based
    selected-`B` normal covers no longer discards its distinguished branch.
    The next issue-#16 step is to instantiate this construction on the four
    facewise middle covers and transport their based equivalences through the
    common semantic bases.
84. The branch-preserving scalar rebase is now instantiated on all four
    relocated right-family normal covers.  Their complete parameter/source
    fields, including the algebraic `c` face, embed in the one selected
    semantic/reference joint field.  Rebasing over that field and taking a
    supremum gives `fourRelocatedRightRebasedCover`, a literal common finite
    normal codomain.  Four named maps from the one mapped selected-`B`
    complete branch enter this cover through the full family-locus
    equivalences, while four companion maps carry the entire mapped native
    normal cover through the selected-branch-corrected normal equivalences
    before scalar rebase.  The next issue-#16 step is to transport this
    common right cover from the finite selected joint base back to the
    literal semantic common source (using algebraicity of the joint field),
    adjoin it to the selected graph source, and extend the four maps to the
    independent common middle/target charts required by `RightRestriction`.
85. The common four-face right cover has now been transported from the
    finite selected joint base back to the literal semantic common source.
    The chosen algebraic-closure equivalence is proved to preserve that
    smaller source, the transported field is finite by the two-stage
    source/joint/right-cover tower, and its normal closure is joined with
    `selectedGraphSourceCover` to form `selectedGraphRightSourceCover`.
    Consequently one finite normal source now contains both all established
    repeated-coordinate graph coherence and all four selected right-family
    normal covers.  The four established source-chart automorphisms extend
    across the enlargement, the four strict composition triangles are
    available on it, and the selected complete-branch and native-normal
    maps all land in it.  The next issue-#16 step is to turn those four
    right embeddings into independent common middle/target charts whose
    restrictions are the semantic right arrows, then package the resulting
    non-vacuous `RightRestriction` for issue #14.
86. The coefficient-moving source charts needed for that construction are
    now explicit.  Besides the original independent `(s,e,a,b)` tuple, the
    fourth right label admits the independent presentation `(s,sA,a,c)`.
    Reordering these presentations gives four nine-coordinate rational
    sources whose one distinguished rank-two block is literally `e`, `a`,
    `b`, or `c`, while their last coordinate is the same formal curve
    source.  All four tuples are algebraically independent, so equality of
    their zero locus ideals gives canonical ground-field function-field
    equivalences with exact coordinate formulas.  The `e`-ordered source is
    proved to be the existing semantic common source itself; hence the
    resulting maps are genuine semilinear base changes that move the
    coefficient presentation, not deck transformations linear over the old
    source.  The next issue-#16 step is to lift these three base equivalences
    to compatible finite normal source covers and use their distinguished
    `e/a/b/c` coordinate formulas to choose independent common middle and
    target charts with the required normalized right restrictions.
87. The `a`- and `b`-ordered source presentations have now been closed back
    into the literal semantic common source.  They are permutations of the
    original nine displayed generators, so their intermediate fields are
    proved equal to the `e` source and the two coordinatewise equivalences
    become ground-field automorphisms of that one source.  Both
    automorphisms retain exact same-position formulas on named semantic
    source coordinates.  Their chosen algebraic-closure lifts now transport
    `selectedGraphRightSourceCover` to finite normal `a` and `b` source
    covers, and the restricted finite-cover equivalences have exact
    coordinate formulas.  The remaining source-level case is deliberately
    different: the independent `(s,sA,a,c)` field is not identified with the
    original ambient source by a permutation.  It must be joined through the
    selected semantic/reference finite field and normalized over a compatible
    common base before the middle/target charts and `RightRestriction` are
    assembled.
88. The genuine algebraic-output source has now been lifted without making
    that false identification.  Composing the four interalgebraicity faces
    gives the explicit closure equality
    `racl(s,e,a,b) = racl(s,sA,a,c)`; after embedding and adjoining the
    common formal curve coordinate, the two concrete nine-coordinate source
    presentations still have equal relative algebraic closures.  The exact
    `e→c` source equivalence consequently lifts to algebraic closures, maps
    `selectedGraphRightSourceCover` to a finite normal cover over the literal
    `c` source, and retains its same-position coordinate formula on the
    restricted finite cover.  For the compatibility step the two embedded
    sources are retained in the literal compositum
    `rightSourceJointField = S ⊔ Sc`; both inclusions are named, and the
    compositum is proved finite over both `S` and `Sc`.  The next issue-#16
    step is to normalize the selected graph covers over this joint source,
    select the common semilinear middle/target charts, and prove their four
    whole-field normalized coefficient restrictions before constructing
    `RightRestriction`.
89. The four semilinear source covers now have one honest finite normal
    codomain over that joint source.  A reusable finite-base rebase takes a
    chosen algebraic-closure equivalence extending an embedding `E → E'`,
    adjoins the transported values of a finite basis, normalizes over `E'`,
    and retains a selected map from the entire original cover with an exact
    base-element formula.  Applying it to the inclusions `S → S ⊔ Sc` and
    `Sc → S ⊔ Sc` rebases the `e`, `a`, `b`, and genuine `c` selected graph
    covers; their supremum is `fourSelectedGraphJointCover`.  Four named maps
    from the original selected graph/right source enter this one codomain,
    and all nine displayed coordinates land exactly on their same-position
    `e/a/b/c` coordinates through the appropriate literal inclusion in the
    joint base.  The remaining issue-#16 work is no longer a base/codomain
    compatibility problem: extend/select these four embeddings as compatible
    common middle/target equivalences, prove the repeated-arrow equations and
    whole intrinsic coefficient restrictions, and package the resulting
    non-vacuous `RightRestriction`.
90. The four selected embeddings into `fourSelectedGraphJointCover` now
    agree with their coefficient-moving base maps on the entire semantic
    source field, not only on its nine displayed generators.  Twisting the
    source algebra structure by the `a` and `b` automorphisms, and by the
    genuine `S ≃ Sc` chart for `c`, preserves finiteness of the joint source.
    Since the joint cover is finite over that source, each selected embedding
    makes its target algebraic over the original selected graph/right source.
    A reusable `EmbeddingClosureEquiv` API extends such an embedding to an
    equivalence of algebraic closures while retaining its exact restriction;
    all four `e/a/b/c` extensions are instantiated.  These closure
    equivalences are comparison data, not finite-cover charts themselves.
    The next step must use them to construct a finite common chart stable
    under the necessary comparisons, then prove the repeated arrows and the
    whole intrinsic coefficient-field `RightRestriction` on that chart.
91. The semilinear source charts now restrict to the whole intrinsic
    selected-`B` germ coefficient field before any finite-cover descent.  The
    relocated `e`, `a`, and `b` parameter fields are included literally in
    the semantic common source, while the relocated algebraic-output `c`
    parameter field is included in its genuine independent source.  Composing
    the intrinsic germ map with those inclusions gives four named whole-field
    embeddings.  The common-source `a` and `b` automorphisms, and the genuine
    `e→c` source equivalence, carry the `e` embedding exactly to the `a`, `b`,
    and `c` embeddings.  Thus the required coefficient square is no longer a
    generator-level or gauge-trivial statement.  It remains to close these
    source identities under a finite stable common chart, prove the repeated
    middle/target-arrow equations there, and expose the resulting non-vacuous
    four-arrow `RightRestriction` required by issues #16 and #14.
92. The four chosen algebraic-closure comparisons now restrict to honest
    finite charts with one literal codomain.  A reusable pullback construction
    takes the inverse image of any target intermediate field under an
    embedding-preserving closure equivalence, restricts the equivalence to
    that inverse image, and proves finiteness after a finite embedded base
    change.  Pulling back the base field of `fourSelectedGraphJointCover`
    along the `e/a/b/c` extensions gives four finite source fields, each
    finite over `selectedGraphRightSourceCover`, and four field equivalences
    onto the same joint cover.  On the entire old source cover each chart is
    exactly its originally selected embedding; on the whole intrinsic germ
    field the four charts give the normalized `e`, `a`, `b`, and genuine `c`
    target maps.  Thus the comparison data are no longer merely equivalences
    of infinite algebraic closures.  It remains to transport the four strict
    composition triangles to these finite pullback sources, choose compatible
    common middle and target charts, prove the repeated `s/sA/u/uB` equations,
    and package the resulting non-vacuous `RightRestriction`.
93. Strict semantic composition now extends across those four finite
    pullback sources without an unsupported normality change of base.  A
    generic source-extension construction lifts the left and right arrows of
    any literal `CompositionTriangle` to algebraic closures, defines the new
    direct arrow as their composite, and restricts all three arrows to the
    transported intermediate fields.  The enlarged arrows recover the old
    left, right, and direct equivalences on the entire original fields.
    Instantiating it gives strict finite `s·e=u`, `sA·a=u`, `s·b=uB`, and
    `sA·c=uB` triangles on the four semilinear pullback fields, while their
    source charts still restrict to the selected whole-source `e/a/b/c`
    embeddings into the literal joint cover.  It remains to select the
    independent common middle and target charts that identify the repeated
    `s/sA/u/uB` branches and whose four right arrows have the whole intrinsic
    germ restrictions required by `RightRestriction`.
94. The four selected complete right branches now enter the middle and target
    fields of those finite extended triangles with exact whole-field
    commuting squares.  Generically, the old middle and target fields embed
    literally into a source-extended triangle, and its new right equivalence
    composed with the old-middle embedding equals the old right equivalence
    followed by the old-target embedding.  Applying this to the selected
    `e/a/b/c` complete branches gives named middle maps, named target maps,
    and four exact restriction theorems.  This is stronger than a coordinate
    or curve-generator calculation and fixes the concrete anchors that the
    remaining common middle/target equivalences must preserve.  Issue #16 is
    still open: those four middle embeddings must be identified with one
    common intrinsic embedding, the repeated `s/sA/u/uB` arrows must be made
    literal, and the normalized whole-germ target restrictions must be
    packaged as the non-vacuous `RightRestriction`.
95. The semilinear source charts are now reoriented in the direction needed
    by a faithful common middle.  The forward `e→a`, `e→b`, and genuine
    `e→c` finite-cover equivalences carry the whole intrinsic `e` germ to the
    corresponding intrinsic target germ.  Conjugating the three semantic
    triangles onto those transported source covers and then using the inverse
    equivalences as their common-source charts sends the entire `a`, `b`, and
    `c` germs back to the one literal `e` embedding in
    `selectedGraphRightSourceCover`; the `e` chart is the identity.  A single
    four-way theorem records these ring-hom equalities.  This orientation is
    essential: the old forward charts sent the same `e` source to four
    distinct images and therefore could not be followed by one injective
    repeated-left chart.  The next step is to extend these inverse-oriented
    triangles to compatible finite common middle/target covers, preserve the
    complete-branch squares of item 94, and construct `RightRestriction`.
96. A reusable source-square constructor now isolates the exact data needed
    for the final non-vacuous restriction.  Two coefficient embeddings in the
    common source chart—one for the repeated `s` faces and one for the repeated
    `sA` faces—must have one literal image in the common middle chart, while
    the repeated `u` and `uB` composites must carry them to the four prescribed
    target embeddings.  The four semantic face identities then produce a
    `FourArrowDiagram.RightRestriction` automatically.  Thus the remaining
    issue-#16 work is reduced to six named whole-field source squares, with no
    possibility of closing the obligation by a source-induced identity gauge.
97. The four inverse-oriented semantic triangles now extend across finite
    pullbacks of one prescribed common source.  The `e` pullback supplies the
    literal finite common field; the `a`, `b`, and genuine `c` sources are
    pulled back through their inverse semilinear charts before the strict
    triangles are extended.  The resulting four restricted charts have that
    one literal codomain and carry the entire intrinsic germ to one shared
    embedding there.  Thus the source side of the final reference diagram is
    finite and literally common, rather than only semilinearly identified.
    Issue #16 is now confined to compatible common middle/target charts and
    the six whole-field squares required by item 96.
98. The whole selected complete right branches now survive those
    inverse-oriented common-source extensions.  For each `e/a/b/c` face, the
    old middle branch is included in the new middle field, its image is named
    in the new target field, and the extended right equivalence satisfies an
    exact ring-hom square on the entire branch.  These four branch anchors are
    the preservation conditions for the independent common middle and target
    charts; issue #16 still requires constructing those charts, identifying
    the repeated `s/sA/u/uB` arrows, and discharging the six source squares.
99. The based `e` face now exposes a complete intrinsic-germ restriction
    through its inverse-oriented common-source triangle.  The relocated `e`
    parameter field is included in the common eight-input coefficient field,
    and the resulting germ maps in the finite source, selected middle branch,
    and selected target are named explicitly.  Exact left, right, and strict
    direct squares are proved on the whole intrinsic field.  A reusable
    `CompositionTriangle.direct_comp_of_left_right` derives the direct square
    from the adjacent two without unfolding deeply nested cover types.  This
    supplies the prototype for the remaining `a/b/c` face squares; those must
    retain inverse semilinear source charts before repeated `s/sA/u/uB`
    middle/target maps can be identified.
100. The inverse-oriented `a`, direct `b`, and inverse-oriented `c` faces now
    carry the same complete intrinsic-germ restriction package as the based
    `e` face.  In each case the source chart returns the intrinsic germ to the
    selected `e` source embedding, the finite left arrow sends it to a named
    common-coefficient anchor in that face's middle cover, and source
    extension preserves exact left, right, and strict direct squares.  A
    reusable finite-cover lemma records that every left arrow fixes an
    arbitrary map into its coefficient field.  The four middle anchors are
    still separately typed and are intentionally not equated with the four
    preserved selected branches: compatible common middle/target charts must
    identify both embeddings, after which the repeated `s/sA/u/uB` maps and
    the non-vacuous `RightRestriction` can be assembled.
101. The common-coefficient middle and target anchors on all four faces now
    factor through the preserved complete right branches on the entire
    intrinsic germ.  For `a/b/c`, named maps first include the based germ in
    each selected semantic right branch; the selected-branch embedding into
    the old middle cover is proved equal to the common-coefficient anchor,
    and the equality is transported pointwise to the extended middle and
    target fields.  The `e` factorization is definitional and is recorded by
    the same interface.  Pointwise extended statements are intentional: an
    equivalent ring-hom equality makes Lean normalize the full nested-cover
    types and exceeded the 30 GiB memory safety floor.  The remaining
    issue-#16 step is therefore purely cross-face: construct common middle
    and target charts retaining these now-unified anchors, identify repeated
    `s/sA/u/uB`, and instantiate the non-vacuous `RightRestriction`.
102. The literal finite common source now lies in one finite stable source
    on which all four selected graph/right charts act.  Concretely, its
    normal closure over the semantic common source is formed inside the
    algebraic closure of the selected graph/right source.  It is proved
    finite and normal over the semantic source, and the old graph/right
    source and finite common source both embed literally in it.  Each of the
    four generally nontrivial selected source automorphisms extends across
    this normal field with an exact restriction theorem on the entire old
    source.  The next issue-#16 increment is to extend/pull back the four
    inverse-oriented triangles to this stable field, use these four extended
    automorphisms as their source charts, and then construct compatible
    common middle and target charts.
103. The four inverse-oriented semantic triangles now extend over the stable
    source with one literal source-chart codomain and nontrivial selected
    graph actions.  The `e` triangle extends directly; the `a/b/c` triangles
    extend over the pullbacks of the stable source through their inverse
    semilinear charts.  Each restricted pullback chart is postcomposed with
    the corresponding stable selected-graph automorphism.  A generic
    pullback restriction lemma proves that this composite acts on any
    whole-field source embedding by the prescribed old chart followed by
    the stable correction.  Specializing it gives exact intrinsic-germ
    restrictions for all four faces, including genuine algebraic-output
    `c`.  The remaining issue-#16 construction is now the independent common
    middle and target chart layer: choose its repeated `s/sA/u/uB` arrows,
    prove the four semantic right restrictions, and instantiate the
    non-vacuous `RightRestriction`.
104. The source embeddings are now grouped correctly for that final
    restriction.  A reusable closure-comparison constructor precomposes an
    embedding-preserving algebraic-closure equivalence by a source field
    equivalence while retaining the exact composite embedding.  Applying it
    to the selected joint cover gives four finite pullback sources and four
    strict extended triangles with one literal chart codomain.  On the whole
    intrinsic germ, the `e/b` charts restrict to one selected source
    embedding and the `a/c` charts restrict to a second selected source
    embedding, exactly matching the two repeated left labels.  Finiteness of
    all four pullbacks is proved, including transport through the three
    nontrivial source equivalences.  Pointwise restriction statements are
    intentional because normalization of the equivalent deeply nested
    ring-hom equality crossed the 30 GiB memory safety floor.  Issue #16 now
    requires the analogous grouped common middle and target charts, followed
    by the four semantic right squares and the non-vacuous
    `RightRestriction` package.
105. The grouped finite triangles now retain the full intrinsic restriction
    package.  For each `e/a/b/c` face, the old selected-branch middle anchor
    and its target image are included into the new source extension, and
    exact whole-germ squares are proved for the left, right, and strict
    direct arrows.  Consequently the future cross-face middle and target
    charts have explicit preservation obligations on all four faces; they
    cannot satisfy coherence by discarding the chosen normalized branch
    embeddings.  The remaining issue-#16 construction is to place those
    four preserved middle anchors in one common middle chart, place their
    four target images in one common target chart, identify the repeated
    `s/sA/u/uB` maps, and instantiate the non-vacuous `RightRestriction`.
106. The entire selected `e/a/b/c` right branches now survive in the grouped
    middle and target fields, not just their intrinsic germ points.  Each
    grouped right arrow forms an exact ring-hom square with its complete
    selected branch embedding, and pointwise factorization theorems identify
    the intrinsic middle and target anchors of item 105 with the restrictions
    of those branch embeddings.  This includes the genuine algebraic-output
    `c` branch.  The remaining issue-#16 construction is cross-face only:
    build common middle and target charts preserving these four concrete
    normalized branches, identify the repeated `s/sA/u/uB` arrows, and use
    the six source/direct squares to construct `RightRestriction`.
107. The build graph is reorganized for the remaining issue-#16 work.  The
    four grouped selected-branch families now live in independent `E/A/B/C`
    sibling modules behind a thin compatibility aggregator, and their large
    expanded coherence equalities have named proposition interfaces so
    downstream artifacts stay compact.  The same declarations serialize in
    parallel in roughly 140 seconds instead of the former 1,592-second
    monolithic checkpoint.  Each Verso chapter now imports only the layers
    and stable compatibility endpoints that it documents rather than the
    whole-project umbrella.  A representative new module after the grouped
    checkpoint therefore completes the default build in roughly ten seconds
    without rebuilding any chapter.  New four-face constructions should
    retain this sibling-plus-thin-aggregator layout, and the configurations
    chapter should remain pinned to the stable grouped checkpoint until it
    is intentionally extended.
108. The remaining cross-face obligation is now isolated as the finite
    `GroupedCommonChartData` interface.  It asks for one common middle field,
    one common target field, the repeated `s/sA/u/uB` equivalences, the five
    intrinsic coefficient embeddings, and exactly the six whole-germ squares
    relating them to the two grouped source embeddings.  Any inhabitant
    canonically produces the non-induced four-triangle reference, its
    faithful four-arrow diagram, and the non-vacuous intrinsic
    `RightRestriction`; the resulting `c = b e⁻¹ a` factorization is exposed
    directly.  This keeps the next construction focused on common-chart
    existence while preventing a source-induced gauge choice from satisfying
    the semantic endpoint vacuously.
109. The repeated-`s` common-middle alignment now survives both finite source
    enlargements.  Its established deck transformation on the comparison
    cover extends first to the selected graph source and then to the
    right-enlarged selected graph source, with an exact restriction theorem
    at each boundary.  The restrictions intentionally remain two composable
    lemmas: forcing Lean to normalize both nested inclusions in one theorem is
    a slow elaboration boundary and adds no mathematical content.  Construct
    the repeated-`sA` sibling in the same way, then transport the resulting
    source-cover alignments through the joint-base rebase into a finite stable
    common middle chart.
110. Both coherent repeated-`sA` total-anchor corrections now survive the same
    two finite source enlargements, again with exact restriction equations at
    each boundary.  They live in a sibling leaf to the repeated-`s` lift and
    are collected only by a thin grouped-middle compatibility module, so the
    three normal-cover extension families serialize in parallel.  The next
    mathematical boundary is no longer branch alignment over the literal
    common source: it is transporting these source-linear alignments through
    the semilinear joint-base rebase and extending them to one finite stable
    middle cover.
111. The semilinear joint-base obstruction is now handled by a finite stable
    cover with the correct base of normality.  The complete four-face joint
    cover is finite over the original semantic source; its normal closure over
    that source is finite, contains the joint cover, and is normal over the
    field fixed by all established repeated-arrow alignments.  The whole
    selected graph/right source embeds into this cover through the selected
    `e` leg, and every semantic-source-linear deck transformation extends with
    an exact whole-cover restriction.  In particular, the repeated-`s` and
    both coherent repeated-`sA` anchor corrections now act on this one stable
    finite cover.  The stable cover, generic extension mechanism, and `s`/`sA`
    families remain parallel leaves behind a thin compatibility module.  Next
    pull all four grouped triangles back to this stable source and orient the
    three corrections into the two common left-arrow charts.
112. All four grouped triangles now live on finite pullback sources charted to
    the one stable grouped cover.  The `e/a/b/c` faces are independent sibling
    leaves, each with its exact intrinsic germ restriction; after charting,
    `e,b` share the literal stable `groupedStableSourceS` embedding and `a,c`
    share `groupedStableSourceSA`.  The pullback leaves take roughly three to
    four seconds apiece to elaborate and serialize independently behind a
    thin compatibility module.  The next step is to orient the stable
    repeated-`s` and two `sA` anchor automorphisms into common left charts and
    prove their two common-middle coefficient squares.
113. The coefficient-moving `e→a` automorphism of the whole semantic source
    is now proved involutive, not merely on the distinguished rank-two block.
    The proof uses the literal nine-coordinate generating presentation and
    checks the `e/a` block transposition coordinate by coordinate; this avoids
    an expensive definitional-equality search through the nested source-field
    presentation.  Next use this finite-order base chart to form the
    two-orbit finite normal cover stable under its algebraic-closure lift, then
    restrict the lift to the common left chart and combine it with the stable
    repeated-`s` and `sA` corrections.
114. The `e→a` lift now acts on one finite normal grouped source.  The previous
    stable cover is transported from the algebraic closure of the joint cover
    to the canonical algebraic closure of the semantic source, then enlarged
    by the two-element orbit of the lifted base chart.  A reusable
    `FiniteNormalOrbit` layer proves that the possible non-functorial defect
    in the square of the chosen lift is source-linear and hence stabilizes
    every finite normal cover.  The resulting restricted ring equivalence has
    its exact semilinearity square, contains the whole joint cover, and is
    finite over it.  The repeated-`s` and both coherent repeated-`sA`
    corrections have also been extended to this final orbit cover with exact
    restriction to the preceding stable source.  Next extend the four grouped
    triangles across finite pullbacks charted to this orbit cover, keeping the
    four constructions in independent sibling leaves.
115. The `e`, `a`, `b`, and `c` grouped triangles now extend across four
    finite pullback sources charted to the literal `e/a`-stable orbit cover.
    Each leaf constructs its explicit embedding through the old joint-source
    chart, transports finiteness from the joint cover, extends that embedding
    to algebraic closures, and proves the exact intrinsic restriction to
    `groupedStableAOrbitSourceS` or `groupedStableAOrbitSourceSA`.  The four
    leaves remain independent behind thin triangle and compatibility
    aggregators.  Next orient their extended left arrows with the stable
    repeated-`s`, repeated-`sA`, and semilinear `e→a` charts to obtain one
    common middle field and its two exact coefficient squares.
116. The final orbit source now carries two explicitly oriented candidate
    left maps with one literal ambient codomain.  The repeated-`s` map
    uses the exact whole-branch `e/b` correction followed by the restricted
    finite `e→a` semilinear chart; the repeated-`sA` map is the relative
    correction between the two selected `sA` branches through their coherent
    total-field anchor.  The semilinear chart is proved on the entire
    intrinsic germ field to carry `groupedStableAOrbitSourceS` to
    `groupedStableAOrbitSourceSA`, while source-linearity proves that every
    branch correction fixes the applicable source embedding.  Consequently
    both candidate maps have the same exact whole-germ coefficient
    restriction.  This coefficient-square leaf and the four triangle leaves
    elaborate independently behind the thin final compatibility module.  It
    is not yet a common middle chart for the four selected branches: an
    injective common postcomposition cannot make distinct face embeddings
    equal.  Next construct face-specific source charts on a finite compositum
    which align each selected left and direct branch simultaneously; only then
    use the candidate maps to obtain common middle and target charts and prove
    the four normalized `e/a/b/c` restrictions.
117. The simultaneous-alignment domain is now isolated explicitly.  A
    reusable `selectedWholeFaceField` adjoins a composition face's middle and
    target coordinates to its literal source; both the complete selected left
    branch and the complete selected direct branch are proved literal
    subextensions of this one finite field.  The four semantic faces now have
    named whole-face extensions inside the common ten-coordinate
    `selectedSemanticBranchExtension`; the genuine `c` field additionally
    retains both algebraic output parameters.  All four are finite over the
    common semantic source and map to `selectedGraphSourceCover` by restriction
    of the single coherent ten-coordinate embedding.  Thus the next
    normal-branch alignment can be selected on one whole-face domain per face,
    rather than composing unrelated left-only and direct-only corrections.
    This is the precise mechanism needed to make each future source chart
    preserve both branches simultaneously.

**Historical next step (superseded by the audit, #19):** turn the selected relational multiplication and inverse
into dominant rational maps on one common positive-dimensional normalized
parameter cover.  Items 25--27 put the four normalized based projections on
one literal source and target and identify every generic-point map with an
explicit field embedding.  Item 28 provides the faithful semantic
field-equivalence target and one strict selected composition triangle.
Items 29--40 give four strict finite-normal-cover curve triangles, the exact
semantic target for aligning them, and one formal curve source shared by all
four embedded loci over one eight-input coefficient field; item 35 also
places all four actions on one literal finite normal source compositum, and
items 36--54 supply selected-branch-preserving comparisons, equality of the
curve relations, and source-level re-elaboration integrity after the honest
independent scalar extensions.  The
repeated `s` relation already lives over the literal common input field, and
the repeated `sA`, direct `u`, and direct `uB` comparisons have now been
transported explicitly into that base.  Each alternative comparison has a
finite pairwise normal source extension containing both literal branches;
all three comparison covers have been rebased and adjoined to the common
source cover, and their actual selected branches have been aligned there.
The four direct-anchor corrections now provide the coefficient/source
charts, the induced middle and target charts have exact selected-branch
restriction formulas, and the resulting common-cover reference already
carries literal semantic cancellation.  The selected right `e`, `a`, `b`,
and `c` branches have also been embedded in the transported middle covers;
their charted endpoints satisfy the original canonical equations, while all
middle and target charts fix the common coefficient field.  The original
normalized reference cover has now been transported into the same canonical
source algebraic closure and joined with the semantic branch cover; the four
explicit `toReference` field maps therefore have the same literal codomain
as the semantic action, their eight-input coefficient square commutes, and
their restrictions to the intrinsic `B` germ coefficient field are the
canonical transports to the four displayed parameter fields.  Those
transports are now proved to be exactly the coefficients of the four
relocated right-branch curve equations.  The four complete selected edges
have also been scalar-extended to the common sixteen-coordinate field and
embedded, coordinate-for-coordinate, into the common formal-source cover.
The promoted reference embeddings now agree there with the literal
complete-edge inclusions on every element of all four selected nonnormal
`B/T` scalar extensions, and their intrinsic-germ restrictions are the
named coefficient transports.  Their action on the entire selected
normalized function field is also exactly the based ambient normal-cover
transport.  The complete semantic curve-branch maps have now been named in
the same final cover with exact charted-arrow formulas.  The intrinsic germ
maps into all four relocated parameter fields are also defined on the whole
field, are characterized by canonical curve coefficients, and factor the
the four normalized reference restrictions.  Those complete-branch
embeddings and their whole intrinsic-field reference identifications are now
established, and the four semantic branches factor through one coherent
whole-face anchor.  The mapped selected `B` family is also now one common
complete middle branch whose four full branch equivalences recover the
relocated `e/a/b/c` intrinsic maps exactly.  Its one canonical normal cover
now has four selected-branch-preserving equivalences to the relocated normal
covers.  Scalar-extend these separately based covers into compatible common
semantic middle and target covers, join them to the selected graph source,
construct the resulting `RightRestriction`, and use its faithful
cancellation theorem to prove that `toReferenceC` factors through
`toReferenceE`, `toReferenceA`, and `toReferenceB`.  This is the precise
auxiliary-`s` independence statement: the factorization must descend to the
intrinsic two-input germ chart, not merely hold on the eight-input relational
source.  Then extract multiplication and inverse on that single chart with
strict rational identities.
Use the resulting maps to construct the translation-indexed Weil atlas and
glue its multiplication, unit, and inverse with the strict field/rational
cocycle.  The resulting group scheme is automatically separated by item 16;
then extract a finite subatlas and package it in the scheme-level
algebraic-group target.  After that, identify the already constructed
categorical rank-one normal kernel with the connected component of its
scheme-theoretic kernel, apply the completed affine-action classification,
and finish affine-grid extraction (8.5) and Q correctness.

Do not substitute the finite deck group for the parameter group.  The deck
group only records the vertical ambiguity of chosen lifts; the parameter
base still has two independent rank-two inputs.

## Historical handoff: P6 automorphism rigidity (completed)

**Statement to prove (core)**: for genus `g ≥ 2`, every k-derivation
`D : F → F` (k-linear + Leibniz `D(ab) = aD(b) + bD(a)`, `D` kills k)
that is *regular everywhere* (`∀ P, D(O_P) ⊆ O_P`) is zero. Then a
`g = 1` variant: a regular derivation vanishing at one place (image in
the maximal ideal there) is zero. These feed the blueprint's argument
that no positive-dimensional connected automorphism group exists for
`g ≥ 1` (blueprint §8, around lines 1430–1470 of blueprint.tex), which
combines with the genus-0 endgame (`P⁴`-checkpoint, Möbius bricks) in
P7.

**The settled design (fully elementary — no chain rule, no
separability theory, no completions).** All residue ingredients are
already formalized except items (a)–(e) below.

1. Fix a derivation `D`, regular everywhere, `D ≠ 0`; pick `u₀` with
   `Du₀ ≠ 0`. Fix any place `P₀`, let `π := P₀.pi`.
2. `t := π + c • u₀` for a good `c ∈ k`: since `g ↦ ω_g :=
   residueFunctional g` is k-linear in g (residue bilinearity in the
   second slot — the linear-map packaging of `g ↦ ω_g` is a small
   missing lemma) and `ω_π ≠ 0`, at most one `c` kills
   `ω_t = ω_π + c·ω_{u₀}`; since k is infinite, choose `c ≠ 0` with
   `ω_t ≠ 0`. Then `Dt = c·Du₀ ≠ 0`.
3. `ω_t` is a nonzero Weil differential; let `W_t` be its divisor
   (its greatest level — machinery in `Differentials.lean`:
   `exists_isGreatest_level`; the pointwise value `w_P := (W_t) P` is
   characterized by: `ω_t` kills all single-place adeles at `P` of
   order `≥ −w_P`, and there is a single-place adele of order
   `−w_P − 1` not killed — from the one-point step
   `adeleSpace_add_single` and maximality; this "local level"
   extraction is missing lemma (c) below).
4. **Local bound at places where `t ∈ O_P`**: Taylor-expand
   (`Place.exists_taylor`) `t = Σ_{i<n} c_i π_P^i + π_P^n b` with
   `n > w_P + 1`. Single-place evaluation of `ω_t` (missing lemma (b))
   plus bilinearity plus the monomial table give
   `res_P(π^{−i}, t) = (i:k)·c_i` for `i < n` — the tail term dies by
   the *mirror threshold* (missing lemma (a)). Level-vanishing then
   forces `(i:k)·c_i = 0` for all `i ≤ w_P`. Now apply `D` to the
   Taylor expansion using only Leibniz on finite sums:
   `Dt = Σ_i c_i·(i·π^{i−1})·Dπ_P + n π^{n−1} b Dπ_P + π^n Db`
   (note `D(c_i • π^i) = c_i • (i:k)-scaled…`; the terms with
   `i ≤ w_P` vanish because the scalar `(i:k)c_i = 0`); every
   surviving term has `ord_P ≥ w_P` using regularity
   (`ord(Dπ_P) ≥ 0`, `ord(Db) ≥ 0`). Hence `ord_P(Dt) ≥ w_P`.
5. **At poles of `t`** (finitely many): `t⁻¹ ∈ O_P`; from Leibniz on
   `1 = t·t⁻¹`: `Dt = −t²·D(t⁻¹)`; and from the residue Leibniz rule
   the levels of `ω_t` and `ω_{t⁻¹}` at `P` differ by `2·ord_P(t)`
   (`res(f, t) = −res(f·t², t⁻¹)` — derive from `residue_mul_right`
   applied twice, e.g. via `0 = res(f·t, t·t⁻¹·…)`-style
   manipulations). Then the step-4 bound at `t⁻¹` transports to `t`.
   (Missing lemma (d); do the bookkeeping carefully on paper first.)
6. Conclusion: `div(Dt) ≥ W_t` pointwise, i.e. `Dt ∈ L(−W_t)`. Since
   `deg W_t = 2g−2` (proportionality `exists_eq_comp_adeleSMul` +
   level-shift `isGreatest_level_comp` transport the degree from the
   canonical divisor of `exists_canonicalDivisor`; small missing lemma
   (e)), `deg(−W_t) = 2−2g < 0`, so `L(−W_t) = 0`
   (`riemannSpace_eq_bot_of_deg_neg`), so `Dt = 0`, contradicting
   `Dt = c·Du₀ ≠ 0`. ∎

**Missing lemmas, in recommended order:**

(a) **Mirror threshold**: `res_P(f, g) = 0` when `ord f ≥ −m` and
    `ord g ≥ m + 1` (`m : ℕ`). Proof pattern: mirror of
    `residue_eq_zero_of_ord_ge` (same z-iteration nilpotency; now the
    commutator kills `π^m O_P` — for `x` there, `fx ∈ O` and
    `fgx ∈ πO ⊆ O` so both projections fix — lands in `O`, and the
    depth-gain via `ord(fg) ≥ 1` runs the same way; design notes in
    the m3a memory file if available, else re-derive: it is the same
    five-have skeleton: `hδO`, `hsub_ord`, `hfy`, `hstep`, `hrange`,
    `hpow` induction, `hnil`).
    Needed for the Taylor tail `res(π^{−i}, π^n b) = 0` for `n ≥ i+1`:
    apply with `f := π^{−i}` (`ord = −i ≥ −m` with `m := i`) and
    `g := π^n b` (`ord ≥ n ≥ i + 1 = m + 1`). ✓ exactly fits.

(b) **Single-place evaluation**:
    `residueFunctional g (adeleSingle P f) = P.residue f g` — via
    `residueFunctional_eq_sum` with `S := {P}` (other coordinates are
    0, `residue_zero_left`), `Finset.sum_singleton`,
    `adeleSinglePi_apply_self`. Trivial with existing pieces.

(c) **Local level extraction**: package, for a nonzero Weil
    differential `ω` with greatest level `W`
    (`exists_isGreatest_level`), the two facts
    (i) `∀ f, ord_P f ≥ −(W P) → ω (adeleSingle P f) = 0`
    (single-place adeles of bounded order lie in `boundedSubmodule W`;
    memberships are straightforward) and
    (ii) `∃ f, ω (adeleSingle P f) ≠ 0 ∧ ord_P f = −(W P) − 1`
    (maximality: `ω ∉ Ω(W + single P 1)`; use
    `adeleSpace_add_single` to decompose a witness into an `A(W)`
    part, killed, plus a monomial multiple — the monomial
    `adeleMonomial P (−(W P) − 1)` is essentially `adeleSingle P
    (π^{−W P −1})`, compare the two constructions, they agree
    definitionally at the coordinate level).

(d) **Pole-place transport** (step 5 above), and

(e) **Degree of the divisor of any nonzero differential = 2g−2**:
    from `exists_canonicalDivisor`'s `W₀` and proportionality: any
    nonzero `ω = ω₀ ∘ (mult by h)` (`exists_eq_comp_adeleSMul`), and
    `isGreatest_level_comp` says levels shift by `div h`;
    `deg div h = 0` finishes. Check exact statement shapes in
    `Differentials.lean` / `Canonical.lean`.

Then assemble the core theorem, state the `g = 1` variant (same
argument, but the vector field additionally vanishes at the fixed
place, giving `Dt ∈ L(−W_t − P)` of degree `−1 < 0` when `2g−2 = 0`),
and post on #13.

## Remaining project roadmap

- **M4** (#6, #12, #21, #22): repair the extraction target, state and prove
  Lemma 8.4 (action bridge), re-plan the group-chunk step (8.2/8.3) from the
  corrected target, then prove Q, Q′ and J completeness over algebraically
  closed fields.
- **M5** (#7): T1–T3, algebraic-base lattice/point/rank and configuration
  lifts, point-level (1)⇔(2), (4)⇒(3), semantic J assembly and finite-base
  soundness are on main. Conditional four-way packaging names the open
  ACF completeness (3)⇒(2) input, which still needs M4. The old
  arbitrary-field Q/Q′ consequences have concrete Lean refutations over
  characteristic-zero rational function fields in five variables (#25).
- **M6–M8** (#8–#10, #23): Frobenius classes and generic arithmetic (after
  corrected §10–12 operation predicates), ratio-field interpretation, base/point
  recovery, public theorem variants and the functorial quotient formulation.
  The rank-five kernel, two-generic intersection, trdeg transport and compatible
  induced-map converse and supplied-endpoint uniqueness/Frobenius fibre are
  proved. Full functorial definitions and assembly remain open.
- **Book**: keep each chapter synchronized with the library and free of
  overclaims. Verso requires docstrings on every referenced declaration *and
  its structure fields*.

## Lean gotchas (hard-won; read before writing proofs)

- (v4.34.1) `MvPolynomial.coeff` is gone: write `p.coeff m`. The lemmas
  `MvPolynomial.coeff_add` and `MvPolynomial.coeff_zero` are protected.
- (v4.34.1) `rw` and `simp` unify only up to instance transparency. A
  rewrite through a `def` such as `Point` or a local `Field` instance can
  fail; use `exact`/`refine` with the lemma, which checks definitional
  equality.
- (v4.34.1) `Function.Injective.encard_range` is now an equality, and
  `TrivSqZeroExt` pair literals no longer simp-normalize their `fst`/`snd`.
- Check single files with the toolchain `lean` and the lakefile options
  (`-DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false`); without them,
  instance search behaves differently.
- Bare `LinearMap.id - P.conjProj g` (or any operator-subtraction)
  *applied to an argument* gives "Function expected ?m" — type-ascribe
  `(… : F →ₗ[k] F)` at every application site.
- `set`-bound operators don't pattern-match in *freshly created*
  goals; unfold the *hypotheses* (`rw [hdef] at h`) rather than trying
  to fold the goal.
- Dot-notation on type-ascribed terms fails
  (`(x : Divisor k F).deg` looks up `Finsupp.deg`) — use qualified
  names.
- `rw [h] at hyp` where `h : D P = 0` splits `ord`-atoms containing
  `(D P).toNat` — omega understands `toNat` natively, so don't rewrite.
- `Finset.sum_eq_single` as a rewrite mis-infers the function from
  side-condition lambdas (defeq-not-syntactic) — state it as a typed
  `have` first.
- `congr 1` on `zpow`-exponent goals is unreliable (`a + -b` is defeq
  to `a - b` in ℤ, so congr may close everything and orphan the next
  tactic); use explicit exponent `have`s + `rw`.
- `← zpow_one x` rewrites `x` inside *other* zpow bases; use
  `zpow_add_one₀` directly.
- `linarith` fails over an unordered field — use
  `linear_combination`.
- `rw [map_zero]` rewrites *all* instances of the instantiated
  pattern at once; count remaining occurrences.
- Membership goals of the form `x ∈ ↑S` (set-coe of a submodule) need
  `change P.val.valuation x ≤ 1`-style, not `rw [mem_iff]`.
- `push Not` normalizes `¬(1 < v)` directly to `v ≤ 1`.
- `omega` handles `Int.toNat`, `min`/`max`; give it product-atoms via
  `have`-equations (`ord_mul` etc.) first.
- Coordinate goals under `Subtype.mk` need `change` before `rw
  [map_zero]` (motive failures otherwise).
- `Submodule.finiteDimensional_of_le`'s named argument is `S₂`.
- `Submodule.map_comap_subtype` yields `p ⊓ q` in that order.
- When python-rewriting file spans, anchor on unique full lines —
  substring anchors have silently eaten declarations before.
- `Submonoid.closure_induction` uses `| mem | one | mul` cases.
- `pow_succ'` (not `pow_succ`) for `C^{n+1} x = C (C^n x)`.
- Verso `{docstring X}` requires docstrings on structure fields too.

## Session mechanics for an agent

Each work session: (1) check the issues on adamtopaz/acl_geom for Adam's
steering and `chit inbox` for the peer agent; (2) agree on file ownership;
(3) do one small verifiable increment; (4) validate with a full `lake build`
and `lake exe book` (one build family at a time in a shared checkout);
(5) commit and push; (6) leave a progress comment on the relevant issue.
CI runs on push (build + Pages deploy). Until a fresh run on the current
`main` succeeds, local validation is the authoritative evidence.

## Lean/Mathlib 4.34.1 compatibility checkpoint (#20)

The direct pins are Lean/Mathlib v4.34.1 and Verso v4.34.0. Mathlib's resolved
revision is recorded in `lake-manifest.json`; Verso v4.34.0 is the compatible
stable tag for this Lean minor version. These were the latest stable releases
verified against the upstream release pages on 2026-10-06/07.

Reproduce with the toolchain's available C compiler on `PATH`, then run:

```sh
LEAN_NUM_THREADS=2 lake exe cache get
LEAN_NUM_THREADS=2 lake build
LEAN_NUM_THREADS=2 lake exe book
```

The host's previous compiler wrapper referenced a removed Nix path. For the
migration measurements, GCC was supplied from
`/nix/store/79mr0jw3qccq7hhf1hh62knxd88dwazc-gcc-wrapper-15.3.0/bin` on `PATH`.
That path is a local workaround; another machine should use its installed
compiler. These migration measurements used a monitor sampling `MemAvailable`
and process-family RSS every two seconds, interrupting only its own family below
30 GiB available. The current policy is the 20 GB family cap described above.

The compatibility changes update Mathlib lattice/rank, polynomial and
category APIs, replace deprecated declarations, and expose scalar inclusions
through the correct restricted intermediate fields. The largest repair is
`ChunkCurveCommonSource`: canonical closure transport is now over the native
source field before restricting the whole-total map to each preserved branch.
This retains a single map on the complete source and its coefficient action,
rather than constructing unrelated branch maps. The book documents the new
presentation. Abstract coefficient/composition lemmas are reused downstream.
Commented local elaboration settings unfold transparent field aliases; the
Lean kernel still checks all resulting terms.

The final transport modules exposed a separate export bottleneck: Lean's optional
symbol-frequency index traverses their deeply nested theorem signatures without
a heartbeat bound. The original 115-line orbit-triangle E module checked in 6.03
seconds without artifact emission but exceeded a 180-second compiled-output probe.
An extension-by-extension diagnostic isolated `symbolFrequency` preprocessing.
The documented `nameDenyListExt` entry excludes the exact frozen technical
namespace `PsiCurveFourArrowCommonSourceRealizations` from the optional premise
selectors and frequency statistics. It preserves every declaration, proof term,
kernel check, direct reference, simp/instance attribute and book docstring. The
private emitted-module probe then passed in 6.03 seconds, with all eight public
declarations using standard axioms. The full shared build and book also passed,
as recorded below; this is not a clean-build speed claim.

Validation on 2026-10-07 (two Lean threads):

| check | elapsed | sampled peak family RSS | minimum available RAM |
|---|---:|---:|---:|
| Full default `lake build`, pass 16 | 876.62 s | 12.46 GiB | 35.71 GiB |
| `lake exe book` | 12.08 s | 1.55 GiB | 40.67 GiB |

Both exited successfully, with no memory safety stop. The full pass rebuilt the
common-source family after the metadata entry, using dependency artifacts prepared
by earlier migration passes; it is not a clean-build measurement. Book generation
writes the multi-page HTML to `_out/html-multi`.

The compiled root axiom check covers seven representative declarations, including
all three native raw roundtrips, whole-source branch composition, soundness and
j-rigidity. Each uses only `propext`, `Classical.choice` and `Quot.sound`. Earlier
focused axiom checks cover the 68 native-source declarations, 428 reference-bridge
declarations, 34 middle-field declarations and the alignment repair. A lexical
scan of all 196 library/root files finds no proof placeholders or project axioms.
`git diff --check` passes, and the final logs have no deprecation warnings in the
changed files. Existing style suggestions and warnings in untouched files remain.

The upgrade does not close the performance gate #18. The final pass measured
`ChunkCurveCommonSource` at 209 seconds, `ChunkCurveReferenceBridge` at 129 seconds,
the four common-middle modules at 5.3–6.1 seconds, grouped restriction at 10 seconds,
and orbit-triangle E at 4.4 seconds. Earlier migration passes took 596/304 seconds
for CommonSource/ReferenceBridge, hundreds of seconds for small middle modules,
and 1439 seconds for grouped restriction; the original orbit-triangle compiled
probe exceeded its 180-second cap. These observations separate the optional export
bottleneck from kernel work; they are not controlled clean-build speed ratios.
Focused dependency cuts and the remaining native instance-path/kernel costs are
still tracked under #18.

## Audit cleanup checkpoint (#19/#22/#23/#24/#25)

This checkpoint builds on the pushed v4.34.1 migration `8a54b54` and retains
all existing proved mathematics. The 117-step M4a record remains frozen.

- `Geometry/Representatives` proves the finite representative calculus
  (12 public theorems), consumed by the arithmetic refutations. The other
  foundational carryovers in #24 remain open or privately reviewed.
- `Config/AffineGrid` retains the literal-target refutation and constrains
  only three joins and fifteen points in the corrected target. Extraction
  and `QCompletenessACF` were subsequently refuted by an actual degenerate witness (#27).
  Guarded extraction/completeness require I≠D and I≠P and remain open; current
  conditional correctness uses the guarded input over algebraically closed fields.
- `Counterexamples/GenericArithmetic` records the literal JAdd/JMul and
  full-class RatioEq refutations (26 public theorems), with every witness's
  geometric class membership proved. Corrected class operations, totalization
  and ratio decoding remain open.
- `Interpretation/FrobLinkIncidence` gives the geometric concurrence
  reduction (five public theorems) without configuration completeness.
  Direct-link semantics and the two-hop bridge are separate obligations.
- The source retains the original wording's provenance, withdraws the false
  arbitrary-field Q/Q′ consequences and marks their mathematical
  counterexamples as not yet formalized. It also withdraws the invalid
  common-representative proof and the refuted literal arithmetic/ratio claims.
  Module status, book exposition and the current issue map match these limits.

Validation on 2026-10-07 used the same GCC path, two Lean threads and owned
process-family 30 GiB available-memory guard documented above:

| check | elapsed | sampled peak family RSS | minimum available RAM |
|---|---:|---:|---:|
| Full default `lake build` | 1085.79 s | 10.18 GiB | 35.09 GiB |
| `lake exe book` | 10.08 s | 1.43 GiB | 41.44 GiB |

Both exit successfully with no memory safety stop. This is an incremental
full gate following the audit's upstream documentation/interface changes; it
is not a clean-cache benchmark. It rebuilt the frozen configuration chain.
CommonSource/ReferenceBridge took 210/131 seconds, intrinsic source
restriction 51 seconds, grouped restriction 11 seconds, orbit-triangle E
4.5 seconds, and the root library 4.2 seconds.

The configuration book module took 300 seconds in Lean, then 131 seconds
for its roughly 60 MiB generated C object; executable linking took 8.8 seconds.
That chapter contains 1152 docstring references and is a concrete remaining
#18 target for focused book sections and reduced incremental rebuild costs.
The rendered multi-page HTML contains the new calculus/refutation sections.

All 64 expected public theorem axiom reports for representative calculus,
corrected extraction/refutation, rank-five correctness, concurrence and
literal arithmetic/ratio refutations use exactly `propext`, `Classical.choice`
and `Quot.sound`; none is missing. The lexical audit covers all 199
library/root files and finds no placeholders or project axioms.
`git diff --check` passes. The changed files have no deprecation warnings;
existing warnings in untouched files are separate.

The revised TeX builds to 54 pages without undefined references or overfull
boxes. The title/provenance, corrected grid, Q/Q′ counterexamples,
Frobenius-proof audit, generic-operation audit and ratio warning were visually
checked in scratch renders. These PDFs and the supplied primary-source papers
remain outside git.

At this audit checkpoint, #18 was next: strict compiled-declaration/body and
metadata preservation, paired emitted-module timings and isolated Lake
measurements. The focused-module checkpoint below records those results and
its remaining measurements. The historical M4a work remains frozen.


## Focused module checkpoint (#18)

This refactor starts from the audited `f6964f0` sources on Lean/Mathlib 4.34.1.
It preserves all 1082 exported signatures and 1073 definition/theorem bodies
of the two oversized configuration modules, subject only to the reviewed
proof changes listed below. It does not prove an additional blueprint target
or restart the frozen M4a program.

### Dependency organization

The existing CommonSource and ReferenceBridge module names remain the cores,
so the 76 downstream library importers keep their imports. Seven leaves are
explicitly imported by `AclGeom.lean` and only the relevant book sections:

| module suffix | source lines | direct split dependencies |
|---|---:|---|
| `ChunkCurveCommonSource` | 3848 | existing upstream chain |
| `ChunkCurveCommonSourceComparison` | 1036 | CommonSource |
| `ChunkCurveCommonSourceExistence` | 251 | CommonSource |
| `ChunkCurveCommonSourceRebasing` | 2004 | CommonSource |
| `ChunkCurveReferenceBridge` | 2830 | CommonSource |
| `ChunkCurveReferenceBridgeBGermComplete` | 1396 | ReferenceBridge |
| `ChunkCurveReferenceBridgeSelectedBScalar` | 2433 | ReferenceBridge |
| `ChunkCurveReferenceBridgeSemanticBranches` | 720 | ReferenceBridge, Comparison |
| `ChunkCurveReferenceBridgeFinal` | 306 | ReferenceBridge, BGermComplete, SelectedBScalar |

The two original sources had 6942 and 7493 lines. The remaining CommonSource
core is still large because its live families form one connected dependency
component; no independent parallel cut was found. Book-only existence,
comparison and rebasing results now elaborate independently of the downstream
library chain. Nothing was discarded as unused.

`AclGeomBook/Configurations` now contains six focused sections:
CorrespondenceFields, ParameterTransport, CommonSourceCovers,
ReferenceBranches, SemilinearCommonFields and AlgebraizationPrerequisites.
A small GroupChunkRecord wrapper preserves the old group-record section and
frozen-work notice. Each section imports its declaration providers rather
than all configuration modules. The original 1152 docstring references and
nine tags remain in exactly their original order; six unique subsection tags
are added. Generated HTML retains all 64 page paths, the old section 6.8 and
its ordered subsections 6.8.1–6.8.6. Three prose corrections remove residual
by-construction claims about equation (8.6) and describe the chosen
coordinate-field equivalence accurately.

### Mathematical and artifact checks

The split preserves names, statements, attributes, reducibility and
noncomputability. `curveEmbedding` becomes a documented public abbreviation
because SelectedBScalar consumes it. This is the sole intended privacy and
documentation change among the original constants.

Six membership proofs use the inclusion supplied by an equality instead of
transporting membership with `Eq.rec`. Six later duplicate branch-inclusion
proofs alias the already proved native statements. The three
`commonSourceToRight{A,B,C}SourceEquiv_apply` type hashes change only in their
membership proof arguments, which are equal by proof irrelevance. Exactly
eleven normalized bodies change: the six aliases, those three apply lemmas
and `commonSourceRight{A,B}Aut_apply`. All changes were reviewed; the coordinate
definitions themselves have unchanged raw values.

Independent dumps from the actual isolated Lake artifacts match the frozen
1082-signature/1073-body baseline with no missing or new constants, unexpected
changes or nonstandard axioms. The exported premise-index deny entry has the
same module, kind and string. Differences caused by renamed compiler-generated
`_proof_N` theorem references are normalized only by their recursively
normalized statements; other constants and bodies are compared strictly.
All seven structural mutation checks and all 22 saved-dump comparator controls
and mutations behave as required. The existing metadata workaround remains
in CommonSource once; it does not weaken Lean kernel checking.

### Controlled measurements

Both private worktrees start at `f6964f0`, with separate regular project build
outputs and the same isolated, pinned dependency/cache snapshot. Only Codex's
one build family runs during each measured interval. All runs use two Lean
threads, the GCC path recorded above and the 30 GiB available-memory guard.
The OS cache is warm; the following are component or incremental measurements,
not whole-project clean-build ratios.

| check | elapsed | sampled peak family RSS | minimum available RAM |
|---|---:|---:|---:|
| Original six-target component rebuild | 560.85 s | 8.00 GiB | 39.05 GiB |
| Refactored six-target component rebuild | 331.76 s | 7.74 GiB | 41.09 GiB |
| Original monolithic book native-object control | 134.66 s | 5.36 GiB | 36.14 GiB |
| Focused book full build, library outputs cached | 221.09 s | 10.85 GiB | 38.53 GiB |
| Focused HTML generation | 8.05 s | 1.42 GiB | 41.02 GiB |
| Full build after one leaf docstring edit | 84.41 s | 8.81 GiB | 38.22 GiB |
| Canonical full build after reverting that fixture | 84.44 s | 8.59 GiB | 38.15 GiB |
| Canonical HTML generation | 8.04 s | 1.53 GiB | 39.75 GiB |
| Warm no-change full build | 4.02 s | 0.96 GiB | 40.28 GiB |
| Warm no-change HTML generation | 8.04 s | 1.51 GiB | 39.91 GiB |

The paired six-target experiment rebuilds exactly the same 54 library modules
in both worktrees; upstream and package outputs are reused. Targets are
IntrinsicSourceRestriction, SelectedWholeFace, SemilinearGroupedMiddleS,
SemilinearGroupedMiddleSA, SemilinearGroupedRestriction and
SemilinearGroupedStableOrbitATriangleE (each prefixed by `AclGeom.Config.ChunkCurve`).
CommonSource takes 208 → 98 seconds, ReferenceBridge 129 → 33, intrinsic
restriction 52 → 25, grouped restriction 10 → 10 and orbit-triangle E
4.2 → 4.2. The 41% wall-time reduction applies only to that component rebuild.

The original staged full build reused its unchanged book C object whereas
the math-only variant regenerated it; their raw full-build times are not a
fair speed ratio. A separately forced original native-object control takes
130 seconds in C. An earlier control overlapped a short peer Lean run and
was discarded for timing; the reported rerun has no such overlap. The original
monolithic book takes 299 seconds in Lean. The six focused sections take
28/26/51/53/73/33 seconds in Lean and 14/13/22/21/29/15 seconds in C, with the
full focused build above including their wrapper, parents and executable.
No memory guard stopped any reported run.

The temporary documentation edit was in
`QWitness.exists_psiCurveCompositionBaseChangeRealization`, cited only by
CommonSourceCovers. The full build rebuilt only Existence and the library
root, then that book section, its parents, its native object and the executable.
None of the 54 measured heavy library consumers rebuilt, and no other book
section rebuilt. The fixture was reverted before the canonical signatures,
bodies and full/book gates. A mathematical proof edit still needs its own
full gate; these measurements show the improved import fan-out.

Shared-checkout validation on 2026-10-07, with the same flags and guard:

| check | elapsed | sampled peak family RSS | minimum available RAM |
|---|---:|---:|---:|
| Full default `lake build` after source integration | 581.07 s | 12.00 GiB | 37.81 GiB |
| `lake exe book` | 14.08 s | 1.47 GiB | 39.91 GiB |
| Final full gate after book EOF whitespace cleanup | 132.71 s | 10.66 GiB | 36.52 GiB |
| Final `lake exe book` | 8.04 s | 1.55 GiB | 39.88 GiB |

All pass without a memory stop. The first full gate rebuilds the affected library
chain and all six new book sections; it is incremental, not project-clean.
The final gate follows removal of trailing blank lines in six new book sources;
no mathematical source changes in that cleanup. Fresh dumps from the shared artifacts repeat the 1082/1073 signature/body and
standard-axiom checks with exactly the reviewed exceptions and no additions.
The rendered shared book has the same 64 page paths as both private variants
and preserves the frozen notice. The 206-file library/root lexical audit
finds no placeholders or project axioms; `git diff --check` passes and no touched
file emits a deprecation warning. Only the nineteen reviewed source/doc paths
changed; no generated artifacts were copied to the shared build.

The green focused-module code checkpoint was committed and pushed as
`31864cd2c70831ebe70df9bffb98ead19dd30499` before the longer project-clean
experiment. Its full CI run also passes, as recorded above. Three native
round-trip kernel checks remain potential optimization work; they were not
claimed as completed kernel fixes. The measured gate below allows the next
mathematical checkpoints, with M4 re-planned against #12/#21 and the corrected
configuration targets.

### Project-clean measurements and gate acceptance

Both isolated worktrees use the `f6964f0` base. The candidate has exactly the
reviewed nine math modules, seven root imports and eight focused book sources
(including final EOF whitespace cleanup). Each regular `.lake/build` directory
was moved aside before its full default build. The same pinned dependency
snapshot remained populated: **neither run built any package output**. These
are whole-project clean-output builds with cached dependencies and warm OS
caches, not fresh-machine or dependency-clean benchmarks. The runs are
sequential, with no other Lean family, two Lean threads and the same 30 GiB
available-memory guard. This is one measured pair, not a statistical study.

| check | elapsed | sampled peak family RSS | minimum available RAM |
|---|---:|---:|---:|
| Original project-clean full build | 1131.89 s | 11.73 GiB | 34.93 GiB |
| Original HTML generation | 8.04 s | 1.56 GiB | 40.00 GiB |
| Refactored project-clean full build | 792.14 s | 12.27 GiB | 37.77 GiB |
| Refactored HTML generation | 8.04 s | 1.52 GiB | 40.33 GiB |

All four commands pass without a memory stop. Whole-project wall time falls
by 30.02% in this pair. Sampled family peak RSS is slightly higher with the
parallel leaves/book sections; the resource acceptance is the safe host
envelope, rather than a claim that every peak is lower.

The original run actually builds all 199 library/root modules and 417 project
tasks including native objects and the executable. The candidate builds all
206 library/root modules and 445 project tasks. Their task-set difference is
exactly the fourteen new math/book modules and their fourteen native objects;
no original task is missing or reused and no dependency task is rebuilt.
CommonSource/ReferenceBridge take 206/128 seconds originally and 98/33 seconds
in the candidate. Intrinsic restriction takes 48/26 seconds. The original
monolithic book takes 294 seconds in Lean and 131 seconds in C; the focused
sections and their native objects are all regenerated in the candidate.
Both rendered books retain the same 64 page paths and the candidate preserves
the six ordered subsections and frozen-work notice.

Fresh dumps from the project-clean candidate again match all 1082 signatures
and 1073 bodies with exactly the reviewed type/body and helper documentation/
privacy exceptions, no missing or additional constants or nonstandard axioms,
and equal exported metadata. Source hashes match the reviewed canonical
candidate; no generated artifacts are injected into the shared checkout.

The #18 acceptance criteria are met: warm full/book gates are 4.02/8.04 s,
the changed-leaf full gate is 84.41 s and avoids every unrelated heavy library
consumer and book section, reported resource measurements stay above the
30 GiB guard, and the module organization/timing/artifact/hygiene evidence is
recorded here. A core or genuinely upstream change can still require the
whole dependency chain; the measurement does not promise instant builds for
those edits. The old M4a route stays frozen.

Final shared gates for this measurement-documentation checkpoint pass:
`lake build` takes 12.10 s (sampled family peak 1.11 GiB, minimum available
40.84 GiB) and `lake exe book` takes 8.05 s (1.51 GiB, 40.52 GiB), with no
memory stop. The 206-file hygiene audit and final staged diff check also pass.
Only this continuation guide changes in the measurement checkpoint.

## Finite-base soundness checkpoint (#24)

The atom-clause specialization argument now works over any base field. It
specializes the zero substitution polynomial at two distinct elements of
`racl k {t}`, which is infinite because `t` is transcendental over `k`.
Both values and their nonzero difference lie in that closure, so division
recovers the line coefficients there. This contradicts their independence.
The new `infinite_racl_singleton` has the named consumer
`exists_two_specializations`; no new freshness assumption enters the
configuration soundness statements.

The witness proof, semantic Q/Q′/J soundness, their rank-five wrappers,
affine-grid-to-Psi implication and geometric sum/product wrappers no longer
require `[Infinite k]`. The audited three-join/fifteen-point extraction
interface and literal-table refutation remain intact. ACF completeness
still requires the explicit unproved hypothesis, the arbitrary-field
Q/Q′ Lean refutations in #25 remain open, and the blueprint derivation
calculation remains a separate obligation. The book describes the actual
specialization field.

Claude supplied the original private repair. Codex rebased it onto the
audited targets, independently compiled the exact 17-module reverse
chain with Mathlib standard linters (20.11 s, peak 2.65 GiB, minimum
available 40.71 GiB), checked all 22 selected strengthened/boundary
theorems for standard axioms, and compiled the revised book module
without warnings (10.05 s, peak 4.01 GiB, minimum available 40.36 GiB).
The integrated full `lake build` passed in 52.29 s (peak family RSS
8.35 GiB, minimum available 38.34 GiB), and `lake exe book` passed in
8.04 s (peak 1.55 GiB, minimum available 40.13 GiB). A fresh shared
probe checks all 22 theorem axioms and public statements; it finds only
standard axioms and no infinite-base binder. All 206 library/root Lean
files pass the placeholder/project-axiom scan. All 64 rendered HTML page
paths are preserved, the specialization prose is checked, and the frozen
group-chunk notice remains present. Touched modules have no deprecation
diagnostics. This is the finite-base item in #24, not completion of its
remaining foundational carryovers.

## Focused semantic j-coordinate and Frobenius-soundness checkpoint (#23)

`Config/JCoordinates` owns the semantic `jTupleOf` constructor and its
coordinate API. `Interpretation/FrobLinkSoundness` owns explicit geometric
sum/product witnesses and common-parameter links;
`Counterexamples/GenericArithmetic` now contains the literal predicates
and refutations. Existing public names are preserved. Four superseded
private helpers are replaced by the representative-calculus API or
Mathlib's `AlgebraicIndependent.ne_zero`. There are no duplicate aliases.

Eight new declarations have named consumers: generic triple-to-pair
selection and its nonvanishing lemma serve the refutations/links; power
transport of an independent pair, semantic tuple normalization and
positive Frobenius point normalization serve `frobEq_of_frobenius_twist`.
This theorem proves that semantic tuples whose parameters differ by a
positive Frobenius power satisfy `FrobEq`, using a fresh common-parameter
bridge. The displayed wrappers retain `[Infinite k]` and rank five;
removing their now-redundant infinite-base binders is a separate
strengthening. The converse and semantic completeness remain open.

Claude prepared the focused extraction. Codex independently checked all
six extraction/arithmetic modules on the pushed finite-base baseline
(34.17 s, peak 3.48 GiB, minimum available 39.69 GiB); the arithmetic
modules remain private pending their own checkpoint. Baseline/split
artifact comparisons cover 63/67 declarations and check placements,
axioms, statements, bodies and deny-list metadata. The only deletions
are the four superseded private helpers; the eight additions are exact.
Six statement differences name the replacement proof arguments.
Applying only the three explicit helper renames and private-name
normalization makes all common statement hashes identical and leaves
exactly three body differences: two Mathlib nonvanishing replacements
and one inlined pair-range proof. In particular both nonfunctional
existence refutation bodies agree under that exact ledger; reference-set
equality was not used as proof-body identity. The source edits were
reviewed directly. Later changes are module documentation and two
docstring line wraps only. The code was committed and pushed as `c171657`. Shared full `lake build`
passed in 22.11 s (peak family RSS 7.21 GiB, minimum available 38.45 GiB),
and `lake exe book` passed in 8.04 s (peak 1.53 GiB, minimum available
40.12 GiB). Fresh shared Sig/Proof/Rename probes preserve the reviewed
67 statements/values, exact eight additions/four private deletions, all
66 authored module placements and standard axioms. The on-demand
`jTupleOf.congr_simp` equation retains its original Counterexamples
consumer placement; an extra provenance assertion initially assumed the
constructor's module and was corrected against the actual baseline and
shared artifacts. The only additional signature differences are the two
documented docstring line wraps. Hygiene covers 208 library/root Lean
files. The 64 HTML page paths and frozen notice are preserved; the new
semantic soundness prose is present. Touched modules have no deprecations. Fixed-class arithmetic, totalization, ratio
semantics and the historical M4a chain remain open or frozen as before.

The documentation-only evidence follow-up also passes the required full
build (4.02 s) and rendered book (8.04 s).

## Generic meet/join arithmetic checkpoint (#23)

`Interpretation/JArith` implements the four subtraction and five division
meets from EH95 Lemma 2.11, Figures 4–5. Their independent-input coordinate
identities imply generic negation, inverse, addition and multiplication.
`JArithSem` uses the shared `jTupleOf` constructor, defines Point-valued
relations by those geometric operations, and proves their function
properties, independent-input unique outputs and semantic membership.
Rank-five soundness gives geometric J membership over any base field;
six redundant infinite-base binders are removed from these new wrappers.
No configuration completeness is used in the arithmetic computations.
The source/book status is updated; literal-refutation provenance stays
intact. The new book subsection documents the coupled construction.

Claude supplied the generic arithmetic and deduplicated semantic draft.
Codex independently checked the final two modules against the focused
main APIs (30.15 s, peak 3.47 GiB, minimum available 39.61 GiB), without
warnings. A 102-record canonical/final statement/body comparison finds
exactly the six strengthened membership wrappers and no other changes.
All 100 public artifact axiom reports are standard; excluding generated
equations, these cover 89 authored public declarations (theorems and
definitions). The shared full `lake build` passed in 48.27 s (peak family RSS 6.15 GiB,
minimum available 38.34 GiB); `lake exe book` passed in 8.04 s (peak
1.54 GiB, minimum available 40.02 GiB). Fresh shared signature/body
comparisons match the independently checked 102-record final artifacts
without exceptions; all 100 public axiom reports match the standard-axiom
review. Hygiene covers 210 library/root Lean files. All 64 existing HTML
page paths remain, and the coupled-arithmetic subsection adds one page
(65 total); its computation and open-boundary prose is checked. The
blueprint renders to 54 pages without undefined/overfull diagnostics;
the changed status paragraph on page 34 is visually reviewed. New
arithmetic modules compile without warnings.

Fixed-class/Frobenius correctness, extension to all input pairs, totalized
field operations and ratio semantics remain open. This checkpoint proves
the generic coordinate computations and preserves the corrected
configuration completeness boundary.

## Specific Q/Q′ counterexample prerequisites (#25)

Three focused modules support the named `Counterexamples.QDescent`
targets over ℚ(s,t,e₁,e₂,e₃): `Closure/RationalFunctions` proves that
algebraic elements over the coefficient field are constants and that a
nonzero constant times a variable is not a square;
`Correspondence/WeightedSupport` proves algebraicity of `s/u²` from a
`(2,1)`-weighted-homogeneous equation and its support-pair criterion;
`Correspondence/MultiplicativeQuotient` derives interalgebraic coordinate
quotients from common nonzero coset exponents, and applies the existing
multiplicative correspondence theorem with its ACF/freshness hypotheses.
The integer-power closure helper is made public for that named consumer;
its type and proof are unchanged. No second correspondence classification
or duplicated helper is introduced. These facts are prerequisites; the
concrete Q/Q′ geometric witnesses, semantic contradiction and general
completeness statements are not proved by this checkpoint.

Claude prepared the lemmas. Codex independently compiled all four modules
(6.03 s, peak 2.30 GiB, minimum available 40.57 GiB) and verified nine
standard-axiom reports including the promoted helper. The strict
71→79 signature and 68→76 body comparisons have exactly eight new
lemmas and no existing type/body change; only the single helper privacy
flag changes, and exported deny-list metadata is unchanged. Subsequent
source edits are module documentation only. The book identifies the
remaining concrete-witness and semantic-contradiction obligations.
The shared full `lake build` passed in 52.30 s (peak family RSS 10.27 GiB,
minimum available 37.45 GiB), and `lake exe book` passed in 8.04 s
(peak 1.53 GiB, minimum available 40.02 GiB). Fresh shared 79-record
signature and 76-record body comparisons match the independent review
without exceptions; all nine selected theorem axiom reports match,
and each new lemma's authored module placement is checked. The existing
`Multiplicative` source changes only at the single visibility word. Hygiene
covers 213 library/root Lean files. All prior HTML paths remain (65 pages
total); the new prerequisite prose and remaining obligations are checked.
Touched modules have no deprecation diagnostics.

## Algebraic-base lattice and configuration lift (#7, #25)

`Transfer/Lift` now proves closure trace, an injective order-preserving
closed-field lift, bottom/finite-join preservation, exact matroid rank
and point transport along a k-embedding with an algebraic enlarged base.
Over an algebraically closed overfield it preserves binary meets. Its
finite-generator atom-capture transfer uses the existing one-quantifier
theorem and needs no transcendence-degree or infinite-base hypothesis.
`Transfer/LiftConfig` lifts partial quadrangles, full Q witnesses and
Q/Q′ configurations. It reflects partial quadrangles and multiplication
diagrams of lifted points, and reflects a Q witness when the three
clause-(vi) quadrangle witnesses are explicitly supplied as K-points.
It asserts no general descent of existential witnesses. Neither module
imports the private JAssembly completeness interface. Their named
consumers are the remaining point-level J arrows and the explicit
`Counterexamples.QDescent` geometric witnesses. Both concrete #25 Lean
refutations and unconditional J ACF completeness remain open.

Claude supplied the drafts. Codex compiled both against main 3061254
(6.00 s, peak 2.42 GiB, minimum available 40.31 GiB), repairing two
reflection proof rewrites for the A/C joins without changing statements.
The historical configuration-lift block is preserved verbatim. An
independently compiled reduced historical block permits an exact
37→41 signature and body comparison: four explicitly reviewed reflection
additions, zero existing type/body changes, and unchanged deny metadata.
All 41 public axiom reports use only standard axioms. The book corrects
its stale finite-base and arbitrary-field Q/Q′ status prose.
The shared full `lake build` passed after the module-documentation line
wrap (20.01 s, peak family RSS 10.49 GiB, minimum available 39.31 GiB),
and the rendered book passed in 8.00 s (peak 1.55 GiB, minimum available
39.79 GiB). Fresh shared signatures, bodies, axiom reports and explicit
reflection statements match the independent review exactly, including
the K-valued quadrangle hypothesis. The 41 artifact records cover 40
authored public declarations and one generated congruence theorem;
all authored/generated module placements are checked. Hygiene covers
215 library/root files, all 65 HTML paths are preserved, and the
finite-base/counterexample/completeness/frozen notices are verified.
Both new modules have no diagnostics. The eight prerequisite lemmas'
preceding commit 3061254 now has successful full CI.

## Semantic J assembly and point-level descent (#6, #7)

`Config/JAssembly` assembles semantic Q and two Q′ projections into one
semantic J tuple over an algebraically closed pair of rank at least five.
It aligns their additive/multiplicative correspondences through affine
Frobenius and shifted-binomial rigidity. Geometric J completeness is
packaged as `JCompletenessACF` and reduced to explicit ACF Q/Q′
completeness hypotheses; these inputs remain unproved. Its shifted
binomial lemmas are also the named prerequisites of the reviewed
Frobenius-incidence converse, avoiding a second proof family.
`Transfer/JDescent` proves point-level (1)⇔(2) for perfect K of rank at
least five and geometric (4)⇒(3). With the existing finite-base (1)⇒(4),
it packages J equivalence under explicit `JCompletenessACF`, including
the canonical algebraic closure form. No infinite-base assumption or
arbitrary-field Q/Q′ equivalence enters these arrows. The unconditional
T4 completeness obligation stays open.

Claude supplied the drafts and extracted the already integrated
configuration-lift block from JDescent. Codex independently compiled the
remaining two modules on main 2f25a78 (6.00 s, peak 2.74 GiB, minimum
available 40.15 GiB), without diagnostics. A fresh historical/full versus
focused comparison covers 77→81 signature and body records with zero
existing changes; the only four additions are the reflection lemmas
already on main in 2f25a78. All 40 public declarations of these two new
modules have standard axiom reports. The conditional hypotheses are
inspected in the emitted statements. The book adds a semantic-assembly
section and updates the point-descent status; the blueprint correction
records the still-open ACF inputs. Lift checkpoint 2f25a78 has successful
full CI.
The shared full `lake build` passed in 36.01 s (peak family RSS 11.68 GiB,
minimum available 38.14 GiB); `lake exe book` passed in 8.00 s (peak
1.55 GiB, minimum available 39.80 GiB). All 81 shared signature/body
records, the 40 axiom reports and six inspected conditional statements
match the independent review exactly. The two new modules contribute
29 semantic-assembly and 11 point-descent declarations, with unchanged
source bodies and no diagnostics. Hygiene covers 217 library/root files.
All 65 prior HTML paths remain, and one semantic-assembly page is added
(66 total); conditional-completeness, concrete-refutation and frozen
boundaries are checked. The revised blueprint renders to 54 pages
without undefined/overfull diagnostics; the changed status on page 31
is visually reviewed. Claude acknowledged the source-only geometric
consumer task after the corrected chit resend and retains no build slot.

## Frobenius incidence rigidity and semantic consumers (#23)

`Interpretation/FrobLinkRigidity` proves that concurrence of the three
closure lines forces the parameters to differ by a natural Frobenius
power, over an algebraically closed pair. Its scaled-locus argument
reads both signed characters from one support pair, extracts common
primitive exponents and applies shifted-binomial rigidity from the
existing JAssembly chain. `FrobLinkRelative` transfers the algebraic
facts to an algebraically closed overfield/algebraic base and reflects
the exact conclusion along the embedding. `FrobLinkSemantic` consumes
the geometric concurrency, rank and parameter clauses with explicit
semantic endpoint equations over any base. `FrobEqForward` composes
the two twists under an explicit semantic-middle-tuple hypothesis;
the canonical form names perfection, rank five and unproved ACF
`JCompletenessACF`. No unconditional bridge completeness, original
common-representative alignment, setoid law or field operation law
is claimed. These results retain the original geometric predicates.

Claude supplied the canonical drafts. Codex compiled all four on main
a8233d8 (6.00 s, peak 2.65 GiB, minimum available 40.19 GiB) and checked
a final focused version (6.00 s, peak 2.65 GiB, minimum available
40.17 GiB), without diagnostics. The final core module is named
FrobLinkRigidity. Three duplicate/one-use helpers are removed in favor
of Mathlib's unit theorem and the existing point-representative API.
An exact 24→21 signature/body comparison has these three deletions,
exactly two proof edits, zero surviving statement changes and unchanged
deny metadata. All 21 public authored theorems have standard axiom
reports; the five displayed rigidity/conditional-converse interfaces
are inspected. Module documentation changes only after the reviewed
proofs are accepted. The source/book identify the still-open
common-representative and completeness obligations.
The shared full build passed in 26.01 s (peak family RSS 10.15 GiB,
minimum available 38.07 GiB); the rendered book passed in 8.00 s
(peak 1.55 GiB, minimum available 38.67 GiB). Fresh shared 21-record
signatures/bodies, axiom reports and five typed interfaces match the
independent review exactly. All 21 authored module placements and
proof-source bodies are checked; final module-documentation edits are
the only source differences. Hygiene covers 221 library/root files.
All 66 existing HTML paths remain, and the semantic/completeness,
infinite-base soundness-wrapper and frozen boundaries are verified.
The revised blueprint renders to 54 pages without undefined/overfull
diagnostics; its changed status across pages 32–33 is visually checked.
The four new modules have no diagnostics. The preceding semantic J
assembly/point-transfer commit a8233d8 now has successful full CI.


## Concrete Q/Q′ refutations (#25)

Counterexamples/QDescent reflects the explicit table-7.1 and table-7.2
witnesses and the eight-point multiplication diagram from an algebraic
closure. All supplied points arise by images, inverses or squares of
elements of K. Its Q/Q′ consumers need five independent elements over
the base; no geometric completeness hypothesis or general witness
descent theorem is used.

Counterexamples/QSemantic proves the characteristic-zero obstruction:
semantic representatives for ([s],[st²],[s(1+t)²],[t]) force s/x² to be
algebraic. It fixes one curve polynomial before both scaled loci,
derives characters at one support pair, and uses the signed-character
result at exponential characteristic one to fix y/x=t. Applying the
first character to every support pair gives (2,1)-weighted homogeneity.
The Q′ ratio follows from the multiplicative-quotient theorem with an
explicit fresh independent element. Algebraic-base invariance and
ambient transport return the obstruction to the original fields.

Counterexamples/QRefutation combines the explicit geometric witnesses
with the semantic obstruction. Both correctness assertions fail over
FractionRing (MvPolynomial (Fin 5) k) for every characteristic-zero k.
Closure/RationalFunctions contains the generic independent-variable
lemma and proves X_i/x² transcendental for nonzero x from its existing
constant-element/nonsquare theorems. Test/RationalFunctionField now uses
that generic independence lemma instead of duplicating its proof.
The original geometric definitions and withdrawn statement provenance
remain; both specific refutations are proved, while general witness
descent, corrected arbitrary-field semantics and ACF completeness are
separate open obligations.

Claude supplied source-only drafts and a source fidelity/dependency
audit. Codex independently compiled owned copies against 4b66682. The
geometric draft needed two finite-vector elaboration repairs; the
semantic/refutation draft was immediately proof-green. The final
focused chain fixes the three style diagnostics, removes the JArith
import by direct membership rewrites, and drops unused algebraic-closure
assumptions on exactly four pure helper statements. The independent
artifact ledger preserves every other statement, all module placements,
and only the nine corresponding new proof edits plus the one existing
acceptance-test deduplication. All 28 new authored public theorems use
standard axioms; typed interfaces verify both generic characteristic-zero
and rational concrete refutations, perfection, rank at least five and
relatively algebraically closed constants. For the private rational
specialization probe, the canonical coefficient-field algebra instance
is selected explicitly; the two Mathlib rational-algebra instances are
propositionally equal but not definitionally equal.
The final independent focused chain passed in 12.00 s (peak family RSS
2.76 GiB, minimum available 39.76 GiB) without diagnostics. A strict
40→40 signature/body ledger includes the existing nine-declaration
rational-function acceptance module: four helper statements strengthen,
exactly ten proof edits match the reviewed scope, and no declarations
are added or removed relative to the compiled draft/test baseline. All
40 public declarations have standard axiom reports; the 28 new authored
theorems occupy the intended modules. The seven typed interfaces pass.
The shared full build passed in 42.01 s (peak 10.83 GiB, minimum available
37.76 GiB); the book passed in 8.00 s (peak 1.53 GiB, minimum available
39.55 GiB). Fresh shared signatures, proof bodies, all axiom reports
and typed interfaces match the independent artifacts exactly (6.00 s,
peak 2.60 GiB, minimum available 40.00 GiB). Hygiene covers 224
library/root files. All 66 existing HTML paths remain; both refutations,
their seven docstrings, open general-descent/ACF boundaries and the
frozen M4a notice are checked. The revised blueprint renders to 54
pages without undefined/overfull diagnostics, and pages 31–32 are
visually reviewed. The final prerequisite documentation reflow and
this validation record receive the mandatory repeated build/book gates.


## Foundation transport, existence and naturality (#24, #10)

`Closure/CrossBase` proves equivariance of relative closure and closed-lattice
transport for a field isomorphism carrying one base image onto the other.
It constructs the induced compatible scalar isomorphism and proves the
identity/composition/inverse transport laws. Compatibility is an explicit
hypothesis; no reconstruction or completeness input is assumed.

`Geometry/Transport` extends a closure-preserving point equivalence uniquely
to an order isomorphism and recovers the original point map. Order
isomorphisms preserve finite independence, finite geometric rank and
arbitrary independent representative families. Transcendence degree is
invariant, with universe lifts when necessary, and exact finite geometric
rank agrees with the transcendence degree of the closed intermediate field.
No infinite-base or perfect-field hypothesis is needed for these interfaces.

`Perfection/Existence` supplies a chosen perfection in every exponential
characteristic using the relative perfect closure inside an algebraic
closure. This focused leaf keeps the algebraic-closure constructor out of
the existing Subfield/Lattice dependency cone. The existing `ofCharZero`
constructor and its rational-function acceptance consumer are unchanged.
`Perfection/Naturality` extends a field isomorphism uniquely to arbitrary
chosen perfections, proves its groupoid laws, and transports perfected
subfields and compatible perfected bases. The perfection lattice
isomorphisms intertwine this transport; the identity field map compares two
choices and acts as the identity on the original closed-field lattice.

Claude audited the frozen source drafts and their blueprint consumers with
no builds or main edits. Codex independently compiled owned snapshots
against `8798315`, removed exactly two unused helpers, and made exactly two
proof edits: the deprecated `if_pos` becomes `ite_eq_left` in the existing
`Perfection.isRAC_perfIF`, and `haveI` becomes `have` in the new
transcendence-basis/closure bridge. All 113 surviving declaration statements,
definition bodies, attributes and declaration docstrings match the original
115-record draft ledger. The two constructor/instance declarations move
byte-for-byte from Subfield to Existence. The previous-main 55-record ledger
is preserved, with only the documented existing proof edit. There are 57
new authored declarations and one reviewed generated `baseRingHom.eq_1`;
all 110 public definitions/theorems have standard-axiom reports.

The final six-module independent compile passes without diagnostics in
6.00 s (peak family RSS 1.14 GiB, minimum available 40.10 GiB). Nine typed
interfaces pass, including arbitrary-characteristic existence, the ZMod 3
constructor, closure-compatible point transport, rank/trdeg agreement,
cross-base closure transport, naturality and comparison of two choices.
The shared full build passes in 680.21 s (peak 12.06 GiB, minimum available
37.86 GiB); it recompiles the dependents of the foundational documentation
corrections. The rendered book passes in 8.00 s (peak 1.56 GiB, minimum
available 39.88 GiB). Fresh shared signatures, proof bodies, public axiom
reports and all nine interfaces match the independent artifacts exactly
(6.00 s, peak 2.42 GiB, minimum available 40.43 GiB). Hygiene covers 228
library/root files. All 66 existing HTML paths remain among 69 pages; the
new transport/naturality sections, all displayed interfaces, preserved
representative calculus and frozen M4a notice are checked. The blueprint
renders to 55 pages without undefined/overfull diagnostics; the new
foundation status on page 11 and the following page are visually reviewed.
This final documentation record receives the mandatory repeated full-build
and book gates before commit.

At that transport checkpoint, explicit `Induces` packaging remained open
(#24); the next checkpoint below completes it. The literal/quotient functors,
existence of reconstruction and uniqueness-up-to-Frobenius converse remain
open (#8–#10). The source-only design audit for `Induces`
distinguishes the intersection formula (no extra base hypothesis) from
recovery of the literal perfected bases (both bases relatively algebraically
closed), as required by the main theorem's context. No checkbox for these
remaining obligations was discharged by that transport checkpoint.


## Explicit induced-map interface (#24, #10)

`Perfection/Induces` implements the blueprint's exact equality of perfected
closed subfields. Its membership theorem gives the intersection formula as
preimage along the target inclusion; the inducing field map determines its
lattice map uniquely. At the bottom it always transports the perfected
relative algebraic closures of the bases. Recovery of the literal perfected
bases explicitly assumes both bases relatively algebraically closed, as in
the main theorem. The contextual qualification and a source-level example
with ℚ and ℚ(√2) were recorded on #24 before the draft and source clarification.

A compatible isomorphism of chosen perfections induces the conjugated
closed-lattice map, without a rank or extra base hypothesis; inducing is
exactly equality with this map. Original field isomorphisms induce their
direct closed-field transport through the unique perfection extensions.
The identity compares two choices and induces the identity lattice map.
Integral Frobenius twists of an inducing field map induce the same map.
The converse uniqueness-up-to-Frobenius implication remains open, as does
existence of a field map for an arbitrary lattice isomorphism and full
literal/quotient functorial assembly (#8–#10).

Claude supplied a frozen 155-line source-only draft against the accepted
foundation inputs; Codex verified the source/input hashes and independently
compiled it against `665ee50`. The original source compiled unchanged and
without diagnostics. A coercion rewrite in the private set-preimage test
harness was repaired using `Subfield.mem_map`; no public source change was
needed. The final module changes only its status documentation, and its
namespace is byte-for-byte the original. The exact 14→14 signature/body
ledger preserves all statements, bodies, attributes, declaration docstrings
and exported deny-list metadata. It comprises ten authored public APIs,
one private bottom helper, and three explicitly audited generated public
lemmas: `Perfection.inducedIso.eq_1`, `Perfection.inducedIso.congr_simp` and
`CrossBase.closedIFMap.congr_simp`. All three are emitted in the Induces
module; their namespace prefixes do not change their module placement.
All 13 public and the private-helper axiom reports use standard axioms.

The final private compile/probe gate passes in 6.00 s (peak family RSS
2.45 GiB, minimum available 40.07 GiB). Nine typed interfaces pass, including
the actual set-preimage formula, unique lattice map, explicitly qualified
base recovery, assumption-free compatible converse, Frobenius invariance,
two-choice comparison and agreement with original field transport. The
shared full build passes in 24.01 s (peak 8.27 GiB, minimum available
38.16 GiB); the rendered book passes in 8.00 s (peak 1.56 GiB, minimum
available 39.81 GiB). Fresh shared signatures, proof bodies, public axiom
reports and all nine interfaces match the independent artifacts exactly
(6.00 s, peak 2.42 GiB, minimum available 40.30 GiB). Hygiene covers 229
library/root files. All 69 existing HTML paths remain among 70 pages; all
ten displayed interfaces, base hypotheses, remaining reconstruction
boundaries and frozen M4a notice are checked. The blueprint renders to 55
pages without undefined/overfull diagnostics; pages 5, 11 and 12 are
visually reviewed. This final documentation record receives the mandatory
repeated full-build and book gates before commit.

The foundational #24 checklist is complete with this explicit interface.
The public reconstruction existence, full uniqueness and functorial
milestones remain open; the U3–U5 checkboxes in #10 are not discharged.


## Frobenius kernel, two-generic intersection and rank refutation (#9)

The kernel theorem is proved with an explicit rank-five hypothesis:
`exists_eq_frobeniusZPow_of_point_fixed` applies to every field automorphism
of a perfect field fixing the transcendental points. It needs neither base
preservation nor a relatively closed base. The proof transports elementwise
j-rigidity through algebraic closures, compares independent pairs using fresh
elements and recovers algebraic elements by addition and cancellation.
`eq_refl_of_point_fixed` gives characteristic-zero identity; the independent
`frobeniusZPow_injective` clause needs only a transcendental element and
positive characteristic.

The displayed source theorem had omitted the rank hypothesis, despite its
proof and the main target using it. This was reported on #9 before any source
change. `Counterexamples/KernelRank.not_forall_eq_refl_of_point_fixed` refutes
the rank-free characteristic-zero claim over ℚ(t)/ℚ and records the
relatively closed base. The local translation fixes every point and moves t.
The corrected blueprint retains the full original displayed wording from
`641a09e` in source comments and an audit remark. Five typed refutation
interfaces check characteristic zero, perfection, relative closedness,
the literal refutation and preservation of the coefficient field.

`racl_pair_mul_inf_racl_pair_mul` proves the literal two-generic intersection.
Its helper `racl_insert_inf_racl_insert` is an infimum-equality wrapper around
the existing `mem_racl_of_mem_racl_insert` and accepts arbitrary base sets:
finiteness and the other element's freshness are unnecessary. The all-point
recovery half of R3 remains open. The bypassed #11 linear-disjointness
obligations also remain open.

Claude supplied and source-audited the frozen drafts; Codex independently
compiled immutable original, split and final snapshots against `641a09e`.
The original→split ledger preserves all 46 declarations, with five authored
Frobenius APIs plus their generated equation moved and one held-consumer iff
temporarily added. Final cleanup removes that unused iff and two duplicate
helpers; the surviving kernel statements are unchanged. The 47→44 ledger
records one generic intersection statement strengthening, the shared
`Perfection.frobZPow` definition body, its generated equation type and four
theorem proof edits. The nested generated proof renaming in exponent
separation is matched only by identical theorem-statement keys, including
numeric underscore suffixes; no blanket type normalization is used.

The counterexample has one authored declaration and the public generated
`AclGeom.Test.t.eq_1` emitted in its module. Its source-only draft needed
explicit M1 type parameters and restricted generator simplification; no
heartbeat increase was used. A final collaborator review generalized the
statement from ℚ to every field and quantified base-preserving algebra
automorphisms explicitly, removing the temporary coefficient-algebra
instance priority. The exact ledger records this authored statement/docstring
and proof strengthening; the generated equation's type and proof are unchanged. All 46 combined public declarations use only standard axioms, every
generated declaration has an explicit module placement, and all 15 typed
interfaces pass. The common Frobenius implementation also preserves the
original perfection group-power expression definitionally and the existing
Induces forward fibre law.

After the counterexample strengthening and line-length cleanup, the full
shared library build passed in 16.00 s (peak family RSS 10.60 GiB, minimum
available memory 37.29 GiB); the book passed in 10.00 s. All 46 shared
signature/proof/axiom records match the independent final artifacts exactly,
and all 15 interfaces pass (10.00 s, peak 2.56 GiB, minimum available 38.31 GiB).
Hygiene covers 232 library files. All 70 previous HTML paths remain among
76 pages; the new chapter's eleven displayed docstrings, rank qualification,
open recovery/linear-disjointness boundaries and frozen 117-declaration
notice pass review. The blueprint is 55 pages; pages 39–40 were rendered
and visually checked, with no undefined references or overfull boxes.
Final documentation build/book and staged-byte/push gates are required before
the checkpoint commit. U1 and the intersection part of R3 are this
checkpoint's scope; R1/R2/R4, recovery of all points, reconstruction existence,
full functorial assembly, M4 and the held FrobEqCorrect/L2 work remain open.


## Supplied-endpoint uniqueness and the Frobenius fibre (#9, #10)

`Reconstruct/Uniqueness` proves the uniqueness clause of the main target
for explicit inducing isomorphisms of arbitrary chosen perfections.
`Induces.point_symm_trans` shows that their target difference fixes every
principal closure, without rank or relatively closed base hypotheses.
The same Induces equations identify the image of every perfected closed
subfield; the perfection lattice isomorphism makes these all target closed
subfields. An order isomorphism of the original lattices and the target
perfection order isomorphism transport source rank five to the perfected
target, with universe lifts handled by the existing transport API.

The kernel yields `Induces.exists_eq_trans_frobZPow` with the correct
orientation `Φ₂ = Φ₁.trans (ρ.frobZPow n)`. Together with the accepted
forward invariance, `Induces.iff_exists_eq_trans_frobZPow` describes the
full fibre once one inducing map is supplied. The independent
`trans_frobZPow_injective` clause takes the lattice isomorphism and rank
explicitly, with no unused Induces hypothesis. `Induces.eq_of_p_eq_one`
gives literal uniqueness in characteristic zero. No agreement of the two
recorded exponential characteristics, target-rank or relatively closed-base
hypothesis is added. Reconstruction existence and assembly remain open.

Claude supplied the frozen source-only drafts; Codex verified both draft
hashes and all six input hashes against pushed `76484ae`. The draft note
still named `641a09e` with working-tree kernel candidates; chit #3663
confirmed, and the independent ledger verified, that these inputs are exactly
the pushed kernel checkpoint. The raw draft compiles unchanged and preserves
all 15 old declaration signatures and normalized proof bodies.

The final 22→22 ledger has zero statement, attribute, docstring or definition
body changes. Exactly two existing Kernel theorem proofs now use the shared
`frobeniusZPow_eq_one_of_eq_one`, removing duplicated characteristic-zero
computations. There are six new authored public theorems, one private shared
rank helper and no new generated declarations; the existing
`frobeniusZPow.eq_1` has an explicit placement check. All 21 public reports
and the private helper use standard axioms. Twelve identical original/final
typed interfaces pass, including independent universe levels, original-field
characteristic zero, characteristic three, original compatible transport
and the comparison of two arbitrary choices of perfection.

The full shared library build passes in 24.02 s (peak family RSS 8.07 GiB,
minimum available memory 34.85 GiB), and the rendered book passes in 10.00 s.
The isolated reconstruction chapter required its explicit Uniqueness import;
that integration error was fixed before these gates passed. The exact 22
shared signatures/proofs, 21 public standard-axiom reports, private helper and
all twelve interfaces match the independent final review (8.00 s, peak
2.54 GiB, minimum available 36.58 GiB). The unchanged Induces namespace is
byte-checked. Hygiene covers 233 library files; all 76 previous HTML paths
remain among 77 pages, with the six new displayed docstrings and explicit
source-rank/endpoints/open-existence boundaries checked. The 55-page blueprint
has visual review of pages 40–42 with no undefined references or overfull boxes.

Visual review also found the old assembly paragraph still claiming a complete
proof of existence. This status overclaim was reported on #9 before correction;
the original phrasing is retained in source comments. The target and planned
interface are unchanged, while the assembly text now explicitly depends on the
open interpretation and recovery inputs. Final documentation build/book and
staged-byte/push gates remain required before the checkpoint commit.
The supplied-endpoint uniqueness half is this checkpoint's scope. R1/R2/R3b/R4
recovery, reconstruction existence, full functorial assembly, M4 and the held
FrobEqCorrect/L2 work remain open.


## Conditional point recovery and atomistic extension (#9)

`Reconstruct/Points` now proves `eq_closedIFMap_of_point_eq`: a compatible
field isomorphism agreeing with the prescribed lattice isomorphism on
principal closures outside `racl {a}` induces the whole lattice map.
Compatibility and that outside-point formula are explicit hypotheses.
They are the outputs of still-open base recovery R1 and scalar elimination
R2, rather than claims that those tasks have been proved.

The proof follows a shorter route than the blueprint's meet/intersection
argument. Exchange identifies every point represented inside `racl {a}`
with the single exceptional point. Two bijections agreeing away from one
point agree there as well; the existing `latticeIsoOfPointEquiv_unique`
then identifies the lattice maps. No rank, freshness or relatively closed
base assumption is needed. The parameter may be algebraic. The existing
`ClosedIF.mem_point_symm` supplies the exchange step, avoiding a duplicate
representative-transcendence calculation.

`CrossBase.closedIFMap_point` supplies point transport for the compatible
isomorphism and immediately yields the all-point formula. Its narrow import
changes from `Closure.ClosedLattice` to `Geometry.Points`, the module defining
principal closures; there is no cycle. The Points skeleton drops its broad
`Reconstruct.Base` import in favour of CrossBase and Geometry.Transport.
The only public additions are these two blueprint-facing theorems, with
one private bijection helper and no new generated declarations.

Claude supplied frozen source-only drafts; Codex independently verified the
two hashes and seven dependencies against pushed `33c4d07`. The private
compile exposed a default-simplifier rewrite from a representative's
principal closure back to its point. The reviewed original uses narrowly
listed singleton/point-membership rewrites. A follow-up harness typo used
the namespace-qualified singleton lemma, which was corrected before the
green private original gates. The frozen source files remain preserved.

The 22→25 ledger preserves all 22 old signatures and raw proof/body hashes
exactly, including generated `CrossBase.baseRingHom.eq_1` and its module.
Reviewed original and final 25-record signatures agree completely:
statements, attributes, declaration docstrings and definition bodies do
not change. The sole proof cleanup is the new point theorem's use of the
existing point-exchange API. All 24 public reports and the private helper
use standard axioms.

Eight identical original/final typed interfaces pass with independent
universe levels. They test principal-closure transport, the precise
conditional lattice equality, every point, every closed-field image,
the lift to chosen perfections and its inducing relation, perfected-lattice
conjugacy back to original fields, an algebraic zero parameter and identity
specialization.

The full library build passes in 50.01 seconds (peak family RSS 10.25 GiB,
minimum available memory 34.25 GiB), and the rendered book in 14.00 seconds.
The shared artifact check reproduces the exact 25-record signature/proof
ledger, 24 public standard-axiom reports plus the private helper, and all eight
typed interfaces (6.00 seconds, peak 2.32 GiB, minimum available 37.24 GiB).
The code sources are byte-exact with the private accepted candidate.
Hygiene covers 233 library files. All 77 old HTML paths remain among 78 pages,
with both new docstrings, explicit hypotheses, open recovery and the frozen
117-item notice checked. The blueprint renders in two passes without undefined
references or overfull boxes, now 56 pages; pages 38–43 were visually reviewed.
Final documentation build/book and the exact five-path staged-byte gate follow
before commit and push. R1/R2, unconditional R3b/R4, reconstruction
existence and final assembly remain open. The two-generic intersection
remains a proved blueprint lemma despite the different propagation proof;
#11's bypassed obligations, frozen M4a and held FrobEqCorrect/L2 are unaffected.


## Conditional Frobenius-link equivalence and fixed-class description (#23)

`Interpretation/FrobEqCorrect` proves the exact Frobenius-link equivalence
for supplied semantic endpoints, both with natural powers in either orientation
and with integer Frobenius powers. The immediate consumer
`frobEq_jTupleOf_iff` identifies the class of `j(x₀,a)` with all semantic
tuples `j(x,a)` having the same literal parameter. A geometric endpoint is
made semantic by the existing J descent API, and inverse Frobenius normalizes
its parameter without moving any closed point.

Perfection, source rank five and the still-open ACF `JCompletenessACF`
input are explicit. No relatively closed base or infinite-base hypothesis is
added. The predicates remain the original geometric `FrobEq` and `J`.
The natural/integral conversion `exists_frobeniusZPow_iff`, previously held
for lack of a landed consumer, now has the immediate literal-equivalence
consumer. There are exactly four new public theorems and no new private or
generated declarations.

Seven `FrobLinkSoundness` wrappers lose redundant `Infinite k` hypotheses:
the independent sum/product witnesses and five Frobenius-class soundness
theorems. The existing arbitrary-base rank-five configuration soundness
already supplies their proofs. A narrowly defined check removes only an
unused forall binder of type `Infinite` and proves all fourteen old
remaining types structurally identical; exactly seven such binders disappear.
Their seven type/proof hash changes are ledgered. All other old signatures,
attributes, declaration docstrings, definition bodies and raw proof bodies
remain exact. The old generated `frobeniusZPow.eq_1` placement is explicit.

Claude supplied frozen source-only drafts. Codex verified two draft hashes
and seven main dependency hashes against `7681ac3`, together with the
owned finite-base Soundness input `9427859f`. The frozen draft compiles
unchanged. Reviewed original and final eighteen-record signatures and raw
proof bodies agree exactly; all eighteen public declarations use standard
axioms. Fourteen identical original/final typed interfaces test all seven
finite-base wrappers, generic exponent conversion, the two semantic
equivalences, same-parameter class description, characteristic-zero literal
parameter equality, anchor-independent class membership and finite-base
class membership. The characteristic-zero test has no finite-base assumption.
A harness namespace typo and accidental literal Status newline escapes were
repaired privately before the green gates; no main code contained placeholders.

The R1/R2 displayed proofs depend on the refuted literal RatioEq/JMul semantics.
This dependency was reported on #23 and #9 before adding a source warning.
The original propositions and proofs are preserved. Their outputs remain the
explicit inputs of conditional point propagation, rather than proved recovery.

The full library build passes in 48.01 seconds (peak family RSS 8.33 GiB,
minimum available memory 33.94 GiB), and the rendered book in 10.00 seconds,
with no touched-module diagnostics. The shared check reproduces all eighteen
signatures and raw bodies, standard-axiom reports and fourteen interfaces
(6.00 seconds, peak 2.61 GiB, minimum available 36.70 GiB); code bytes match
the private accepted candidate. Hygiene covers 234 library files. All 78 old
HTML paths remain among 79 pages; all four new docstrings, explicit completeness,
finite-base soundness and open class-operation boundaries pass inspection.
The frozen 117-item notice is retained. The first TeX render found an overfull
line joining long theorem names; splitting the sentences fixes it. Two-pass
TeX now has no undefined references or overfull boxes and remains 56 pages,
with visual review of pages 32–34 and 38–40. The original R1/R2 propositions
and proofs and the FrobClass namespace are byte-exact with the pushed baseline.
The continuation-text integration assertion needed a documentation-only match
repair before acceptance; all eight scoped paths are now complete. Final
full build/book and exact staged-byte checks follow before commit and push.
Unconditional ACF completeness, the original simultaneous-representative
calculation, setoid laws, the coordinate bijection, corrected fixed-class
operations, ratio semantics, totalization, R1/R2 and reconstruction existence
remain open. The frozen M4a chain is untouched.


## Coordinates on the fixed Frobenius class (#23)

`Interpretation/ClassCoordinates` proves blueprint Lemma `mu-bij`.
`eq_of_jTupleOf_eq` shows that two tuples with the same literal parameter
coincide only if their first field coordinates coincide. It uses rank-five
freshness and the accepted arbitrary-field j-rigidity, with the exponential
characteristic chosen internally as `ringExpChar k`. The transcendental
parameter separates natural Frobenius exponents; in characteristic zero
Frobenius is the identity. This injectivity needs no perfection, relative
algebraic closedness, infinite base or configuration-completeness input.

`jClassEquiv` is the actual coordinate equivalence from the geometric
`FrobEq` class of `j(x₀,a)` onto the elements outside `racl k {a}`.
The inverse sends such an element to its semantic tuple, with independence
supplied by exchange. Surjectivity onto the geometric class uses the accepted
class description, keeping perfection, rank five and ACF `JCompletenessACF`
explicit. `jClassEquiv_jTupleOf` gives the blueprint evaluation formula
`μ(j(x,a)) = x`. These are three public declarations with two private
helpers, all consumed by the displayed coordinate bijection. No generated
declaration is introduced.

Claude supplied the frozen source-only draft `5ce5c0fb`. Codex verified
all eight dependency hashes against pushed `2ec826b`, then compiled it
independently. The initial bijective-constructor placeholders did not infer
the independence proof terms through the private encoding definition; the
reviewed original supplies the existing private proofs explicitly. Frozen
source provenance is retained. Original and final five-record signatures and
raw proof/definition bodies agree exactly, with unchanged statements,
attributes and declaration docstrings. All three public and both private
axiom reports are standard, including the private encoding definition.

Nine identical original/final interfaces pass with independent universe
levels. They include arbitrary-field, finite-base and characteristic-zero
injectivity, the actual geometric-class/domain equivalence, bijectivity,
coordinate evaluation, inverse encoding, every outside-closure coordinate
and a finite-base equivalence. The equivalence-valued harness examples were
marked noncomputable, and private Status newline escapes were corrected
before the green gates. Main code contains no proof placeholders.

The full library build passes in 38.01 s (8.19 GiB sampled peak family RSS,
minimum 34.45 GiB available); the book passes in 10 s. Shared probes pass in
8 s, reproducing all five signatures and raw bodies exactly, both private
and all public standard axiom reports, and the same nine typed interfaces.
All 235 library files are free of proof placeholders and project axioms.
The book has 80 HTML pages, retaining all 79 old paths and displaying the
three new docstrings, the explicit completeness input and the open arithmetic
scope. The frozen 117-declaration M4a page is preserved. Two source passes
produce 56 pages without undefined references or overflow. The actual
changed page 34 was rendered and visually checked; the original coordinate
lemma and proof are byte-exact. Both existing module namespaces are also
byte-exact; only their status headers changed. Final full build/book checks
are repeated after recording these results.
Corrected fixed-class generic operations are the next consumer. Unconditional
ACF completeness, the original simultaneous-representative calculation,
setoid laws, ratio semantics, totalization, R1/R2 and reconstruction existence
remain open; the frozen M4a chain is untouched.

## Corrected generic arithmetic on the fixed class (#23)

`Interpretation/ClassArithmetic` computes the four coupled EH95 relations
on the original geometric Frobenius class. If two class members satisfy
`PointTripleIndependent` on their first coordinates and the parameter,
then every `JAddRel`, `JMulRel`, `JSubRel` or `JDivRel` output belongs to
the same class and its `jClassEquiv` coordinate is the sum, product,
difference or quotient of the input coordinates. Perfection, rank five,
the exponential characteristic and still-open ACF J-completeness remain
explicit. No relatively closed or infinite base hypothesis is used.

One private helper presents the two geometric inputs as tuples with the
same literal parameter. The accepted rank-three closure lemma supplies
independent generators; the accepted coupled generic semantics gives the
output tuple, soundness gives its class membership, and the coordinate
evaluation law gives the field formula. The predicates are geometric
meet/join relations, and the genericity hypothesis remains geometric;
no semantic redefinition is introduced.

Claude's immutable source-only draft `2e59baa0` was recorded against local
`2df132b` during transient GitHub write failures. That exact checkpoint
was subsequently pushed before this review. Codex checked all seven input
hashes against the published pin. The frozen draft compiled without repairs.
Original and final private chains pass in 8 s each, with all five signatures
and raw proofs exact, four public and one private standard axiom reports,
and no generated declarations. Twelve byte-identical interfaces pass with
independent universe levels: all four operations over arbitrary bases,
finite bases and characteristic zero. Only the module status header changes
from the immutable draft; statements, attributes and declaration docstrings
are exact.

Four existing module namespaces are byte-exact; their status headers now
point to the conditional generic class semantics. The book displays all
four results. The source retains the original literal definitions, theorem
statements and historical proofs. A residual blanket assertion that all
transcription-table items were already proved was reported on issue #1
(comment 6041011479) before its status prose was corrected; the original
wording is retained in a source comment.

The full library build passes in 36.01 s (10.19 GiB sampled peak family
RSS, minimum 34.98 GiB available); the book passes in 8 s. Shared artifact
probes pass in 6 s, reproducing the same five signatures/raw proofs, four
public and one private standard axiom reports, and twelve typed interfaces.
All 236 library files pass proof-placeholder/project-axiom hygiene. The
book has 81 HTML pages, retaining all 80 old paths and displaying all four
docstrings with geometric genericity and explicit completeness. The frozen
117-declaration M4a page is preserved. Two source passes produce 56 pages
without undefined references or overflow. Actual changed pages 1, 34–36,
38 and 52 were rendered and visually checked, including the ratio warning
after normalizing extracted whitespace to identify it. All 49 original
mathematical statement blocks and 44 original proof blocks are byte-exact.
The original checklist status wording is retained as a source comment.
Final full build/book checks are repeated after recording these results.
Non-generic totalization, corrected ratio semantics, setoid laws, unconditional
ACF completeness, the bypassed simultaneous-representative obligation,
R1/R2 and reconstruction existence remain open. The frozen M4a chain is
untouched.

## Corrected ratio semantics with the exact rank-five budget (#23)

`Interpretation/Ratio` replaces the empty M0 skeleton with the corrected
geometric ratio predicate and its forward, reverse and equivalence theorems.
The predicate retains four products through four auxiliary class members,
using the coupled `JMulRel` and a `PointTripleIndependent` clause for each
product. It contains no semantic coordinates. The four input class
memberships are explicit in the semantic theorems.

`RatioEq.div_eq` applies to every geometric witness, converts its four
products to field equations by the accepted generic class semantics, and
cancels nonzero coordinates. `ratioEq_of_div_eq` presents the four input
members with the same literal parameter. Equality of ratios recovers one
coordinate from the other three; a multiplier fresh over the explicit
four-element set consisting of the parameter and those three coordinates
therefore avoids all five values. The rank-five oracle supplies it.
Four independent triples establish all four product genericity clauses.
Their pair restrictions provide independence and class membership for
all auxiliary tuples, without duplicating or promoting the private
coordinate-pair helper. `ratioEq_iff` gives the exact decoded-ratio
equivalence. Perfection, exponential characteristic, rank five and
still-open ACF J-completeness remain explicit throughout the semantic
theorems; the predicate itself is geometric over arbitrary fields.

Claude supplied frozen source-only draft `f1faad39`. Codex checked all
eleven dependency hashes and the original empty skeleton against pushed
`04846d1`, independently audited the equations and rank budget, and compiled
the immutable source without repairs. The old skeleton has zero records.
Original and final six-record signatures and raw proof/definition bodies
agree exactly. All four public and two private axiom reports are standard,
including the geometric predicate definition. No generated declaration
is introduced, and no statement, attribute or declaration docstring changes.
The private source passes in 12 s and the final chain in 8 s.

Nine byte-identical original/final interfaces and behavior probes pass
with independent universe levels. They check arbitrary bases, finite
bases and characteristic zero, the universal forward witness and reverse
orientation, repeated input pairs, pair reversal, chained decoded equalities
and all diagonal pairs representing one. Genericity is required in the
witness products, not between numerator and denominator. These probes do
not package a main ratio setoid or construct its quotient/decoding.

Four existing module namespaces are byte-exact; only status headers change.
The original literal ratio definition and refutation remain preserved, and
the source displays the corrected geometric predicate separately, with
the explicit unproved completeness input.

The full library build passes in 32.01 s (6.69 GiB sampled peak family RSS,
minimum 36.79 GiB available), and the book in 8 s. Shared artifact probes
pass in 6 s with the same six signatures/raw bodies, all four public and
two private standard axiom reports and nine interfaces/behaviors. All
236 library files pass proof-placeholder/project-axiom hygiene. The book
has 82 HTML pages, preserving all 81 old paths and the frozen
117-declaration M4a page; four new docstrings display each product's
geometric genericity, explicit completeness and open quotient/totalization
scope. Source verification now requires stable auxiliary/contents output:
the initial two-pass output had stale contents page references. Four passes
produce 57 pages with stable auxiliary, contents and bookmark hashes and
no undefined references, overflow or rerun warnings. Actual changed pages
1, 2, 34–37 and 53 were rendered and visually checked after convergence.
All 49 original mathematical statement blocks and 44 original proof blocks
remain byte-exact. Final full build/book checks are repeated after recording
these results.
Ratio setoid/quotient construction, decoding, non-generic totalization,
field graphs, unconditional completeness, the bypassed representative
obligation, R1/R2 and reconstruction existence remain open. The frozen
M4a chain is untouched.

## The geometric ratio quotient and bijective nonzero decoding (#23/#8)

`Interpretation/Decode` proves the corrected ratio relation an equivalence
on pairs of members of the fixed geometric class, packages its setoid and
quotient, and decodes that quotient bijectively to the actual nonzero
field elements `Kˣ`. These six public declarations establish the nonzero
part of blueprint `decode-equiv`; every semantic statement and definition
keeps perfection, exponential characteristic, rank five and the still-open
ACF `JCompletenessACF` input explicit. The setoid relation itself is the
geometric `RatioEq`, with no semantic replacement.

`ratioDecode` descends by `Quotient.lift` and the universal corrected
ratio semantics. Its evaluation law computes a representative as the
ratio of its two coordinates. Injectivity uses the reverse ratio
implication. For surjectivity, a multiplier is fresh over the explicit
three-element set `{a,z,x₀}`; cancellation of the nonzero `z` shows
both `t` and `z*t` avoid the closure of `{x₀,a}`. Independent
triples and their pair restrictions supply the two class members
`j(z*t,a)` and `j(t,a)`, with ratio `z`. No pair helper is
promoted or duplicated, and the one exclusion calculation stays in place.
The theorem retains the uniform rank-five input used for class soundness.

The one new coordinate helper `jClassEquiv_ne_zero` is consumed by the
quotient decoding and by a separately ledgered proof-only cleanup of
`RatioEq.div_eq`. All eleven older signatures, attributes and declaration
docstrings are exact. Ten older raw proof/definition bodies are exact;
only that named proof changes. All eighteen original/final signatures
and raw bodies agree exactly. All fourteen public and four private axiom
reports are standard, including the three new definitions. There are no
new private helpers or generated declarations.

Claude froze source-only bundle `34d2ca37` (Decode), `09be3b60`
(coordinates) and `1b186aab` (Ratio) against pushed `2cb0133`. Codex
checked eight dependency hashes and both byte-exact bases, independently
reviewed the geometric quotient and freshness budget, and compiled all
three frozen sources without repairs in 14 s. Final sources pass in 10 s;
a private quotient-equality probe required the setoid supplied explicitly
to `Quotient.sound`, then all fifteen interfaces pass in 4 s on both
overlays. They use independent universes and check arbitrary/finite bases,
characteristic zero, actual geometric setoid relation, both evaluation
routes, quotient equality, global injectivity, surjectivity and the
nonzero helper. No source proof needed repair.

Three additional existing module namespaces remain byte-exact; their
status headers now identify the nonzero decoding. Original mathematical
statement/proof blocks and the literal refutation remain preserved.
The full library build passes in 36.01 s (10.18 GiB sampled peak family
RSS, minimum 36.38 GiB available); the book passes in 8 s. Shared artifact
probes pass in 6 s, reproducing all eighteen signatures/raw bodies, fourteen
public/four private standard-axiom reports and fifteen interfaces.
All 237 library files pass proof-placeholder/project-axiom hygiene.
The book has 83 HTML pages, retaining all 82 old paths and the frozen
117-declaration M4a page. Seven new docstrings display the geometric setoid,
three-element freshness, explicit completeness and still-open zero/TOT
scope. Four source passes produce 57 pages with stable auxiliary, contents
and bookmark hashes, with no undefined references, overflow or rerun
warnings. Actual changed pages 1, 2, 34–37 and 53 are rendered and visually
checked; page 36's final equation ends at 771.93 pt, before the footer
at 787.71 pt. All 49 original mathematical statement blocks and 44 proof
blocks stay byte-exact. Final full build/book checks repeat after recording
these results.
Adjoining zero, non-generic totalization, quotient field operations, global
Frobenius setoid, unconditional completeness, simultaneous representatives,
field graphs, R1/R2 and reconstruction remain open. The frozen M4a chain
is untouched.

## The adjoined-zero carrier and full decoding equivalence (#23/#8)

`Interpretation/Interp` defines the corrected geometric ratio quotient
with an adjoined zero, as `RatioInterp := WithZero (Quotient ratioSetoid)`.
Its `ratioInterpDecode` is an actual equivalence onto all of `K`,
with the named zero and representative evaluation laws both reducing by
`rfl`. This proves the full corrected blueprint `decode-equiv`.
Perfection, exponential characteristic, rank five and the still-open ACF
`JCompletenessACF` input remain explicit throughout. No quotient field
operations or transported field structure are installed before totalization.

The proof uses Mathlib directly: `Equiv.optionCongr` extends the accepted
nonzero decoding, and `WithZero.withZeroUnitsEquiv.toEquiv` identifies
the units with an adjoined zero with the field. The carrier abbreviation
is reducible, with the actual geometric quotient inside it. There is
no local bijectivity or zero-detection boilerplate.

Claude supplied source-only draft `a56e1fa8` pinned to pushed `e15d81d`.
Codex checked the three local and two Mathlib hashes, independently
audited the construction and compiled its immutable source without
repairs in 6 s. The Status-only final chain passes in 8 s.
All four original/final signatures and raw proof/definition bodies
are exact, and all four public axiom reports are standard, including
both definitions. No private helper or generated declaration is added.
Fifteen byte-identical interfaces pass on both overlays, with independent
universes, arbitrary/finite bases and characteristic zero. They check the
literal WithZero quotient carrier, equivalence onto all K, named zero and
representative evaluation, global zero detection and surjectivity, both
inverse laws, and that genuine quotient representatives decode nonzero.

Seven existing module namespaces remain byte-exact. Six headers identify
the new full decoding; the field skeleton imports its carrier but retains
open field operations, total graphs, naturality and reconstruction.
Original mathematical statement/proof blocks and literal refutation
provenance remain preserved.
The full library build passes in 38.01 s (10.17 GiB sampled peak family
RSS, minimum 36.48 GiB available), and the book in 8 s. Shared artifact
probes pass in 6 s with all four exact signatures/raw bodies, all four
public standard-axiom reports including both definitions and fifteen
interfaces. All 238 library files pass proof-placeholder/project-axiom
hygiene. The book has 84 HTML pages, preserving all 83 old paths and the
frozen 117-declaration M4a page; four new docstrings show the actual
carrier, explicit completeness, zero/representative evaluations and
still-open field/TOT scope. Source checking caught one overfull line in
the new evaluation-law prose, which was fixed by a paragraph break before
acceptance. Four passes then produce 58 pages with stable auxiliary,
contents and bookmark hashes, with no undefined references, overflow
or rerun warnings. Actual changed pages 1, 2, 34–37 and 54 are rendered
and visually checked. All original 49 mathematical statement blocks
and 44 proof blocks remain byte-exact. Final full build/book checks
repeat after recording these results.
Non-generic totalization, quotient field operations, global Frobenius
setoid, unconditional completeness, simultaneous representatives, field
graphs, R1/R2 and reconstruction remain open. The frozen M4a chain is
untouched.

## Corrected two-addition total negation and shared geometric genericity (#23/#8)

`Interpretation/TotalOps` begins corrected non-generic totalization with
the blueprint's two-addition negation detour. `JNegTotalRel` retains
two auxiliary class members `z,r`, the coupled clauses `u+z=r`
and `v+r=z`, and a geometric `PointTripleIndependent` input clause
for each addition. The predicate contains no semantic coordinates.
`JNegTotalRel.neg_eq` applies to every witness, giving `µ(v)=-µ(u)`.
The converse presents inputs with the common literal parameter and uses
a multiplier fresh over the explicit two-element set `{a,x}`. Insertion
gives `(x,z,a)` independent; mutual closure membership gives
`(-x,x+z,a)` independent. The witnesses `j(z,a)` and `j(x+z,a)`
are both class members and both additions are generic.
`jNegTotalRel_iff` proves the exact corrected semantic equivalence,
under explicit perfection, exponential characteristic, uniform rank five
and still-open ACF J completeness, over arbitrary base fields.
No genericity between the original two inputs is assumed.

The one existing `pointTripleIndependent_jTupleOf` helper moves from
private Ratio to public `FrobLinkSoundness` before any `include htr`.
Its type, declaration docstring and raw proof are exact. Its signature
uses no perfection, characteristic, rank-five, completeness or infinite
base assumption. Named consumers are four ratio products, two negation
additions and the direct-link proof. Only the named
`directFrobLink_jTupleOf` proof replaces its inline duplicate with
this helper. No new rank, linear or pair helper is introduced.

Claude supplied frozen sources `94853196` (TotalOps), `0964b535`
(soundness) and `e9fcbc6d` (Ratio) against pushed `0231f69`.
Codex checked eight dependency hashes and exact base files, independently
audited the relation and witness budget, and compiled the immutable
bundle without proof repairs in 14 s. Two `show` style warnings are
fixed to `change` in the private final; the final passes in 10 s
with no warning and the same kernel proof bodies.

The thirteen older signatures, attributes and declaration docs are
exact except the single ledgered helper module/visibility change.
Twelve older raw bodies are exact; only the direct-link proof consumes
the helper. All seventeen original/final signatures and raw bodies are
exact. All sixteen public and one private axiom reports are standard,
including the new geometric predicate. Four public declarations are new
and one existing helper is promoted/moved; no private/generated
declaration is added.

Ten byte-identical original/final typed interfaces pass with independent
universes. They check arbitrary and finite bases, characteristic zero,
every witness and the converse orientation, reversal, tuple-level double
negation, characteristic-zero irreflexivity, the pure geometric predicate,
and the moved helper without rank/perfection/completeness hypotheses.
The original literal negation and totalization expressions/derivation
stay byte-exact, in addition to the original mathematical statement and
proof blocks. They remain historical/open because their argument uses
the refuted literal generic semantics; no separate negation-detour
counterexample is claimed.
The full library build passes in 40.01 s (7.71 GiB sampled peak family
RSS, minimum 36.44 GiB available), the book in 8 s and shared probes in
6 s. Shared artifacts reproduce all seventeen exact signature/raw-body
records, sixteen public/one private standard-axiom reports and ten
independent interfaces. All 239 library files pass placeholder/project
axiom hygiene. The book has 85 HTML pages, retaining all 84 old paths
and the frozen 117-declaration M4a page. Five new/promoted docstrings
show the two geometric additions, each genericity clause, fresh
two-element set, explicit completeness and still-open full addition/TOT
scope. Four source passes converge to 58 pages with stable auxiliary,
contents and bookmarks, with no undefined references, overflow or rerun
warnings. Actual changed pages 1, 2, 35 and 36 are rendered and visually
checked. The source paragraph audit restores the abstract's explicit
completeness phrase before acceptance. All original49 mathematical
statement blocks/44 proofs and the literal negation/TOT derivation remain
byte-exact. Final full build/book checks repeat after recording these results.
Total nonzero addition, full totalization, quotient field operations,
global Frobenius setoid, unconditional completeness, simultaneous
representatives, total graphs, R1/R2 and reconstruction remain open.
The frozen M4a chain is untouched.

## Corrected total nonzero addition with derived output membership (#23/#8)

`Interpretation/TotalOps` now proves the corrected counterpart of
blueprint `lem:total-nonzero-add`. `JAddTotalNZRel` retains four
auxiliary class members `z,nz,r,s`, corrected negation of `z`,
and three coupled generic additions `u+z=r`, `v+nz=s` and
`r+s=w`. Its geometric definition does not assume output membership
or input genericity and contains no semantic coordinates.

`JAddTotalNZRel.exists_mem_add` applies to every witness, deriving
`w` in the class and `µ(w)=µ(u)+µ(v)`. The converse presents all
three tuples with the common literal parameter, so `c=x+y`.
One element fresh over the explicit three-element set `{a,x,y}`
gives `(x,z,a)` and `(y,-z,a)` by insertion, and
`(c,x+z,a)` because membership of `x+z` in its closure would
put `z=(x+z)-x` in the original closure. Mutual closure membership
gives `(x+z,y-z,a)`. The four canonical tuples are class members;
the negation theorem and the three generic-sum theorems provide the
geometric witnesses. `jAddTotalNZRel_iff` leaves membership in the
right-hand existential for arbitrary raw output tuples.

This is class-level totalization for sums outside `racl k {a}`,
a stronger condition than being merely nonzero in `K`. Perfection,
exponential characteristic, uniform rank five and still-open ACF
J completeness remain explicit over arbitrary base fields. The local
freshness set has size three; no claim lowers the uniform rank bound.

Claude supplied immutable source `64ba2297` against pushed
`173d6ec`, with ten exact dependency hashes and an exact base copy.
Codex verified its append-only namespace and compiled the frozen source
without repairs in 14 s (peak 2.62 GiB, minimum available 36.59 GiB).
The header/status-only final passes in 10 s with no warnings and its
entire namespace is byte-exact to the draft. All nine original/final
signature and raw-body records are exact: four old declarations, four
authored new public declarations, and one generated match definition
`jAddTotalNZRel_iff.match_1_1` from existential destructuring.
All eight authored public and the generated definition use only
standard axioms, including both geometric predicates. No private
helper is added, and all four old attributes/docstrings/types/bodies
remain exact.

Ten byte-identical independent interfaces pass in separate universes:
arbitrary and finite bases, characteristic zero, every-witness output
membership/value, constructed converse, canonical raw-output equivalence
with the blueprint's actual Out condition, symmetry, raw-tuple
functionality, the pure geometric definition and the zero obstruction.
All original 49 mathematical statement blocks, 44 proof blocks and
the literal negation/TOT expressions and argument stay byte-exact.
The literal detour remains historical/open; no separate counterexample
is asserted. Full library/book passes in 46.01/10.00 s, with peak
8.36 GiB and minimum available 34.24 GiB for the library. All nine
independent/shared signature and raw-body records, eight authored public
and one generated standard-axiom reports and all ten interfaces pass.
Hygiene covers 239 library files with no proof placeholders or project
axioms. The book preserves all 85 older HTML paths among 86 and checks
the four new declaration docs, explicit completeness, derived output
membership, exact Out condition and open full-TOT obligations.
Four source passes converge in auxiliary/contents/bookmark hashes,
with 59 pages and no undefined references, overflows or rerun warnings.
Changed pages 1, 2 and 36 have visual review. All original 49 statements,
44 proofs and literal negation/TOT derivation remain exact.
Final documentation library/book and five-path staged-byte gates follow
before commit and push.

The prior `173d6ec` CI library/book job passed, but the overall
run `37655075766` concluded failure with no failed or deploy job.
GitHub refuses retrying that workflow. Issue REST PATCH failures were
bypassed with repository-scoped GraphQL, without changing settings.

Full ratio-carrier totalization, quotient field operations, geometric
graphs, global Frobenius setoid, unconditional completeness, simultaneous
representatives, R1/R2 and reconstruction remain open. The next
read-only peer audit checks the common-denominator addition graph.
The frozen M4a chain is untouched.

## Corrected total geometric operation graphs (#23/#8)

`Interpretation/Field` now proves the corrected totality/functionality
and decoded-operation part of blueprint `thm:total-field-graphs`.
`RatioAddGraph` retains the two named-zero cases and existential
class-member representatives with a common denominator: corrected
negation gives zero, or corrected total nonzero addition gives a ratio.
`RatioMulGraph` retains zero factors and two generic coupled products,
on the numerators and denominators. Quotient equalities use the actual
corrected geometric `ratioSetoid`. Definitions contain no coordinates,
choices or `Quotient.out`.

Both decode iffs apply to every witness, and their converses construct
witnesses for arbitrary carrier elements. Addition uses a common
denominator fresh over `{a,c,d}`, with class members supplied by the
existing coordinate equivalence inverse. Its inner addition detour may
use a fifth independent element, so the full construction retains the
uniform rank-five bound. Multiplication uses successive freshness over
`{a,c,d}` and `{a,c,d,b}`, giving the two independent triples
`(b,e,a)` and `(c*b,d*e,a)`. There is no extra sixth element.
Both `existsUnique` theorems use decoding bijectivity. Perfection,
exponential characteristic, rank five and still-open ACF J completeness
stay explicit, over arbitrary base fields. Common denominators are
existential: a prescribed one may make the numerator sum algebraic over
the parameter, even when the decoded sum is nonzero.

Claude supplied frozen Field `c2870a42`, Ratio `a2876cd8` and
ClassCoordinates `b125d8dd` against published `ebad9db`.
Codex verified thirteen input hashes and three exact bases, then
compiled the seven-module chain in 18 s (peak 2.65 GiB, minimum available
37.45 GiB), without source repairs or warnings. The initial six-second
attempt stopped on a private overlay symlink/root-path harness error
before Field compilation. Materializing unchanged dependency sources
fixed the harness. The final changes only module headers/status and
preserves all seven namespaces.

All seventeen original/final signature and raw-body records are exact.
All eleven old types/docs/attributes/raw bodies are exact except the
two ledgered private-to-public flags on `mul_fresh_notMem` and
`pair_of_notMem`. Their types/docs/proofs are unchanged, with named
old ratio/class and new graph consumers. Six public declarations are
new; no private/generated declaration is added. All sixteen public
and one private axiom reports are standard, including both geometric
graph definitions and the existing class encoding.

Twenty-two byte-identical independent-universe interfaces pass.
They cover arbitrary and finite bases, characteristics zero and two,
every witness and both converses, actual totality/functionality,
named-zero laws, geometric quotient representative invariance,
associativity/distributivity without carrier field operations,
base-valued inputs, opposite-input zero and rank-free helper types.
Only private interface-harness zero/numeral normalization needed repair.
Independent earlier probes also checked the exact common-denominator
and two-generic-product freshness budgets.

The recovery warning's blanket open-status qualification was reported
on issues 9 and 23 before its current-scope update; its earlier wording
is preserved in a source comment. Conditional total graphs do not
discharge R1/R2 or unconditional completeness. All original 49
statement blocks, 44 proof blocks and the literal total-field-graphs
argument remain exact. Full library/book passes in 50.01/10.00 s
(peak 9.84 GiB, minimum available 33.27 GiB), with no touched-module
warnings. All seventeen independent/shared records, sixteen public and
one private standard-axiom reports and twenty-two interfaces pass.
Hygiene covers 239 library files; all 86 old HTML paths survive among
87, with eight new or promoted docs and the frozen M4a status checked.
Four source passes converge in auxiliary/contents/bookmark hashes,
with 59 pages and no undefined references, overflows or rerun warnings.
Changed pages 1, 2, 39, 40 and 41 have visual review. New prose
overflows were fixed before acceptance, and the corrected subsection
was moved before the literal heading to keep that heading with its
original prose. The original mathematical blocks and literal argument
remain exact. Final documentation library/book and ten-path staged-byte
gates are required before commit and push.

Transported field structure, graph naturality, global Frobenius setoid,
unconditional ACF completeness, simultaneous representatives, R1/R2
and reconstruction remain open. A private downstream audit confirms
Mathlib's `Equiv.field` and `Equiv.ringEquiv` can give a named
field structure/decoding equivalence, preserving the named zero.
No carrier Field instance or corresponding declaration is installed.
That blueprint obligation remains even if a later route bypasses it.
The frozen M4a chain is untouched.

## Named interpreted field structure and geometric operations (#23/#8)

`Interpretation/Field` now proves the corrected conditional
field-transport obligation after the full geometric graphs. The named
reducible `ratioInterpField` uses Mathlib's `Function.Injective.field`
and the existing carrier zero, with Mathlib equivalence-transfer data
for all other operations, scalar actions and casts. It is not a global
instance. Its zero value and Zero structure agree definitionally with
the geometric adjoined zero, checked using Mathlib's instance-diamond
standard `with_reducible_and_instances rfl`. The stricter
`with_reducible rfl` alone cannot unfold the native instance constant.
There is no zero bridge lemma or additional helper chain.

`ratioInterpRingEquiv` is the actual decoding ring equivalence onto
all of `K`, built using Mathlib's `Equiv.ringEquiv`. Its map and
inverse are exactly the existing decoding equivalence. The two
`ratioAddGraph_iff_eq_add` and `ratioMulGraph_iff_eq_mul` theorems
identify the geometry-only graphs with the installed field operations.
They supply the named consumer for field transport in blueprint
`decode-equiv` and I5c; later graph-preserving carrier transport and
interpreted reconstruction consume these structures and laws.

Claude supplied frozen Field `afe43877` against published
`266cbfb`, with eleven exact project/Mathlib dependency hashes and
an exact base copy. Codex compiled the source unchanged in 12 s
(peak 2.66 GiB, minimum available 38.78 GiB). Two new-proof references
were deprecated in Mathlib. The final replaces them by the literal
Mathlib alias body `Equiv.eq_symm_apply.symm`, without changing their
types/docs/attributes. No source proof failure or mathematical repair
was needed. The final ten-second compilation is warning-free.

All ten original/final signatures/types/docs/attributes are exact.
Eight raw bodies are exact; only the two new theorem proof references
change as ledgered. All six existing graph declarations retain their
source, signatures and raw bodies. Four public declarations are new,
with no private helpers, generated declarations or global instances.
All ten axiom reports are standard, including the Field and RingEquiv
definitions. Eleven other touched library modules change only headers,
with their namespaces exact. The incidence module also reflows one existing
overlong docstring; its five types/attributes/raw bodies stay exact, with
only that whitespace doc hash changing. The final status audit found six older
blueprint paragraphs and six upstream headers with stale scope: accepted
conditional work was listed as open, a historical empty skeleton was not
marked superseded, and supplied-witness rigidity was omitted. This stale-scope finding was
reported on issue 23 before correction; all six earlier source wordings
are retained in TeX comments. These status corrections do not change any
mathematical statement or proof.

Twenty-nine byte-identical independent original/final interfaces pass:
arbitrary and finite bases, characteristic zero, actual Field/RingEquiv
and both graph/operation signatures, native-zero value and structure
coherence, decoding/inverse equality, actual field laws/inversion,
natural and rational casts, characteristic-two actual zero-sum and its
geometric graph, both installed operation outputs, and absence of a
global Field instance. Initial interface attempts needed proof-context
instances and Mathlib's standard reducible-and-instance transparency;
these were harness changes, not source repairs.

The warning-free full library build passes in 44.01 s (peak family
7.46 GiB, minimum available 35.82 GiB); the book passes in 10 s.
Shared acceptance takes 12 s and matches the final ten Field and five
incidence signature/raw-body/axiom records, plus the identical 29
interfaces. Fifteen compiled declarations have standard axioms.
Hygiene checks 239 library files without proof placeholders or project
axioms. The book has 88 HTML pages and retains all 87 prior paths,
including the frozen 117-item page and all four new declaration docs.
Four stable source passes produce 60 pages without unresolved labels,
overflow or rerun warnings. Actual final pages 1, 2, 34, 35, 36, 37, 38
and 40 pass visual review. All original 49 statements/44 proofs and the
literal TOT/interpreted-reconstruction argument remain exact; all six
prior status qualifications are preserved. Final documentation
library/book and exact sixteen-path staged-byte checks remain required
before commit and push. Perfection, uniform rank five and still-open ACF J
completeness remain explicit over any base field. Geometric naturality,
unconditional completeness, global Frobenius setoid, simultaneous
representatives, R1/R2 and full reconstruction remain open. The literal
source statements/proofs and frozen M4a chain remain unchanged.

## Pure geometric configuration naturality (#23/#8, I6b1)

`Config/Transport` preserves the configuration layer under an arbitrary
`ClosedIF k K ≃o ClosedIF l L`, with independent base/ambient universe
levels. Partial quadrangles transport through the existing rank and
Mathlib finite-supremum API. `QWitness.map` maps all 21 raw points;
its three join laws are consumed by `QWitness.Psi.map`, which handles
all 24 actual clauses, including all three universal-point clauses and
its quadrangle. Multiplication diagrams transport, and applying the
same maps to the inverse gives the geometric Q/Q′/J iff laws. These
are the configuration consumer for blueprint `interpreted-reconstruction`
and I6b1, with corrected interpretation transport as the next consumer.

Claude supplied frozen source `1dc2a300` against published `ccec377`,
with eleven exact project/Mathlib input hashes and six exact baseline
copies. Codex compiled it unchanged and warning-free in 8.05 s
(peak 2.37 GiB, minimum 37.14 GiB available). The final changes only the
module status qualification and passes in 8.04 s. Ten authored public
declarations and two generated equation lemmas are present
(`QWitness.map.eq_1` and `JGeom.eq_1`), with no private helpers
or global instances. All 12 signatures/types/docs/attributes/raw bodies
and standard-axiom reports are exact between original and final,
including the witness definition. No mathematical or proof repair
was needed.

Sixteen byte-identical original/final independent interfaces pass,
covering the ten exact cross-universe types, full raw-witness round trip,
whole-Psi and partial-quadrangle reflection, successive unrelated
lattices, finite bases and characteristic two. The separate existing-API
probe needed a typed finite-join equality before rewriting a RankEq
goal; that was a harness adjustment, not a source repair.

The latest prior named-field checkpoint `ccec377` has full build/book
and deployment CI success in run 37668882418. The warning-free full library passes in 44.24 s (peak family
11.32 GiB, minimum 34.50 GiB available); the rendered book passes in
10.06 s. Shared acceptance passes in 6.03 s, matching all 12 compiled
records and the identical 16 interfaces. Hygiene checks 240 library
files without proof placeholders or project axioms. The book has 89
HTML pages, retaining all 88 prior paths and all ten declaration docs,
including the frozen 117-item record. Four stable source passes produce
60 pages without undefined labels, overflow or rerun warnings. Actual
final pages 1, 2, 3, 41, 42 and 43 pass visual review. The final
documentation library/book and exact five-path staged-byte checks are
required before commit and push. No existing Lean declaration is changed.
No original 49 source statements or 44 proofs, literal TOT or interpreted
reconstruction arguments, or frozen 117-item M4a record are changed.

This configuration stage needs only Field/Algebra structures and the
closed-lattice order isomorphism, with no semantic, perfection,
rank-five or freshness assumption. Corrected relation/carrier transport,
geometric operation-graph naturality and interpreted reconstruction
remain open. Perfection/rank-five/ACF completeness stay explicit for
the earlier interpreted-field route; unconditional completeness, the
global Frobenius setoid, literal source arguments and R1/R2 remain open.

## Geometric Frobenius-link naturality (#23/#8, I6b2a)

`Interpretation/FrobTransport` proves five purely geometric iff laws
for an arbitrary `ClosedIF k K ≃o ClosedIF l L`: the derived product
relation, geometric J-locus, point-triple independence, directed links
and the two-edge bridge relation. All five directed-link fields
transport in both directions, including a single common multiplier
across all three rigid coordinates. The bridge tuple and both edge
orientations are preserved. The original relations and all existing
library declarations are unchanged. Invariance supplies neither
FrobEq reflexivity/transitivity nor functionality of the refuted
MulPoint relation. SumPoint is omitted because the corrected route
has no named consumer for a separate transport declaration.

The named consumers are directed-link transport, bridge transport,
corrected totalization/ratio transport and the later class/carrier map
in blueprint `interpreted-reconstruction`. There are no duplicate
`.map` or public direct-edge lemmas. Mathlib's `Equiv.piCongrRight`
supplies the tuple bijection; the edge iff is local to the bridge proof.

Claude supplied frozen source `4bd522d1` against published `47bd9f1`,
with eight exact project/Mathlib input hashes and two exact baselines.
Codex compiled it unchanged and warning-free in 6.04 s (peak 2.61 GiB,
minimum 38.47 GiB available). The final changes only its module status
and passes in 8.06 s. Five authored public declarations and one
generated `PointTripleIndependent.eq_1` equation lemma are present,
with no private helper or global instance. All six original/final
signatures/types/docs/attributes/raw bodies and standard-axiom reports
are exact. No source or interface-harness repair was needed.

Twelve byte-identical original/final independent interfaces pass:
five exact cross-universe signatures, an actual arbitrary raw-class
bijection via Mathlib `Equiv.subtypeEquiv`, its RFL pointwise map
and inverse round trip, a single-multiplier output, composition over
six universe levels, finite bases and characteristic two. This raw
class bijection uses invariant predicates and does not assume a
global Frobenius equivalence relation. The separate existing Mathlib
tuple-quantifier/inverse/parameter-equality API probe also passes.

The prior configuration checkpoint `47bd9f1` has full library/book
and deployment CI success in run 37672585265. The warning-free full library passes in 46.29 s (peak family
8.18 GiB, minimum 36.47 GiB available); the book passes in 10.07 s.
Shared acceptance passes in 6.04 s, matching all six compiled records
and the identical twelve interfaces. Hygiene checks 241 library files
without proof placeholders or project axioms. The book has 90 HTML
pages, retaining all 89 prior paths and all five declaration docs,
including the frozen 117-item record. Four stable source passes produce
60 pages without undefined labels, overflow or rerun warnings. Actual
final pages 1, 2, 3, 41, 42 and 43 pass visual review. Final
documentation library/book and exact five-path staged-byte checks are
required before commit and push. Original 49 source statements and
44 proofs, literal TOT/interpreted reconstruction arguments and the
frozen 117-item M4a record remain exact.

This relation stage takes no semantics, completeness, perfection,
rank-five, exponential-characteristic, Infinite or freshness input.
N2b coupled arithmetic and N2c totalization/ratio transport remain
held, as do the quotient-carrier and operation-graph naturality and
interpreted reconstruction. Earlier interpreted-field semantics keep
perfection/rank-five/ACF completeness explicit. Unconditional
completeness, the global Frobenius setoid, literal source obligations,
base recovery and scalar-one inputs remain open.

## Coupled arithmetic naturality (#23/#8, I6b2b)

`Interpretation/JArithTransport` imports only `JArithSem` and
proves four public transport laws across arbitrary closed-lattice
order isomorphisms, bases and universe levels. `jSub_map` and
`jDiv_map` hold for all closed-lattice five-tuples, with their
original coordinate order and coupling intact. Their named consumers
`jAddRel_map_iff` and `jMulRel_map_iff` preserve and reflect
the coupled sum/product relations on arbitrary point tuples.
Coordinate transport is RFL/local; the derived operations transport
locally, and Mathlib `Function.Injective.comp_left.eq_iff` reflects
the coordinate equalities. No extra normalization helper chain,
instance, genericity or semantic assumption is introduced.

The four declarations supply corrected total negation/nonzero addition
and ratio transport, and later full-carrier graph preservation, in
blueprint `interpreted-reconstruction`. No existing lattice/point
operation or interpretation definition is changed.

Claude supplied frozen source `9983d949` against published `9f9ee07`,
with eight exact project/Mathlib input hashes and two exact baseline
copies. Codex compiled it unchanged and warning-free in 8.06 s
(peak 2.62 GiB, minimum 39.08 GiB available). The final changes only
its module-status qualification and reflows that paragraph, passing
in 8.05 s. All eight original/final signatures/types/docs/attributes,
raw bodies and standard-axiom reports are exact. Four authored public
theorems and four generated equation lemmas (`jSub.eq_1`,
`jDiv.eq_1`, `JAddRel.eq_1` and `JMulRel.eq_1`) are
present, with no private helper or global instance. No mathematical,
proof or interface-harness repair was needed.

Ten byte-identical original/final independent interfaces pass:
four exact cross-universe types, whole raw-output reflection for
difference/quotient, composition over six universe levels, reflection
of actual unique point-tuple output, finite bases and characteristic
two. Separate existing-API probes for coordinate RFL, composition
injection and nested lattice formulas pass with the same narrow import.

The prior Frobenius-link checkpoint `9f9ee07` has full library/book
and deployment CI success in run 37674711938. The full library passes
in 54.35 s (peak 9.18 GiB, minimum 35.54 GiB available); the book
passes in 8.00 s. Shared acceptance passes in 6.00 s, matching all
eight compiled records and the identical ten interfaces. Hygiene checks
242 library files without proof placeholders or project axioms. The book
has 91 HTML pages, retaining all 90 prior paths and the four new
declaration docstrings, including the frozen 117-item record. Four stable
source passes produce 61 pages without undefined labels, overflow or
rerun warnings. Actual final pages 1, 2, 3, 42 and 43 pass visual
review. Final library/book and exact five-path staged-byte checks are
required before this natural checkpoint is committed and pushed. The preceding source progress paragraph still
listed coupled arithmetic as open; its scope correction was reported
on #23 before updating and its earlier wording is retained in a TeX
comment. All original 49 source statements and 44 proofs, literal
TOT/interpreted reconstruction arguments and the frozen 117-item M4a
record remain exact.

This stage takes no semantics, genericity, completeness, perfection,
rank-five, exponential-characteristic, Infinite or freshness input.
N2c totalization/ratio transport remains held, followed by carrier/
operation-graph naturality and interpreted reconstruction. Earlier
interpreted-field semantics keep perfection/rank-five/ACF completeness
explicit. Unconditional completeness, the global Frobenius setoid,
literal source obligations, base recovery and scalar-one inputs
remain open.

## Corrected totalization and ratio naturality (#23/#8, I6b2c)

`Interpretation/TotalTransport` imports only `FrobTransport`,
`JArithTransport` and `TotalOps`. Three public iff laws preserve
and reflect corrected negation, total nonzero addition and ratio
relation on arbitrary raw point tuples and arbitrary base tuples,
across independent bases and universe levels.

All 2/4/4 witness tuples are retained, with the two/three/four generic
coupled-operation clauses and every rank-three independence condition.
Mathlib `Equiv.piCongrRight` supplies witness preimages; lower
relation iff laws transfer the conjuncts. No extra hypothesis, global
setoid, private helper, instance or normalization chain is introduced.
Named consumers are class-pair quotient well-definedness and full-carrier
operation-graph preservation in blueprint `interpreted-reconstruction`.

Claude supplied frozen source `97eddeb3` against published `fb030c4`,
with eight exact project/Mathlib input hashes and four exact baselines.
Codex compiled it unchanged and warning-free in 6.00 s (peak 2.62 GiB,
minimum 37.71 GiB available). The status-only final passes in 8.00 s;
all three signatures/types/docs/attributes/raw bodies and standard-axiom
reports are exact. There are three authored public theorems, no new
generated equation lemmas and no private helper or global instance.
No source, proof or independent-interface repair was needed.

Ten byte-identical original/final interfaces pass: exact cross-universe
types, arbitrary target-output existence reflection, six-universe
addition/ratio composition, an actual corrected quotient/adjoined-zero
map under explicit semantic inputs and a supplied canonical-base image
equality, finite bases and characteristic two. Separate existing-API
probes for canonical image tuples, raw class equivalences and quotient/
option representative RFL pass without main changes.

The prior coupled-arithmetic checkpoint `fb030c4` has full library/
book and deployment CI success in run 37677086411. Three preceding
current source-progress qualifications were reported on #23 before
updating and retained in provenance comments. Three upstream transport
module status paragraphs are corrected in this checkpoint; their
namespaces are byte-exact, with combined compiled-record integrity
checks. Full library/book passes in 50.01/10.00 s (full peak 8.82 GiB,
minimum 35.44 GiB available). The book has 92 HTML pages, retaining
all 91 prior paths and the three new declaration docstrings. Four stable
source passes produce 61 pages without undefined labels, overflow or
rerun warnings; actual final pages 1, 2, 3, 41, 42, 43 and 44
pass visual review. Shared acceptance passes in 12.00 s: all three new
records and all 29 combined types/docs/attributes/raw bodies/standard
axiom reports match, with the identical ten interfaces. The three
existing library namespaces are byte-exact. Hygiene checks 243 library
files without proof placeholders or project axioms. Final sequential
library/book pass in 4.00/10.00 s without touched-module warnings.
Exact eight-path staged-byte gates remain required before this natural
checkpoint is committed and pushed. All original
49 source statements and 44 proofs, literal TOT/interpreted-reconstruction
arguments and the frozen 117-item M4a record remain exact.

This completes the pure corrected-relation transport stage I6b2, with
no semantic, genericity, completeness, perfection, rank-five, exponential-
characteristic, Infinite or freshness input. Quotient-carrier and full
operation-graph naturality and interpreted reconstruction remain open.
The separate four-public carrier/graph plan is agreed with the peer;
its draft remains held until this checkpoint is published. Earlier
field semantics keep perfection/rank-five/ACF completeness explicit.
Unconditional completeness, global Frobenius setoid, literal source
obligations, base recovery and scalar-one inputs remain open.

## Conditional geometric carrier and graph naturality (#23/#8, I6b3)

`Interpretation/Naturality` imports only `Field` and
`TotalTransport`. Four public declarations construct the actual
pointwise fixed-class map and corrected quotient/adjoined-zero map,
then preserve and reflect both total geometric operation graphs.
Every addition zero/common-denominator/opposite/nonzero branch and
multiplication zero/generic-product branch transfers with all witnesses
and rank-three independence clauses. Zero/representative and class-value
laws are RFL and remain inline. Witnesses pull back by surjectivity,
and equalities reflect by injectivity. No helper chain, private item,
global instance, `Quotient.out` or decoding-defined substitute is added.

The canonical image-base equality is an explicit hypothesis; rewriting
it is confined to propositions after restating class-map values in
pointwise form. The raw class map needs no semantic hypothesis. The
actual interpreted carriers retain perfection/rank-five/ACF-completeness
inputs and independent exponential characteristics on both sides,
across four independent universe levels and bases.

Claude supplied frozen source `e7159aa2` against published `b3f1262`,
with eleven exact project/Mathlib input hashes and six exact baseline
copies. Codex compiled it unchanged and warning-free in 6.00 s
(peak 2.57 GiB, minimum 36.47 GiB available). The status-only final
passes in 8.00 s. All four signatures/types/docs/attributes/raw bodies
and standard-axiom reports match, including both definitions; no new
generated declaration, private helper or global instance appears.
No source or proof repair was needed.

Sixteen accepted original/final interfaces are byte-identical:
raw class types/value/inverse/round-trip without semantic inputs;
actual carrier equivalence, native zero/representative/inverse-zero RFL;
both full-carrier graph iff types; actual named-field add/mul preservation
and a genuine RingEquiv consumer whose underlying Equiv is the geometric
map; output-functionality reflection, finite bases and characteristic two.
The root interface harness initially used unparenthesized notation-dot
projections and redundant proof-local `letI`; parentheses and
proof-local `let` instances fix those parser/style issues. The frozen
source and all mathematical proofs are unchanged.

The prior totalization/ratio checkpoint `b3f1262` has full library/
book and deployment CI success in run 37679279737. The conditional
image-base scope was reported on #23 before updating preceding source
progress and four upstream transport headers. Earlier source wording
is retained in provenance comments; old library namespaces and combined
compiled records stay exact. The full library/book passes in 54.01/8.00 s
(peak 8.93 GiB, minimum 36.34 GiB available for the build), and shared
comparison passes in 12.00 s (peak 2.61 GiB, minimum 38.19 GiB). All
33 combined types/docs/attributes/raw bodies and standard-axiom records
match, as do the sixteen accepted interface bytes. Hygiene covers 244
library files. The book retains all 92 prior HTML paths and adds one
four-docstring conditional naturality section. Earlier current source/book
progress scopes and the recovery warning were also reported before
qualification; old source wording is retained in comments. Original 49
source statements/44 proofs, literal TOT/interpreted-reconstruction
arguments and the frozen 117-item M4a record remain exact. Four stable TeX
passes produce 62 pages; actual visual review covers pages 1/2/3/33/34/35/37/
38/40/42/43/44/45, including earlier qualified scopes and the recovery warning.
A first layout check found an overflow in only the new paragraph; reflow
fixed it without a mathematical change. The pre-stage byte gate also caught
one overlong upstream header line; reflow leaves that namespace unchanged.
Final sequential library/book passes in 38.01/8.00 s (minimum available
37.41/37.95 GiB), with no touched-module warnings. Exact nine-path staged-byte
gates are checked before commit and push.

I6b3 is accepted with the image-base equality and carrier inputs explicit.
Its parent I6b and interpreted reconstruction I6c remain open: image-base
existence and the named induced RingEquiv/composed field isomorphism are
not yet declared. The separate two-public RingEquiv plan is agreed;
its draft remains held until this checkpoint is published. Unconditional
completeness, global Frobenius setoid, literal source obligations, base
recovery and scalar-one inputs remain open.


## Conditional induced ring isomorphisms (#23/#8, I6c1)

Two public definitions are appended in `Interpretation/Naturality`, with
no new import/helper/global instance: `ratioInterpMapRingEquiv` has exactly
the geometric `ratioInterpMap` as its underlying Equiv, and
`interpretedRingEquiv` is the actual `K ≃+* L` composite of the inverse
source decoding, geometric carrier map and target decoding. Add/mul laws
use the graph characterizations and naturality. Native zero, representative
and forward/inverse composite values are definitional; Mathlib supplies
one/inverse laws. All four prior declaration bytes are unchanged.

Claude froze source `07766340` against published `603c57b`, with eleven
exact inputs and three baseline copies. Original compilation passes in
6.00 s (peak 2.59 GiB, minimum 37.16 GiB available). Four unused explicit
lambda-binder warnings are fixed by naming `(r := r) (s := s)` in the two
source graph iffs. The final passes in 10.00 s (peak 2.62 GiB, minimum
36.94 GiB). All six original/final types/docs/attributes/raw bodies and
standard-axiom records remain exact, including both new definitions and
all four previous records. No mathematical source/proof repair is needed.

Eighteen accepted original/final interfaces have identical bytes and pass
warning-free: genuine named-field RingEquiv/type and exact geometric
toEquiv/pointwise map; native zero, inverse zero and representatives RFL;
actual add/mul/one/inverse laws; actual K-to-L type; forward/inverse
decode compositions RFL; the forward decode diagram, actual ring laws
and inverse roundtrip; independent universes/bases/separate exponents,
finite bases and characteristic two. The root harness initially lacked
proof-local named field contexts at projections/inverse/decode diagrams;
adding those contexts is only a fixture repair. The frozen source is
unchanged and all compiled final bodies remain exact.

Prior `603c57b` has full build/book/deployment CI success in run
37684293833. The current conditional reconstruction scope and five
upstream header-only qualifications were reported on #23 before changing
source/status prose. All five old namespaces and 43 prior compiled records
remain exact; all 45 combined public records have standard axioms. The full
library/book passes in 56.01/8.00 s (peak 8.90 GiB, minimum 36.39 GiB
available for the build). Shared six-record/eighteen-interface and 43-old/
45-total comparison passes in 14.00 s (peak 2.60 GiB, minimum 38.38 GiB).
Hygiene covers 244 files; the 94-page HTML book retains all 93 prior paths
and adds the two-docstring conditional induced-isomorphism section. Four
stable TeX passes produce 62 pages; actual visual review covers pages
1/2/3/41/42/43/44/45. The visual audit caught one earlier coupled status
missed by the first qualifier pass; the reported scope is fixed with old
wording retained in a comment. All original 49 source statements/44 proofs
and literal TOT/interpreted-reconstruction arguments remain exact. The
final prose review distinguishes definitional forward/inverse composite
values from the commuting decoding diagram, which uses inverse laws.
Final sequential library/book passes in 50.01/8.00 s (minimum available
36.98/38.72 GiB), with no touched-module warning. Exact nine-path staged-byte
gates precede commit/push.

This accepts I6c1, corrected interpreted reconstruction GIVEN the
canonical image-base equality, with both sides' perfection, rank-five,
separate exponential characteristic and ACF-completeness inputs explicit.
Parent I6b/I6c remain open until image-base existence and the conditional
existence endpoint; that separate two-public plan is agreed and remains
held until this checkpoint is published. R1/R2, unconditional completeness,
global Frobenius setoid, literal source obligations, full inducing
reconstruction and the frozen M4a obligations remain open/preserved.


## Conditional canonical image base and field-isomorphism existence (#23/#8, I6c2)

Exactly two public theorems are appended in `Interpretation/Naturality`,
with unchanged imports and no helper/private/global instance/evaluation
declaration. `exists_map_jTupleOf_eq` supplies an actual independent target
pair and the canonical tuple equality from source rank/pair, the lattice
map and target perfection/exponential characteristic/ACF J completeness.
Target rank is derived locally by the lifted transcendence-degree transport.
Source perfection/completeness and target rank are absent from its inputs.
Its consumer `nonempty_ringEquiv_of_closedIF_orderIso` chooses a source
pair inline using rank-five freshness and exchange, obtains the image pair
and applies `interpretedRingEquiv`. The conclusion is actual
`Nonempty (K ≃+* L)`. Both perfections, separate exponents, source rank five
and BOTH still-open ACF J-completeness hypotheses remain explicit; no
source/target pair, target rank or image-base equality is supplied.

Claude froze source `ac56183e` against published `f014650`, with eleven
exact peer inputs, nine root inputs and one exact baseline copy. The six
accepted declaration prefix bytes are unchanged. Original compilation is
warning-free in 8.00 s (peak 2.55 GiB, minimum 36.40 GiB available). A
header/status-only final passes in 12.00 s (peak 2.61 GiB, minimum
36.28 GiB). All eight original/final types/docs/attributes/raw bodies and
standard-axiom records remain exact, including the prior six. No production
mathematical/source/proof repair is needed.

Twenty-seven accepted original/final interfaces have identical bytes and
pass warning-free: all eighteen accepted actual geometric/named-field
RingEquiv checks plus nine minimal-signature, actual image coordinate/point,
reverse image/field equivalence, finite-base and characteristic-zero/two
checks across four independent universes. Root initially copied an older
pre-acceptance RingEquiv fixture; it failed only for missing proof-local
field contexts. Restoring the exact accepted eighteen-interface fixture is
a harness-copy correction only. All nine new fixtures pass unchanged. The
accepted original/interface/45-prior-record run takes 10.00 s (peak 2.61 GiB,
minimum 36.19 GiB). No production repair is hidden by this fixture correction.

Prior `f014650` has exact CI37686716943 full library/book/deployment success.
The conditional scope was reported on #23 before integration and before
qualifying fourteen current source progress paragraphs and five upstream
headers. Earlier source wording is retained in comments. All five old
namespaces and 45 prior compiled records must remain exact; shared 47-total
standard-axiom records, all original 49 source statements/44 proofs and the
literal TOT/interpreted-reconstruction arguments are checked before push.
Full library/book, hygiene, retained HTML, actual rendered-source/provenance
and exact nine-path staged-byte gates precede commit/push.

This accepts I6c2 only in its conditional scope. The theorem asserts field
isomorphism existence; it does not prove `Induces` compatibility with the
given lattice map or recovery of the base fields. General I6b/I6c retain
their original/open scope. R1/R2, unconditional completeness, global
Frobenius setoid, literal/TOT/simultaneous-representative obligations, full
inducing reconstruction and frozen M4a remain open/preserved.


The integrated gates pass: full library/book **58.33/8.04 s** (library
peak **8.88 GiB**, minimum **35.43 GiB** available), shared eight-record/
twenty-seven-interface/45-old/47-total comparison **16.00 s** (peak
**2.63 GiB**, minimum **37.73 GiB**). All 45 old types/docs/attributes/raw
bodies and axioms are exact; all 47 combined public records use only standard
axioms. All five upstream namespaces are byte-exact with header-only
changes. Hygiene passes for **244** library files. HTML has **95** pages
retaining all **94** old paths and both new theorem docstrings; the frozen
117-item M4a page is unchanged in scope. The source is stable after four
passes at **63** pages, with no unresolved reference/overflow and actual
visual review of pages **1/2/3/33/34/35/38/40/41/42/43/44/45/46**. All 49
original statements/44 proofs and the complete literal TOT/interpreted
reconstruction arguments are byte-exact. Final serial library/book and
exact staged-byte gates precede the nine-path checkpoint commit/push.


## No-fresh relative base-ratio corollary (#5/#9, R1a/C7b)

Two public theorems replace the empty `Reconstruct/Base` skeleton. Imports
are only `Interpretation.Naturality` and Mathlib's `RatFunc.AsPolynomial`;
there is no helper/private/global instance/evaluation declaration or local
algebra structure. `base_ratio_rel` states ratio algebraicity over arbitrary
k/K from the actual independent pair and both element/product
interalgebraicity pairs. No fresh element in K, rank, perfection,
completeness or exponential-characteristic input is assumed. The proof
embeds K into the algebraic closure of K(X), enlarges the base algebraically,
uses the transcendental variable as the required third element, applies
the existing base-ratio correspondence lemma, and pulls algebraicity back.
`base_ratio_mem_range` gives the original u₁/u₂ ratio in the actual image
of k, with explicit IsRAC of the intermediate-field bottom. Its consumers
are the literal corollary and actual R1b interpreted-ring base recovery.

Claude froze `f66a0a45` against published `e7179bd`, with eleven peer/eleven
root input hashes and an exact skeleton baseline. Original compilation and
nine interfaces pass unchanged and warning-free in 8.00 s (peak 2.86 GiB,
minimum 39.35 GiB available). A header/status-only final and before-main
47-public-record capture pass in 14.00 s (peak 2.87 GiB, minimum 39.32 GiB).
All two original/final types/docs/attributes/raw bodies and standard-axiom
records are exact, with identical namespace bytes and nine fixture bytes.
The checks cover minimal no-fresh/algebraicity signatures, inverse
orientation, actual RAC-base range/witness/subfield membership, independent
base/ambient universes, finite bases, characteristics zero/two and the
original algebraically closed-base case without ambient closure. All nine
new interfaces pass unchanged. No production proof/source repair is needed.

The combined baseline harness initially imported only the old Base skeleton,
which does not import Naturality/Transport. Root added an explicit
Naturality import to that capture fixture; this was a harness import repair
only, with no production change. The accepted original/final records and
all 47 old records are captured after that correction. Root's prior
RatFunc/algebraic-closure freshness and RAC-membership API probe uses
existing global instances and passes in about 1 s (nested peak 2.85 GiB;
the outer two-second sampler missed the RSS peak).

Prior e7179bd exact CI37689183902 is fully green including library/book and
deployment. The source proof discrepancy and intended scope were reported
on #5 before code, and the five-path integration scope on #9 before source
qualifications. The original corollary proof incorrectly names independent
correspondence points (u₁,b)/(u₂,b); the formal core uses (u₁,u₂)/(b,b).
All original 49 source statements/44 proofs and literal TOT/interpreted
reconstruction arguments remain exact. Full library/book, shared
two-record/nine-interface/47-old/49-total, hygiene, retained HTML and actual
rendered-source/provenance plus exact five-path staged bytes precede push.

This proves R1a/C7b, the base-ratio corollary prerequisite. Actual R1b
`CrossBase.Compatible (interpretedRingEquiv …)`, scalar one, full Induces
reconstruction, unconditional J completeness, the remaining C7/group/
three-pair/tensor obligations and frozen M4a remain open/preserved. The
separate three-public R1b plan is held until this checkpoint is published.

The integrated full library/book pass in 40.22/8.04 s; the shared two-record,
nine-interface and 47-old/49-total comparison passes in 12.07 s. All 47 prior
compiled types/docs/attributes/raw bodies and axioms are exact; all 49
combined public records use standard axioms. All ten prior root inputs
except the replaced Base skeleton are byte-exact, including Naturality
and the root import. Hygiene covers 244 files with no placeholders/project
axioms. All 95 old HTML paths remain among 96 pages, with both new
base-ratio docstrings and the open recovery boundaries checked. The source
renders in four stable passes, still 63 pages; all six changed/reflowed
pages (1, 2, 3, 26, 27, 28) were actually visually inspected and pass.
No touched-module warning or mathematical source/proof repair is needed.
The final serial library/book and exact five-path staging gate precede
commit/push; CI for this new checkpoint is reported in the issues.


## Actual conditional base recovery (#9, R1b)

Exactly three public theorems are appended in `Reconstruct/Base`, with
the one justified `Closure.CrossBase` import. All existing carrier,
rank-five/perfection, separate exponential-characteristic, both ACF
J-completeness and image-pair inputs remain explicit. Forward
`interpretedRingEquiv_algebraMap_mem` needs target RAC only, handles zero
and encodes a nonzero base scalar as the ratio of `j(c x₀,a)` to the
canonical denominator `j(x₀,a)`. The denominator's target tuple is pinned
by hφ. Target B1 yields the numerator; only zero/product point coordinates
and the accepted no-fresh base-ratio corollary are needed.
`interpretedRingEquiv_symm` identifies the actual inverse with the swapped
construction, without RAC and with the redundant inverse tuple equality
explicit. Its pointwise composite values agree by reflexivity.
`interpretedRingEquiv_compatible` derives the inverse tuple equality
inline and applies forward inclusion both ways under both RAC bases.
Its conclusion is actual `CrossBase.Compatible (interpretedRingEquiv …)`.

Claude froze `4cf53a47` against published `29bbb8a`, with eleven peer
inputs, twelve root inputs and one exact baseline. The initial uncompiled
source failed at a redundant symmetry tail after congr had already closed
the goal (2.01 s). Root and Claude agreed the bounded replacement
`RingEquiv.ext fun _ ↦ rfl`, deleting unused local inverse proofs. Both
passing ext/reflexivity variants showed an unintended simplifier-generated
`interpretedRingEquiv.congr_simp`. Replacing the forward zero-case
`by simp` with explicit map_zero/congrArg/trans identities removes it.
The failed original and both passing generated-inventory variants are
preserved. There is no other production repair; all public statements,
binders, docs, attributes, imports/counts and the two old declaration bytes
stay unchanged. Peer ACKs are 3919/3922.

The accepted review and header/status-only final pass in 10.05/10.06 s,
with peaks 2.86/2.91 GiB and minimum available memory 38.90/38.82 GiB.
All five accepted original/final theorem types/docs/attributes/raw bodies
and standard-axiom records are exact; their namespaces are identical.
There is no helper/private/global instance/evaluation/generated declaration.
All twelve new and nine old interfaces pass unchanged and warning-free:
minimal target-only RAC membership, no-RAC actual inverse, both-RAC
Compatible, actual forward/inverse scalar witnesses, base-range image
equality, an actual induced base-field RingEquiv, compatible principal-point
transport, zero, finite bases and characteristics zero/two, across
independent universes. Before-main capture of all 49 old compiled records
passes in 6.03 s and matches the prior accepted shared inventory.

The prior 29bbb8a exact CI37692166084 is fully green, including library/book
and deployment. The seven-path integration and source qualifications were
reported on #9 before main edits. Naturality changes only its header; its
eight declarations remain exact. Older current source progress wording
is retained in comments, with conditional R1b distinguished from the open
unconditional R1/R2 scope. All original 49 statements/44 proofs and literal
TOT/interpreted arguments remain exact. Full library/book, shared
five-record/21-interface/49-old/52-total comparison, hygiene, retained HTML,
stable source rendering/actual visual review and exact staged bytes
precede commit/push.

This accepts corrected conditional R1b, not unconditional source R1.
Scalar one/R2, Induces, unconditional J completeness, full inducing
reconstruction, global/literal/TOT obligations and broader C7/group/
three-pair/tensor/frozen M4a remain open/preserved. Earlier checkpoint
sections retain their historical scope.

The integrated full library/book pass in 58.31/8.04 s; the shared
five-record/21-interface and 49-old/52-total comparison passes in 14.08 s.
All 49 prior compiled types/docs/attributes/raw bodies and axioms remain
exact, and all 52 combined public records use standard axioms. Naturality
is header-only with its complete namespace unchanged; all ten other prior
root inputs and the root import are byte-exact. Hygiene covers 244 files.
All 96 old HTML paths remain among 97 pages, with the three new recovery
docstrings, explicit hypotheses and open general boundaries checked. The
source renders in four stable passes, now 64 pages; all sixteen changed/
context pages (1, 2, 3, 26–29, 42–47, 49–51) were actually visually
inspected and pass. No touched-module warning remains. Final serial
library/book and exact seven-path staging precede commit/push; CI for the
new checkpoint is reported in the issues.


## Actual conditional scalar one and outside-point recovery (#9, R2a/b/c)

The focused new `Reconstruct/Scalar` imports Base only and has exactly
three public theorems, with no helper/private/global instance/evaluation/
generated declaration or duplicate RingEquiv. For the same actual map H,
`interpretedRingEquiv_coord` proves y·H(x₀)=H(x)·x₀' from actual tuple
images. `interpretedRingEquiv_base_coord` proves H(x₀)=x₀'.
`interpretedRingEquiv_point` proves e([x])=[H(x)] outside racl_k{a}.
None assumes RAC. Both perfections/rank-five bounds, separate exponential
characteristics, both still-open ACF J-completeness inputs and the actual
canonical image-base equality remain explicit. Source genericity uses two
fresh elements over a. Target genericity comes from mapped point-triple
independence plus tuple-image coordinates 0/0/4, then the semantic coupled
product and three multiplied coordinate identities force scalar one.
This geometrical route replaces the original choice over acl(a,x₀,t₀),
which is preserved as a literal proof obligation with its statement.

Claude froze c9089e23 against published eb4546d (10 peer inputs, 15 root
inputs, exact Base/Naturality baseline copies). The initial source run
failed only at two unqualified pair_mul_a references (2.00 s). The bounded
repair qualifies them as JArith.pair_mul_a, with peer ACK3950; all public
statements/binders/docs/attributes/imports/count stay unchanged. The next
source run compiled all three records but exposed a root-only dependent
rewrite in fixture9; evaluation via congrArg/trans repairs that fixture
proof only. Both failed evidence sets and the frozen source are preserved.
There is no other production repair.

Accepted original/header-status-only final pass in 12.00/10.00 s (peak
2.88 GiB, minimum available 38.28/38.26 GiB). All three types/docs/attributes/
raw bodies and standard-axiom records are exact; namespace bytes match.
All twelve new and twenty-one byte-exact old typed interfaces pass without
warnings: minimal no-RAC coordinate/base/outside-point laws, independent
input point recovery, full tuple-image consequence from actual B1 and the
public laws, actual inverse/base-coordinate behavior, swapped inverse point
recovery, feeding actual compatibility and outside points to the existing
whole-lattice API, all principal points, finite bases and characteristics
zero/two across independent universes. These fixtures check downstream
behavior but do not supply the held public R3/R4 declarations. Before-main
capture passes in 6.03 s with all 52 prior records exact.

The scope/route qualification was reported on issue9 before main/source
edits. Integration adds Scalar/root import and current book/source status;
Base, Naturality and Points change only module prose/status headers, with
all complete namespaces and old compiled records exact. The previously
promised whole-file baseline preservation is qualified solely for those
current-status headers, with the root integration scope communicated to
the peer before edits. The source preserves old progress in comments,
every original 49 statements/44 proofs and the literal TOT/interpretation
chunk. Prior eb4546d CI37695087697 is fully green for build/book/deploy.
Full serial library/book, shared 3-record/33-interface/52-old/55-total checks,
hygiene, retained HTML, stable source rendering with actual visual review,
final serial build/book and exact staging precede commit/push.
The initial integrated full build passed in 60.01 s but the pre-staging
warning gate caught one newly long Points status-header line. Wrapping
that prose line preserves its complete namespace; the post-wrap full
build passes in 20.00 s with no touched-module warning. The new source
prose initially put a Lean listing inside math mode; moving the listing
outside math fixes rendering, with the failed PDF evidence retained.
Actual visual review also found two old scalar-open consumer scopes;
they are qualified with their prior wording retained, making five current
source progress qualifications. The final stable source has 65 pages,
with 13 affected/context pages actually reviewed.

Only corrected conditional R2a/b/c are accepted. General unconditional
R1/R2, public inducing/existence assembly, chosen-perfection reconstruction,
unconditional J completeness and global/literal/TOT/three-pair/tensor/
frozen M4a remain open. The next named consumer is a bounded two-public
actual closedIFMap inducing/existence slice; peer drafting remains held
until this checkpoint is published. Historical checkpoint sections retain
their earlier scope.


## Actual conditional inducing equality and existence (#9, perfected R3/R4)

The focused new `Reconstruct/Existence` imports Points and Scalar only.
Exactly two public theorems, no helpers/private/generated/global-instance/
evaluation/duplicate RingEquiv: `closedIFMap_interpretedRingEquiv` uses
actual compatibility and outside points to prove e=closedIFMap H for the
same interpretedRingEquiv. Its exact carrier, image-pair and both RAC
inputs are explicit. `exists_ringEquiv_closedIFMap_eq` then proves
there is a compatible RingEquiv inducing e, with only source rank five,
both perfect ambient fields, separate exponential characteristics, both
still-open ACF J-completeness hypotheses and both RAC bases. Source pair,
target rank and actual image pair are derived inline. No pair, target
rank, image equality, point/scalar oracle or inducing endpoint is supplied.

Claude froze bea65e68 against published e6f35fc (10 peer inputs, 18 root
inputs and exact Scalar/Base/Naturality/Points baseline copies). Original
and header/status-only final pass in 12.00/12.00 s, peaks 2.90 GiB and
minimum available 38.18/38.26 GiB. The original source is byte-exact
frozen; no production or fixture-proof repair is needed. All two types/
docs/attributes/raw bodies/standard-axiom records and namespaces are exact.
Twelve new independent typed behaviors and 33 byte-exact previous
fixtures pass warning-free: minimal actual H equality, every principal
point, every closed-field set image, full inverse point recovery, minimal
no-pair inducing existence and its all-point/image consequences, actual
compatible base RingEquiv, finite bases and characteristics zero/two.
One behavior checks extension to arbitrary chosen perfections of these
already-perfect inputs, not the general nonperfect-field theorem.
Before-main capture passes in 6.00 s with all 55 prior records exact.

The perfected conditional scope and original-field caveats were posted
on issue9 before main/source edits. Base, Naturality, Scalar and Points
change only current status headers, preserving all complete namespaces.
Root adds only the Existence import. Current source progress is qualified
with prior wording retained; every original 49 statements/44 proofs and
the literal interpretation/TOT chunk remain exact. Prior e6f35fc
CI37697686422 is fully green for library/book/deploy. Full serial library/
book, shared two-record/45-interface/55-old/57-total comparison, hygiene,
retained HTML, stable PDF and actual affected/context visual review,
final serial library/book and exact staging precede commit/push.

This accepts only the corrected conditional perfect-field inducing/
existence step. The original nonperfect fields require chosen-perfection
lattice transport, RAC of the perfected base, actual Perfection.Induces
existence and assembly with the landed Frobenius uniqueness. These are
the named next consumers and remain open. General unconditional
R1/R2/R3/R4, unconditional ACF completeness, literal RatioEq/TOT/scalar
arguments, bypassed linear-disjointness and frozen M4a scope retain their
recorded status. Historical checkpoint sections keep their earlier scope.


## Actual conditional original-field existence through chosen perfections (#9)

The focused new Reconstruct/Target imports Perfection.Induces and
Reconstruct.Existence only. Exactly two public results in namespace
Perfection, no helper/private/generated/global-instance/evaluation/duplicate
RingEquiv: isRAC_basePerf derives perfected-base RAC from ORIGINAL-base RAC
with no rank or completeness. exists_induces constructs a compatible map
of arbitrary chosen perfections inducing the original lattice isomorphism.
The original fields need not be perfect. Only original source rank five,
both original RAC bases, the bundles and both exact perfected ACF
J-completeness hypotheses are supplied. Perfected source rank, perfected-base
RAC and conjugation are derived inline; separate bundle characteristic
parameters stay separate. Two local Prop-valued PerfectField witnesses are
necessary because the bundle supplies PerfectRing; no local Algebra instance,
pair, target rank, point/scalar or inducing oracle is supplied.

Claude froze 1dbeb730 against dab374c (16 peer inputs, 24 root inputs and
four exact baseline copies). Frozen production source compiles with two local haveI style warnings. Root
initially missed these in private logs; the full warning gate caught them before
staging. Only two local Prop-valued haveI commands are replaced by Mathlib-
preferred have, agreed by peer4021, with warned source/proof/log evidence
preserved. Accepted original/header-only final pass14.00/14.01s, peaks2.91GiB
and minimum available38.01/37.98GiB. Frozen signatures/docs/attributes/types
and standard axioms are exact; accepted original/final raw bodies match. Two types/docs/attributes/raw bodies,
namespace bytes and standard-axiom records are exact. No other production repair.
One new root fixture's unused existential compatibility binder was renamed
_hPhi; source-success/fixture-warning evidence is retained. A root preflight
declaration scanner misread header prose and was corrected before actual
Lean compilation, retaining failed guard/missing-directory evidence.

Twelve new warning-free typed behaviors and all 45 byte-exact previous
interfaces pass (57 total): minimal RAC and actual algebraic membership,
minimal original-field existence, literal perfected-subfield equalities,
every intersection formula, actual compatible base RingEquiv, inducing-map
conjugacy, all Frobenius twists and exact fibre for this constructed witness,
finite bases and characteristics zero/two across independent universes.
The fibre is a private consumer check, not an extra public assembler.
Before-main capture passes 8.00s with all 57 prior records exact and main clean.

Scope and stale source status were reported on issue9 before main/source
edits (6048732435). Existence and Induces change only current headers with
full namespaces exact; root adds Target only. All nine changed current source scopes preserve earlier wording; every original49 statements/44 proofs and literal interpretation,
TOT and proposed assembly proof remain exact. Prior dab374c CI37699869146 is
fully green for library/book/deploy. Full serial library/book, shared two-record,
57-interface/57-old/59-total comparison, hygiene, retained HTML, stable PDF,
actual affected/context visual review, final serial library/book and exact
scoped staging precede commit/push.

Only conditional original-field chosen-perfection inducing existence is
accepted. The next named consumer is a public conditional target assembly
combining rank, base/intersection formulas, Frobenius uniqueness and converse.
Final Reconstructs/target assembly, general unconditional R1/R2/R3/R4,
unconditional completeness, literal/TOT/scalar, bypassed linear-disjointness
and broader group/three-pair/tensor/frozen obligations remain open. Historical
checkpoint sections retain their earlier scope; peer assembly drafting remains
held until this checkpoint is published.

Actual source review also found crowded double-digit subsection numbers in
the table of contents; the number column alone is widened before final rendering.


## Public conditional lattice-form reconstruction target (#9/#10)

Main's empty skeleton is replaced by exactly three public declarations:
Reconstructs, a reducible alias of the actual Perfection.Induces equality;
exists_reconstruction, the minimal conditional public existence signature;
and reconstruction_target, one assembled conditional blueprint Thm target.
It provides lifted rank equality, a compatible field isomorphism of arbitrary
chosen perfections, every perfected image/original intersection formula,
the exact Frobenius fibre, characteristic-zero literal uniqueness,
positive-characteristic injectivity of the integral exponent, and the
compatible converse. Only both original RAC bases, original source rank
five, the bundles and both EXACT perfected ACF J-completeness inputs are
supplied. No original PerfectField, target rank, pair, image equality,
point/scalar/Induces oracle or matching characteristic parameter is assumed.

Claude froze Main c9b87be2 against published6e7b7b3, with ten input hashes
and a byte copy of the empty-skeleton baseline; root pins26 inputs.
Frozen original passes unchanged in 14.08 s; accepted final passes
16.09 s and changes only the current status header. All three compiled
public types/docs/attributes/raw bodies/namespace and standard axiom reports
are exact. No production or fixture repair, helper, private/generated
item, global/local instance, evaluation or duplicate relation is added.
Main imports only Target and Uniqueness; the root already imports Main and
Functorial separately and stays byte-exact.

Fifteen new warning-free independent typed behaviors plus all 57 previous
byte-exact fixtures pass (72 total). They check minimal public existence,
the actual perfected-base Subfield image, actual set intersection inside
the ORIGINAL target field, both directions of the fibre, actual ∃! integral
exponent, literal ∃! reconstruction in ORIGINAL characteristic zero and
unique exponent in ORIGINAL characteristic two for arbitrary bundles,
finite bases, independent universes, compatible converse and uniqueness of
the induced lattice map without rank/completeness. Before-main59 capture
passes 6.03s with all 59 prior compiled records exact and main clean.

Conditional scope/current source status corrections were reported on issue9
before integration (6049028844). Only four old Lean headers change; their full
namespaces remain byte-exact. Every original49 mathematical statements and
44 proof blocks, literal interpretation/TOT, assembly listing/proposed proof
and frozen 117-item M4a remain exact; earlier current progress wording is
preserved in source comments. Full serial library/book, shared3-record/
72-interface/59-old/62-total comparison, hygiene, retained HTML, stable PDF
with actual affected/context visual inspection, final full library/book and
exact ten-path staging precede commit and push. Previous6e7b7b3 CI37702330392
is fully green for library/book and deployment.

Only conditional public U2b/U2c subitems are accepted. Both perfected
completeness inputs, general unconditional recovery/reconstruction, literal
ratio/TOT/scalar, bypassed linear-disjointness, broader group/three-pair/
tensor/frozen M4a, point-geometry/automorphism and functorial forms remain
open. The next bounded public consumer is chosen only after publication.


## Completeness dependency and current-status reconciliation (#6/#22)

The public lattice-form target is now conditional on both exact perfected
ACF J-completeness inputs. The next mathematical priority is discharging
those inputs, rather than adding public wrappers. Semantic J assembly
now reduces each rank-five ACF input to guarded Q completeness and Q′ completeness (#27).
The old unguarded AffineGridExtraction and QCompletenessACF were subsequently refuted
even for ACF pairs with five independent elements. Guarded extraction requires
I≠D and I≠P; both guards come from J multiplication distinctness. Guarded Q
completeness needs only the four outputs and remains open. The frozen 117-item M4a stays frozen.

The audit found stale current prose: Config.Correctness and issues 6/22
still called the accepted concrete arbitrary-field Q/Q′ refutations open;
issue 6 still called concrete geometry transport open. Both are proved:
Config.Transport maps partial quadrangles, all Psi clauses, multiplication
diagrams and Q/Q′/J along arbitrary closed-lattice order isomorphisms,
without completeness/perfection/rank/freshness. Counterexamples.QRefutation
proves not_forall_qGeom_imp_qSem and not_forall_q'Geom_imp_q'Sem in
characteristic zero over rational functions in five variables.
Correctness/Transport change current headers only, with full namespaces
byte-exact. The configuration chapter's current overview/transport status
is reconciled; no declaration, proof, source statement or source PDF changes.
Status discrepancies and the scope were reported before edits on issue 6
(6049189938). Full library/book and scoped commit/push validate the cleanup.

Claude's read-only G1 audit 4068 confirms Language's incidence/collinearity,
partial quadrangle and named-triple permutation, FiniteRank's finite-rank
interfaces and concrete invariance in Geometry/Config Transport. Broad G1
remained open at ed61c33 with unimplemented generic-formula recursion and named
MemCl/Col invariance interfaces. That historical gap is addressed in the G1c
checkpoint below; the earlier concrete per-predicate route had bypassed the
blueprint's proposed generic recursion method. No bypassed obligation is silently
closed. General ACF Q/Q′/J completeness, corrected
extraction, geometric projection identities, general witness descent and
group/action integration remain open. The completeness-engine audit is
read-only; no new source draft, Lean/main ownership, child agents or frozen
bookkeeping expansion is delegated.


## Degenerate Psi refutation and guarded completeness repair (#27/#6/#22)

The literal Psi allows Q=E=G=T=[c], H=S=[a], I=D=[ax] in the independent
five-coordinate table. The four changed meets are proved, not assumed; all
remaining clauses use the verified table witness. QSem.ratio_ne and
ratio_ne_fst prove both necessary output inequalities. The counterexample
refutes unguarded geometric Q completeness over any field with five independent
elements, and the exact legacy QCompletenessACF and AffineGridExtraction with
both actual ACF assumptions. It also refutes the unguarded geometric Q
projection to J. The old #25 unguarded Q conclusion is superseded; the
independent arbitrary-field Q′ refutation remains relevant.

GuardedAffineGridExtraction and GuardedQCompletenessACF require both I≠D and
I≠P. They are explicit OPEN propositions, never axioms or proved classification
interfaces. Actual multiplication distinctness supplies both outer guards in J.
The two existing JAssembly inputs are retyped to guarded Q completeness;
JCompletenessACF and every Main public target are unchanged. Guarded correctness
and geometric projection are conditional on the explicit guarded input. The
three vacuous unguarded correctness wrappers are removed; legacy target definitions
remain marked refuted with this issue reference for their negative consumers.

The source error and concrete scope were reported BEFORE main/source edits on
issues 6/22/12, then both guards on 27/6. All 49 original full mathematical statement
blocks remain in the source, including the two refuted statements in explicitly
labelled historical false branches from ed61c33. Of the 49 active statements,
47 stay exact; q-correct and affine-grid-extraction gain both guards and explicit
OPEN completeness qualification. All 44 proof blocks, original listings and the
literal ratio/TOT section stay byte-exact. Q′/J statements are unchanged and
qualified as completeness obligations using guarded Q. No supplied private paper
is committed or reproduced. Frozen 117-item M4a remains untouched.

Claude supplied the source-only degeneration and read-only guard/consumer audit.
The first frozen draft failed 28.14s on a namespace call and full-record kernel
comparison. The private repair uses one opaque witness helper, the explicit
namespace call and omit hind in; the second run failed 2.01s on that section binder,
and the third passed 2.00s. Seven public/four private authored declarations and
four actual behaviors passed independently with standard axioms. The original
frozen bytes and both failures remain outside git. The repaired guarded nine-module
chain passes 16.00s warning-free. The previous run compiled with six touched
show→change warnings, one unused Fin.snoc simp argument, and five new long lines;
those exact style repairs are recorded, with no weakened checking. Normalized
proof bodies for every old declaration remain exact except the two deliberately
retyped JAssembly theorems. The diagnostic harness initially expected 18 additions;
its actual 24 authored additions (20 public/four private) and all ten genuine
behaviors passed; the count assertion was corrected with no source/fixture repair.

The separate origin-shift refutation privately passed default checking with two
public/two private declarations and two actual behaviors, but is deferred from
this focused checkpoint. It refutes action-origin uniqueness, not guarded
completeness. Next work is the genuine guarded extraction/group-action engine
and multiplication converse; no new frozen bookkeeping is authorized.


Final shared QA for the guarded checkpoint: full library/book compilation is green
80.02s (minimum available 35.93GiB, sampled family RSS10.91GiB); website generation
is green 8.00s (minimum 37.65GiB/RSS1.56GiB). The initial applied fullbuild stopped
98.03s at 29.22GiB as required; its evidence is retained and excluded from acceptance.
The serialized warm retry passed 10.00s (minimum 35.30GiB/RSS3.30GiB). Root waited for
each actual process exit before the next Lean/Lake family; the guarded slot stayed exclusive.

All 72 earlier actual fixtures and their62 combined public signatures/proofs/axioms
remain exact against the final main imports. The nine touched modules'125 scoped
declarations and ten new actual guarded/refutation behaviors also match the private
acceptance, with standard axioms only. This is a scoped audit, not a whole-library
axiom audit. The first shared harness added production style lint to the historical
external fixtures and found old whitespace diagnostics; that failed evidence is retained.
The fixtures are byte-exact and use their historical diagnostic lint scope; new actual
behaviors and production use standard lint, and every kernel invocation uses default
checking. No fixture or production proof was repaired for that harness mismatch.
The corrected shared run passed 20.00s (minimum 37.30GiB/RSS2.90GiB).

Claude's read-only final review found a nolinkurl escaping bug, clearer naming of both
source refutations, historical-sketch wording, missing spaces and two grammar nits.
These were fixed with no mathematics change. Source PDF now has 69pages after four
stable passes with no overflow/undefined label. All 20 selected current pages are visually
accepted: 13 current image bytes match previously actually viewed renders, and seven
changed/new pages were actually viewed after final repairs. Actual review caught an
orphaned final bibliography entry; two failed layouts remain outside git, and the
bibliography now starts on its own page. All 101 HTML pages remain, with current
refuted/guarded/open status and the frozen 117 record visible. Full source/byte guards
and exact 13-path stage/commit/push complete the checkpoint. Only the refutations,
necessary guards and conditional reduction are accepted; both guarded completeness
inputs, multiplication converse, ACF Q′/J completeness and group/action extraction remain open.


## Generic finite-formula invariance and incidence consumers (#6, G1c)

Geometry/FormulaInvariance implements the blueprint's generic recursion theorem
in the small geometry language. GeometryTerm has point variables, bottom/top,
finite point joins and binary joins/meets. GeometryFormula has equality/order,
exact/bounded finite rank, negation/conjunction/disjunction/implication and both
point quantifiers. Quantification extends the assignment with Fin.cons, with the
bound variable at index zero. Term evaluation commutes with every closed-lattice
order isomorphism; structural recursion proves satisfaction invariant, using
point-map surjectivity for both quantifiers. The proved presentation bridge
supplies the same theorem for closure-preserving point equivalences.

memCl_map_iff and col_map_iff are actual instances of generic formula invariance,
not a restatement of the old concrete configuration transport. The only module
imports are Geometry.Transport and Config.Language. No ACF, completeness,
perfection, transcendence-degree bound, fresh element or field semantics occurs
in this proof. Together with the accepted G1a/G1b interfaces, this discharges
G1 small-language transport. The separate group/action and guarded configuration
obligations remain open (G3–G5). Main, all old Lean declarations, the corrected guarded
boundary and the frozen 117-item M4a are unchanged.

The actual inventory has 25 authored public declarations: two inductive types,
sixteen constructors, two evaluation definitions and five transport/consumer
theorems. It also has 138 compiler-generated declarations, including eighteen
private auxiliaries; these are counted separately. The scoped signature,
proof-body and axiom audit allows only the standard Lean axioms. Actual external
behaviors exercise nested quantifiers, rank and Boolean atoms, the empty finite
join, the point-geometry bridge, arbitrary-arity incidence and collinearity.

Root's first two production elaboration attempts failed on an automatically
generalized assignment and vector-index simplification; the exact failures are
retained outside git. The corrected production module passes standard lint with
default checking. The first four nested-quantifier behavior harnesses had finite
assignment simplification errors; their exact bytes/logs are retained, with no
production proof change or weakened checking. Source concordance adds only a
progress paragraph: all current 49 active statement blocks, the 49 original
statements' explicit provenance, all 44 original proof blocks, every listing and
the literal ratio/TOT section remain exact. Broad extraction/completeness,
multiplication converse and genuine group/action integration remain open (#27).


The first applied full library build passed 46.01s (minimum available 35.87GiB,
sampled family RSS7.77GiB). The first TeX render found a 1.47pt overflow in the
new concordance paragraph; that failed render is retained and the prose was
reflowed before acceptance. No source mathematical block changed.


Final shared acceptance preserves all 72 earlier fixture bytes and their 62
combined public signature/proof/axiom records, the guarded checkpoint's 125
scoped records and ten actual behaviors, and the new module's 163 scoped records
and six actual behaviors. New records match private types/bodies/metadata/axioms
exactly. The serial shared run passed 22.00s (minimum available 37.91GiB,
sampled RSS2.89GiB); old diagnostic fixtures retain their historical lint scope,
new behaviors and production use standard lint, and kernel checking is default.
This is a scoped audit rather than whole-library axiom certification.

The full library/book gates passed 46.01s/8.00s before final documentary QA.
All 101 HTML paths remain, with all nine incidence-language docstrings and the
open-engine qualification visible. The corrected source has four stable passes,
69 pages and no overflow/undefined label. Nine current selected pages are
accepted visually: eight exact images were previously actually viewed and the
changed page 68 was actually viewed after reflow. All 247 previous Lean module
sources, Main, all 49 current active statements and original provenance, all
44 proofs/listings/literal interpretation remain exact. G1 small-language
transport is accepted through G1a/G1b/G1c; guarded extraction/Q completeness, multiplication converse, unconditional J
completeness and group/action integration remain open.


## Necessary Psi incidences for genuine meet elimination (#27, L0)

Config.PsiLattice proves four coordinate-free consequences of actual Psi:
P≤A and Q≠T under I≠D, and unconditional P≠S and Q≤B. They supply the
incidences/distinctness needed at the meet-elimination seam of the corrected
blueprint extraction proof. Finite rank, matroid submodularity and exchange
prove them without an action/group/classification or completeness input.
The actual QDegenerate witness has Q=T, so Q-distinctness needs the guard.
The proposed P-incidence counterexample remains hand-only and is not accepted.
Guarded extraction, action presentation/linearity, multiplication converse
and unconditional J completeness remain open; frozen M4a is untouched.

Claude supplied two immutable source-only drafts. Root independently checked
all nine pinned inputs against 7482885 and the unchanged current imports.
The first original compilation failed 8.00s at the default 200k elaborator
limit. Explicit sets and a typed intermediate exposed the swapped convention
of add_le_add_left in the second 2.00s failure. The corresponding inequality
repairs only the submodularity proof, with every v2 statement and default
checker option unchanged. Both freezes and both failures remain outside git.
The v2 source minimizes Q≤B to an unconditional consequence and deletes the
now-unused AT_inf_C helper. The repaired production passed 2.00s warning-free.

The actual inventory is four public/thirty-three private authored theorems,
with no generated additions. All 84 scoped signature/proof/axiom records
(47 earlier and 37 new) and five real abstract/table/degeneration consumers
passed 4.00s with standard axioms. The existing rankEq_iff_eRk theorem moves
unchanged from Transfer.Lift to Geometry.FiniteRank; Config.PsiLattice then
imports only Config.Psi. The private three-module chain passed 4.00s, and
all 84 compiled types, normalized bodies, attributes, docstrings and axiom
records stayed exact except that single theorem's module location. The five
actual consumers plus an isolated FiniteRank-only rank-bridge consumer pass
8.00s. An initial narrowed diagnostic still requested Transfer.Lift without
explicitly importing it; its failed bytes/log are retained and the audit
harness alone now imports all three audited modules. No production proof,
actual fixture or kernel option changed for that harness correction.

G1c's published generic recursion proof has Claude's read-only fidelity
acceptance and exact CI37713273164 fully green for library/book/deploy.
Both generic and pre-existing concrete transport mechanisms remain visible.
This L0 checkpoint accepts only the four necessary consequences and the pure
rank-bridge relocation. Every original public Main target and guarded
completeness proposition stays unchanged. Source concordance adds one status
paragraph; all 49 current active statements and original provenance, all
44 proof blocks/listings and the literal ratio/TOT content remain exact.

Claude's read-only review accepts all seven paths. Its documentary correction
is applied: the P-incidence degeneration is hand-checked, unformalized and not
accepted; the Q=T necessity witness is formally proved. Root's actual shared
cold full build passes 1020.41s (minimum available 35.00GiB, peak family RSS
12.36GiB). After that comment-only qualification, full build/book pass
88.04s/16.01s, with no memory stop. Untouched frozen modules replay earlier
warnings; the three touched production modules were independently warning-free.

Actual main imports pass the 22-check shared family in 42.02s: all 72 old
fixtures/62 public records, guarded 125 records/ten behaviors, generic 163
records/six behaviors and lattice 84 records/six consumers stay exact to their
accepted baselines. The old rank bridge's module location is the sole scoped
metadata difference from its original baseline. New production and behaviors
use standard lint/default checking; old fixtures retain exact bytes and their
historical diagnostic lint scope. This is a scoped axiom/body audit, not a
whole-library axiom certification. All 250 Lean sources pass placeholder and
project-axiom hygiene; the 246 other prior module/Main/G1 sources stay exact.

All 101 book HTML paths remain, with the four new necessary-incidence and
existing pure-rank docstrings visible alongside all nine G1c entries. Source
rendering passes four stable runs/69 pages without overflow or undefined
labels. Nine selected current pages are visually checked: eight are byte-exact
to previously actually viewed images and changed page 68 is actually viewed.
All 49 current active statements and original provenance, 44 proof blocks,
listings and literal ratio/TOT content stay exact; only the concordance status
paragraph is added. The isolated rank-bridge consumer confirms the narrowed
import. These gates precede exact seven-path staging and commit/push.

## First-meet difference-cocycle data lemma (#27, L1a)

Correspondence.DifferenceCocycle proves one plain-field prerequisite:
two affine presentations a'x'+b'=ax+b sharing p and δ have b−b'∈racl{a,a'}.
Its explicit inputs are independent a,b,x; a' fresh over their closure;
p∈racl{a,b} outside racl{a}; δ∈racl{a,x} outside racl{a}; and the corresponding
primed memberships. It constructs no second presentation. The genuine named
consumers are corrected 8.5 first-meet elimination and its common-center step.
Literal parameter-fixing relocation, linearity, guarded extraction/Q completeness,
multiplication converse and unconditional J completeness remain open.

Claude's immutable source-only freeze is pinned to 61b8b42; root verifies both
input hashes, all draft/root hashes and the single-import root proposal. It
imports only Closure.Basic. Its first actual source elaboration passes 2.00s
warning-free/default checking with no proof/type repair. An earlier overlay
lookup failed before source elaboration because cached project object links
were missing; the source and failure remain preserved outside git.

The inventory is one public/two private authored theorems, no generated
additions. Both exchange helpers have actual consumers. All three scoped
types/normalized bodies/attributes/docstrings/axiom records pass, with only
standard Lean axioms; this is not a whole-library axiom certification. Two
actual consumers pass 8.00s with standard lint: the exact plain-field interface
and a nontrivially shifted presentation with four independent coordinates,
valid in every characteristic. Two external fixture failures remain recorded:
injectivity arity/qualified API/membership metavariables, then prefix-function
equality and a residual field identity. Only those new external fixtures and
their diagnostic count expectations changed; no production proof, historical
fixture or checking option changed.

The L0 checkpoint 61b8b42 is committed/pushed after full library/book and actual
shared/source gates. G1 remains complete through G1a/b/c; frozen 117 M4a and
all public Main targets/guarded completeness definitions stay unchanged.

Claude's refreshed five-path read-only review is ACCEPT. Its optional clarity
and spacing corrections are applied: shared closure memberships and
non-memberships are explicit. The touched book receives a proper module
header, removal of the display-only pp.rawOnError option and an old long-line
wrap. A private attempt applied Mathlib submission linters to Verso's required
#doc command; those genre findings are retained. The book uses canonical
Verso/lake lint scope; new mathematical source and consumers keep all standard
Mathlib linters and default kernel checking, with no checking option disabled.

The actual shared full library/book pass 88.04s/16.01s (minimum available
35.31GiB, peak family RSS 8.18GiB for the full build), without a memory stop.
The 26-check actual-main family passes 50.02s: the earlier 22 check inputs and
all their scoped types/normalized bodies/attributes/docstrings/axiom records
stay exact, covering 72 old fixtures/62 public records, guarded 125 records
and ten behaviors, generic 163 records and six behaviors, and lattice 84
records and six consumers. The new three records/two actual consumers stay
exact to their privately accepted baseline. All 251 Lean sources pass
placeholder/project-axiom hygiene; all 249 prior module/Main sources stay exact.

All 101 HTML paths remain, with the new data docstring and existing L0/G1c
entries visible. The source has four stable passes and 70 pages; all ten
selected current pages are visually accepted. Nine current images are
byte-identical to previously actually viewed images, and final changed page
68 is actually viewed. The bibliography is wholly on page 70; no single-line
orphan or overflow occurs. All 49 active statement blocks/original provenance,
44 proof blocks/listings and the literal ratio/TOT content remain exact.
Only a concordance status paragraph is added. These gates precede exact
five-path staging and commit/push; completeness and relocation remain open.

## D/F genericity prerequisites for first-meet elimination (#27, L0b)

The existing PsiLattice gains three necessary consequences under Psi and
I≠D: D lies outside A∨B∨C, hence D≠S, and F≠U. D≠S supplies the shared-point
non-membership required by L1a when affine coordinates are supplied. F≠U is
the generic multiplier projection prerequisite for the proposed finite-fibre
linearity argument. Neither coordinates, literal relocation, a curve action
nor linearity/extraction/completeness is constructed.

Root proves them using only existing point exchange, P≤A/P≠S and the literal
D/F meets. D inside the parameter join would force D=S and then Y≤A; F=U
would put D on T∨U inside that join. The first production check passes
2.00s with standard lint/default kernel; no proof repair, new helper or
checking option is used. The first scoped/actual-consumer check passes
8.01s. All 84 earlier type/body/attribute/docstring/axiom records stay exact;
the new scoped total is 87. The module has 40 authored theorems, seven public
and 33 private, with no generated additions. All checked axioms are standard
Lean axioms; this remains a scoped audit. Two actual consumers are the exact
abstract guarded interface and the canonical independent table.

L1a is published at cae7151, with its one public/two private data theorems
and exact earlier source/Main/frozen provenance. The first fixed-three
relocation plan would not preserve c/f literally. The corrected source-only
L1b plan fixes p,y,δ,c,f, with f∈racl{c,δ} and δ∈racl{p,y} keeping the fixed
base closure inside {p,y,c}. That constructive proof remains unaccepted.
The genuine group/action/classification, guarded completeness and multiplication
converse remain open; the frozen 117-item M4a is unchanged.

Claude's read-only review accepts all three proofs and all four paths. The
actual-main full library/book pass 102.05s/18.01s (minimum available 35.05GiB,
peak full-family RSS 8.34GiB), with no memory stop. The 30-check actual-main
family passes 56.03s: all 26 earlier fixture inputs and prior scoped records
remain exact, including the old 84 lattice records; the sole lattice addition
is the three named theorems. The new 87-record audit and two actual consumers
match the accepted private baseline. Old 72 fixtures/62 public records,
guarded 125/ten behaviors, generic 163/six and cocycle three/two stay exact.
New production/behaviors use standard lint/default checking; historical
fixtures retain exact bytes and their established diagnostic scope. All 251
Lean sources pass placeholder/project-axiom hygiene; every 249 other old
module/Main source and the entire root import file remain byte-exact.

All 101 HTML paths remain with the D/F and prior L0/L1a/G1c docstrings visible.
The source passes four stable runs/70 pages, with ten selected pages visually
accepted: eight are byte-identical to previous actual views, and changed
pages 68/69 are newly viewed. All 49 active statement blocks/original
provenance, 44 proofs/listings and literal ratio/TOT content remain exact;
only one concordance paragraph is added. Frozen 117 M4a remains unchanged.
These actual gates precede exact four-path staging and commit/push. Both
prior L0/L1a exact CI runs are fully green, including every build/book/deploy
job and step. L1b and all completeness/action/classification obligations
remain unaccepted; its original private source passes standard production
without repair, but inventory/consumer/integration gates are still pending.


## Literal fixed-five affine relocation (#27, L1b)

Correspondence.AffineRelocation constructs a second presentation a′x′+b′=ax+b
from independent a,b,x,c, p∈racl{a,b} outside racl{a}, δ∈racl{a,x}∩racl{p,ax+b},
f∈racl{c,δ}, and a given a₀ fresh over a,b,x,c. It literally fixes p,ax+b,δ,c,f
and preserves their joint vanishing ideal with the moved triple. The new a′
is algebraic over p,ax+b,c,a₀ and fresh over a,b,x,c. No a′=a₀ or existence
of a₀ is asserted. Together with D≠S this constructs the actual L1a consumer;
literal c/f fibre preservation is the named prerequisite for proposed L2
linearity. Coordinate extraction, curve action, linearity, guarded Q/Q′
completeness, multiplication converse and unconditional reconstruction remain
open. This supersedes the earlier checkpoint's pending L1b status only.

Claude's immutable one-theorem source-only freeze is pinned to cae7151. Root
verifies five imported/root input hashes, all draft/base hashes and the three
Lean/toolchain/Lake pins. L0b's four-path checkpoint 13529c9 changes none of
these inputs. The original standard-lint/default-kernel production passes
4.00s without proof repair, warning or checking option. The scoped inventory
is one public theorem, no private helper or generated addition; its exact
type/body/attributes/docstring/axiom records use standard Lean axioms.

Two genuine consumers pass 18.01s with standard lint/default checking:
constructing the full fixed-five/controlled-fresh presentation supplies the
published L1a difference-cocycle theorem; the canonical table p=b,δ=ax,f=c(ax)
preserves the same literal c/f fibre equation through the joint ideal.
A first new external canonical fixture omitted the result type of a closure
subtraction, leaving membership metavariables. Its source/log and green scoped
records are retained outside git; only that explicit fixture type changed.
No production proof, old fixture or checker option changed. This remains a
scoped audit, not a whole-library axiom certification. Integration acceptance
and actual-main/library/book/source gates are still pending at this proposal.

The private six-path proposal adds one module/import, status-only text in
DifferenceCocycle, book exposition, a source concordance paragraph and two
concordance status corrections, plus this record. All mathematical statements,
proof blocks, historical provenance and literal source content remain exact;
all older declaration types/proofs/attributes/docstrings remain unchanged.
Frozen 117 M4a and all public Main targets are unchanged. L0b 13529c9 is
committed/pushed and locally green; its exact CI is pending, while both prior
L0/L1a exact runs are fully green including every build/book/deploy job/step.

Claude accepts all six paths and both actual consumers. The first private
book import failed before book elaboration because this overlay lacked the
cached Configurations/GroupChunkRecord object link; both mathematical modules
passed standard lint. The first four-pass TeX run retained a 5.94pt overflow
in the new long module name. The cache lookup and prose wrapping are repaired
without any production proof, fixture or checking-option change. Failed
source/logs are retained outside git and excluded from acceptance.

The second prose reflow still overflowed by 72.20pt because the separate
namespace was unbreakable. That failed source/render is also retained;
the new paragraph now uses the existing breakable Lean-name macro. The
second private mathematical/book chain passes 42.02s warning-free/default
checking after the cached import link repair. Source layout acceptance is
still pending, with all production proofs and checking options unchanged.

The third new-paragraph reflow still overflowed by 6.48pt: actual PDF
inspection locates it in the run-in heading plus long module name. That
failed source/render is retained. A short prose lead now gives TeX a normal
break before the module name; no mathematical or checker change is made.

The final source render passes four stable runs/70 pages without overflow,
undefined labels or rerun requests. Ten selected current pages are visually
accepted: eight are byte-identical to the previous actually viewed images;
changed pages 68/69 are newly viewed. All original mathematical blocks and
whole source recovery, except the new paragraph/two concordance status
sentences, remain exact. All three earlier L0/L1a/L0b exact CI runs are now
fully green, including every library/book/deploy job and step. Actual-main
integration and commit acceptance remain pending before application.

Actual-main full library/book pass 94.03s/16.01s, with minimum available
36.69GiB and full-family RSS8.23GiB, no memory stop. The 34-check actual-main
family passes 70.04s: all 30 prior fixture inputs and their scoped
type/body/attribute/docstring/axiom records remain exact, including old72
fixtures/62 public records, guarded125/ten behaviors, generic163/six,
lattice87/six plus two D/F consumers, and cocycle three/two. The new
one-record/two genuine consumers stay exact to the accepted private baseline.
All 252 Lean sources pass placeholder/project-axiom hygiene. All 249 other
old module/Main sources stay byte-exact; DifferenceCocycle changes only
module-status text and retains all declaration metadata/proofs. The root
adds exactly one import. The new proof source is byte-exact to the peer's
immutable original except its module-status text.

All 101 HTML paths remain, with the new relocation and every previous
L0/L0b/L1a/G1c entry visible. The source has four stable runs/70 pages and
ten selected current pages accepted: eight exact previous actual views
and final changed68/69 newly viewed. All 49 active mathematical statements
and original provenance, 44 proofs/listings/literal ratio/TOT content and
frozen 117 M4a remain exact. Whole old source recovery permits only the new
concordance paragraph and two current status sentences. These actual gates
precede exact six-path staging and commit/push; supplied fresh a₀/original
coordinates, iterated ambient freshness, component/stabilizer linearity,
genuine action/classification and guarded completeness remain explicit.


## Multiplier-curve and generic finite-fibre prerequisites (#27, L2a)

Correspondence.MultiplierCurve proves three plain-field raw-data prerequisites:
equality of vanishing ideals transfers the same polynomial map; L1b's literal
fixed-five joint ideal transfers the same (f,a′c,x′) locus and f's closure
membership/non-membership, hence x′∈racl{a′c,f}; independent A,B,M,X with
f∈racl{M,X} outside racl{M} gives X∈racl{M,f}, M∉racl{A,B,f} and
f∉racl{A,B}. The source projection is M; X need not be generic over that
parameter field (f=X is a counterexample). The genuine named consumers are
the proposed first-meet multiplier-curve argument and the existing
CurveIdeal.exists_prime_span_idealOf over k(A,B,f), with tower conversions.
No component action, stabilizer or linearity is assumed or proved. Iterated
ambient freshness, coordinate extraction, genuine group/action/classification
and guarded Q/Q′ completeness remain open; frozen 117 M4a is unchanged.

Claude's immutable source-only freeze is pinned to 091acbd. Root verifies
six input hashes (including Lean/toolchain/Lake), all three draft/base/root
hashes and the explicit published-commit annotation. The original source is
164 lines, three public theorems and no private helper/generated addition.
Its first actual standard-lint/default-kernel source elaboration passes
2.00s unchanged, minimum available 39.16GiB, without proof repair or option.
An earlier root parser treated the commit annotation as a file path after
all six actual file hashes were verified; a missequenced missing-overlay
invocation then failed before any Lean elaboration. Both infrastructure
failures remain recorded outside git and excluded from acceptance. The
strict manifest parser is repaired; immutable source/main were unchanged.

All three scoped type/body/attribute/docstring/axiom records pass with only
standard Lean axioms. Three genuine examples and their consumed prime-curve
helper pass 8.00s with standard lint/default checking: actual constructed
relocation yields the same multiplier locus/fibre; the horizontal f=X and
shifted f=M(X−1) models produce prime equations over the actual parameter
field through the raw genericity theorem and existing CurveIdeal API.
The latter is characteristic-free and exercises a nonzero origin. No new
fixture/proof repair is needed. This is a scoped audit, not a whole-library
axiom certification. Actual-main/library/book/source/integration acceptance
is still pending in this five-path private proposal.

L1b 091acbd is committed/pushed with one constructive fixed-five relocation
theorem and all earlier source/Main/frozen provenance exact. Its exact CI is now fully green; together with L0, L1a and L0b,
all four prior exact runs are verified including every library/book/deploy
job and step. This proposal adds one module/import,
three book docstrings, a source concordance paragraph and this record only;
all previous mathematical declaration/source blocks remain unchanged.

Claude accepts the five-path mathematical/documentary scope and all genuine
consumers, but finds a literal backslash-n in root’s new module-status text.
The first private chain exits zero with a long-line warning; that diagnostic
finding is retained and excluded from acceptance. The actual line break is
repaired. Published AffineRelocation/DifferenceCocycle contain no such escape.
No declaration proof/type/attribute/docstring or checking option changes.
The first source render also retains a 42.30pt new-paragraph overflow; source
layout acceptance remains pending until actual reflow and visual checks.

The repaired private mathematical/book chain passes 30.01s warning-free,
minimum available38.52GiB, with standard mathematical/default checking and
canonical Verso scope. The final source render passes four stable runs/70
pages without overflow or undefined/rerun requests. Ten selected current
pages are accepted: nine are byte-identical to previous actual views and
final changed69 is newly viewed. Only a new concordance paragraph changes;
all old mathematical source blocks/provenance remain exact. Actual-main
integration and the five-path commit gates remain pending before application.

Claude's refreshed five-path/consumer review is ACCEPT after the status
escape correction and prose reflow. Actual full library/book pass76.03s/10.00s
(minimum available36.78GiB, full-family RSS10.74GiB), no memory stop.
The38-check actual-main family passes60.02s: all34 previous fixture inputs
and scoped type/body/attribute/docstring/axiom records remain exact, including
old72 fixtures/62 public records, guarded125/ten behaviors, generic163/six,
lattice87/six plus two D/F examples, cocycle three/two and relocation one/two.
New three-record/three-example checks match the accepted private baseline.
All253 Lean sources pass placeholder/project-axiom hygiene. Every251 earlier
module/Main source remains byte-exact; root adds exactly one import. The new
source equals the immutable peer original except the real module-status text.

All101 HTML paths remain, with new three docstrings and all prior
L0/L0b/L1a/L1b/G1c entries visible. The source passes four stable runs/70 pages
with ten current selected pages accepted: nine exact previous actual views
and final changed69 newly viewed. All49 active statement blocks and original
provenance,44 proofs/listings/literal ratio/TOT and frozen117 remain exact;
whole old source recovery permits only the new concordance paragraph. These
actual gates precede exact five-path staging and commit/push. Same joint
k-locus is the precise proved equality; fixed-parameter relative-locus and
finite-color/base-change/stabilizer arguments remain obligations. All four
prior exact CI runs are fully green including every build/book/deploy step.


## Shared prime multiplier equation and uniformly bounded curve loci (#27, L2b)

Correspondence.MultiplierPrimeCurve starts from the original L1b independence
of a,b,x,c, derives independence of a,b,ac,x, and combines L2a with the
existing FamilyCover common-parameter theorem. A literal fixed-five
relocation has the same prime pair ideal over the actual field k(f).
One public theorem and one consumed private tuple-independence helper give
this genuine producer; all larger-base genericity and stabilizers remain
open. The first isolated source check lacked the focused
Geometry.Representatives import; that diagnostic is retained. Adding that
import gives standard-lint/default-kernel success in 2.00s, minimum
available 39.38GiB, without changing the proof or checking options.

Correspondence.FiniteCurveLoci supplies two public theorems: all generic
dependent pair ideals on one nonzero planar equation F lie in one Finset
with cardinality at most totalDegree F, hence form a finite set. One
consumed private helper bounds the number of prime factors counted with
multiplicity by total degree. This is the finite-component selection input
for corrected affine-grid meet elimination, without any geometric-primality,
action, stabilizer, linearity or guarded completeness hypothesis.

Claude's immutable 102-line replacement is pinned to 761fd99 and root's
immutable input. All 8 source/toolchain inputs, 8 Mathlib API files and 5
draft hashes verify; the earlier finite theorem's TYPE text remains exact.
Its first actual standard-lint/default-kernel check passes unchanged in
2.00s, minimum available 39.40GiB. No weaker option or proof repair is used.
The earlier root 53-line finite-only proof, its post-review explicit K,
author/doc clarity changes and all prior accepted/failed fixtures are kept
outside git. The API audit finds the literal fixed-parameter pair transfer
already proved in FamilyCover; a redundant FixedParameterLocus draft is
cancelled before any source is produced. That discovery supersedes the
earlier relative pair-ideal audit gap, while larger-base geometric producers
and the separate #11 blueprint obligation remain open.

The actual uniform shared-equation consumer has five examples and all five
scoped records (three public/two private, no generated declaration) checked
with only standard Lean axioms. It passes 8.00s warning-free, minimum
available 38.99GiB: an arbitrary family finite range, two distinct horizontal
loci on the reducible X1(X1−1), actual constructive L1b from AI(a,b,x,c) to
the public shared prime equation, mapped shared-equation finite loci with
explicit larger-base genericity, and a color Finset bounded by the ORIGINAL
equation degree after coefficient extension. This is a scoped axiom audit.

The quantitative route chooses n=3D+1 before relocations, D=totalDegree F.
The earlier plan-only 4N−3 formula fails for small N and is superseded.
No corresponding theorem or source statement was changed. Mere finiteness
is sufficient for an alternate route that first supplies one infinite
independent ambient family, then fixes its single relatively closed
coefficient field and uses infinite pigeonhole. The finite-n route instead
uses the uniform degree bound. Both require genuine ambient enlargement
and descent, which this checkpoint does not prove. The proposed common
final field may avoid geometric primality in this engine; original #11
remains an independent blueprint obligation. Pairwise L1a, larger-base
genericity, finite translation stabilizers and conjugation in every
characteristic, linearity, ambient/descent, coordinate extraction and all
guarded completeness remain open, with no hidden oracle.

Private diagnostic findings are retained and excluded from acceptance:
a pre-compiler quoted-argv wrapper failure; original fixture implicit K
before .subset and two unnecessarySimpa warnings; a dependent coefficient
subtype rewrite needing typed parameter/rw; private doc long lines; a
tuple-AI simplifier rewriting the closure range without resolving the
displayed coordinate; and an incomplete Book cache namespace before any
book elaboration. The latter is corrected by complete cached Book links.
A precheck assertion after optional nits stopped before hash refresh, but
a dependent book call incorrectly proceeded; it is retained. A subsequent
call selected the Mathlib submission linter for Verso's mandatory #doc;
that genre finding is excluded. The final book uses canonical Verso/lake
lint; mathematical sources and actual fixtures use the standard Mathlib
set/default kernel, with no checking-option weakening.

L2a 761fd99 is cleanly committed/pushed and CI37727164446 is fully green,
including every library/book/deployment job and step. All five prior
owned current body references are synchronized. This six-path private
proposal adds two focused modules/imports, three book docstrings, ONE source
concordance paragraph and this record. Every 252 earlier module/Main source,
49 active mathematical blocks and historical provenance, 44 original
proofs/listings/literal content, all public reconstruction assumptions and
frozen 117 remain unchanged. Final private book/source/visual gates, renewed
peer review and actual-main acceptance precede application and commit/push.


Claude's refreshed six-path and all actual-fixture review is ACCEPT after
the two source accuracy qualifications and optional final spacing repair.
The canonical mathematical/book chain passes 24.01s warning-free, minimum
available 38.39GiB. Mathematical modules retain standard lint/default kernel;
Verso uses its canonical checking genre. Final source rendering has four
stable runs/70 pages with no overflow or undefined/rerun request. Ten selected
current pages are accepted: nine byte-identical to previous actual views
and changed 69 newly viewed, including all three long module names. This
precedes hash-guarded main application and actual library/book/regressions.


Actual-main full library/book pass 58.02s/8.00s, minimum available 36.84GiB
(full-family RSS 8.38GiB), with no memory stop. The 44-check regression family
passes 86.04s, minimum available 38.09GiB/RSS 2.90GiB. All 38 earlier fixture
inputs and scoped TYPE/RAW/ATTR/DOC/AX records remain exact, including
old 72 fixtures/62 public records, guarded 125/ten, generic 163/six,
lattice 87/six plus two D/F, cocycle 3/two, relocation 1/two and multiplier 3/three.
The new five-record/five-example checks match the accepted private baseline.
All 255 Lean sources pass placeholder/project-axiom hygiene. Every 252 earlier
module/Main source is byte-exact; root adds exactly two imports. The uniform
module is exact to Claude's immutable original, and the shared-prime source
is exact to the accepted root proof except its real module-status text.

All 101 HTML paths remain, with the three new docstrings and prior
L0/L0b/L1a/L1b/L2a/G1c entries visible. Source passes four stable runs/70
pages and ten current selected visual checks: nine exact earlier actual
views and changed 69 newly viewed. All 49 active statements/provenance,
44 proofs/listings/literal ratio/TOT and frozen 117 remain exact; whole old
source recovery permits only ONE added concordance paragraph. The entire
historical CONT prefix is preserved exactly. These actual gates precede
the final precommit library/book pair and exact six-path staging/push.
Only shared-prime/uniform-color prerequisites are proved; geometric
genericity producers, ambient/descent, stabilizers, linearity and all
guarded/unconditional reconstruction remain open.


## L2c finite-stage scale genericity and a fixed-equation private consumer

Pinned to clean published L2b 35d6d97, with CI37730759281 fully green
including every library/book/deployment job and step. Claude's SOURCE-ONLY
GO4451 produces an immutable, uncompiled 151-line MultiplierPrimeCurve
draft (+55 lines, old 93-line prefix and final namespace closes exact).
All eight project/toolchain inputs, four Mathlib API files and five draft
SHA1 values are checked. The first actual standard-lint/default-kernel
check passes 2.00s warning-free, minimum available 39.40GiB, without any
proof repair. The private multiplier_tuple_independent gains a second
consumer; there is ONE new public theorem, no new private or generated
declaration. The old five scoped TYPE/RAW/ATTR/DOC/AX and proof records
remain exact; only the new scale theorem is added, with standard axioms.
Metadata passes 6.00s, minimum available 39.10GiB.

The theorem proves c outside acl(a,f,finite selected multipliers), from
AI(a,b,x,c), f in acl(ac,x) but not acl(ac), and each supplied a'_i fresh
over original a,b,x,c plus earlier selected multipliers. Direct exchange
induction supplies the bounded finite-stage result; no infinite family
or existence/enlargement theorem is inserted. The library module's real
Status text is qualified accordingly; its imports and every old declaration
remain unchanged. The root file remains WHOLE byte-exact.

A genuine generic-field bridge passes 2.00s standard-lint/default-kernel,
minimum available 39.47GiB: c outside the relatively closed L, nonzero a
inside L and x in acl(ac,f), with f in L, imply transcendence of ac over
L and algebraicity of x over L(ac). The actual colored literal-relocation
consumer uses L=acl(original a,f,all selected a'_i), not just new multipliers.
Keeping original a supports the next original-versus-i L1a consumer.
The separate delta outside acl(a) hypothesis needed for L1a remains
explicit; it is not silently treated as an L1b input.

Claude's READ-ONLY review4463 caught a PRIVATE STATEMENT defect before any
main integration: an existential prime F with no original pair-ideal span
could give a vacuous bound by an unrelated high-degree prime. The earlier
green proof selected the right F but its statement failed to require it.
The earlier fixture/output/acceptance are retained and EXCLUDED, and
#27 reports the defect before changes. The strengthened actual consumer
takes F, Prime F and the ORIGINAL pair-ideal span as inputs before all
future family sizes and choices. Its final example first obtains such F
from the published producer, then quantifies over EVERY supplied finite
fresh literal-relocation family. It gives one common relatively closed L
and a color Finset bounded by THAT ORIGINAL totalDegree F, via actual
injective coefficient-map degree preservation. It passes 4.00s warning-free,
minimum available 39.13GiB/RSS 2.64GiB. Two actual examples and two consumed
private fixture helpers are accepted; production scale source is unchanged.
Claude's renewed READ-ONLY review4470 ACCEPTS the corrected quantifier
order and original span, resolving the defect.

Earlier letI style warnings are retained and excluded; local let instances
give standard Mathlib lint with no weakened checking option. Diagnostic
metadata keeps its historical checking genre. No public color-composition
theorem is claimed: these are actual PRIVATE consumers of the public scale,
shared-equation and uniform-color producers. Given sequential freshness,
larger-base genericity in this composition is now derived. Existence of
fresh relocation inputs, stronger fresh relocation output from L1b,
ambient enlargement/descent, finite translation stabilizers and conjugation
in every characteristic, linearity, coordinate extraction and all guarded
or unconditional reconstruction/completeness remain open. The separate
#11 blueprint geometric-primality obligation remains open.

This proposal changes FOUR paths only: the existing mathematical module,
one book docstring/qualified account, ONE source concordance paragraph and
this append-only record. All 253 other earlier mathematical module/Main
sources, whole root, 49 active source statements and historical provenance,
44 proofs/listings/literal content and frozen 117 remain byte-exact.
Private canonical book/source rendering, current visual acceptance,
renewed four-path peer review and actual-main gates precede commit/push.


Private canonical mathematical/book chain passes 24.01s warning-free,
minimum available 38.46GiB/RSS 4.37GiB. The first four-pass source rendering
has a 29.14pt overfull new module-name lead; its PDF/log are retained and
failed page 69 actually viewed. A normal-word lead fixes layout only;
this failed render is excluded from acceptance. Source rerender follows.


Claude's four-path review4475/4476 ACCEPTS. The source now names L(a'_i c)
explicitly and uses consistent totalDegree notation. A warning-free stable
71-page render is actually inspected (changed 3,69,70,71); its two-line
tail on 70 is excluded from final visual acceptance. Concision of ONLY the
new paragraph repairs that tail without altering any mathematical claim.


Final source rendering passes four stable runs/70 pages, with no overflow,
undefined/rerun request or two-line tail. All ten current selected pages
are accepted: nine byte-identical to earlier actual views and changed 69
newly inspected after the final wording/layout repairs. The bibliography
and its contents entry are whole byte-identical to earlier actual views.
The final four-path proposal is hash-pinned; actual main gates follow.


Final peer refresh4483 ACCEPTS all four current paths after source concision.
Actual-main full library/book pass 98.04s/8.00s, minimum available 36.87GiB
(full-family RSS 8.38GiB); no memory stop. The strict 49-check family passes
62.02s, minimum available 38.94GiB/RSS 3.19GiB. All 44 older fixture inputs
remain byte-exact, and every old scoped TYPE/RAW/ATTR/DOC/AX/proof and deny-list
record remains exact. ONLY the named scale theorem is permitted as an extra
in the three combined curve metadata fixtures; old five rows remain exact.
The new six combined records/two actual examples match the accepted private
baseline with standard mathematical/behavior lint and default kernel.
Historical diagnostic checking genres remain unchanged. Untouched historical
warning replay is retained; the touched mathematical/book sources are clean.

All 255 mathematical sources pass placeholder/project-axiom hygiene.
All 101 HTML paths remain with the new scale docstring and earlier entries.
The root is WHOLE byte-exact, as are all 253 other mathematical module/Main
sources, toolchain/manifest/lakefile, 49 active source blocks and historical
provenance, 44 proofs/listings/literal content and frozen 117. Whole old source
recovery permits ONLY the one new concordance paragraph; whole old CONT
prefix is exact. Source final four stable runs/70 pages and ten current visual
selections pass, nine exact earlier views and changed 69 newly inspected.
These actual gates precede the final required library/book pair and guarded
four-path stage/commit/push. Supplied finite-family scale genericity only
is accepted; ambient/fresh-input existence, stabilizers/linearity, extraction
and all guarded/unconditional completeness remain open.


## L2d literal relocation fresh over supplied extra data

Pinned to clean published 2c1fd36, with exact CI37733565596 fully green:
every library/book/deployment job and step verified, all seven owned
current issue-body references synchronized. Claude's SOURCE-ONLY GO4493
freezes a 263-line uncompiled AffineRelocation draft, +38 append-only lines.
All eight project/toolchain inputs, two Mathlib API files and five draft
SHA1 values are checked; old 221-line prefix and four closes are exact.
The FIRST actual standard-Mathlib-lint/default-kernel check passes unchanged
2.00s warning-free, minimum available 39.38GiB. No proof or option repair.
ONE new public theorem, no helpers/imports/generated declarations; the old
L1b TYPE/RAW/ATTR/DOC/AX/proof/deny-list records remain exact. Metadata passes
4.00s, minimum available 39.04GiB. Its consumed old producer returns the
same literal joint ideal, controlled algebraicity, p/δ memberships and value,
now with freshness over original a,b,x,c PLUS arbitrary supplied T.

The genuine PRIVATE consumer starts with ONE upfront supplied input family
t_i fresh over the original data and earlier inputs. Each relocation is
constructed independently via the new producer with T=earlier inputs;
controlled algebraicity places all earlier OUTPUTS in that input closure,
so OUTPUT sequential freshness follows. There is no recursion, literal
joint-ideal or output-freshness oracle. One prime F and its ORIGINAL span
are fixed before ALL n/input-family choices. Published scale/shared-equation/
color producers give a common relatively closed final field L and colors
bounded by THAT original degree. Actual L1a also gives every b−b'_i in L,
with delta outside acl(a) explicitly added to the consumer, not hidden as
an L1b hypothesis. The actual single example/three consumed private fixture
helpers pass 4.00s standard/default warning-free, minimum available
38.96GiB/RSS 2.69GiB. The first private fixture has a final untyped Set
inclusion inference error and one long docstring; findings retained/excluded,
fixed only in the private consumer. Production proof remains unchanged.

The library publishes ONLY the stronger single-relocation producer;
all family/color/cocycle compositions are actual PRIVATE checks.
Existence of the upfront fresh input family, ambient enlargement/descent,
finite vertical translation stabilizers, characteristic-free conjugation,
linearity, coordinate extraction and all guarded/unconditional completeness
remain open. The next substantive target is the measured finite vertical
translation stabilizer; no assumed action/linearity is introduced. Original
#11 remains a blueprint obligation. The root stays WHOLE unchanged.

This FOUR-path proposal changes the existing mathematical module's appended
theorem/real Status, adds one book docstring with accurate scope, ONE source
concordance paragraph and this append-only record. All 253 other mathematical
module/Main sources, root, source 49 active statements/provenance, 44 proofs/
listings/literal content and frozen 117 stay exact. Renewed peer consumer/
four-path review, canonical private book/source/visual and actual-main
full/library/book/strict regressions precede guarded commit/push.


Claude's READ-ONLY consumer review4501 ACCEPTS the construction, output
freshness, fixed original equation/quantifier order and explicit L1a delta
hypothesis. The first private canonical book chain fails only on an
unescaped underscore in new plain prose; the mathematical source passes.
The finding is retained/excluded and fixed by ordinary words in book prose.


Final private mathematical/canonical Verso book chain passes 24.01s
warning-free, minimum available 38.30GiB/RSS 4.39GiB, with mathematical
standard lint/default kernel and canonical book genre. Source passes four
stable runs/71 pages with no overflow, undefined/rerun request or orphan tail.
All eleven current selected pages are accepted: seven byte-identical to
earlier actual views and changed 3,69,70,71 actually inspected. Generic
invariance starts intact on 70; bibliography and contents reflect page 71.
These gates precede hash-guarded main application and actual acceptance.


Claude's exact four-path review4508 ACCEPTS. Actual-main full library/book
pass 58.02s/8.00s, minimum available 36.73GiB/full-family RSS 8.39GiB,
with no memory stop. The strict 53-check family passes 68.02s, minimum
available 38.78GiB/RSS 2.90GiB. All 49 earlier fixture inputs remain
byte-exact, every old scoped TYPE/RAW/ATTR/DOC/AX/proof/deny-list row stays
exact; ONLY the named stronger relocation is allowed as an extra in the
three old relocation metadata fixtures. New two-record/one actual constructed
family check matches the accepted private baseline. The diagnostic genres
stay unchanged; actual mathematics/behaviors retain standard lint/default
kernel. Untouched historical warning replay is retained, touched sources clean.

All 255-source placeholder/project-axiom hygiene, 101 HTML paths/new and prior
docstrings, four stable source runs/71 pages and eleven current visual gates
pass: seven exact earlier views and changed 3,69,70,71 newly inspected.
Root WHOLE and all 253 other mathematical module/Main sources stay exact.
Source whole recovery permits ONE added concordance paragraph; all 49 active
statements/provenance, 44 proofs/listings/literal content and frozen 117 stay
exact. Entire old CONT prefix remains exact. These actual gates precede the
required final library/book pair and exact four-path stage/commit/push.
Only the supplied-extra-data freshness producer is accepted; ambient input
existence/enlargement/descent, stabilizers/conjugation, linearity, extraction
and guarded/unconditional completeness remain open.


## B1 finite equal-ideal fibres and characteristic-free private stabilizer consumer

Pinned to clean published 05e9aeb, whose exact CI37735173995 is fully green
at every library/book/deployment job and step; all eight owned issue-body
references are synchronized. Claude's SOURCE-ONLY GO4519 freezes an
immutable 199-line MultiplierPrimeCurve draft with a 47-line append.
All eight project/toolchain inputs, six Mathlib API files and five draft
SHA1 values are checked; old 148-line prefix and four closes are exact.
The FIRST actual standard-Mathlib-lint/default-kernel check passes unchanged
2.00s warning-free, minimum available 39.30GiB. No production proof or option
repair. ONE new public theorem, no helpers/imports/generated declarations.
For arbitrary fields k,K, x algebraic over k(m) makes the actual set of z
with idealOf_k(m,z)=idealOf_k(m,x) finite, by the minimal polynomial's root
set over k(m). No genericity, ACF, action or geometric primality is assumed.
Existing polynomial-image transfer appends zero; existing common-parameter
transfer then supplies the relative pair ideal. No redundant polynomial
specialization API is added. All six older scoped TYPE/RAW/ATTR/DOC/AX/proof
records remain exact; the new seven-record audit passes 4.00s warning-free,
minimum available 39.00GiB/RSS 2.65GiB, with standard Lean axioms only.

The actual PRIVATE power-orbit bridge uses transcendence over ORIGINAL k,
not merely lambda != 1, to prove powers injective in every characteristic.
Actual polynomial-image conjugation gives z -> z*lambda without an action
or stability oracle. Finite equal-ideal fibres then force every preserving
vertical translation whose coefficient belongs to L to be zero. This does
not assert vanishing of all ambient-K translation coefficients. The genuine
same-color relocation consumer derives lambda=a'_j/a'_i and its original-k
transcendence from sequential output freshness; original-a cocycles put
nu=(b'_i-b'_j)/a'_j in L, and the shared affine value gives the actual map
between pair coordinates. Its point-ideal preservation comes from the
actual equal-color hypothesis. No scaling-preservation/conjugation/order
oracle is supplied. Each standalone actual consumer passes 2.00s warning-free
with standard lint/default kernel; Claude4530/4535 ACCEPT their mathematics.
Initial parser, coercion/arithmetic and style findings are retained/excluded
and repaired only in PRIVATE consumers; the production proof stays exact.

The combined actual PRIVATE 395-line consumer starts from the supplied
upfront sequentially fresh INPUT family and constructs each relocation.
It derives OUTPUT freshness, literal joint ideals, all original-a cocycles,
larger-base pair algebraicity and original-degree-bounded colors over ONE
common relatively closed final field L. The original prime F/span precedes
ALL family sizes and input choices. Its explicit separate delta outside
acl(a) input supplies L1a; it is not hidden as a relocation hypothesis.
At EVERY actual equal-color pair i<j it derives zero L-coefficient vertical
translations; all scaling, conjugation and orbit ingredients are derived.
ONE actual example consumes nine private fixture helpers. The first merged
fixture omitted the MvPolynomial namespace and had two long lines; it is
retained/excluded. Namespace/style-only repair passes 6.00s warning-free,
minimum available 38.56GiB/RSS 2.77GiB. Claude's READ-ONLY review 4541
ACCEPTS the full consumer and unchanged finite-fibre producer; equal-color
selection remains explicitly open.

Only the finite-fibre producer is a new public library theorem; all
stabilizer and full-family compositions remain PRIVATE actual checks.
Equal-color pigeonhole selection, commutators, common centers, linearity,
ambient fresh-input existence/enlargement/descent, coordinate extraction
and all guarded/unconditional completeness remain open. Original #11 is
an independent blueprint obligation, and frozen 117 remains unchanged.

This FOUR-path proposal changes the existing mathematical module's appended
theorem/accurate Status, adds one book docstring and qualified account, ONE
source concordance paragraph and this append-only record. Whole root and
all 253 other mathematical module/Main sources remain exact; 49 active source
statements/provenance and 44 proofs/listings/literals remain exact.
Private canonical book/source rendering, current visual acceptance, renewed
peer four-path review and actual-main full/library/book/strict regressions
precede guarded commit/push.


Claude's four-path READ-ONLY review4546 ACCEPTS all four current proposals.
Its wrapping nit is corrected only in this append. The private mathematical/
canonical Verso book chain passes 24.01s warning-free, minimum available
38.11GiB/RSS 4.50GiB. The first four-pass source render has a 36.25pt
overfull module-name lead on page 70; failed PDF/log/source are retained,
the failed page is actually viewed, and this render is excluded. A longer
ordinary-word lead in ONLY the new paragraph repairs layout without
changing any mathematical claim. Final source rendering follows.


The second source lead reduces the overflow to 2.09pt but is still excluded;
its source/PDF/log remain retained. Only the new lead and its grammar are
corrected for the next render; mathematical claims remain identical.


Final source rendering passes four stable runs/71 pages with no overflow,
undefined/rerun request or orphan tail. All eleven current selected pages
are accepted: ten byte-identical to earlier ACTUAL views and changed page
70 newly inspected after the final lead/grammar repair. Generic invariance
is intact below the new paragraph; bibliography and contents are byte-exact
to prior actual views. The current four-path proposal is hash-pinned;
actual-main full/library/book/strict acceptance follows.


Final peer refresh4550 ACCEPTS all four current paths. Actual-main full
library/book pass 58.01s/8.00s, minimum available 36.63GiB/full-family RSS
8.40GiB, no memory stop. The strict 61-check family passes 78.02s, minimum
available 38.62GiB/RSS 2.91GiB. All 53 earlier fixture inputs remain
byte-exact, every old scoped TYPE/RAW/ATTR/DOC/AX/proof/deny-list record
stays exact. ONLY the named finite-fibre theorem is permitted as an extra
in the six old combined curve/scale metadata scopes. The new seven-record
audit and five actual private consumer examples match the accepted
baselines; full constructed consumer has nine consumed private helpers.
Mathematics/actual behaviors retain standard lint/default kernel, and the
historical diagnostic genres remain unchanged. All 707 historical warning
replay headers are exact to the prior full run; touched sources are clean.

All 255-source placeholder/project-axiom hygiene, 101 HTML paths/new and
prior docstrings, four stable source runs/71 pages and eleven current
visual gates pass: ten exact prior ACTUAL views, changed70 newly inspected.
Whole root and all 253 other mathematical module/Main sources stay exact.
Source whole recovery permits ONE added concordance paragraph; all 49
active statements/provenance, 44 proofs/listings/literals and frozen117
stay exact. Entire old CONT prefix remains exact. These actual gates precede
the required final library/book pair and guarded four-path stage/commit/push.
Only finite equal-ideal fibres are a new public theorem. Zero L-coefficient
translations at every equal-color pair in the constructed family are
private derived checks; pigeonhole selection, commutators, common centers,
linearity, ambient fresh-input existence/enlargement/descent, extraction and
all guarded/unconditional completeness remain open.


## B2 actual affine-locus commutation and privately selected family centers

Pinned to clean published 11e185c, whose exact CI37738517910 is fully green
at every library/book/deployment job and step; all nine owned issue-body
references are synchronized. Claude's SOURCE-ONLY GO4556 freezes a 211-line
new focused AffineLocusCommutation module. All ten project/toolchain/private
inputs, two Mathlib API files and six immutable draft SHA1 values are checked.
The FIRST actual standard-Mathlib-lint/default-kernel check passes unchanged
2.00s warning-free, minimum available 39.17GiB. No production proof/option
repair. ONE public theorem and FOUR consumed private helpers, no generated
declarations; the only import is the existing MultiplierPrimeCurve.
The three private characteristic-free power/orbit/conjugation proofs are
byte-exact copies of the accepted B1 consumer; its last actual zero-translation
example becomes the fourth private bridge. The scoped five-record metadata
audit passes 4.00s warning-free, minimum available 38.86GiB/RSS 2.66GiB,
standard Lean axioms only. Historical diagnostic genre remains unchanged.

For two concrete coefficient-L affine maps preserving the SAME pair ideal,
x algebraic over L(m), lambda transcendental over ORIGINAL k and rho != 0,
the public theorem proves lambda*(rho-1)*nu = rho*(lambda-1)*omega in L.
Three existing polynomial-image transfers produce the actual preserving
vertical translation; no action, commutator or stability oracle is supplied.
The private finite-fibre/conjugation/orbit bridge forces that translation
to vanish in every characteristic. This is a genuine commutation balance;
with both multipliers != 1 it gives equal fixed centers.

Root's genuine PRIVATE source-data consumer derives coefficient membership
from original-a cocycles, both actual preserving maps from shared affine
values and same-color pair ideals, and lambda transcendence from sequential
output freshness. It concludes (b_i-b_j)/(a_j-a_i)=(b_i-b_r)/(a_r-a_i):
the three relocated affine lines are concurrent. Its first private zero-index
projection failure is retained/excluded; an explicit coordinate change ONLY
repairs the fixture. The actual second check passes 2.00s warning-free,
minimum available 39.18GiB, standard lint/default kernel. Claude4567 ACCEPTS
its faithful, characteristic-free, non-vacuous statement and mathematics.

The private Mathlib pigeonhole bridge selects a color triple at size 2D+1,
with its least index i as the common base and i<j,i<r,j!=r. The first exit0
has an unused DecidableEq typeclass warning and is retained/excluded;
removing that redundant binder leaves its existing classical proof intact.
The second actual standard/default check passes 2.00s warning-free, minimum
available 39.18GiB. Claude4562 ACCEPTS its mathematics. An early peer message
wrongly called the first exit0 warning-free; immediate correction4559 and
verified second-only acceptance4560 preserve the truthful record.

The combined genuine PRIVATE 377-line consumer fixes ONE original prime
F and its ORIGINAL span before ALL supplied fresh ambient INPUT choices.
Its family size is 2*totalDegree F+1. It constructs the literal relocations
and derives OUTPUT freshness, shared values, original-a cocycles and colors
bounded by THAT original degree over ONE common relatively closed final L.
The Mathlib selector gives an ACTUAL equal-color triple; actual scale/curve
producers give the needed pair algebraicity over L, and both preserving maps,
ratio transcendence, commutation balance and the common center are derived.
There is no literal-joint-ideal, output-freshness, equal-color, action or
center oracle. The separate delta outside acl(a) input stays explicit.
ONE actual example consumes eight private fixture helpers. Its first exit0
long renamed-header warning is retained/excluded; wrapping-only repair
passes 6.00s warning-free, minimum available 38.70GiB/RSS 2.78GiB.
Claude4571 ACCEPTS the full consumer: one selected triple per supplied input
family, not all triples. The supplied family may not exist at small
transcendence degree; ambient existence/enlargement/descent remains open.
All production proof bytes stay exact.

Only the concrete commutation balance is a new public result; selected
triples and common centers are actual PRIVATE compositions. Four-point/C4
linearity, ambient input existence/enlargement/descent, coordinate extraction
and all guarded/unconditional completeness remain open. Original #11 and
frozen117 stay independent obligations; no arbitrary-curve action is claimed.

This FIVE-path proposal adds the focused mathematical module and one root
import, one Book docstring/account and import, ONE source concordance
paragraph, and this append-only record. All 254 prior mathematical module/
Main sources remain byte-exact; root differs ONLY by the one new import.
All 49 active source statements/provenance and 44 proofs/listings/literals
remain exact. Renewed peer five-path review, private canonical book/source/
current visuals, actual-main library/book and strict regressions precede
guarded commit/push.


Claude's exact five-path review4574 ACCEPTS. The private mathematical/root/
canonical Verso book chain passes 26.01s warning-free, minimum available
38.04GiB/RSS 4.41GiB, standard mathematical lint/default kernel and canonical
book genre. Source FIRST rendering passes four stable runs/71 pages with
no overflow, undefined/rerun request or orphan tail. All eleven current
selected pages are accepted: ten byte-identical to prior ACTUAL views and
changed70 newly inspected. Both the new balance account and whole generic
invariance account fit intact on 70; bibliography and contents remain exact.
Current five-path hashes are pinned; actual-main gates follow.


Final peer refresh4577 ACCEPTS all five current paths. Actual-main full
library/book pass 58.01s/8.00s, minimum available 36.56GiB/full-family RSS
7.50GiB, no memory stop. The strict 67-check family passes 88.02s, minimum
available 37.69GiB/RSS 2.91GiB. All 61 earlier fixture inputs remain byte-exact;
every old scoped TYPE/RAW/ATTR/DOC/AX/proof/deny-list record stays exact,
with NO old-scope addition. The new five-record audit and three genuine
actual private examples match the accepted baselines. The full constructed
consumer has eight consumed private helpers. Math/behaviors retain standard
lint/default kernel, and diagnostic genres stay unchanged. All 707 historical
warning headers are exact to the prior full run; touched sources are clean.

All 256-source placeholder/project-axiom hygiene, 101 HTML paths/new and prior
docstrings, four stable source runs/71 pages and eleven current visual gates
pass: ten exact prior ACTUAL views, changed page 70 newly inspected. All 254
prior mathematical module/Main sources stay exact; root differs ONLY by one
new import. Source whole recovery permits ONE added concordance paragraph;
all 49 active statements/provenance, 44 proofs/listings/literals and frozen117
stay exact. Entire old CONT prefix is exact. These actual gates precede the
required final library/book pair and guarded five-path stage/commit/push.
Only concrete commutation balance is public. The selected common-center
triple for each supplied fresh input family is a PRIVATE derived composition;
ambient existence/enlargement/descent, four-point/C4 linearity, extraction
and all guarded/unconditional completeness remain open.


## B3 pairwise relocation cocycles and private original-base algebraic centers

Pinned to clean published 21683e5, exact CI37741230346 FULLGREEN at every
library/book/deployment job and step; all ten owned body references are
synchronized. The initial source-only GO4587 had a WRONG import-closure
premise: Family's existing projection API was absent from AffineRelocation.
Claude4590 stopped BEFORE any draft or main change; #27 records the error
and concrete correction BEFORE revisedGO4591. Two existing imports, Family
and DifferenceCocycle, replace the false one-import scope. No projection
API is duplicated. This is an implementation-scope correction; the audited
mathematical target is unchanged and sufficient/non-vacuous.

Claude's immutable uncompiled freeze4594 appends ONE public theorem:
old 264 -> 332 lines, two imports plus 66-line append. All eight inputs,
two Mathlib API files and five frozen draft SHA1 values/modes are checked;
old header, whole body/proofs/module docs and closes remain byte-exact after
removing ONLY the two imports/new append. FIRST actual standard-Mathlib-lint/
default-kernel check passes UNCHANGED 2.00s warning-free, minimum available
39.12GiB. ONE new public/no helpers/generated declarations. The old two
scoped TYPE/RAW/ATTR/DOC/AX/proof/deny-list records stay exact, only the new
third public record added, standard Lean axioms. Metadata passes 4.00 s,
minimum available 38.79 GiB/RSS 2.42 GiB, warning-free; diagnostic genre unchanged.

The public pairwise cocycle uses original AI(a,b,x), explicit p/δ memberships
and nonmemberships, the FIRST actual fixed-five joint ideal, the actual
p/δ/value outputs for BOTH tuples, and later aj fresh over original a,b,x
plus ai. It derives independence and p/δ nonmemberships at the first tuple
by existing Family/FunctionField transport. Exchange places its bi/xi in
the original-data-plus-ai closure, deriving the later freshness needed by
published L1a. Thus bi-bj lies in acl(ai,aj), removing the original a from
the difference closure. No second joint ideal, separate first freshness or
delta membership in acl(p,y) is needed by this theorem. Those raw outputs
are derived from the actual relocation producer in the genuine consumer.

Root's private constant-center bridge passes FIRST 2.00 s unchanged, standard
lint/default kernel/EMPTY log, minimum available 39.15 GiB. Given pairwise
cocycles and actual concurrence, field algebra makes the THIRD pair share
the same center; no second B2 call at base j or inverse-ratio transcendence
is needed. Three uses of the 8.9a closure brick put the center in racl k ∅,
hence algebraic over ORIGINAL k, in every characteristic. The bridge's
pairwise inputs were initially explicit, and Claude4598 ACCEPTS its scope,
non-vacuity and mathematics; they are DERIVED in the full consumer below.

The genuine PRIVATE 490-line consumer fixes ONE original prime F/span before
ALL supplied fresh INPUT families of size 2*totalDegree F+1. It constructs
the relocations, derives OUTPUT freshness and their actual p/δ/value outputs,
original-a cocycles, larger-base pair algebraicity and degree-bounded colors
over ONE common final L. Actual selection gives one same-color triple;
actual maps and B2 give concurrence. B3 derives ALL ordered pairwise
cocycles from the actual outputs, and j<r OR r<j cases order the three closure
intersections correctly. The selected center is therefore algebraic over
ORIGINAL k; there is no pairwise-cocycle or constant-center oracle.
ONE actual example consumes ten private fixture helpers. Its FIRST 6.00 s
standard/default check is UNCHANGED warning-free, minimum available 38.59 GiB/
RSS 2.79 GiB. No proof, fixture or checking-option repair. Claude4601 ACCEPTS
the full statement, fixed-F quantifier order and both-order composition.

Only pairwise relocation cocycles are a new public result. One selected
triple's original-base algebraic center per supplied input family is an
actual PRIVATE composition. This does not yet put the center in k or
transfer an affine shift back along a k-joint ideal: that separate consumer
needs k algebraically closed, as the guarded blueprint assumes. P/Q
normalization/compatibility, remaining meets, ambient input existence/
enlargement/descent, the action presentation and all guarded/unconditional
completeness remain open. Original #11 and frozen117 remain obligations.

This FOUR-path proposal changes the existing AffineRelocation module's
two imports/appended theorem/real Status, adds one Book docstring/account,
ONE source concordance paragraph and this append-only record. Whole root
and all 254 OTHER mathematical module/Main sources remain exact; 49 active
source statements/provenance and 44 proof/listings/literals remain exact.
Renewed peer four-path review, private canonical book/source/current visual
gates, actual-main library/book and strict regressions precede commit/push.

Private canonical AffineRelocation/Book compilation passes 24.01 s, minimum
available 38.23 GiB/RSS 4.42 GiB, with no warning/error. Four source passes
are stable, 71 pages, no overflow/undefined/rerun. All eleven selected
current pages are accepted: ten byte-identical earlier ACTUAL views plus
changed page 70 newly ACTUALLY inspected, with no orphan tail. No source
layout repair. Claude4605 accepts all four paths; optional spacing nits
in this new append alone are corrected. Actual-main gates remain pending.

Actual-main gates pass after exact four-path/hash application and peer4609
refresh acceptance: full library 58.02 s (minimum available 36.63 GiB/RSS
7.81 GiB), book 8.00 s, all 72 strict scoped checks 96.02 s (minimum
available 38.59 GiB/RSS 2.90 GiB), default kernel/standard lint for math
and actual behaviors. All 67 earlier fixture inputs and every old scoped
TYPE/RAW/ATTR/DOC/AX/proof/deny-list record stay exact. Only the named B3
record is added in the six older AffineRelocation metadata scopes; new
three-record scope matches accepted private results. Two actual private
examples and the ten consumed full-family helpers are warning-free.

256-source placeholder/project-axiom hygiene is clear. All 101 HTML paths
and prior docs remain; new B3 docstring and accurate private original-base
center account are visible. Whole root and all 254 OTHER math/Main sources,
toolchain/dependencies, all 49 active source statements and original
provenance, all 44 proofs/listings/literals, frozen117 and historical CONT
prefix are exact. The 707 historical full/book warning HEADER MULTISETS
are byte-exact; parallel output ordering is not constrained. Touched math
and all actual behaviors have no warnings. An initial order-sensitive log
comparison was rejected (707/707 identical multiset, no additions/removals)
and corrected to a multiset comparison; no source or checking-option change.
Final required full-library/book checks follow this append before guarded
four-path commit/push. P/Q, ambient inputs/descent, actions/extraction and
all completeness obligations remain open; the durable goal continues.


## P1 concurrent-P closure and private original-P shift transfer

Pinned to clean published a2b76f0, exact CI37744568032 FULLGREEN at every
library/book/deployment job and step. All five owned reports/bodies and
eleven current body-owner references are synchronized. Claude4612 audits
the minimal closure target and actual k-valued shift transfer. Source-only
GO4615 and the concrete #27 scope precede every draft; ownership remains
peer source-only under that GO and root sole compiler/main integrator.

Claude's immutable uncompiled freeze4617 appends ONE public theorem to
DifferenceCocycle: 126 -> 181 lines, 55-line append, 45-line proof, no new
imports/helpers/options. All thirteen project inputs, the pinned genuine
490-line consumer, two allowed Mathlib API hashes and five draft hashes/
read-only modes are verified. Old whole 122-line prefix and four closes
are byte-exact. FIRST standard-Mathlib-lint/default-kernel production check
passes UNCHANGED 2.00 s, EMPTY log, minimum available 39.06 GiB. Existing
private exchange helper is reused; no new generated declaration.

Scoped metadata passes 4.00 s, minimum available 38.71 GiB/RSS 2.41 GiB.
All three old SIG/proof records and the one old PUBLIC AX record remain
exact, plus the new public record; the four-record scope has two old
private helpers and two public theorems, standard Lean axioms only.
TYPE/RAW/ATTR/DOC/AX/proof/deny-list comparisons are scoped. An initial
metadata harness incorrectly expected three PUBLIC AX records; its failure
is retained/excluded. The unchanged AX fixture intentionally exposes only
public declarations (one old, two new). ONLY the expected AX count was
repaired; all Lean diagnostic fixture bytes/proofs/checking options stay
exact. A generic printed old3 label was subsequently corrected to the
actual count without another compiler run; acceptance fields record the
precise three SIG/proof and one public AX counts.

The public closure theorem has explicit original-base algebraic t,
p memberships at the two pairs, p outside acl(ai), later aj outside
acl(ai,p), and actual shifted concurrence. Exchange shows the common
shifted intercept w is outside acl(ai,aj); then aj is outside acl(ai,w).
The independent-variable intersection puts p in acl(w), and exchange over
the empty set gives w in acl(p). It is characteristic-free, with no ACF or
literal-joint-ideal hypothesis. Non-vacuity is the linear t=0, bi=bj=p model.
The actual full-family chain below derives every one of those raw inputs.

Root's PRIVATE 72-line consumer combines the public closure theorem with
the actual k-polynomial image of a fixed-five joint ideal. With a specified
constant in k, it derives relocated-P closure equality from explicit raw
membership/freshness/concurrence, then transports BOTH closure directions
to original b+(a-1)t. No original-P or shifted-P normal-form oracle.
ONE actual example and one consumed private transfer helper pass FIRST
2.00 s unchanged, standard lint/default kernel/EMPTY log, minimum available
39.03 GiB.

The genuine PRIVATE 575-line consumer extends accepted B3 full490,
retaining one original prime F/span BEFORE ALL supplied fresh INPUT
families of size 2*totalDegree F+1. It constructs relocations, derives OUTPUT
freshness/literal joint ideals/p and delta memberships/values/common-field
colors, selects a same-color triple, derives all pairwise cocycles and
concurrence, and the original-base algebraic center in BOTH later-index
orders. Actual joint-ideal transport gives p outside acl(ai); later output
freshness plus original p membership gives aj outside acl(ai,p). Field
algebra derives shifted concurrence. The public theorem gives relocated-P
interalgebraicity. Explicit [IsAlgClosed k] turns the derived center into
a constant in k using existing BaseChange API; actual k-polynomial-image/
joint-ideal transfer gives original P interalgebraic with b+(a-1)t.
No constant-center/cocycle/shifted-P/original-P oracle is supplied. Ambient
algebraic closedness and separate delta outside acl(a) remain explicit.
ONE actual example consumes ELEVEN private helpers. Its FIRST compiler
check passes 6.00 s, standard lint/default kernel/EMPTY log, minimum
available 38.51 GiB/RSS 2.87 GiB. A single 105-character new example header
was wrapped during uncompiled source preflight; no failed Lean check or
proof/fixture/option repair. Claude4629 ACCEPTS both private consumers,
signed shift, quantifier order, non-vacuity and a four-path checkpoint.

Only the conditional concurrent-P closure lemma is a new public result.
The original-P k-valued shift transfer per supplied fresh input family
under k/ambient ACF is an actual PRIVATE composition. Q normalization,
the combined generator presentation, remaining meets, ambient input
existence/enlargement/descent, action presentation, linearity, extraction
and guarded/unconditional completeness remain open. The independent #11
and frozen117 obligations are untouched. A uniqueness remark and any
claim about using one common shift are research, not additional theorems.

This FOUR-path proposal updates the existing DifferenceCocycle theorem/
real Status, ONE Book docstring/account, ONE source concordance paragraph
and append-only CONT. Whole root and all 254 OTHER math/Main sources,
toolchain/dependencies, 49 active source statements/original provenance,
44 proofs/listings/literals and frozen117 stay exact. Private canonical
Book/source/current-visual gates, peer four-path review, actual library/
book and 77 strict regressions precede final full/book and commit/push.


Private canonical DifferenceCocycle/Book compilation passes 24.01 s,
minimum available 37.96 GiB/RSS 4.43 GiB, no warning/error. FIRST source
render passes all four stable runs: 72 pages, no overflow/undefined/rerun.
All twelve current selected views are accepted: eight byte-identical prior
ACTUAL views plus pages 3,70,71,72 newly ACTUALLY inspected. Page 71 has a
complete paragraph, not an orphan tail; bibliography/contents are correct.
No source layout repair. Claude4634 ACCEPTS all four exact paths.

Research-only Claude4632 confirms that independent k-translations of
x,y,z preserve the chosen generator/table presentation when both P/Q
normalizations are known; a common shift is not required by the corrected
statement. H/G/Q coupled normalization still needs proof; the I-meet alone
does not force H=a/b (the proposed h=ab alternative is a warning about that
inference, not a new refutation theorem). No common-shift, uniqueness or
H/G/Q theorem is added, and no guard sufficiency claim is made. Actual-main
full/book and 77 strict checks are pending.


Actual-main gates pass after guarded exact-four-path application and
Claude4638 refresh acceptance: full library 62.02 s (minimum available
35.68 GiB/RSS 9.67 GiB), book 8.00 s, all 77 strict scoped checks
104.02 s (minimum available 38.47 GiB/RSS 2.91 GiB). All 72 earlier
fixture inputs and every old scoped TYPE/RAW/ATTR/DOC/AX/proof/deny-list
record stay exact. Only the named P1 record is added in the three older
DifferenceCocycle metadata scopes; new four-record scope matches accepted
private results (SIG/proofs three old plus new, PUBLIC AX one old plus new).
Both new actual private consumers and all old actual behaviors are
warning-free under standard Mathlib lint/default kernel; historical
diagnostic genres/options are unchanged.

256-source hygiene finds no placeholder/project axiom. All 101 HTML paths
and earlier docs remain, with accurate P1 docstring and private original-P
account visible. Whole root/all 254 OTHER mathematical module/Main
sources/toolchain/dependencies, all 49 active source statements and
original provenance, all 44 proofs/listings/literals, frozen117 and whole
historical CONT prefix are exact. Four source runs are stable at 72 pages;
all twelve current selected views are accepted (eight exact prior ACTUAL
views, changed 3,70,71,72 newly ACTUALLY viewed). No source layout repair.
The 707 historical full/book warning-header MULTISETS remain byte-exact;
touched mathematics and all actual behaviors have no warnings.

Tracking-body cleanup is prepared for publication after push: retire ONLY
the repeated owned Current-checkpoint lead paragraphs (11 in #27,9 in #6),
keep every existing work-item checklist byte and historical progress
comment, add the concrete P1 status, and synchronize all twelve body-owner
references after live-body guards. No issue closure or broader L2/G3/G4/G5
completion is inferred. Final required full-library/book checks follow
this factual append before guarded four-path commit/push. Original-P
composition stays PRIVATE under explicit k/ambient ACF and supplied INPUT
families; Q/combined generator presentation/ambient/actions/extraction/
completeness stay open. Durable goal remains active.


## P2 conditional shifted D/F/R meets and private constructed-family rows

Pinned to clean published 74fdcdd, exact CI37748038718 FULLGREEN at every
library/book/deployment job and step. All twelve owned tracking-body
references are synchronized; duplicate historical Current leads were
retired without altering checked work items or earlier progress comments.

Claude's SOURCE-ONLY GO4658 and the concrete #27 scope precede the first
new ShiftedAffineMeets draft. The first draft disclosed an extra read of
WitnessTable beyond its 22 input pins. Root verified its tracked hash and
MeetEquations import closure, recorded 23 inputs and posted the correction
BEFORE the first Lean check. A premature peer notification after a failed
payload preparation was explicitly corrected in4666; actual posted
correction6055989373 and verification precede any compiler. No unreported
production change or input expansion is accepted.

The immutable FIRST 213-line draft failed default/standard checking after
8.00s with a 200000-heartbeat whnf timeout in the combined declaration.
SECOND 213 lines added a consumed private opaque bundle of the THREE
existing soundness meets; it still failed 8.00 s in the combined declaration.
Both unchanged source trees and actual failure logs/metrics are retained
and excluded from acceptance. A deliberately INVALID proof of the unchanged
combined TYPE failed promptly 2.00 s with the expected type mismatch; that
diagnostic is retained and excluded, not a proved mathematical result.
No resource limit, checking option or public statement was changed.

After concrete #27 report6056297711, source-only DEFAULT repair GO4682
freezes THIRD 4686: 257 lines, EXACT same two imports and two public TYPEs.
The whole SECOND 112-line prefix (first public proof, element-meet brick
and table-meet bundle) and combined public docstring/TYPE stay exact.
Three consumed private transport boundaries use atom coordinates and
explicit linking equalities; a shared pair-closure helper is consumed
six times. This avoids compound closure/coercion metavariables within
one declaration's budget. All 23 project pins, six actually read extra
pins, two allowed Mathlib API files and five immutable artifact hashes/
read-only modes are verified. FIRST/SECOND trees remain exact.
The actual THIRD standard-Mathlib-lint/default-kernel check passes
UNCHANGED 2.00 s, EMPTY log, minimum available 38.94 GiB. No option/budget
repair. Scoped metadata passes FIRST 4.00 s, minimum available 38.62 GiB/
RSS 2.41 GiB: eight exact named SIG/proof records, two PUBLIC AX records,
two public and six consumed private theorems, zero generated records
in this scope, standard Lean axioms only. Diagnostic genres are unchanged.

The first public theorem proves independence of the triangular shifted
table from ORIGINAL AI5 and a constant in k by explicit forward/inverse
closure memberships. The second has explicit original AI5, constant in k,
P closure equality, raw delta/f/r incidences and non-memberships. It
derives acl(delta)=acl(a(x-kappa)), acl(f)=acl(ac(x-kappa)) and
acl(r)=acl(bc+d+ac*kappa) from the EXISTING table soundness meets and
exchange. The last entry is the starred intercept modulo a base constant.
Neither public theorem needs algebraic closedness. The shifted linear
table provides a non-vacuous model. E/G/H/I/Q and compatibility with their
presentation are not supplied as normalized inputs or claimed outputs.

Root's actual PRIVATE ZeroOriginMeetConsumer 27 has one example, no helper:
p=b and kappa=0 derive the P hypothesis, arbitrary raw delta/f/r meet
memberships/non-memberships give all three original rows. No D/F/R
normal-form hypothesis or ACF. FIRST standard/default check passes
UNCHANGED 2.00 s EMPTY log, minimum available 38.94 GiB.

The genuine PRIVATE ConstructedFamilyShiftedMeets 598 extends accepted
P1 full575. All ELEVEN consumed private helper blocks remain BYTE-EXACT.
Original AI5 and raw ORIGINAL R incidences are supplied; the Fin4-to-Fin5
projection is DERIVED. ONE original prime F/span precedes EVERY supplied
fresh INPUT family of size 2*totalDegree F+1. Constructed relocations give
OUTPUT freshness, literal joint ideals, raw memberships/values and common-L
colors; selection gives an actual triple. All pairwise cocycles,
concurrence, original-base algebraic center in BOTH later-index orders,
constant in k and ACTUAL k-polynomial-image/joint original-P transfer are
DERIVED as in P1. THEN both new public theorems give starred independence
and the D/F/R closure rows. No P/D/F/R normal-form or output-freshness
oracle. Explicit k/ambient ACF, supplied fresh INPUTs and separate delta
outside acl(a) remain. FIRST standard/default check passes UNCHANGED
8.00s EMPTY log, minimum available 38.41 GiB/RSS 2.87 GiB. One actual example,
eleven consumed helpers; supplied input existence may fail at small
transcendence degree and is still an obligation.

Only the two conditional table-shift/meet statements are public; the
actual full-family chain remains PRIVATE. E/G/H/I/Q, the combined
generator presentation, ambient input existence/enlargement/descent,
the action presentation, linearity, extraction and guarded/unconditional
completeness remain open. Original #11 and frozen117 are untouched.
Independent origin shifts require no common-kappa/uniqueness theorem.

This FIVE-path proposal adds the focused module and ONE root import,
ONE Book account with TWO public docstrings and ONE import, ONE source
concordance paragraph, and append-only CONT. All 255 prior math/Main
sources, dependency pins, 49 active source statements/original provenance,
44 proofs/listings/literals and frozen117 remain exact. Private source
rendering already passes FIRST four stable 72-page runs with no layout
repair; all 12 current selected views pass (eleven prior ACTUAL byte-exact,
new 71 ACTUALLY inspected). Peer consumer/five-path review, private canonical
Book, actual full library/book, strict 82 checks and final full/book gates
precede commit/push. Prior tracking checklists remain exact.


Actual P2 acceptance: Claude4692 ACCEPTS both private consumers; 4695
ACCEPTS all five concrete paths, with optional spacing nits fixed only in
the new CONT append. Guarded integration leaves every prior source exact.
Actual full lake build passes 62.01 s, minimum available 36.28 GiB/RSS
8.35 GiB; lake exe book passes 10.00 s, minimum available 38.20 GiB/RSS
1.52 GiB. Strict 82 actual-main checks pass 114.03 s, minimum available
38.26 GiB/RSS 2.91 GiB. All 77 older fixture bytes and every old scoped
TYPE/RAW/ATTR/DOC/AX/proof/deny-list record stay exact, with NO old-scope
additions. New eight-record scopes and both actual consumers match the
accepted private results; math and actual behaviors use standard lint/
default kernel, and historical diagnostic fixture genres stay exact.

Hygiene passes 257 files without proof placeholders or project axioms.
All 101 HTML paths remain; both new public docstrings are visible.
All 255 prior math/Main sources, root except its ONE new import, dependency
pins, source 49 active statements/original provenance/44 proofs/listings/
literals and frozen117 are byte-exact. FOUR stable 72-page source runs and
all 12 current selected views pass (eleven prior ACTUAL byte-exact ; 71 newly
ACTUALLY viewed), no layout repair. Historical full/book warning-line
multisets stay exact (707 Lean-source warning headers plus four other
cached warning lines); touched mathematics and actual examples are
warning-free. Scoped checks establish no whole-library axiom certificate.
Final full build/book after this append are required before commit/push.
The durable goal continues; no additional completeness claim.


## P3a reusable supplied-input point producer and private nested P/Q chain

Pinned to clean published 65b9a6a, exact CI37755299430 FULLGREEN at every
library/book/deployment job and step. All thirteen owned tracking-body
references are synchronized. Concrete #27 research scope and corrected
reciprocal plan precede SOURCE-ONLY GO4715. Claude4709/4711 audits the
inverse substitution (c,d,b,(ac)^-1,q,g,h^-1): it reuses the existing
negative-covariance pipeline, with no positive-covariance/rational-image
API or new curve/scale/relocation lemma. Root remains sole compiler/main
integrator; the peer is source-only under the GO and otherwise read-only.

Immutable uncompiled freeze4718 has 599 lines, exactly the SIX old575
imports, ALL ELEVEN byte-copied consumed private helper blocks, and ONE
public racl_normalized_P_of_supplied_fresh_inputs. Its proof is the old575
actual example body, with only the final tuple narrowed to the derived
constant and original-P closure. All 21 project input pins, the old575
copy source and explicitly allowed old598 consumer, and five artifact
hashes/read-only modes are verified. No Mathlib source was read for this
copy. Root's first input preflight initially omitted the explicitly
allowed598 path from its checker allowlist; that failed before ANY copy or
Lean check. Only the checker allowlist was corrected to the actual GO.
No peer source-read violation or production proof/options repair occurred.

FIRST standard-Mathlib-lint/default-kernel producer passes UNCHANGED
6.00 s, EMPTY log, minimum available 38.38 GiB/RSS 2.87 GiB.
FIRST scoped metadata passes 4.00 s, minimum available 38.63 GiB/
RSS 2.65 GiB: twelve exact named SIG/proof records, ONE PUBLIC AX record,
one public and eleven consumed private theorems, zero generated records
in this scope, standard Lean axioms only. Diagnostic genres/options stay
exact. The twelve/one counts were fixed before the first metadata check.
This is a scoped audit, not a whole-library axiom certificate.

The public producer has explicit k/ambient algebraic closedness,
AI(a,b,x,c), raw p/delta/f incidences and non-memberships. It fixes the
ORIGINAL prime F/span BEFORE ALL supplied fresh INPUT families of size
2*totalDegree F+1. Every relocation output, output freshness, literal joint
ideal, color, selected triple, pairwise cocycle, concurrence, original-base
algebraic center, k-valued constant and original-P joint transfer is
DERIVED internally. No output-freshness or P normal-form oracle.

Root's actual PRIVATE ReciprocalQNormalization 96 has ONE example and
TWO consumed private helpers. AI(c,d,b,(ac)^-1) is DERIVED from AI5 and
closed-field generation; inverse memberships/non-memberships and
c*(ac)^-1=a^-1 are DERIVED. Raw q in acl(c,d), g in acl(c,b) intersection
acl(q,bc+d), h in acl(ac,g) intersection acl(a,b), with explicit q/g
outside acl(c) and h outside acl(a), feed the SAME public producer.
The original Q-side prime locus (a^-1,b) over k(h^-1) precedes ALL second
fresh INPUT families. It derives q interalgebraic with d+(c-1)*eta,
eta in k. FIRST standard/default check passes UNCHANGED 2.00 s,
EMPTY log, minimum available 38.96 GiB. Claude4727 ACCEPTS.

The genuine PRIVATE TwoFamilyPQNormalization 215 has ONE example and
SIX consumed private helpers. Original AI5 projects to P AI4; the first
producer derives kappa/P, then P2 derives D/F/R and starred independence.
Let B=b+(a-1)*kappa, D=d+(c-1)*kappa. Actual pair-closure equalities
transport q into acl(c,D) and h into acl(a,B); the DERIVED P/R rows
transport raw g incidences into acl(B,c) intersection acl(q,Bc+D).
The R expression differs from Bc+D by the base constant kappa.
THEN the inverse Q consumer at this starred table fixes its original
prime curve before ALL second supplied INPUT families and derives eta/Q.
The nested order is original FP, every P INPUT family, kappa, original
FQ, every Q INPUT family, eta. No P/Q/H normal-form or output-freshness
oracle. Constants may depend on supplied families; no common-shift or
uniqueness claim is needed or added.

FIRST two-family check failed 2.00 s at an untyped singleton-subset
membership alignment in the PRIVATE affine-pair shift helper. Its exact
source/log/metrics are retained and excluded. ONLY an explicit typed
membership have is inserted before singleton_subset; TYPEs, producer,
inverse96 and all checking/resource options stay exact. SECOND check
passes 2.00 s, EMPTY log, minimum available 38.96 GiB. Claude4734 ACCEPTS
the actual nested chain and a five-path checkpoint. The canonical linear
model is non-vacuous with both supplied INPUT families.

The q/g/h non-memberships stay EXPLICIT raw guard consequences; deriving
them from an ACTUAL Psi witness remains work. ONLY the reusable
conditional P producer is a new public theorem. Reciprocal Q and the
nested P/D/F/R/Q chain are PRIVATE under explicit k/ambient ACF and
supplied inputs. Both input-existence/enlargement/descent obligations
(which may fail at small transcendence degree), remaining E/G/H/I rows,
combined generator presentation, initial action chart, actions, linearity,
extraction, guarded/unconditional completeness, #11 and frozen117 remain.

The exact FIVE paths are the focused module/real Status, ONE root import,
ONE Book account/docstring/import, ONE source concordance paragraph and
append-only CONT. All 256 prior math/Main sources, toolchain/dependencies,
49 active source statements/original provenance/44 proofs/listings/
literals and frozen117 stay exact. Peer five-path review, private
canonical Book/source/current visual, actual full build/book, 87 strict
scoped checks and final full/book precede commit/push. The durable goal
continues; broader L2/G3/G4/G5 remain open.


Actual P3a acceptance: Claude4740 ACCEPTS all five concrete paths; 4727
and 4734 ACCEPT the reciprocal 96 and nested 215 actual private consumers.
Guarded integration leaves all 256 prior math/Main sources exact.
Actual full lake build passes 66.02 s, minimum available 35.63 GiB/
RSS 10.85 GiB; lake exe book passes 10.00 s, minimum available
38.39 GiB/RSS 1.58 GiB. All 87 strict actual-main checks pass 120.03 s,
minimum available 38.55 GiB/RSS 2.91 GiB. All 82 older fixture bytes and
EVERY old scoped TYPE/RAW/ATTR/DOC/AX/proof/deny-list record stay exact,
with NO old-scope additions. The new twelve-record scope/one PUBLIC AX
and both actual examples match the accepted private records. Mathematics
and actual behaviors use standard Mathlib lint/default kernel; historical
diagnostic fixture genres/options remain exact.

Hygiene passes 258 files without proof placeholders or project axioms;
all 101 HTML paths remain and the new public docstring is visible.
Root changes only by ONE import. All prior 256 math/Main sources,
toolchain/dependencies, source 49 active statements/original provenance/
44 proofs/listings/literals and frozen117 stay exact. FOUR stable
72-page source runs and all twelve current selected views pass
(eleven prior ACTUAL byte-exact, changed 71 newly ACTUALLY inspected),
no layout repair. Historical full/book warning-line MULTISETS stay exact:
707 Lean-source warning headers plus four other cached warning lines.
Touched mathematics and all actual examples are warning-free.
Only the conditional supplied-input P producer is newly public; inverse
Q and nested P/D/F/R/Q stay PRIVATE. Actual guarded-Psi non-memberships,
remaining E/G/H/I, combined presentation, initial chart, both supplied
input existence/enlargement/descent obligations, actions, extraction,
all completeness, #11 and frozen117 stay open. Scoped checks give no
whole-library axiom certificate. Final full build/book AFTER this factual
append precede commit/push. The durable goal continues.


## P3b conditional remaining G/H/I/E meets and actual nested family consumer

Pinned to clean published 2f49a59, exact CI37761551954 FULLGREEN at every
library/book/deployment job and step; all five owned reports/bodies and
fourteen current tracking-body references reconciled. Claude4749 audits
the Q-origin shift, raw A-plane in H, meet order, signs and non-vacuity.
Concrete #27 scope6057695445 and exact public TYPEs precede SOURCE-ONLY
GO4758/ACK4759. Root remains sole compiler/main integrator.

Immutable freeze4765 has 295 lines, EXACT TWO imports, TWO public TYPEs
and SEVEN consumed private helpers: two byte-copied P2 element/pair bricks,
one variable-level soundness bundle, four typed-atom transports. No public
ACF hypothesis, definitions/aliases/instances/options/resource changes.
Both public TYPEs match the proposed instruction exactly after whitespace
normalization. All twelve project pins, allowed private215 and TYPE pins,
five artifact hashes and immutable modes are verified. Mathlib source
reads are truthfully NONE.

The peer disclosed extra reads of its OWN earlier freeze artifacts for
format conventions. Root asked4767 BEFORE copy/Lean, received4768 exact
paths/hashes and verified SIX opened formatting artifacts plus THREE
inherited NOTE summaries (not reopened while drafting). Reads were a
directory listing, first-five-line diff/copyright header, hash ledgers and
short ledger segments; the peer's nonmathematical read-boundary reminder
was also used. No extra project/Mathlib source or API was read. The scope
correction was posted6057865259 BEFORE ANY copy or first compiler; frozen
295/five artifacts remain unchanged. No hidden mathematical input expansion.

FIRST standard-Mathlib-lint/default-kernel production check passes
UNCHANGED 2.00 s, EMPTY log, minimum available 38.96 GiB. No production
proof, TYPE, fixture, checking option or budget repair. FIRST scoped
metadata passes 4.00 s, minimum available 38.69 GiB/RSS 2.42 GiB:
NINE exact named SIG/proof records, TWO PUBLIC AX records, two public/
seven private theorems, zero generated records IN THIS SCOPE, standard
Lean axioms only. The exact nine/two expectations precede the first
metadata check. Diagnostic genres/options stay unchanged. Both byte-copied
helper TYPE/RAW/ATTR/DOC/AX/proof records match P2 except the module column.
No whole-library axiom certificate is claimed.

The first public theorem preserves AI5 at (a,b-eta,c,d+(c-1)*eta,x).
The second explicitly assumes normalized P/Q/R and raw G/H/I/E incidences
and nonconstancy. Existing soundness meets on that shifted table yield
G=[(b-eta)c], H=[a/(b-eta)], I=[ax/(b-eta)], E=[c(ax+b-eta)].
G is derived first, H from G and its RAW A-plane, I from H; E uses its
own two joins. Every transport uses typed atom-coordinate memberships
with explicit linking equalities. Neither public theorem needs ACF.
The canonical model is non-vacuous for every base constant eta.

Root's actual PRIVATE TwoFamilyRemainingMeets 274 extends accepted215.
The whole namespace/variable block and all SIX old helper blocks remain
BYTE-EXACT. ONE new consumed pair_translate helper transports four raw
X/Y/Z incidences. The original FP/span precedes ALL supplied P INPUTs;
the SAME producer derives kappa/P, then P2 gives D/F/R and starred AI.
Raw Q/G/H incidences are transported via the DERIVED closures, and the
inverse producer fixes ORIGINAL FQ/span BEFORE ALL second Q INPUTs,
then derives eta/Q. Actual original raw I/E incidences and nonconstancy
are transported to the kappa-absorbed chart; BOTH new public theorems
derive final AI and G/H/I/E. No normalized-input or OUTPUT-freshness
oracle; explicit k/ambient ACF, both supplied INPUT families, strong
Q-producer non-memberships and raw I/E nonconstancy remain. FIRST check
passes UNCHANGED 2.00 s, EMPTY log, minimum available 39.01 GiB.

The actual PRIVATE ZeroOriginRemainingMeets 30 has ONE example/no helper:
arbitrary raw G/H/I/E representatives, canonical P=b/Q=d/R=bc+d, eta=0.
No ACF or remaining-row normal-form input. FIRST check passes UNCHANGED
2.00 s, EMPTY log, minimum available 38.99 GiB. Both actual consumers
have default kernel/standard Mathlib lint; no failed Lean check/repair.

Only the conditional origin-shift/four-meet statements are newly public;
the genuine full two-family chain stays PRIVATE. Initial action chart,
actual guarded-Psi input derivation, fresh INPUT existence/enlargement/
descent, combined generator presentation, actions, linearity, extraction
and guarded/unconditional completeness remain open. #11 and frozen117
are independent obligations. No uniqueness/common-shift theorem.

FIRST private source rendering passes four stable runs in 8.00 s at
73 pages without TeX warnings. Actual views show the old generic-formula
paragraph split after its heading/two lines on 71, with a short continuation
on 72. That initial layout is retained/excluded. ONE page break attached
ONLY to the newly added P3b concordance paragraph keeps both paragraphs
complete. No original source statement/proof or older paragraph byte is
changed. Second four-pass rendering/current visual acceptance follows.

Second four stable source runs pass 8.00 s at 73 pages after that ONE
new-paragraph page break. All THIRTEEN current views are accepted: nine
prior ACTUAL byte-exact plus changed 3,71,72,73 newly ACTUALLY inspected.
Both new and generic paragraphs are complete; contents/bibliography match.
Private canonical module/root/Book passes 28.01 s, minimum available
38.05 GiB/RSS 5.92 GiB, only CHECK/PASS lines. Claude4776 accepts both
actual consumers and 4780 the initial five paths. Updated source/CONT
layout/factual pins are sent for refresh before guarded integration.

Cross-reference follow-up: the untouched older P2/P3a module Status
lists still refer to their open actual guarded-Psi rows. P3b proves the
conditional rows under the explicit raw/normalization hypotheses; the
actual-Psi rows remain open. A later accurate pointer can reconcile those
older Status lists without changing their theorems; no seven-path scope
expansion is made here. Combined presentation is NOT yet a theorem.

The exact FIVE paths add this focused module/real Status, ONE root import,
ONE Book import/account/TWO public docstrings, ONE source concordance
paragraph, and append-only CONT. All 257 prior math/Main sources,
dependency pins, source49 active statements/original provenance/44 proofs/
listings/literals and frozen117 stay exact. Private canonical Book/source/
current visual, peer consumer/five-path review, actual full library/book,
92 strict scoped checks and final full/book precede commit/push.
The durable goal continues; broader L2/G3/G4/G5 remain open.


Actual P3b acceptance: Claude4776 ACCEPTS both actual consumers; 4780
accepts the initial five paths and 4784 the two source/CONT refresh pins.
Guarded integration leaves all 257 prior math/Main sources exact.
Actual full lake build passes 66.01 s, minimum available 37.32 GiB/
RSS 8.30 GiB; lake exe book passes 10.00 s, minimum available 39.11 GiB/
RSS 1.55 GiB. All 92 strict actual-main checks pass 126.03 s, minimum
available 39.18 GiB/RSS 2.86 GiB. All 87 older fixture bytes and EVERY old
scoped TYPE/RAW/ATTR/DOC/AX/proof/deny-list record stay exact with NO
old-scope additions. New nine-record scopes/two PUBLIC AX and both actual
consumers match accepted private results. Mathematics/actual behaviors use
standard Mathlib lint/default kernel; historical diagnostic genres/options
stay exact. Scoped records give no whole-library axiom certificate.

Hygiene passes 259 files without proof placeholders/project axioms.
All 101 HTML paths remain; both new public docstrings are visible.
Root changes only by ONE import. All 257 prior math/Main sources,
toolchain/dependencies, source 49 active statements/original provenance/
44 proofs/listings/literals and frozen117 stay byte-exact. SECOND four
stable 73-page source runs and all THIRTEEN current selected views pass
(nine prior ACTUAL byte-exact, changed 3/71/72/73 newly ACTUALLY inspected),
after ONE page break attached only to the new P3b paragraph. The FIRST
technically-green layout remains retained/excluded. All older paragraph
bytes are exact and both final paragraphs are complete.
Historical full/book warning-line MULTISETS remain exact: 707 Lean-source
warning headers plus four other cached warning lines. Touched mathematics
and all actual examples are warning-free.

Only conditional Q-origin independence/G/H/I/E statements are public;
the full two-family P/DFR/Q/remaining-row chain stays PRIVATE with explicit
k/ambient ACF, supplied INPUTs and raw non-memberships/nonconstancy.
Initial chart, actual guarded-Psi input derivation, input existence/
enlargement/descent, combined generator presentation, actions, linearity,
extraction, all completeness, #11 and frozen117 stay open. No uniqueness
or common-shift theorem. Final required full build/book AFTER this factual
append precede commit/push. The durable goal continues.


## L0c ratio-guard consequences and an actual guarded configuration consumer

Pinned to clean published 6bcf918, exact CI37766201900 FULL GREEN at
every library/book/deployment job and step. All five owned records and
all fifteen current body-owner references are reconciled. Peer4799
PLAN-ONLY audit finds G_ne_T and H_ne_S true and the actual raw-input
bridge feasible. Concrete #27 scope6058485548 and exact TWO public TYPEs
precede SOURCE-ONLY GO4800/ACK4801. Root remains sole compiler/integrator.

Immutable freeze4802 adds TWO public guards to PsiLattice after F_ne_U,
with no imports/private helpers/options/budgets/definitions/aliases/instances.
G=T uses the existing private I_eq_D_of_G_eq_T; H=S rewrites the defining
meets of I and D using inf_comm. Every existing declaration/proof/docstring
stays byte-exact. The module documentation and real Status are accurate.
All thirteen input pins (eleven project SHA1, actual274 SHA256, TYPE SHA1),
five artifact hashes and immutable modes are verified. PLAN opened only
PsiLattice, Psi, Points, Equivalence, ClosedLattice and AtomClause; draft
opened the pinned PsiLattice base and TYPE file. The remaining sources,
actual274 and NOTE-format context were inherited only. No older freeze
format artifacts reopened; Mathlib source reads are truthfully NONE.

FIRST default-kernel/standard-lint production passes UNCHANGED 2.00 s,
EMPTY log, minimum available 39.26 GiB. The first metadata run is retained
and excluded: root's comparator incorrectly expected theorem reducibility
irred; the actual/default value is semi, also recorded for old Q_ne_T.
ONLY that comparator expectation is corrected. No producer proof/TYPE,
fixture byte, checking option or budget changes. Second metadata passes
4.00 s, minimum available 39.18 GiB/RSS 2.23 GiB: all 87 old SIG/proof
and 54 old PUBLIC AX records exact, with ONLY TWO named public additions.
No new private/generated records in this scope; standard Lean axioms only.
No whole-library axiom certificate is claimed.

Root's actual PRIVATE GuardedTwoFamilyRemainingMeets414 preserves all
SEVEN old helper blocks BYTE-EXACT. The old274 example is only named
two_family_remaining_rows; its original TYPE/proof stay byte-exact.
One uncompiled name-prefix line wrap meets the existing 100-column style
before the FIRST compiler; the overlong uncompiled version is retained.
ONE new private point-nonmembership bridge is consumed SIX times.
ONE actual example derives ALL 25 raw inputs at actual Point.rep values:
16 memberships from actual Psi meets/incidences, SIX non-memberships
from P_ne_S/D_ne_S/F_ne_U/Q_ne_T/G_ne_T/H_ne_S and THREE nonconstancies
from point representatives. No raw field incidence/non-membership/
nonconstancy is supplied. All NINE initial chart equalities and AI5 are
explicit and consumed; chart existence is NOT proved.
The named old producer then derives P, D/F/R, Q, G/H/I/E and final AI.
Both ORIGINAL prime/spans precede ALL corresponding supplied INPUT
families. Base/ambient ACF and supplied families remain explicit.
FIRST actual consumer passes UNCHANGED 4.00 s, EMPTY log, minimum
available 39.04 GiB/RSS 2.73 GiB. No Lean proof/TYPE/options/budget repair.

Only TWO necessary lattice guards are newly public, without ACF/chart.
The genuine conditional guarded-chart two-family chain remains PRIVATE.
Initial action-chart existence, fresh INPUT existence/enlargement/descent,
combined generator presentation, actions, linearity, extraction and every
completeness statement remain open; #11 and frozen117 are independent.
Older P2/P3a/P3b Status lists still name open actual-Psi extraction/chart
obligations; this conditional private bridge supplies their raw inputs
only once the initial chart is given. No expanded old-module Status scope.

The exact FOUR paths update PsiLattice/module Status, the Book account/
TWO public docstrings, ONE source concordance paragraph and append-only
CONT. Root/Book imports are byte-exact. Every other 257 math/Main sources,
dependency pins, source49 active statements/original provenance/44 proofs/
listings/literals and frozen117 stay exact. Private canonical Book/source/
current visual, peer consumer/four-path review, actual full library/book,
strict scoped checks and final full/book precede commit/push.
The durable goal continues; broader L2/G3/G4/G5 remain open.


Private canonical first run is retained/excluded after the unchanged root
source symlink resolved outside the overlay -R. The focused producer had
already passed. Root materializes only the private root source BYTE-EXACT;
no main/math TYPE/proof/option/budget change. SECOND canonical module/root/
Book passes 34.01 s, minimum available 38.05 GiB/RSS 4.72 GiB, only CHECK/
PASS lines. Peer4804 ACCEPTS the actual414 and all 25 derivations/nesting.
FIRST source rendering passes four stable runs 8.00 s at 73 pages, no
TeX warnings; all THIRTEEN current selected views accepted: TWELVE prior
ACTUAL byte-exact, changed72 newly ACTUALLY inspected. All three page72
paragraphs remain complete. No source layout repair or new page break.

Before integration, root's historical-fixture inventory finds TWO legacy
suites querying the SAME three-module lattice scope: Lattice* and
PsiGeneric*. The THREE metadata GENRES (SIG, proof, PUBLIC AX) therefore
gain the SAME TWO named public guards in SIX fixture outputs. Every old
record/deny-list and all other scopes remain exact, and every earlier
fixture byte/diagnostic genre is unchanged. This concrete clarification is
recorded on the owned #27 scope before integration/shared checking. No
mathematical source, import, theorem or guard scope is expanded.


Actual L0c acceptance: Claude4804 ACCEPTS the actual guarded414 and
4806 ACCEPTS the initial FOUR paths. Guarded integration leaves all
257 other math/Main sources exact, with no root/Book import change.
Actual full lake build passes 84.03 s, minimum available
36.85 GiB/RSS 8.28 GiB; lake exe book passes
10.00 s, minimum available 38.55 GiB/RSS 1.61 GiB.
All 93 strict actual-main checks pass 162.07 s, minimum available
38.72 GiB/RSS 2.90 GiB. All 92 older fixture bytes and
EVERY old scoped TYPE/RAW/ATTR/DOC/AX/proof/deny-list record stay exact.
ONLY TWO named public guard additions appear in the SIX expected outputs
of the two legacy lattice metadata suites; all other scopes stay exact.
New guard records match accepted private metadata. No new private/
generated records in this scope; standard Lean axioms only. Mathematics/
actual behaviors use standard Mathlib lint/default kernel; historical
diagnostic genres/options stay exact. No whole-library axiom certificate.

Hygiene passes 259 files without proof placeholders/project axioms.
All 101 HTML paths remain; both new public docstrings are visible.
All 257 other math/Main sources, every older production declaration/
TYPE/proof/docstring, root/Book imports, toolchain/dependencies, source
49 active statements/original provenance/44 proofs/listings/literals and
frozen117 stay byte-exact. FIRST four stable 73-page source runs and all
THIRTEEN current views pass: TWELVE prior ACTUAL byte-exact, changed72
newly ACTUALLY inspected. All page72 paragraphs are complete; no source
layout repair or new page break. Historical full/book warning-line
MULTISETS stay exact: 707 Lean-source headers plus four other cached
warning lines. Touched mathematics and every actual example are warning-free.

Only TWO necessary lattice guards G_ne_T/H_ne_S are newly public, under
Psi/I≠D without chart or ACF. The actual guarded two-family composition
remains PRIVATE under explicit initial AI5/chart/base-ambient ACF and
supplied INPUT families. It derives ALL 25 raw field inputs from the actual
witness; no field-level membership/non-membership/nonconstancy hypothesis.
Both original curves precede ALL corresponding inputs. Initial action-chart
existence, INPUT existence/enlargement/descent, combined generators, actions,
linearity, extraction, all completeness, #11 and frozen117 remain open.
Final required full build/book AFTER this actual factual append precede
commit/push. The durable goal continues.



## P4 conditional full affine-grid presentation from an actual guarded chart

Pinned to clean published c2ca770, exact CI37770932869 FULL GREEN at
every library/book/deployment job and step. All five owned records and
sixteen tracking-body owners are synchronized. Peer4812 PLAN-ONLY audit
checks all eighteen rows and reports the initial-chart dependencies.
Concrete #27 scope6059264967 and exact ONE public TYPE precede
SOURCE-ONLY GO4814/ACK4815. Root remains sole compiler/main integrator.

The source's historical fixed-point evaluation-map claim near lines
1765-1770 is false by dimension: a two-dimensional group maps to a
one-dimensional orbit, with affine fibre {(a,y-at): a != 0}.
Peer4813 confirms both fixed- and varying-point interpretations.
Issue #21 comment6059251162 reports this BEFORE any original statement
change. A graph/germ parameter map or two-point evaluation with the
appropriate kernel/stabilizer proof may repair the historical sketch;
no such bridge is proved here, and the original wording remains exact.
An unaudited Mathlib genus/Riemann-Roch assertion is explicitly excluded.

Immutable freeze4816 adds AffineGridNormalization669 with EXACT SEVEN
imports (the old guarded414 imports plus AffineGrid), ONE public TYPE
and FIFTEEN consumed private helpers. All seventeen read pins, five
artifact hashes and immutable modes are verified before copying or Lean.
All old guarded414 namespace/variables/math-region bytes remain exact,
except naming its example guarded_two_family_rows. The old seven
helpers, two_family_remaining_rows and point_rep_notMem_of_ne are exact.
No definitions, aliases, instances, options, show, haveI, sorry or budgets.
PLAN opened AffineGrid, part of WitnessTable/Closure.Basic, a ClosedLattice
grep and blueprint sections. DRAFT opened the actual414 and TYPE file;
other permitted project/actual274/NOTE context was inherited only.
No earlier freeze-format artifacts reopened; Mathlib reads are NONE.

The public TYPE keeps actual Psi, I != D, ACF, AI5 and all NINE initial
chart equalities explicit. It derives every raw field input internally.
The original FP prime/span precedes ALL supplied first INPUT families;
after the family, kappa and original FQ prime/span precede ALL second
INPUT families. After both, the conclusion is HasAffineGridCoordinates.
There is no caller normal-form or OUTPUT-freshness oracle.
The five new consumed bricks convert representative singleton closures
to points, transport constant translates and triangular joins, assemble
a variable-level grid, and apply those bricks to final atom coordinates.
The actual final chart is
(a, b+(a-1)kappa-eta, c, d+(c-1)kappa+(c-1)eta, x-kappa).
All THREE joins and FIFTEEN closed points are derived. The six original
generator points are not constrained; no common shift or uniqueness.
I != P is unnecessary for THIS explicitly charted supplied-input result;
no global extraction guard is removed or arbitrary-w chart constructed.

FIRST unchanged standard-lint/default-kernel production passes 4.00 s,
EMPTY log, minimum available 39.07 GiB/RSS 2.76 GiB. FIRST scoped
metadata passes 6.00 s, minimum available 39.07 GiB/RSS 2.69 GiB:
exact SIXTEEN SIG/proof records and ONE PUBLIC AX record, one public/
fifteen consumed private, zero generated records IN THIS SCOPE,
standard Lean axioms only. Expected counts precede the first metadata.
Historical diagnostic genres/options remain exact. No whole-library
axiom certificate; no proof/TYPE/options/budget repair.

Root's ACTUAL ChartSuppliedInputsQSem41 preserves the public hypotheses
and full prime/span-before-ALL-INPUT nesting. ONE example and no helpers
derive the full grid before QWitness.qSem_of_hasAffineGridCoordinates.
FIRST unchanged standard/default check passes 2.00 s, EMPTY log,
minimum available 39.31 GiB. Root's actual CanonicalInitialChart24
jointly realizes Psi, I != D and all nine chart equalities in qWitness,
using the existing grid/QSem ratio_ne API. ONE example, no helpers,
no ACF; FIRST unchanged standard/default check passes 2.00 s, EMPTY,
minimum available 39.33 GiB. This proves a canonical joint chart only:
fresh INPUT existence and arbitrary-w chart existence are still open.

The exact FIVE paths add the module/real Status, ONE root import,
ONE Book import/account/public docstring, ONE source concordance
paragraph and append-only CONT. All 258 prior math/Main sources,
dependency pins, source49 active statements/original provenance/44
proofs/listings/literals and frozen117 stay exact. Private canonical
Book/source/current visual, peer consumers/five-path review, actual
full library/book, strict scoped checks and final full/book precede
commit/push. Initial chart existence, input existence/enlargement/descent,
actions, classification and scheme bridges, guarded/unconditional
extraction and ALL completeness remain open; #11/frozen117 independent.
The durable goal continues; broader L2/G3/G4/G5 remain open.


Actual P4 acceptance: Claude4818 ACCEPTS both actual consumers;
4820 ACCEPTS the initial FIVE paths; 4822/4824 ACCEPT only the new
source long-token and attached-paragraph page-break repairs. Every
prior mathematical source remains exact. The private canonical module,
root and Book checks pass FIRST 34.01 s, minimum available 38.04 GiB/
RSS 4.52 GiB, with ONLY the expected three CHECK/PASS pairs.
Actual full lake build passes 82.03 s, minimum available
36.72 GiB/RSS 8.40 GiB; lake exe book passes
10.00 s, minimum available 38.51 GiB/RSS 1.59 GiB.
All 98 strict actual-main checks pass 178.07 s, minimum available
38.64 GiB/RSS 2.90 GiB. ALL 93 older fixture bytes and
EVERY old scoped TYPE/RAW/ATTR/DOC/AX/proof/deny-list record stay exact,
with NO old-scope additions. The three new metadata suites and two
actual consumers match their accepted private sources/records.
ONE new public and FIFTEEN consumed private theorems, zero generated
records IN THIS SCOPE, standard Lean axioms only. Mathematics and
actual behaviors use standard Mathlib lint/default kernel; historical
diagnostic genres/options stay exact. No whole-library axiom certificate.

Hygiene passes 260 files without proof placeholders/project axioms.
All 101 HTML paths remain, with the new public docstring and older
prerequisites visible. All 258 prior math/Main sources, dependencies,
source49 active statements/original provenance/44 proofs/listings/
literals and frozen117 remain exact. Root/Book each gain ONLY ONE
new module import. The FIRST source four-pass render is retained/
excluded for one long-module-token overfull box; the SECOND stable
74-page render is retained/excluded after actual inspection found
the older generic-invariance paragraph split across pages72/73.
ONLY the NEW paragraph loses that long token and gains one attached
clearpage. THIRD four-pass rendering is stable at 74 pages, with all
FOURTEEN current selected views accepted: TEN prior ACTUAL byte-exact,
pages3/72/73/74 newly ACTUALLY inspected. Both P4 and the older generic
paragraph are complete, clear and unclipped; no original source bytes
change. Historical full/book warning-line MULTISETS stay exact:
707 Lean-source warning headers plus four other cached warning lines.
Touched mathematics and all actual examples are warning-free.
No Lean proof, TYPE, checking option or resource budget repair.

The full grid is conditional on actual Psi, I != D, explicit AI5 and
all nine initial-chart equalities, base/ambient ACF and supplied fresh
INPUT families. Every raw field condition is derived. Both original
prime curves/spans precede ALL corresponding inputs. The actual
consumer derives the grid before QSem; canonical non-vacuity covers
the joint Psi/ratio-guard/initial chart, not INPUT existence.
Initial chart existence, INPUT existence/enlargement/descent, actions,
classification/scheme bridges, guarded/unconditional extraction and
ALL completeness remain open; #11/frozen117 are independent.
Final required full build/book AFTER this actual factual append precede
commit/push. The durable goal continues.



## P5 constructed fresh inputs over an ambient field of infinite transcendence degree

Pinned to clean published 7c063071, exact CI37777667633 FULL GREEN at
every library/book/deployment job and step. All five owned records and
seventeen body-owner references reconciled. Peer4832 PLAN-ONLY audit
finds both public TYPEs true and the existing API sufficient. Concrete
#27 scope6060174271 precedes SOURCE-ONLY GO4834/ACK4836. Root remains
sole Lean/Lake compiler and main integrator.

Immutable freeze4837 adds AffineGridInfinite87, EXACT THREE imports,
TWO public theorems and no private helpers/definitions/aliases/instances/
options/show/haveI/sorry/resource changes. Both TYPEs match the proposed
instruction after whitespace. All FOURTEEN input pins (ten project/
two Mathlib SHA1, old actualQSem41 SHA256, TYPE SHA1), five artifact
hashes and immutable modes are verified before copying or Lean.
PLAN/DRAFT open Transfer.Transcendence and exact segments/greps of
Mathlib Data.Set.Finite.Basic and SetTheory.Cardinal.Basic. P4/AffineGrid/
Psi/Point/Closure and NOTE format are inherited only. WitnessTable,
Representatives, Closure.Basic, blueprint, AGENTS, CONT and old freezes
are not reopened by the peer. The optional actualQSem41 is hash-verified,
not reopened for drafting. Root's earlier Fintype.Basic alternative
read was unused next-research context, not a P4 or P5 proof input.

The first theorem constructs a whole sequence fresh over finite S and
all previous entries, without ACF, under explicit countable lower bound
on trdeg(k,K). It uses Mathlib's seq_of_forall_finite_exists with
P z T := z notin racl(S union T). A finite union has cardinal less than
aleph0, so the existing finite-cardinality fresh-element theorem supplies
the next entry. No bespoke recursion/choice or new rank helper.
The second theorem consumes it TWICE. The original FP curve precedes
construction of tP over {a,b,x,c}; kappa and the original FQ curve precede
construction of tQ over {c,d+(c-1)map kappa,b+(a-1)map kappa,(ac)^-1}.
Explicit finite-insert/singleton proofs use only verified API.
The public theorem then derives HasAffineGridCoordinates, with NO caller
freshness/normal-form/OUTPUT-freshness or grid hypothesis.
Actual Psi, I != D, AI5, all NINE initial-chart equalities and base/
ambient ACF remain explicit, as does countable ambient transcendence degree.

FIRST unchanged standard-lint/default-kernel production passes 2.00 s,
EMPTY log, minimum available 37.33 GiB. FIRST scoped metadata passes
6.00 s, minimum available 37.29 GiB/RSS 2.55 GiB: exact TWO SIG/proof
and TWO PUBLIC AX records, two public/zero private/zero generated records
IN THIS SCOPE, standard Lean axioms only. Exact counts precede first
metadata; diagnostic genres/options are unchanged. No whole-library
axiom certificate and no Lean proof/TYPE/options/budget repair.

The ACTUAL PRIVATE InfiniteChartQSem27 has ONE example/no helpers,
same countable-trdeg/ACF/Psi/guard/AI5/nine-chart hypotheses, and derives
the grid before applying qSem_of_hasAffineGridCoordinates.
No caller INPUT family or grid/normal-form oracle. An uncompiled root
formatting join is applied BEFORE the first compiler and retained.
FIRST unchanged standard/default check passes 2.00 s, EMPTY log,
minimum available 37.11 GiB. The earlier canonical24 joint chart remains
accepted; this checkpoint does not construct an arbitrary-w chart.

The exact FIVE paths add the module/real Status, ONE root import,
ONE Book import/account/TWO public docstrings, ONE source concordance
paragraph and append-only CONT. All 259 prior math/Main sources,
dependencies, source49 active statements/original provenance/44 proofs/
listings/literals and frozen117 stay exact. All98 old actual-main fixture
bytes/scoped records must remain exact, with NO old-scope additions.
Private canonical Book/source/current visual, peer actual consumer/
five-path review, actual full library/book, strict scoped checks and final
full/book precede commit/push. Fresh INPUTs are constructed ONLY for the
explicit infinite-trdeg ambient case. Finite-trdeg enlargement/descent,
initial chart existence for arbitrary witnesses, actions, classification/
scheme bridges, guarded/unconditional extraction and ALL completeness
remain open; #11/frozen117 independent. No global I != P guard removal,
six-generator constraint, common shift or uniqueness. The goal continues.


Actual P5 acceptance: Claude4842 ACCEPTS the actual27-line consumer,
4845 ACCEPTS the exact FIVE proposed paths. All 259 prior math/Main
sources remain exact; root/Book each gain ONLY ONE import.
FIRST private canonical module/root/Book checks pass 40.02 s,
minimum available 35.47 GiB/RSS 6.27 GiB, ONLY three CHECK/PASS pairs.
Actual full lake build passes 96.04 s, minimum available
33.96 GiB/RSS 8.39 GiB; lake exe book passes
14.01 s, minimum available 35.83 GiB/RSS 1.53 GiB.
All 102 strict actual-main checks pass 230.09 s, minimum available
35.12 GiB/RSS 2.90 GiB. ALL 98 older fixture bytes and
EVERY old scoped TYPE/RAW/ATTR/DOC/AX/proof/deny-list record stay exact,
with NO old-scope additions. Three new metadata suites and ONE actual
consumer match their accepted private sources/records. TWO new public
theorems, zero private/generated declarations IN THIS SCOPE, standard
Lean axioms only. Both fresh sequences are actually constructed before
the grid and QSem. Mathematics/actual behaviors use standard Mathlib
lint/default kernel; historical diagnostic genres/options stay exact.
No whole-library axiom certificate.

Hygiene passes 261 files without proof placeholders/project axioms.
All 101 HTML paths remain, with both new public docstrings and older
prerequisites visible. All 259 prior math/Main sources, dependency pins,
source49 active statements/original provenance/44 proofs/listings/
literals and frozen117 remain exact. FIRST source rendering gives
four stable 74-page runs and all FOURTEEN current views accepted:
THIRTEEN prior ACTUAL byte-exact, page73 newly ACTUALLY inspected.
All P4/P5/generic paragraphs on that page are complete, clear and
unclipped; no source layout repair or additional page break.
Historical full/book warning-line MULTISETS remain exact: 707 Lean
source headers plus four other cached warning lines. Touched mathematics
and all actual examples are warning-free; no proof/TYPE/options/budget
repair. The root consumer's uncompiled formatting-only join preceded
its FIRST compiler and is retained.

Fresh INPUTs are constructed only under explicit countable lower
bound on ambient transcendence degree. Actual Psi/I != D, base/ambient
ACF, AI5 and all NINE initial-chart equalities remain explicit.
Each original prime curve/span is fixed before its corresponding
family is constructed. No caller family/grid/normal-form/OUTPUT-freshness
oracle. Finite-trdeg ambient enlargement/descent, arbitrary-w initial
chart existence, actions, classification/scheme bridges, guarded and
unconditional extraction and ALL completeness remain open;
#11/frozen117 remain independent. No global I != P guard removal,
six-generator constraint, common shift or uniqueness. Final required
full build/book AFTER this actual factual append precede commit/push.
The durable goal continues.



## P6 affine-grid enlargement and descent for an explicit chart

Pinned to clean published 803df49ff2cbcfb07d611d29220de05cf28bfae4;
exact CI37782219474 FULL GREEN at every build/book/deployment step.
All five owned issue reports/bodies and eighteen body-owner references
reconciled. PLAN4863 and Claude4870/4873 find finite-ambient chart
descent sound, including removal of ambient ACF. Base ACF remains.
#27 scope6061006717 precedes the isolated root API checks; concrete
source scope6061078158 precedes SOURCE-ONLY GO4884/ACK4886.
Root remains sole Lean/Lake compiler and main integrator.

The isolated THIRD API probe passes standard Mathlib/default kernel,
2.00 s, minimum available 36.03 GiB, EMPTY log. Four canonical
algebra/tower instances, injective polynomial-to-fraction-to-closure,
countable trdeg and pair/singleton closure reflection are checked.
FIRST failure: instance-valued example needs noncomputable section,
and lift_id does not remove a universe-zero lift. SECOND failure:
missing closing end of that diagnostic section. Both retained;
THIRD uses lift_id prime and the closed noncomputable section.
These affect only the isolated diagnostic, with no checking/resource
option changes or main edits.

Immutable freeze4892 has exactly THREE math sources: FreshSequences43,
AffineGridInfinite74 and AffineGridNormalization917, all lines <=100.
All 32 input entries (24 source SHA1, seven root records SHA1, root
APIProbe SHA256), all nine artifact hashes/manifest/immutable modes
and three exact-base diffs are verified before copying or Lean.
All twenty other P4 blank-line mathematical blocks stay byte-exact.
The old guarded_two_family_rows TYPE/doc remains exact; its 25 typed
haves move byte-exact into guarded_raw_inputs. Only its proof changes.
The fresh-sequence declaration moves byte-exact with its public name,
TYPE/proof/docstring into Geometry.FreshSequences. The P5 chart
public declaration stays byte-exact and its Status marks it subsumed.

Peer PLAN reads Ambient, part of Base and four Mathlib files via
exact ranges/greps; DRAFT reads main P4/P5 and the seven root records.
The five additional allowed Mathlib API pins are verified, not read
by the peer; the checked root API probe supplies those facts.
Transcendence and Shifted/Remaining meets/P4/P5 work are inherited.
During PLAN/DRAFT the peer does not reopen blueprint, Book, AGENTS
or CONT. Root's actual
separate API/source/status reads are recorded in root_read_ledger.
Root clarifies TWO NEW doc passages BEFORE the first project compiler:
at least countable trdeg over k, since K itself may have larger trdeg.
Claude4898 agrees. No old declaration DOC/TYPE/proof or budget change.

FIRST three-source production passes standard Mathlib/default kernel,
8.00 s, minimum available 36.17 GiB/RSS 2.77 GiB, EMPTY log.
FIRST exact scoped metadata passes 6.00 s, minimum available
36.13 GiB/RSS 1.32 GiB: 24 SIG/proof records, FOUR PUBLIC AX records;
P4 two public/twenty private, P5 one public/zero private, Fresh one
public/zero private, zero generated records IN EACH audited scope.
The exact named migrations are the old private guarded RAW proof and
the fresh declaration module column. ALL other old scoped TYPE/RAW/
ATTR/DOC/AX/proof records stay exact. Standard Lean axioms only in
these scopes, diagnostic genres/options unchanged; no whole-library
axiom certificate and no TYPE/proof/options/resource repair.

The raw conditions are derived in K with no ACF or independence
needed for that derivation. Only the 25 facts and AI5 are embedded
into the canonical algebraically closed countable-variable extension;
the globally quantified Psi is NEVER transported. The original FP
precedes construction of tP, and kappa and original FQ precede tQ.
Both constants remain in ORIGINAL k. Nine singleton closure rows
reflect to ORIGINAL K through mutual memberships and ambient
absoluteness. Final AI is derived DIRECTLY in K by the old table
shift and Q-shift lemmas from hind/kappa/eta. The old final-row
assembler gives all three joins and fifteen points there.

The actual PRIVATE FiniteChartQSem has ONE example/no helpers and
FIRST passes standard/default in 2.00 s, minimum available 36.07 GiB,
EMPTY log. It derives the grid BEFORE QSem under ONLY base ACF,
actual Psi/I != D, AI5 and all nine initial-chart equalities.
No ambient ACF/trdeg bound, caller input family/raw field/grid/
normal-form/OUTPUT-freshness oracle. The earlier canonical24 joint
chart and all older actual consumers remain required checks.

The proposed SEVEN paths are the three math modules, ONE root import,
ONE Book import/account/new public docstring, ONE source concordance
paragraph with a clear page attached FROM ITS FIRST proposal, and
append-only CONT. Book/source supersede older enlargement/descent-open
checkpoint scope lines ONLY for the explicit charted theorem.
Initial charts for arbitrary witnesses, actions, classification/scheme
bridges, guarded/unconditional extraction and ALL completeness remain
open; #11/frozen117 independent. No global I != P removal,
six-generator constraint, common shift or uniqueness.
Peer actual consumer/seven-path review, canonical Book/source/visual,
actual full library/book, all 102 older fixture bytes with precisely
named scope migrations, hygiene, and the final full/book pair AFTER
actual factual CONT acceptance append precede commit/push.
The durable goal continues.


Actual P6 acceptance: Claude4901 ACCEPTS FiniteChartQSem25,
4903/4908 ACCEPT the exact SEVEN paths and precise doc repairs.
All 258 other math/Main sources stay exact; root/Book each gain
ONLY ONE focused import. The fresh declaration is byte-exact rehomed,
all older public math TYPE/proof/docstrings stay exact, and only the
named old private guarded RAW proof changes through fact extraction.
Actual full lake build passes 114.04 s,
minimum available 34.13 GiB/RSS 10.96 GiB;
lake exe book passes 14.00 s,
minimum available 35.95 GiB/RSS 1.59 GiB.
All 106 strict actual-main checks pass 222.09 s,
minimum available 37.13 GiB/RSS 2.90 GiB.
ALL 102 older fixture bytes remain exact. The precisely named
guarded-proof/fresh-module migrations and P4 additions reproduce
accepted private records; EVERY OTHER old scoped TYPE/RAW/ATTR/DOC/
AX/proof/deny-list record stays exact. The three new combined metadata
suites and actual no-KACF/no-htr consumer match private acceptance.
ONE new public and FIVE consumed private declarations; P4 scope2/20,
P5 scope1/0, Fresh scope1/0, generated0 IN EACH audited scope.
Standard Lean axioms only there; no whole-library axiom certificate.
Mathematics/actual examples use standard Mathlib/default kernel;
historical diagnostic genres/options remain exact.

SECOND canonical root/Book passes 42.02 s, minimum available
35.32 GiB/RSS 6.43 GiB, ONLY two CHECK/PASS pairs, warning-free.
FIRST retained/excluded: the NEW Book literal polynomial brackets
parse as a Verso link; root's harness also applied inappropriate
Mathlib hashCommand lint to Book. Only NEW account prose is repaired,
and Book's existing canonical Verso diagnostic genre restored.
The failed generated-doc sorry warning is excluded; no source sorry.
No mathematical TYPE/proof/options/resource-budget repair.
SECOND source render gives four stable75-page runs and FIFTEEN
accepted current views: ELEVEN prior ACTUAL byte-exact plus
pages3/73/74/75 ACTUALLY inspected, all clear/complete/unclipped.
FIRST render retained/excluded for the NEW paragraph's countable-
degree factual wording; it now states at least countable over k.
No layout repair; the clearpage was attached ONLY to the new P6
paragraph from its FIRST proposal. Historical full/book warning-line
MULTISETS remain exact: 707 Lean source headers plus four cached lines.
Touched mathematics and all actual examples remain warning-free.

Hygiene passes262 files, HTML101 paths and new/older docstrings remain.
Source49 active statements/original provenance/44 proofs/listings/
literals, dependencies, all other258 math/Main sources and frozen117
remain exact. The charted result now works for ANY ambient extension K
of algebraically closed k: raw facts derived in K, only they and AI5
embedded into a fresh ACF extension, each original curve preceding
its constructed INPUT family, constants in ORIGINAL k, nine rows
descended into ORIGINAL K, final AI by old shifts in K, all three
joins/fifteen points derived BEFORE QSem. Psi is NEVER transported.
No ambient ACF/trdeg bound, caller INPUT/raw/normal-form/grid oracles.
Base ACF, actual Psi/I != D, AI5 and NINE initial-chart equalities
remain explicit. Initial charts for arbitrary witnesses, actions,
classification/schemes, guarded/unconditional extraction and ALL
completeness remain open; #11/frozen117 independent. No global I != P
removal, generator constraint, common shift or uniqueness.
Final required full build/book AFTER this actual factual append
precede commit/push. The durable goal continues.


## ACF-base tensor-domain brick (#11)

Pinned to clean published 069b9646ca84ac7803a1a9b24d0daae58e592cf4; exact CI37790456501
FULL GREEN at every build/book/deployment step. This literal independent
blueprint obligation is resumed after P6; frozen M4a remains unchanged.
PLAN4934/ACK4936 and Claude4942/4943 find the finite-subalgebra
specialization route feasible. #11 scopes6062120850/6062231058/6062315943
precede the isolated API and SOURCE-ONLY GO4947/ACK4948 respectively.
Root remains sole Lean/Lake compiler and main integrator.

THIRD four-example API probe passes standard Mathlib/default kernel,
2.00 s, minimum available 37.02 GiB, EMPTY log. It checks the Jacobson/
Zariski quotient field and algebraic lift, the basis-coordinate identity,
finite-type finite subalgebras and tensor-flat injectivity. FIRST fails
for missing explicit Jacobson base arguments and basis-index decidability
in the statement. SECOND needs an explicit radical prime-bottom proof,
and standard local-instance/unused-simp style repairs. Both retained;
no checking option or resource budget change.

Immutable freeze4949 supplies one new RegularACF source, 177 lines,
all lines <=100. All five artifact hashes/manifest and immutable modes,
the exact new-file diff against /dev/null, and all22 ledger records
(21 SHA1 including the GO pin file, one APIProbe SHA256) are verified
before copying or Lean. The peer's PLAN read ranges/greps and actual
DRAFT reads are recorded separately. DRAFT reads the compiled root API
and acceptance/scope records, with no Mathlib source reads. It does not
open AGENTS, Basis.VectorSpace, or root ledger/preflight beyond hashing.
Root reads AGENTS/CONT and the original source/API independently.

FIRST production fails ONLY because the point-helper call needs
explicit k. Exact source/log/metrics retained; root adds ONLY (k := k)
at that private call, with TYPE/docs/imports/options/budgets unchanged.
SECOND production passes standard Mathlib/default kernel in 4.00 s,
minimum available 35.95 GiB/RSS 2.52 GiB, EMPTY log.
FIRST scoped metadata passes 6.00 s, minimum available 36.11 GiB:
FOUR SIG/proof records, ONE PUBLIC AX record, one public/three private,
generated0 in the NEW audited scope, standard Lean axioms only there.
The old Regular baseline has THIRTEEN SIG/AX/proof records, including
its old fwd.eq_1; those must stay exact. No whole-library certificate.

The public producer covers arbitrary field extensions E/F over ACF k,
with no caller finite-generation, point-density, regularity or domain
oracle. Finite left legs lie in a finitely generated SUBALGEBRA A of E,
never an FG intermediate field assumed finite type. Jacobson/Zariski
derives a k-valued point avoiding a nonzero coefficient product. A basis
of F preserves nonzero coefficients under specialization; flatness
injects A tensor F into E tensor F. All three private helpers are
consumed by the public producer. No new definitions/instances/aliases.

FIRST actual PRIVATE GenericCommonField14 passes standard/default,
2.00 s, minimum available 36.10 GiB, EMPTY log. One example/no helpers
derives the domain instance before Mathlib's common-field construction,
obtaining linearly disjoint images of arbitrary E/F at independent
universes. No FG/finite-type/point/regularity/domain hypothesis.
Claude4959 ACCEPTS the exact one-argument repair, metadata and consumer.

Claude4953 independently confirms the historical proof-sketch gap:
independent-left tensor relations are impossible over ANY base field,
which does not imply absence of zero divisors. Complex tensor complex
over real numbers refutes that inference, not the ACF target statement.
#11 comment6062594506 reports the gap before the new concordance; the
original source statement and proof wording remain untouched.

Exactly SIX paths are proposed: new RegularACF, ONLY the old Regular
module-level superseded Status, ONE root import, Book.HardKernel
import/account/public docstring, ONE source concordance paragraph with
a clear page FROM ITS FIRST proposal, and append-only CONT. The new
proof route is identified; all older mathematical declarations stay
exact. Canonical root/Book/source/visual, full library/book, all106
earlier fixture bytes/scoped records and seven additional checks,
hygiene and peer six-path review precede commit/push. The final full/
book pair AFTER actual factual CONT acceptance append is required.
Only #11's tensor-domain brick is discharged by the producer. Full
generic points, correspondence composition, arbitrary initial charts,
actions/classification/scheme bridges, extraction and all completeness
remain separate obligations. Frozen117 and dependencies stay exact.
The durable goal continues.


Actual #11 acceptance: Claude4959 ACCEPTS the producer/consumer and
4963 ACCEPTS the SIX paths. Actual full lake build passes 58.03 s,
minimum available 32.07 GiB/RSS 8.29 GiB; lake exe book passes
14.01 s, minimum available 33.73 GiB/RSS 1.51 GiB.
All113 strict actual-main checks pass 198.08 s, minimum available
33.52 GiB/RSS 2.91 GiB. ALL106 earlier fixture bytes and scoped
TYPE/RAW/ATTR/DOC/AX/proof/deny-list records stay exact. The old
Regular's THIRTEEN SIG/AX/proof records, including its old generated
fwd.eq_1, stay exact. The new scope's FOUR SIG/proof and ONE PUBLIC
AX records reproduce private acceptance: one public/three consumed
private, generated0 IN THIS NEW audited scope, standard Lean axioms
only there. These are scoped audits, not a whole-library certificate.

The FIRST actual GenericCommonField14 remains exact: arbitrary E/F,
base ACF, fields/algebras only, derived domain BEFORE a common-field
realization with linearly disjoint images. No finite-generation,
finite-type, point-density, regularity or tensor-domain oracle.
All260 other old math/Main sources and dependencies stay exact;
old Regular changes ONLY module-level Status, preserving every
mathematical declaration byte and scoped record. Root and Book each
gain ONE focused import. Hygiene263 passes, and HTML102 retains all101
old paths plus one tensor-domain section with the public docstring.
The older charted-grid and frozen M4a pages remain visible.

SECOND canonical root/Book passes 26.01 s, minimum available
35.41 GiB/RSS 6.13 GiB, ONLY TWO CHECK/PASS pairs, warning-free.
FIRST is retained/excluded: root's partial namespace overlay shadows
fallback imports but lacks old cached project objects. Full Math/Book
source trees and ALL cached artifacts are supplied; every artifact
symlink of a compiled source is unlinked before writing. No source
TYPE/proof/doc/options/resource-budget repair at this gate.
FIRST four-pass source rendering is stable76 pages with SIXTEEN
current accepted views: THIRTEEN prior ACTUAL byte-exact, plus
pages3/75/76 ACTUALLY inspected. Contents, the complete new paragraph
and bibliography are clear/complete/unclipped, with no layout repair.
The new paragraph's clearpage is attached from its FIRST proposal.
All49 active source statements/original provenance/44 proofs/listings/
literals stay exact. The old independent-left tensor-relation proof
gap is reported before concordance edits; original wording retained.

Historical full/book warning totals remain711: all703 OTHER warning
headers stay byte-exact. ONLY the eight old Regular style notices
move by EXACTLY +4 source lines because of its module Status; their
complete style payloads stay exact. They are retained, with no warning
suppression. New mathematics and actual examples are warning-free.
No checking option or resource budget change, and no old proof repair.
The only new production repair is the explicit private-call k argument,
whose FIRST failure remains preserved. Frozen117 remains unchanged.

The tensor-domain brick of #11 is now proved for arbitrary field
extensions of an algebraically closed base. It is independent of the
charted P6 result and does not discharge the full generic-point
statement, correspondence composition, arbitrary-witness charts,
actions/classification/scheme bridges, extraction or reconstruction
completeness. Those remain separate obligations. Final required full
library/book AFTER this ACTUAL factual append precede commit/push.
The durable goal continues.


## Prime polynomial ideals after scalar extension (#5)

Pinned to clean published f5df7f73bd4bad5238e9e655b8757a26a9230dd3.
Regularity CI37802455841 is FULL GREEN at every build/book/deployment
step; six owned reports/bodies and twenty #6/#27 body-owner references
are reconciled with history/checklists preserved. #11 is closed completed
for ONLY its tensor-domain obligation. Full generic extension remains #5.
Chit5021 reports that checkpoint. PLAN5025 and supplements5034/5043
lead to concrete review request5044, ACK5048 and Claude5051 ACCEPT.
Peer AUDIT.md SHA1 ddf66b128a7da960542d5b5eef93a8a5a35e3295 is verified.
Its actual reads are FunctionField40-80/greps, the named project
module declaration greps, BaseChange955-975, source1268-1277 plus
inherited1240-1286, full producer/actual consumer/contraction and
source diffs, expected scope and acceptance heads. It does NOT read
Mathlib, AGENTS/CONT/Book/AffineRelocation or root ledgers in this audit.
The peer owns only read-only audit notes; root remains sole Lean/main
owner. No new source GO has been assigned to the peer. Only the author
credit and private helper wording change after its nonblocking nits;
TYPE/proof/public-doc/import/option/budget bytes remain unchanged.

The original22 PLAN pins stay exact. Root's post-plan actual reads are
recorded in separate ledgers. The two-example API with one consumed
private domain helper passes SECOND, 4.00 s/min32.66 GiB, EMPTY log.
FIRST source/log/metrics retained: quotient-prime statement arguments,
RingHom coercions for ideal map composition, explicit aeval factorization.
The independent contraction API passes THIRD, 4.00 s/min33.80 GiB,
EMPTY log, for ANY ideal over ANY field extension, no ACF/prime premise.
Its first two coercion/rewrite failures are retained. No option or
resource-budget change at any gate.

The temporary named producer and tuple-based consumer APIs pass SECOND,
4.00 s each/min33.76 and33.58 GiB, EMPTY logs. Their first long-line
notices are retained; only declaration-line wrapping repairs them.
The actual private production source passes FIRST, 4.00 s/min33.82 GiB,
EMPTY log, standard Mathlib/default kernel. It has85 lines, four focused
imports, ONE public theorem and ONE consumed private domain helper.
The theorem covers arbitrary prime ideals, arbitrary variable type and
arbitrary field extensions E of ACF k, with no finite-type, geometric
primality, point-density or tensor-domain oracle.
The quotient domain embeds into its fraction field; flatness preserves
the embedding after tensoring with E. RegularACF supplies the field
tensor domain. Tensor quotient and polynomial equivalences transfer
domain-ness to the extended ideal's quotient, proving primeness.

FIRST metadata passes6.00 s/min33.02 GiB: TWO SIG/proof records and
ONE PUBLIC AX, one public/one private, generated0 in the NEW audited
scope and only standard Lean axioms there. No whole-library certificate.
FIRST actual PRIVATE GenericScalarPoint consumer passes4.00 s,
min33.98 GiB, EMPTY log. One example/two consumed private FIXTURE helpers
start from ANY tuple in ANY field F/k, at independent universes u/v/w/z.
The extended ideal's primeness is DERIVED, then its quotient-fraction
field K:Type(max v z) gives a tuple b with EXACT k and E ideals.
Algebraic independence of the original affine-space tuple over k implies
independence of b over E. No prime/domain/density/point/regularity oracle.
Its only change from the green API consumer is the production import.
These fixture helpers are private validation code, never production.

Claude5051 independently confirms root's infinite-cardinal inference
counterexample, reported BEFORE
any concordance on #5 comment6064168573. For independent t_i, E=ACF of
k(t_i), V=A1, v=t0 in E, absolute trdeg is aleph0=aleph0+1 while v is
algebraic over E. This refutes that inference, not the lemma's valid
generic-over-E premise. Original statement/proof wording stays exact.
The Book's stale final prose that #11 remains open is corrected, while
its full generic-extension and other obligations remain visible.

Exactly FIVE paths are proposed: GeometricPrime, one root import, Book
import/account/public docstring and named stale-status prose repair,
one source concordance paragraph with its clearpage FROM FIRST proposal,
and append-only CONT. All existing mathematical declarations stay exact.
Canonical root/Book/source/visual, full library/book, all113 earlier
fixture bytes/scoped records, four new checks, hygiene and final actual
factual acceptance append precede commit/push. General locus-relative
bases, ambient automorphisms, composition, arbitrary initial charts,
actions/classification/schemes, extraction and completeness stay open.
Frozen117/dependencies unchanged. The durable goal continues.


Actual scalar-extension acceptance: Claude5051 ACCEPTS the producer,
real consumer and source-gap scope;5059 ACCEPTS all FIVE paths.
Actual full lake build passes 56.02 s,
minimum available 32.46 GiB/RSS 8.32 GiB;
lake exe book passes 18.01 s,
minimum available 34.15 GiB/RSS 1.57 GiB.
All117 strict actual-main checks pass 170.04 s,
minimum available 33.61 GiB/RSS 2.93 GiB.
ALL113 earlier fixture bytes and scoped TYPE/RAW/ATTR/DOC/AX/proof/
deny-list records stay exact, including the old Regular13 and new
RegularACF4/1 records and derived common-field consumer. The NEW scope
has TWO SIG/proof records and ONE PUBLIC AX, one public/one consumed
private, generated0 IN THIS audited scope, standard Lean axioms only
there. These are scoped audits, not a whole-library certificate.

The actual PRIVATE GenericScalarPoint one-example/two-helper fixture
starts from ANY tuple over ACF k and arbitrary E/F, at independent
universes. Its extended prime ideal is DERIVED; the canonical quotient-
fraction-field tuple has EXACT k/E ideals. Whole-tuple independence
over k implies independence over E. No prime/domain/regularity/density/
point oracle. General subfamily/transcendence-basis/field-freeness
independence is a separate obligation, proposed by Claude5051 finding4.

All262 old mathematical/Main source bytes and dependencies stay exact;
root and Book each gain ONE focused import. Book adds the account and
public docstring and repairs ONLY the named stale #11-open sentence.
Hygiene264 passes; HTML103 preserves all102 prior paths and adds one
prime-ideal section. The charted-grid and frozen117 pages remain visible.
All711 historical full/book warning headers stay BYTE-EXACT, with no
source-position change or suppression. New mathematics and actual
examples are warning-free under standard Mathlib/default kernel.

FIRST canonical root/Book passes30.01 s/min33.50 GiB; SECOND after
the peer's private-doc/header nits passes24.01 s/min34.35 GiB. Both
have ONLY TWO CHECK/PASS pairs, warning-free with proper Book genre.
Full Math/Book namespace sources and ALL cached artifacts are supplied;
every compiled-source cache symlink is unlinked before writing.
The source is85 lines, one public/one private. The ONLY post5051 source
changes are author credit and the private helper docstring. Recheck
passes2.00 s/min34.68 GiB; second metadata6.00 s/min34.67 GiB proves
ALL TYPE/raw/attributes/public DOC/AX/proofs exact, with ONLY the
private DOC hash changed. No checking option or budget change.
The first API failures and the two first long-line notices are retained;
wrapping declaration lines is their only style repair. Private docs
preparation also retains its initial missing-directory failure, repaired
only by creating its own source-output directory, with no main effect.

FIRST four-pass source rendering is stable77 pages, SEVENTEEN current
accepted views: FOURTEEN prior ACTUAL byte-exact, plus pages3/76/77
ACTUALLY inspected. Contents, the entire new paragraph and bibliography
are clear/complete/unclipped, with no layout repair. Its clearpage is
attached FROM FIRST proposal. Removing the one new paragraph recovers
ENTIRE prior source bytes: all49 active statements/original provenance,
all44 proofs/listings/literals exact. The infinite-cardinal inference
gap is reported on #5 BEFORE any concordance and independently confirmed
by Claude5051; it refutes an inference, not the generic-over-E target.
The original source statement/proof wording remains unchanged.

The coordinate-ring prime-extension brick is now proved. #11 remains
closed with exactCI37802455841 FULL GREEN. Full generic extension,
ambient automorphisms, composition, arbitrary initial charts, actions/
classification/schemes, extraction and all reconstruction completeness
remain open. Frozen117 is unchanged. Final required full library/book
AFTER this ACTUAL factual append precede commit/push. The durable goal
continues.


## Constructive generic points and coordinate subfamilies (#5)

Pinned to clean published999a9e251aa59f8969204fc502dffd0f83dabdff.
Geometric-prime CI37810708544 is FULL GREEN in both jobs and EVERY
library/book/deployment step. Six owned reports/bodies and all21 current
#6/#27 body-owner references are reconciled; #5 stays open, #11 closed.
Chit5065/5068 report that checkpoint. The durable goal remains active.

PLAN5069 initially referred to a pin harness that failed on nonexistent
lakefile.lean before producing artifacts. Correction5071 precedes reads;
guarded5072 confirms22 SHA256 pins with inventoried lakefile.toml instead.
No main/source change. Claude5073 confirms the flatness route true/minimal.
Its first pin hashing attempt used SHA1, then reran SHA256. Its precise
actual read ledger, including inherited reads and explicit NOT-read files,
is copied to the private lane. Hashes do not imply files were read.
Root's actual bounded reads/searches are in separate private ledgers.
Root alone owns Lean/Lake/main; peer remains independent read-only with
no source/build GO. No children or frozen-wrapper normalization chain.

ONE public exists_genericPoint_baseChange constructs K:Type(max v z),
an E/k field tower and b from ANY original tuple a:ι→F over ACF k.
E/F/variables are arbitrary with independent universes. Its E ideal is
EXACTLY the extended original ideal and its k ideal EXACTLY the original.
EVERY coordinate subfamily independent over k remains independent over E.
The caller supplies no prime/domain/exact-ideal/density/point/freeness
oracle. Three private helpers are consumed: kernel_fraction_tuple,
contraction and independent_tensor. The latter permits commutative-ring
E/A over field k: flatness preserves E⊗aeval injectivity, and polynomial
tensor equivalence gives independence of1⊗x. In the public proof the
quotient coordinate subfamily is k-independent via kerLiftAlg; quotient
and polynomial tensor equivalences carry it to the fraction-field tuple.
Primeness comes from the preceding checked GeometricPrime theorem.
There is no infinite-cardinal cancellation.

API SEVENTH passes4.00 s/min35.09 GiB, EMPTY log. SIX failed source/
log/metric triples remain retained. Repairs use E-linear identity on
the left tensor map, explicit k evaluation arguments, function equalities
and quotient/coercion boundaries, and the missing unnamed-section end.
No checking option or heartbeat budget changes. The production source
FIRST passes2.00 s/min37.23 GiB, EMPTY. It adds only header/module docs
and four declaration docstrings to the accepted mathematical source.

The PRIVATE actual GenericSubfamilies consumer has TWO examples and ONE
consumed private FIXTURE helper, never production. It derives maximal
coordinate independence via cross-ambient ideal equality/comap(rename)
and restrictScalars. It also starts from the explicit repeated tuple(x,x),
derives an E-independent singleton, retains b0=b1 and proves BOTH original
and new WHOLE tuples not independent. No caller prime/domain/exact-ideal/
point/freeness oracle or cross-ambient call to the old racl lemma.
FIRST failure and eight letI style notices are retained; composition/set
types and singleton proofs are made explicit and letI becomes plain let.
SECOND passes2.00 s/min35.72 GiB, EMPTY. Actual production-import consumer
passes2.00 s/min37.35 GiB, EMPTY, with ONLY its API import replaced.

Claude5080 ACCEPTS full205-line producer/full93-line consumer and the
API-to-producer diff. Its new4pins are verified; Maps is NOT read. The
only nits are the already-prepared production import and an apparently
unused MvPolynomial.Ideal import. Removing ONLY that import gives204
lines, all at most100 wide, rechecked2.00 s/min37.55 GiB EMPTY.
Scoped metadata FIRST failed its Python harness's stale1-private flag
count, with correct4theorem SIG rows. Harness/source/log retained; ONLY
the count is repaired to3private/1public. SECOND passes4.00 s/min37.55
GiB: FOUR SIG/proof records, ONE PUBLIC AX, generated0 IN THE NEW audited
scope and only standard Lean axioms there. This is not a whole-library
certificate. Post-import-trim metadata4.00 s/min37.41 GiB proves ALL
TYPE/RAW/ATTR/DOC/AX/proof rows BYTE-EXACT. All diagnostic genres/options
are unchanged; new source and actual examples are warning-free under
standard Mathlib lint and default kernel. Book uses canonical Verso genre.

Exactly FIVE paths are proposed: new GenericExtension, ONE aggregate
import, Book import/account/public docstring and ONLY the named old
coordinate-basis status prose, ONE concordance paragraph with clearpage
FROM FIRST proposal, and append-only CONT. All263 earlier Math/Main
sources/dependencies/frozen117 remain exact. Original whole source bytes
are recovered by removing the new concordance: source49/provenance,
44proofs/listings/literals exact. The previously reported absolute
transcendence-degree inference gap remains documented with original wording.

The coordinate form of generic-extension(a) is proved. Explicit rank/
dimension, rational-field freeness and algebraically closed ambient
bridges, automorphisms(b), rational identity(c), the full lemma, C2
composition, arbitrary initial charts, actions/classification/schemes,
extraction and all reconstruction completeness remain open. Frozen117
unchanged. Canonical root/Book/source/views, all117 earlier fixture bytes/
scoped records and four new checks, full library/book, actual factual
acceptance append, peer review and final full/book precede commit/push.
The durable goal continues.


FIRST four-pass source rendering is stable78 pages but fails one overfull
hbox82.4625pt in ONLY the new paragraph5690-5706: its long theorem identifier
runs past the right margin. First source/pins/PDF/logs and actual page77
image are retained; page77 was ACTUALLY inspected before any repair.
ONLY the new identifier is put on its own line with paragraph breaks.
Original whole source bytes remain recoverable, clearpage from FIRST
proposal stays, and no old statement/proof/other-page text is edited.
Re-render/current visual acceptance follows; no failed view is accepted.


SECOND four-pass source render is stable78 pages with no overfull/undefined
errors. EIGHTEEN current selected views are accepted: FIFTEEN prior ACTUAL
page images BYTE-EXACT, plus pages3/77/78 ACTUALLY inspected after the repair.
Contents, the entire new paragraph/identifier and bibliography are clear,
complete and unclipped. The FIRST failed source/page77 is excluded from
acceptance and retained; only new identifier paragraph breaks repair layout.


Actual constructive generic-point acceptance: Claude5080 ACCEPTS the
producer and both real consumers;5083 resolves the two import notes;
5086 ACCEPTS the initial five paths and5090 the final new-layout/CONT
deltas. Actual full lake build passes54.02 s,
minimum available33.15 GiB/RSS8.42 GiB;
lake exe book passes10.00 s,
minimum available35.01 GiB/RSS1.54 GiB.
ALL121 strict actual-main checks pass162.04 s,
minimum available33.23 GiB/RSS2.92 GiB.
ALL117 older fixture BYTES and scoped TYPE/RAW/ATTR/DOC/AX/proof/deny
records stay EXACT, including Regular13, RegularACF4/1 and geometric-prime
2/1 records and both earlier actual point/common-field consumers.
The NEW audited scope has FOUR SIG/proofs and ONE PUBLIC AX,
one public/three CONSUMED private, generated0 IN THIS audited scope
and standard Lean axioms only there. No whole-library certificate.

The public constructive theorem derives exact ideals over k/E and
preserves EVERY coordinate-independent subfamily, over ACF k and
arbitrary E/F/variables at independent universes. It uses the checked
geometric-prime producer, faithful flat contraction and flat tensor
evaluation, not caller prime/domain/exact-ideal/density/point/freeness
oracles. The PRIVATE TWO-example/ONE-helper fixture derives maximal
coordinate independence over E and tests(x,x): its singleton remains
independent, b0=b1 is retained, and BOTH whole tuples are proved NOT
independent. The fixture helper is never production. Subfamily ideal
comparison is cross-ambient; the old single-ambient racl lemma is not
used across fields. No infinite-cardinal cancellation or TYPE changes
to older declarations.

All263 older mathematical/Main sources, dependencies and frozen117
stay exact. Root/Book each add ONE import. Book adds the new account
and public docstring and repairs ONLY the named old coordinate-basis
status. Hygiene265 has no placeholders/project axioms. HTML104 retains
all103 old paths and adds the coordinate-subfamily section, with actual
new docstring and chart/frozen pages visible. ALL711 historical full/book
warning headers remain BYTE-EXACT with no source-position change or
suppression. New mathematics and actual examples are warning-free under
standard Mathlib/default kernel; diagnostics keep their prior genres.

Canonical FIRST root/Book passes32.02 s/min35.18 GiB, only TWO CHECK/
PASS pairs with proper Verso Book genre. Complete Math263+ALL1315cache
and Book15+ALL75cache namespaces are supplied, with compiled-source
cache links unlinked before writing. The final producer has204 lines,
one public/three private, all at most100 wide. The peer's unused-import
trim rechecks2.00 s and all4/1 metadata records remain BYTE-EXACT at
4.00 s. The SIX failed API attempts, first consumer failure/eight letI
notices and stale-count metadata harness failure stay retained; explicit
scalar/evaluation/coercion/subtype boundaries, section closure and plain
let/count repairs suffice, without weakened checking options or budgets.

Source SECOND four-pass rendering is stable78 pages. EIGHTEEN current
views are accepted: FIFTEEN older ACTUAL PNGs BYTE-EXACT and3/77/78
ACTUALLY inspected after repair, clear/complete/unclipped. FIRST source
is stable78 pages but its new identifier overflows82.4625pt; source/PDF/
logs/page77 are retained and ACTUALLY inspected before the repair,
excluded from acceptance. ONLY new identifier paragraph breaks repair
it; clearpage is attached FROMFIRSTproposal. RemovingONEconcordance
recovers ENTIRE previous source bytes, all49 active/original-provenance
statements and44 proofs/listings/literals exact. The original absolute
transcendence-degree inference gap remains reported and wording retained.

The coordinate form of generic-extension(a) is proved. Explicit rank/
dimension, rational-field freeness and algebraically closed ambient
bridges, automorphisms(b), rational identity(c), full generic-extension,
C2 composition, arbitrary initial charts, actions/classification/schemes,
extraction and all reconstruction completeness remain open. #5 remains
open and #11 closed; frozen117 unchanged. Peer final actual-append review
and mandatory final full library/book AFTER this actual factual append
precede commit/push. The durable goal continues.


## Universal genericity and rational-field freeness (#5)

Base clean published e7a73565b8d7444f80aeae3d80f8901cf837c951,
exactCI37817070674 fully green in both jobs/every step. Six owned reports/
bodies and all22 current owners are reconciled; #5 open/#11 closed.
The durable goal remains active. Root owns sole Lean/Lake/main, peer
read-only; no children or frozen normalization/packaging chain.

READ-ONLY PLAN5110 starts with27 SHA256 pins. Claude5112 confirms common
ACF field existence feasible, but root5115 distinguishes existence from
the original UNIVERSAL generic-over-E implication. Claude5116 agrees the
universal implication true/preferable and requests fraction APIs BEFORE
extra reads/drafting. Supplement5121 verifies four actual paths(twoNEW)
before bounded reads: Localization/Module1-75/145-205, Adjoin/Algebra1-75,
FieldLD235-261 and AdjoinDefs30-65. Claude5123 confirms NO ACF is needed:
LinearIndependent.iff_fractionRing and scoped algebraAdjoinAdjoin provide
the exact upgrade from coordinate-ring to rational-field independence.

Structural route5124/5126 uses quotient evaluation to transport include_range
linear disjointness, rather than a common-field packaging chain or hand
clearing of finite denominators. Eval supplement5125 has ONE actual full
path plus descriptive permitted-read key; Claude5127 verifies that full
SHA256 and reads698-724. It is not a second missing source pin.
The range_comp supplement5130 pins TWO actual files: Subalgebra/Lattice
240-263 and Basic547-562. Root read them; peer did NOT read that optional
supplement. Actual root and precise peer read ledgers, including inherited
and NOT-read scopes, are copied privately. Pin checks do not imply reads.

Root-only private probe GO5128. Its initially reported Math263/1315cache
inventory was the previous-before-addition count; correction5129 precedes
proof/review claims. Actual FULL current overlay is Math264/ALL1320cache
and Book15/ALL75cache, with compiled-source cache links unlinked before
writing. No main/cache write-through or partial namespace shadow.

ONE new public isGeneric_baseChange has literal named genericity premise
hgen: ideal_E(b)=I.map(coefficientMap). For EVERY such point, it DERIVES
ideal_k(b)=I and linear disjointness of E-image from k(b), over ARBITRARY
fields/variables and with NO ACF assumption. No primality/domain/dimension/
freeness premise is hidden. Existing contraction is reused directly via
co-location in GenericExtension; every old declaration SOURCE BLOCK and
all old four SIG/proof plus one public AX TYPE/RAW/ATTR/DOC/deny records
stay EXACT. No old declaration type, proof, docstring or flag changes.

ONE new CONSUMED private subalgebra_disjoint_of_generic builds the tensor
quotient/polynomial equivalence into E[X]/ideal_E(b), uses kerLiftAlg for
injective evaluation, and calculates i(x tensor pbar)=x*p(b). The two
factor images become E-image and Algebra.adjoin k(range b); include_range
maps along the injective evaluation. A basis of E-image stays independent
over the coordinate ring, then iff_fractionRing promotes it to k(b).
IntermediateField.LinearDisjoint.of_basis_left concludes field freeness.

API FOURTH passes4.00s/min32.29GiB, EMPTY. THREE failed sources/logs/metrics
retained: explicit idealOf/kernel and mk_AlgHom coercion boundaries and
range_comp rewrite direction are repaired; one unused-simp notice goes
away by removing that argument. No kernel/lint option or heartbeat budget
is weakened. Production FIRST passes4.00s/min32.73GiB EMPTY,327lines/all
at most100 wide. Existing declarations stay byte-exact; only two imports,
module prose and new declaration docstrings accompany the new mathematics.

The PRIVATE real GenericClosedPoint consumer has TWO examples and ZERO
fixture helpers. It DERIVES hgen via exists_genericPoint_baseChange,
embeds SAMEb into AlgebraicClosure K, preserves E-ideal via E-algebra
embedding, and applies the universal theorem IN that closed ambient.
It derives both exact ideals and FULL rational-field LD, while preserving
EVERY coordinate-independent subfamily, at four independent universes;
Omega:Type(max v z). Caller supplies no prime/domain/exact-ideal/point/
freeness oracle. Its second arbitrary-base-field affine-space example
DERIVES hgen with I=bottom from independence over E, then derives k
independence and LD. No ACF assumption in that universal consumer.
FIRST consumer fails on implicit k; explicit k repairs it. SECOND checks
2.00s with ONE long-line notice, retained; ONLY line wrapping repairs it.
THIRD passes2.00s/min33.82GiB EMPTY. Actual PRODUCTION IMPORT consumer
FIRST passes2.00s/min33.42GiB EMPTY; ONLY import differs from checked API.

Metadata FIRST passes4.00s/min33.01GiB. Full co-located module totals
SIX SIG/proofs and TWO public AX; the NEW audited scope is TWO SIG/proofs
and ONE public AX(one public/one consumed private), generated0 there and
standard Lean axioms only there. All four older SIG/proofs/one AX records
and deny entries stay BYTE-EXACT. No whole-library certificate. Diagnostic
genres/options stay exact; new producer/examples standard Mathlib/default
kernel warning-free. Book uses canonical Verso genre, without Mathlib
hash-command lint.

Claude5136 ACCEPTS producer and both real consumers, no findings. Actual
reads:9pins SHA256, producer DIFF against main(all added math/doc changes),
FULL production consumer, heads of metadata/consumer acceptance and new
signature TSV. API/production acceptance bodies, Axioms/Proofs TSV and
optional range_comp supplement NOT read. Unchanged mathematics is not
claimed reread. The precise ledger is retained.

Exactly FOUR proposed paths: extend GenericExtension(no old declarations
changed), Book new account/docstring plus TWO named obsolete status clauses,
ONE source concordance with clearpage and identifier paragraph breaks FROM
FIRST proposal, and append-only CONT. Aggregate/root imports already expose
the co-located theorem; root bytes stay exact. All263 OTHER Math/Main
sources, dependency pins/frozen117 exact. Removing ONE new concordance
recovers the ENTIRE old source bytes: original49active/provenance/raw
historic statements,44proofs/listings/literals exact. Both earlier reported
proof-inference gaps remain visible; original wording is retained.

Constructive existence plus this UNIVERSAL relation/field-freeness theorem
cover source(a)'s content, including the SAMEpoint in an ACF ambient.
Explicit rank/dimension statements, automorphisms(b), rational identity(c),
the full generic-extension lemma, C2composition over nonACF k(W), arbitrary
charts/actions/classification/schemes/extraction and ALL reconstruction
completeness remain OPEN. Frozen117 unchanged. Canonical root/Book/source
views, full library/book, all121 older fixture bytes/scoped records plus
new scope/consumer, actual factual append/peer/finalfullbook precede commit/
push. The durable goal continues.


Actual universal-genericity acceptance: Claude5136 ACCEPTS the new producer
and TWO real consumers;5139 ACCEPTS the four paths, no findings. Actual
full lake build passes54.01s/min34.18GiB/
RSS8.23GiB; lake exe book passes10.00s/
min36.05GiB/RSS1.55GiB.
ALL125 strict actual-main checks pass166.04s/
min34.70GiB/RSS3.21GiB.
ALL121 older fixture INPUT BYTES and SCOPED TYPE/RAW/ATTR/DOC/AX/proof/
deny records stay EXACT. The older GenericExtension diagnostics retain
all4SIG/proofs1AX exact; ONLY the TWO named new theorem records are added
to its co-located module output. Full module6SIG/proofs2AX, NEWscope2SIG/
proofs1AX(onepublic/oneCONSUMEDprivate), generated0/scopedstandardaxioms.
No whole-library certificate. Existing declaration blocks are unchanged.

The universal producer takes ONLY the literal named E-ideal genericity
hypothesis and derives exact contracted k-relations/full rational-field
linear disjointness for EVERY such point, over arbitrary fields/variables
and with NO ACF assumption. It transports include_range along injective
quotient evaluation, then promotes a basis via iff_fractionRing; existing
contraction is directly reused. The private TWO-example/ZERO-helper real
consumer DERIVEShgen from constructive existence, embeds SAMEb into an
algebraic closure, and applies the universal implication IN that ambient.
Both exact ideals/fullfieldLD/allcoordinateAI survive at independent four
universes. Its arbitrary-base affine-space example DERIVEShgen from E-AI.
No caller prime/domain/exactideal/point/freeness oracle in the constructive
consumer. New producer/consumers default kernel/standardlint warning-free.

Exactly FOUR paths: GenericExtension new math/module prose/TWOimports with
ALL old declaration source blocks/records exact; Book newaccount/docstring
and TWO named obsolete status clauses ONLY; ONEconcordance inserted before
bibliography; append-onlyCONT. Root already imports the module and stays
EXACT. All263OTHERMath/Main/dependencies/frozen117 exact. Hygiene265 has
no placeholders/projectaxioms. HTML105 retainsALL104oldpaths, newdocstring
and existingchart/frozen pages visible. ALL711oldfull/bookwarningheaders
BYTE-EXACT; no suppression/source-position changes.

Canonical root/Book FIRST20.01s/min35.40GiB, onlyTWO CHECK/PASSpairs,
properVersoBookgenre/noMathlibhashCommandlint. Actual FULL overlay is
Math264/ALL1320cache and Book15/ALL75cache; compiled-sourcecachelinks
unlinked before writing. Producer327lines/allatmost100wide; metadata4s,
old4/1exact/new2/1. THREEfailedAPI attempts/firstconsumerfailure/second
longlinenotice retained; explicit kernel/quotient/map/scalar boundaries,
explicitk and wrapping repair them, with no weaker checking options.

FIRST source four-pass render stable79pages, NO layout/undefined/rerun
errors and no repair needed. ALL19 current selectedviews accepted:
SIXTEEN older ACTUAL PNGs BYTE-EXACT[1,2,4,5,6,67-77], plus3/78/79
ACTUALLYviewed contents/newconcordance/bibliography clear/complete/unclipped.
Clearpage/identifierparagraphbreaks attached FROMFIRSTproposal. Removing
ONEconcordance recovers ENTIREprevioussourcebytes/all49active and original
provenance/rawhistoricstatements/all44proofs/listings/literals EXACT.
Both reported source-inference gaps and original proofwording retained.

Relation/independence content(a) covered: constructive existence,
UNIVERSAL implication and SAMEpointACFambient. Explicit rank/dimension,
automorphisms(b), rational identities(c), fullgeneric-extension/C2over
nonACF k(W), arbitrary charts/actions/classification/schemes/extraction/
ALLreconstructioncompleteness remainOPEN. #5open/#11closed; frozen117
unchanged. Peeractualappendreview and mandatoryfinalfull/book AFTERthis
actualappend precede commit/push. Durablegoal continues.


## Existing generic-point clauses: audit before new code (#5)

Base clean published 0332dd3ae901e2c5215ab294d981a40abfa140d2;
exact CI37822933827 succeeded in both jobs and every step. Six owned
reports/bodies and all23 body owners are reconciled. #5 remains open,
#11 remains closed; the durable goal continues. Root owns sole main/
Lean/Lake; peer aclgeom.claude remains read-only, with no source/build GO.

READ-ONLY PLAN5149 starts with18 SHA256 pins. The candidate new rational-
field producer is DROPPED BEFORE ANY DRAFT after the existing-work audit.
Supplement5151 pins FamilyCover/FunctionField/quotient Operations;
Claude5154 reads FamilyCover1-70/390-420/745-800 and FunctionField1-15,
NOT Operations. Supplement5156 pins Family1-38/130-269; Claude5157
confirms that locusFunctionFieldEquivOfIdealEq and its coordinate law
already prove (b)'s FIRST clause, for arbitrary fields/index types in the
source's common ambient. Its refl/symm/trans laws are already proved.
No cross-ambient generalization, new producer or TYPE migration is needed.

Supplement5160 pins four actual paths; Claude5161 reads Mathlib's
AlgebraicIndependent/Adjoin1-75 (actual file74 lines), GenericPoints1-125
and RationalFunctions1-40. AlgebraicClosureTransport is NOT read.
Mathlib's aevalEquivField already proves literal (c): canonical rational
evaluation at an independent tuple is an isomorphism onto its generated
field. GenericPoints already consumes it. Root reads Adjoin1-74 and the
same two project spans. Root's first bounded reader fails IndexError on
the short file before emitting API contents or writing its ledger;
min(len) repairs the reader only, with no source/build failure. Precise
root/peer ledgers distinguish pin verification, actual and NOT-read scopes.

Root-private consumer/compiler GO5162. FULL overlay Math264/ALL1320cache
and Book15/ALL75cache; compiled-source links unlinked before writing.
The 52-line ExistingGenericClauses consumer has THREE real examples and
ZERO helpers: (b)-FIRST derives equal ideals from an actual embedding
then uses the existing equivalence and coordinate law; literal (c)
reflects genuine fraction equality while DERIVING BOTH denominators
nonzero from actual independence; the third reflects zero under the
canonical fraction lift. Arbitrary fields/variables, no ACF assumption
or caller injectivity/field-isomorphism oracle. FIRST check passes2.00s/
min34.83GiB, EMPTY, default kernel and standard Mathlib lint; no repair.
Claude5165 ACCEPTS after checking all3 pins and reading the FULL52-line
consumer; acceptance/overlay JSON bodies are NOT read. Optional second-
point suggestion is nonblocking; the accepted consumer is retained.

ZERO mathematical source/dependency changes and ZERO new declarations.
All264 Math/Main sources, aggregate root, dependency pins and frozen117
stay byte-exact. The prior125 fixture INPUTS and scoped OUTPUTS are
retained byte-exact, NOT rerun for this documentation-only checkpoint;
Claude5165 agrees the gate policy. The newly checked three-example
consumer is added to the future126-fixture baseline. Retention is not a
claim of126 fresh checks or a whole-library mathematical certificate.

Exactly THREE paths are proposed: Book adds citations of existing
function-field/Mathlib APIs and updates ONE obsolete status clause;
source inserts ONE concordance before bibliography, with clearpage and
identifier paragraph breaks FROM FIRST proposal; CONT is append-only.
Original49 active statements, all original provenance/historic statements,
44 proofs/listings/literals and the reported source gaps stay unchanged.

The source's (b)-FIRST field-isomorphism clause and literal (c) are
accounted for by already proved APIs and fresh actual consumers. The
ambient-automorphism/enlargement SECOND clause of (b), explicit rank/
dimension, full generic-extension lemma, C2 composition over nonclosed
k(W), initial charts, actions/classification/schemes/extraction and ALL
reconstruction completeness remain open. Frozen M4a is unchanged.
Canonical root/Verso Book, source rendering/views, full library/book,
HTML/hygiene/retention, factual append/peer and final full/book AFTER the
actual append precede commit/push. The durable goal continues.


Actual existing-generic-clause audit acceptance: Claude5165 ACCEPTS the
three real consumer examples;5172 ACCEPTS the three documentation paths;
5174 ACCEPTS the ONE Book-only import repair. Full lake build passes
44.01s/min33.78GiB/RSS8.36GiB;
lake exe book passes10.00s/min35.68GiB/
RSS1.51GiB. ALL711 historical warning headers stay BYTE-EXACT
in both actual logs. Hygiene265 has no placeholders/project axioms;
HTML106 retains all105 old paths and exposes both existing docstrings,
with chart/frozen pages visible. All264 mathematical/Main sources,
aggregate root/dependency pins/frozen117 are byte-exact.

The prior125 fixture INPUTS and scoped OUTPUTS are retained byte-exact
in both the original and copied future baseline, NOT rerun for this
documentation-only checkpoint. ONE fresh actual check validates THREE
real examples under unchanged production imports, default kernel and
standard Mathlib lint: derived ideal equality and coordinate isomorphism,
genuine fraction identity with BOTH denominators derived nonzero, and
canonical fraction-lift zero reflection. Its first2.00s log is EMPTY.
Future baseline126 includes that accepted consumer. No126-fresh-check
or whole-library axiom certificate claim; ZERO new mathematical declarations.

Canonical FIRST root passes, Book fails only because Family is not
imported. Failed Book source/log/metrics are retained. ONE Book import
AclGeom.Correspondence.Family repairs resolution; SECOND canonical root/
proper Verso Book passes20.00s/min35.70GiB/
RSS3.60GiB, only TWO CHECK/PASS pairs. No Mathlib hash-command lint
on Verso Book, weakened checking options or source proof changes.
Claude5174 reads only the one-line delta and failed-directory inventory;
failed logs/metrics and queued/proposed JSON bodies are NOT read by peer.

Source FIRST four-pass render is stable80 pages, with no layout/undefined/
rerun errors and no repair. ALL20 current selected views are accepted:
SEVENTEEN older ACTUAL PNGs byte-exact[1,2,4,5,6,67-78], plus3/79/80
ACTUALLY inspected clear/complete/unclipped. Clearpage and identifier
paragraph breaks attach FROM FIRST proposal. Removing ONE concordance
recovers ENTIRE old source bytes, all49 active/original-provenance/raw
historic statements and44 proofs/listings/literals exact. Original
wording and the reported proof-inference gaps are retained.

Exactly THREE paths: Book new account/TWO existing docstrings/ONE named
obsolete status clause/ONE import; source ONE pure concordance insertion;
CONT append-only. Claude5172 checks7 pins and reads the three diffs plus
bounded context/citation greps; queued/proposed/read-ledger/copied-peer
ledger bodies are NOT read, and transitive imports are not audited there.
Pin verification is not a claim of full-file mathematical rereading.

The already proved first(b) field-isomorphism and literal(c) rational-
identity clauses are accounted for; the proposed duplicate was dropped
BEFORE drafting. Second(b) ambient automorphism after possible enlargement,
explicit rank/dimension, full generic-extension/C2 over nonclosed k(W),
initial charts/actions/classification/schemes/extraction and ALL
reconstruction completeness remain open. #5 open/#11 closed; frozen117
unchanged. Peer actual-append review and mandatory final full/book AFTER
this actual factual append precede commit/push. Durable goal continues.


## Ambient automorphisms of finite generic points (#5)

Base clean published 58bdf10198161c1200e310825ae9772693b611dd;
exact CI37827082206 succeeded in both jobs/every step. Six owned
reports/bodies and all24 current owners are reconciled. #5 open/#11
closed. Root owns sole main/Lean/Lake; aclgeom.claude is read-only,
with no source/compiler GO. The durable goal continues.

READ-ONLY PLAN5179 has14 SHA256 pins. Claude5185 verifies all14 before
bounded reads and confirms the target TRUE for FINITE index types,
ANY base field and a common ACF ambient: equal ideals give a full
generated-field-isomorphism extension to an ambient k-automorphism.
The cancelled transcendence-degree summand is FINITE. No cancellation
of an infinite base summand occurs. No source error or infinite-index
target is proposed. The source's finite-dimensional variety supports
finite tuples; the packaged variety-level statement remains separate.

Supplement5181 verifies4 NEW paths, with FG/EssFiniteType and polynomial
coefficient/rename APIs. Claude5188 accepts the finite-field route.
Supplement5186 has TWO EXISTING paths with NEW bounded scopes, NOT two
new paths: Family280-350 and TranscendenceBasis230-252. Claude5189
confirms the EXISTING adjoinIndependentEquivOfEquiv and its FULL base
law already provide the semilinear relative-field bridge. The proposed
new coefficient/renaming bridge is DROPPED BEFORE drafting.

Two separate264-source hash manifests authorize ONLY five and then
three exact repo-wide name/occurrence inventories. Claude5192/5195
performs the same inventories and finds no duplicate in those literal
forms; automorphisms written with other variable names are not covered
by those patterns. Supplement5190 gives4 NEW paths: bounded lattice-rank
Transport and abstract normal-closure FiniteCover hits, Cardinal.eq and
transcendence-basis comp_equiv. Supplement5196 givesONE NEW FamilyCover
path with230-335 consumer scope; Claude5197 confirms its only old bridge
consumer proves pair-ideal transport, not an ambient automorphism.
Precise root/peer ledgers distinguish pin checks, actual/NOT-read scopes
and inherited continuation context. THREE tool packets fail SyntaxError
before ANY nested tool runs; temporary script/message files repair the
orchestration only, with no source/build effect. One earlier guessed
Closure/AlgebraicClosureTransport path is absent; rg exits2, then the
correct Correspondence path is located via rg --files before actual reads.

Root-private producer/compiler GO5201. Full CURRENT-main overlay is
Math264/ALL1320cache and Book15/ALL75cache. Adding the private probe and
its compiled olean gives265 sources/1321 cached files, NOT1325 yet;
all current main sources/cache are retained. Root/Book compiled-source
links are unlinked BEFORE writing. No write-through or partial shadow.

ONE new public exists_ambientAutomorphism_of_idealOf_eq, ZERO helpers:
finite FG/EssFiniteType derives finite degree; the existing field iso
gives equal degree; the tower formula and FINITE cardinal cancellation
give equal relative-basis cardinality. Bases are chosen and reindexed
by Cardinal.eq/comp_equiv. Existing adjoinIndependentEquivOfEquiv extends
the field iso across them. isAlgebraic_field makes the common ambient an
algebraic closure of each relative field; IsAlgClosure.equivOfEquiv and
its base equation give a k-algebra automorphism extending the ENTIRE old
field iso and carrying every coordinate. No caller rank, basis, algebraic
extension or automorphism oracle; no ACF assumption on the base.

API FIRST fails2.00s on the implicit ambient argument of trdeg_add_eq,
with3 Prop-instance letI style notices; source/log/metrics retained.
Explicit A := Omega and plain let repair ONLY those boundaries. SECOND
passes2.00s/min36.09GiB EMPTY. Production FIRST4.00s/min34.94GiB EMPTY.
Metadata FIRST4.00s/min34.71GiB: ONE SIG/proof/public AX, ZERO generated
records in the new audited scope, standard Lean axioms only there.
Diagnostic genres/options are preserved except target module; no whole-
library certificate. No set_option or increased checking/heartbeat budget.

TWO real private examples/ZERO helpers,45 lines. Existing relocation
uses EXPLICIT ht/hle/halg/hs; its basis, independence and algebraicity
premises are not silently derived. It DERIVES the second point and exact
ideal, then full field extension/coordinate automorphism at SAME point,
retaining algebraicity over the prescribed relocated field. Second example:
an actual endomorphism of ANY nonclosed ambient supplies equal relations;
embedding into AlgebraicClosure derives equal ideals there and obtains
an automorphism matching the FINITE displayed points. No caller second
point/exact ideal/rank/automorphism oracle in the relocation consumer.
FIRST consumer fails ONLY on missing concrete AlgebraicClosure import;
failed source/log/metrics retained. ONE import repairs; SECOND2.00s/
min35.16GiB EMPTY. New mathematics/examples standard lint/default kernel.

Claude5206 ACCEPTS all10 actual pins, FULL86-line producer/FULL45-line
consumer, single AX/SIG rows, top-level production/consumer JSON keys,
and line widths. Proofs TSV body, metadata/read-ledger/overlay JSON bodies
are NOT read. Root adopts ONLY the suggested module source-of-truth/
Status prose:95 lines, all declaration blocks and1SIG/AX/proof EXACT.
Production SECOND4s and unchanged consumer THIRD2s pass EMPTY. Metadata
SECOND4s has only THREE PASS lines, warning-free; all mathematical/type/
docstring/attribute/proof records stay exact.

Exactly FIVE proposed paths: NEW AmbientAutomorphism, aggregate root
ONE import, Book ONE import/new account/SIX named status or historical-
tense clauses, source ONE concordance, append-only CONT. All264 older
mathematical/Main sources, dependencies and frozen117 stay byte-exact.
Removing ONE concordance recovers the ENTIRE old source and all49 active/
original-provenance/historic statements,44 proofs/listings/literals exact.
The source's finite field content of(b) is covered; explicit rank/dimension,
the packaged variety-level lemma, C2 over nonclosed k(W), initial charts,
actions/classification/schemes/extraction and ALL reconstruction completeness
remain open. Canonical root/Verso Book/source views, full library/book,
ALL126 older actual-main fixtures/scoped records plus FOUR new checks,
factual append/peer/final full/book AFTER append precede commit/push.
Frozen M4a is unchanged. The durable goal continues.


Actual ambient-automorphism checkpoint acceptance: Claude5211 verifies
all10 five-path pins and ACCEPTS the producer +9 module-prose-only delta,
ONE root import, Book ONE import/account/SIX named clauses, source ONE
concordance and104-line prefix-exact CONT append. It reads those diffs
and widths, NOT queued/proposed/metadata/production/consumer JSON bodies.
Only its precise Book sentence is adopted: the second point comes from
relocation or the given endomorphism; no caller exact ideal/rank/auto.
No mathematical declaration changes follow Claude5206.

Canonical FIRST root/proper Verso Book passes20.00s; after that ONE
Book prose sentence, SECOND passes20.00s/min35.83GiB/
RSS3.55GiB, only TWO CHECK/PASS pairs. No weakened lint/options,
Book hash-command lint or increased checking budgets. Source FIRST
four-pass render is stable81 pages with NO layout/undefined/rerun error
and NO repair. ALL21 current selected views are accepted:18 older
ACTUALLY viewed PNGs byte-exact[1,2,4,5,6,67-79], plus3/80/81 ACTUALLY
inspected clear/complete/unclipped. Removing ONE concordance recovers
ENTIRE58bdf10 source, all49 active/original-provenance/raw historic
statements and44 proofs/listings/literals BYTE-exact. Prior gaps remain.

Exact FIVE paths integrated on clean58bdf10 AFTER peer/canonical/source
acceptance and fresh issue instruction check with unknown0. A preflight
ledger-heading assertion fails BEFORE copying any source; the exact
case-sensitive existing heading repairs ONLY that gate. One further
functions.exec packet fails SyntaxError BEFORE nested tools (FOUR total
in this lane); temporary files repair orchestration only. One too-broad
tmp filename inventory returns permission-denied exit2; no unrelated
file contents, credentials or account state are read/changed. Subsequent
inventories are restricted to task-prefixed top-level temporary files.

Full lake build passes54.01s/min33.99GiB/
RSS8.41GiB; lake exe book passes10.00s/
min36.00GiB/RSS1.52GiB. ALL711 historical
warning headers stay BYTE-exact in BOTH logs. Hygiene266 has no proof
placeholders/project axioms. HTML107 retains all106 old paths, the new
literal full-field-extension docstring, both old generic-clause
docstrings, chart/frozen pages. Old264 mathematics/Main/dependencies
and frozen117 remain BYTE-exact. Current-main compiled artifacts now
give Math265/ALL1325cache and Book15/ALL75cache; earlier1321 private
count is historical, NOT falsely described as1325 before compilation.

ALL130 FRESH actual-main sequential checks pass176.04s/
min35.95GiB/RSS3.20GiB. ALL126 older
fixture inputs and scoped TYPE/RAW/ATTR/DOC/AX/proof/deny records are
BYTE-exact, with no exception or stale private namespace. FOUR new
checks reproduce accepted ONE SIG/AX/proof and the EMPTY actual
45-line TWO-example consumer. ZERO helpers/generated records in the
new audited scope; standard Lean axioms only THERE, not a whole-library
certificate. Actual consumers use standard lint/default kernel; old
diagnostic genres/options stay exact. Relocation's ht/hle/halg/hs
basis/independence/algebraicity inputs remain EXPLICIT. The nonclosed
endomorphism consumer obtains a closure automorphism at the FINITE
tuple only, not an extension of the whole original endomorphism.

Finite field content of(b) is now proved: full existing rational-field
iso extends to a coordinate-preserving ambient k-automorphism for
FINITE tuples over ANY base in a common ACF. In a nonclosed ambient,
the checked consumer enlarges to its algebraic closure. No unchanged-
ambient infinite-tuple claim. Rank/dimension, packaged variety-level
lemma, C2 over nonclosed k(W), initial charts/actions/classification/
schemes/extraction and ALL reconstruction completeness remain OPEN.
#5 stays open/#11 closed; frozen117 exact; root sole main/compiler owner,
peer read-only. Actual-append peer review and mandatory final full/book
AFTER this factual append precede commit/push. Durable goal continues.


## Numerical generic-point degree after scalar extension (#5)

Base clean published da0144b424f4a7b921665b5df2ceea08aced5304,
exactCI37833355112 SUCCESS BOTHjobs/EVERYstep; sixownedreports/bodies
and ALL25 current body-owner refs reconciled. #5open/#11closed.
Root sole main/Lean/Lake; peer readonly, no source/compiler GO.

READONLYPLAN5220:14 actual pins,265-source hash-only manifest authorizing
ONLY four-pattern trdeg/ringKrullDim/krullDim/dimension inventory.
Claude5224 verifies all14+265hashes, finds same396hits/no duplicate,
and confirms TRUE for ANY fields/index, noACF/finiteness/cancellation.
Precise actual/inherited/NOTread ledger retained. Actual bounded reads
include old universal producer, LI/basis APIs and dimension dictionary.
CONTlast250/AGENTS/source1244-1286/Familylater scopes and selected older
Mathlib scopes are INHERITED, not falsely described as fresh rereads.
Before/readledger JSON and full396hit files are NOTread by peer.
Mathlib literal trdeg file inventory in RingTheory/FieldTheory/
AlgebraicGeometry has FOUR hits; combined LD-trdeg/Krull-trdeg name
inventory zero, NOT proof of absence in other terminology.

Supplement5222 verifies4 NEWpaths, Claude5225: Composition395-455
is ONLY a five-generator racl/AI fiber-product count, not generic
base-change degree; monomial basis, field algebraicity and nested-adjoin
APIs checked. Root prefers a SHORTER existing-closure route.
Supplement5230 has4 further NEWpaths, Claude5232 ACCEPT: old
LinearMap.injective_of_linearIndependent drops the proposed Finsupp/
basis-repr expansion BEFOREdraft. Old Closure.Ambient annihilator and
embedding-closure transport drop new nested-adjoin algebraic-tower
scaffolding BEFOREdraft. No Geometry.Transport import or new transport/
normalization/closure wrapper. Peer Closure.Ambient read1-98 only;
its proof ends99, so no full-proof read claim; root reads83-102 separately.

Root-privateGO5233. Full current namespace startsMath265/ALL1325cache,
Book15/ALL75cache. ALL GenericExtension source/cache links unlinked
BEFOREwrite. Other264sources/ALL1320cache preserved; modified397line
source+one compiledolean ->Math265/1321cached, NOT1325 untilmainLake
compile. No partial namespace or write-through. TWO orchestration
functions.exec packets SyntaxError BEFOREANY nestedtool; tempfiles
repair onlyorchestration, no source/build effect. Two guessed absent
paths Geometry/Basic and FieldTheory/Transcendence returnrgexit2;
actual RingTheory/AlgebraicIndependent paths are then located/read.

ONE new public trdeg_adjoin_of_isGeneric, ZEROnewhelpers. hgenDERIVES
FULLLD via oldisGeneric_baseChange; symmprime/fieldRange_val identify
the generated field's disjointness over E. A chosen k(b)-basis gives
monomial k-linear independence, preserved over E; OLD mapped-spanning-
family injectivity derives polynomial independence INLINE. OLD
ambient closure equivalence maps basis algebraicity into Omega. The
SAME ambient-coefficient annihilator, with coefficients in the larger
adjoin, gives algebraicity over E. OLD closure equivalence back into
E(b) and ring/fraction membership give a basis there. Both degrees are
the SAME cardinality. NoACF/finiteness/cardinal cancellation or caller
rank/basis/LD/algebraic-extension oracle. AllOLD6 mathematical
declaration/docstring blocks remain BYTEexact.

ProducerFIRST4.00s fails ONLY AI goal unfolding and the explicit basek
argument of the old adjoin_subset_adjoin_iff; failedsource/log/metrics
retained. ONLY those boundary repairs; SECOND4.00s/min37.43GiB/
RSS2.58GiB EMPTY. MetadataFIRST4.00s/min37.49GiB/RSS2.51GiB has THREE
PASS lines: fullmodule7SIG/7proof/3AX; ALL6oldTYPE/RAW/ATTR/DOC/proofs
and2AX EXACT. New1SIG/AX/proof/0generated in AUDITEDscope, standard
axioms only THERE; no wholelibrarycertificate. Diagnostic sources/
genres/options BYTEexact to prior UniversalGeneric files.

TWO real51line privateexamples/ZEROhelpers. Both START old actual
point construction, DERIVE hgen/baseideal, and use SAMEpoint. Shared-
universe example uses EXISTING coordinate-ring equivalences/quotient
equality/fraction-field primitive to derive a CROSS-AMBIENT field iso
to ORIGINALtuple. Relative degree equals ORIGINALlocus degree; the old
tower formula gives source absolute line. Four-universe example
derives relative degree atb and lifted absolute tower equation there.
No ALLuniverse original-a comparison is claimed in that second case.
ACFk is EXPLICITONLYfor oldconstruction; numericalproducer anybase.
No callerpoint/exactideal/LD/basis/rank/dimension oracle.
ConsumerFIRST2s missingopenAclGeom; SECOND2s onlyimplicitk stuck;
both failedtriples retained. ONEopen then explicitk repairs only;
THIRD2.00s/min36.46GiB EMPTY. Standardlint/defaultkernel, no
weakenedchecking options or increased budgets.

Claude5238 verifies10 actualpins/oldsource cmpmain and ACCEPTS new
producer diff2imports/prose/newblock328-393 + context34-49, FULL51line
consumer, ONEnewSIG/AX rows, keylists3acceptanceJSONs/widths.
Rest397line oldblocks, ProofsTSV body, readledger/overlay/failure
directories and acceptanceVALUES are NOTread. Root adopts ONLY prose
nits: drop leftover Explicit and tick two API names. ProducerTHIRD4s/
metadataSECOND4s/unchangedconsumerFOURTH2s pass; ALL7mathTYPE/AX/proof/
attrs exact, ONLYNEWtheoremDOC hash intentionally changes. All6old
DOCs exact. No mathematics changes after peer5238.

Exactly FIVE proposedpaths instead of initialfour: GenericExtension
2imports/moduleprose/ONEpublic theorem; AmbientAutomorphism ONLYone
module-status clause distinguishing numerical field degree from still-
open geometric/Krull dimension; Book newaccount/FIVE named status
clauses/NOimport; sourceONEconcordance; append-onlyCONT.
ALL Ambient mathematical blocks stay BYTEexact. Root/dependencies/
frozen117 unchanged; other263Math/Main sources BYTEexact.
Removing ONE concordance recovers ENTIREoldsource/all49active/
originalprovenance/rawhistoric statements/44proofs/listings/literals.

The numerical FIELDdegree of(a) is covered under the existing locus
dimension convention, not Krull/geometric dimension, packaged variety
frontend or a repair of the original independence inference. The
reported gaps/original proofs remain. C2overnonclosedk(W), initial
charts/actions/classification/schemes/extraction and ALL reconstruction
completeness OPEN. Canonical/root/Verso/sourceviews/fullbook/ALL130
older fresh checks plusFOURnew ->134checks, oldSCOPEDrecords exact
with ONLYtheONEnew accepted declaration added to existing Generic-
Extension module dumps, factualappend/peer/finalfullbook AFTERappend
precedecommitpush. Durablegoal continues.



Actual numerical-degree checkpoint acceptance: Claude5245 verifies
all10 five-path pins and ACCEPTS imports/prose/ONEnewpublic block,
AmbientAutomorphism ONLYmodule-status, Book ONEnewaccount/FIVE named
clauses/NOimport, source ONEconcordance +30/0, CONT111line whole-prefix
exact append. Reads producer accepted-to-proposed prose-only diff and
main diffs/AM19-30 context, CONTappend/widths/clearpages; NOT queued/
proposed/acceptance JSON bodies (hash-only). All peer scope/inherited/
NOTread references accurate. ONLY three nonblocking prose nits adopted:
lowercase original in Book, precise linear independence of evaluated
monomials rather than loose basis-preservation phrasing, and ticks on
GenericExtension in AMstatus. NO math/consumer change after Claude5238.

AMprose FIRST/SECOND2.00s EMPTY normal standardlint. Canonical FIRST
root/proper Verso Book passes20.01s; after prose nits SECOND passes
20.01s/min37.74GiB/RSS3.61GiB, TWO CHECK/PASS pairs.
No weakened lint/options, Book hash-command lint or increased budgets.
Source FIRST four-pass render is stable82pages, with NO undefined/
layout/rerun error and NO repair. ALL22selected current pages accepted:
19 older ACTUALLY viewed PNGs byte-exact[1,2,4,5,6,67-80], plus3/81/82
ACTUALLY inspected clear/complete/unclipped. Removing ONE concordance
recovers ENTIREda0144b source, all49active/original-provenance/raw
historic statements, all44proofs/listings/literals BYTEexact.
Reported original source gaps and proofs remain retained.

Exact FIVE paths integrated on clean da0144b AFTER peer/canonical/
source acceptance and fresh issue-instruction check with unknown0.
One broad /tmp filename-only rg returns exit2 for unrelated denied
directories and unrelated filenames; NO unrelated contents, credentials
or account state read/changed. Later inventories restricted to task-
prefixed top-level paths. FIRST fixture prep copies verified130older
fixtures/outputs plus newmetadata, then fails for misnamed consumer
log BEFORE pending/acceptance claim. Retained bytes checked BEFORE
retry; correct log from consumer acceptance. ONLY orchestration,
no Lean source/build effect. TWO earlier JS SyntaxErrors BEFOREtools
and two guessed missing paths remain recorded, not silently dropped.

Full lake build passes48.01s/min35.79GiB/
RSS7.48GiB; lake exe book passes8.00s/
min37.47GiB/RSS1.55GiB. ALL711 historical
warning headers BYTEexact in BOTH logs. Hygiene266 no proof placeholder/
project axiom. HTML108 retains ALL107 older paths and literal newdegree
docstring, previous generic-clause/field-freeness/finite-automorphism
docstrings, chart/frozen pages. Root/dependencies/frozen117 and other
263Math sources exact; ALL6older GenericExtension mathematical/docstring
blocks and ALL AmbientAutomorphism mathematics exact.
Before docs the Gen-only private phase was265/1321cache; unlinked
AMsource/ALL5cache then ownAMolean gave265/1317, NOT1325 before main
compile. Actual current main compile nowMath265/ALL1325cache and Book
15/ALL75cache; ownprivateoleans retained, missing metadata links restored.

FIRST fresh runner70.02s/min37.23GiB fails ONLYharness inference:
AX firstcolumn is AX, not module. Actual added record is precisely
the accepted named public. Explicit SIX oldmodulefixtures repair
that gate, retaining ALLold record/acceptednew row comparisons.
FIRST partialfixtures/outputs/log/metrics retained; no Lean change.
ALL134 SECOND FRESH actual-main sequential checks pass176.04s/
min37.75GiB/RSS2.92GiB. ALL130 older
INPUTbytes and scoped TYPE/RAW/ATTR/DOC/AX/proof/deny records exact;
ALL260 original baseline INPUT/OUTPUT files preserved. SIX older full-
module dumps (GenericExtension and UniversalGeneric, SIG/AX/proof)
add ONLY named accepted AclGeom.trdeg_adjoin_of_isGeneric row. No
false wholeTSV exact claim; no other addition/removal/record exception.
FOURnew fixtures reproduce accepted7SIG/3AX/7proof full-module records
and EMPTY actual51line TWO-example consumer; ONEnew SIG/AX/proof,
ZEROnew helpers/generated records in AUDITEDscope, standard Lean axioms
only THERE, not whole-library certificate. Defaultkernel/standardlint
actualconsumers; all older diagnostic genres/options unchanged.

Numerical FIELDdegree of generic-extension(a) proved over ANY fields/
indices from hgen; LD/basis/algebraicity derived, no finiteness/ACF/
cardinal cancellation. Real consumers construct SAMEpoint, derive
genericity/ideals; shareduniverse obtains ORIGINALlocus degree via old
cross-ambient coordinate/fraction equivalences and source absolute
line. Four independent universes yield lifted equation ATb only.
ACFk used ONLYby earlier point construction. No callerpoint/exactideal/
LD/basis/rank/dimension oracle. No Krull/geometric dimension bridge,
packaged variety frontend or repair of source's own independence
inference is claimed. The separate freeness route proves independence.
C2overnonclosedk(W), charts/actions/classification/schemes/extraction
and ALL reconstruction completeness OPEN; #5open/#11closed, frozen117
exact. Root sole main/compiler; peer readonly. Actualappend peerreview
and mandatory finalfull/book AFTER this append precedecommitpush.
Durablegoal continues.


## Shared evolving project goal (2026-10-13)

Adam requests a Markdown goal statement agreed by aclgeom.codex and
aclgeom.claude, and explicitly authorizes updates as the project evolves.
PROJECT_GOAL.md records the full blueprint objective, unconditional
reconstruction endpoint and variants, evidence-based completion criteria,
current completeness frontier, source fidelity and the shared update protocol.
README and AGENTS link it for discovery and session-start use. Both agents
may update the whole file after chit ownership coordination; no new routine
approval gate or requirement to finish historical frozen wrappers is added.
Actual source statements remain obligations even if a proof route bypasses them.

The baseline is clean da7314fb718a833a2c3f7a00e589b85c879edead. Its exact
CI37840274392 is SUCCESS, BOTHjobs/EVERYstep. The six owned checkpoint
reports/bodies and ALL26 current body-owner references are reconciled on
2026-10-13 before this documentation work; #5open/#11closed. No new
mathematical producer GO. Source, library, Book, dependencies and frozen117
remain byte-exact. No mathematical declaration or source statement changes.

Claude5903 contributes the objective/criteria/frontier proposal, and5905
agrees the file is living for both agents. Root5907 corrects the proposal:
the generic absolute degree equation is TRUE at the constructed point;
infinite cardinal arithmetic prevents its inference to independence.
Tensor-domain sketch is a proof gap, not a false ACF domain statement.
Conditional theorems ARE proved under named inputs, while unconditional
obligations stay open. Initial chart existence is missing; P6 already
derives all grid rows given that independent initial chart. The Qprime
ACF multiplication converse stays open by Correctness11-26 and
JAssembly936-975. The group/chunk/action route is a proposed dependency
plan to audit, not a proved unique necessary route. Frozen117 is historical,
not a demand to complete every wrapper. Final peer document review,
full library/book validation, exact four-path commit/push and exact CI
precede acceptance of this documentation checkpoint. The shared
mathematical goal remains the full unconditional formalization.


Claude5913 verifies allFIVE draft pins and reads FULL122line goal,
README/AGENTS/CONT diffs, proposed bytes and bounded blueprint checks.
Root adopts ALL R1-R5: implication-under-named-open-hypotheses wording,
linked proof gaps, CI in baseline, current open issues versus historical
#19 in README, and issue justification for proposed narrowing without
an approval gate. Claude5915 verifies allFIVE revised pins, reads the
FULL127line goal and README8-20, and FINAL ACCEPTS the four-doc checkpoint.
The shared goal permits either agent to update the ENTIRE document.
Actual final integration, full library/book and clean commit/push follow;
the mathematical library and all original statements remain unchanged.


## Actual Psi incidence germs recover full parameter closures (#27/#5)

Base clean 8ccd90b6051c696c4e3ece694d683a1ce5d77af0, exactCI38426301712
SUCCESS BOTHjobs/EVERYstep. Shared PROJECT_GOAL.md read and kept intact;
objective is full unconditional reconstruction and all source mathematics.
Root sole main/compiler owner; Claude read-only, no compiler/source GO.

Initial-chart audit5924 has18actualpins/265hash-onlysources/75hits.
Claude5928 verifies all and reads bounded source/definitions/current P6;
precise actual/inherited/NOTread ledger retained. Truth remains OPEN.
The initialchart target has full GuardedAffineGridExtraction strength;
no new Prop wrapper is added. Unguarded chart producer is a route
hypothesis from the historical sketch, NOT established truth. Both guards
remain in extraction/Q and multiplication supplies them to J.
Claude5934 corrects the proposed cheap I=P test: no independent shortcut;
its hand lattice consequence G=H=I=P is NOT compiled or accepted here.
Claude5942 F7A directmultiplier sketch has actual algebraic-branch and
invariant-rank-one classification gaps; root5945/Claude5946 record them.
It is not a proved shortcut or source change. Existing group/affine
bookkeeping is not extraction. The known evaluation-fibre proof gap is
not substituted by an easier standalone artefact. Chart/action goals remain.

Root5947 source-facing candidate, Claude5948 hand TRUE: literal free
clauses force coefficient closure to fill each rank-two plane.
READONLY5950:18 API/dependency pins/265hashes/399inventoryhits; no full
inventory-hit file audit. Claude5951 identifies existing CurveEquation.
Supplement5952 pins TWOactual paths. Claude5953/5955 ACCEPT the canonical
reuse route; root drops every-polynomial restriction/AI/normalization
scaffolding BEFOREdraft. CurveEquation already gives canonical monic
prime equations, exact ideals, intrinsic coefficient fields and descent.
Existing RankEq.eq_of_le_of_not_le_point gives the plane conclusion.
No duplicate field definition or unconsumed helper. Frozen
CompositionIdentity signatures are comparison-only, not imported/edited.

Root5960 privateGO. Complete current namespace/cache mirrored BEFOREwrite:
Math265/ALL1325cache, Book15/ALL75cache. Modified source and ALLcache
links unlinked BEFOREwrite; no partial namespace/write-through.
Appendproducer FIRST10s/min35.75GiB/RSS2.58GiB fails only point-coercion
rewrite; SECOND2s/min35.36GiB only underlying-field Set coercion.
Both failedsource/log/metrics retained. Explicit views repair ONLYthose
boundaries; THIRD2s EMPTY. FIRSTmetadata2s/min35.35GiB rejects FIVEold
private TYPE hashes after CurveEquation import into PsiLattice. No
exception is allowed: failedsources/metadata/log/metrics retained.

Root5962/Claude5963 choose a focused Config.ParameterField leaf and
restore PsiLattice's OLDimport/elaboration context. ONLY rankEq_A/B/C
lose their private keyword; ALLold statements/proofs/docs unchanged.
LeafFIRST4s/min35.26GiB finds only an inaccessible oldprivate X_not_le_A
reference; derive it inline from literal Psi.X_notLe, no fourth promotion.
Failedtriple retained. LeafSECOND4s/min35.18GiB/RSS2.51GiB green;
metadataFIRST8s/min35.18GiB verifies ALL89older SIG/proofs exact except
ONLY3 visibility flags, original56AX exact plus3matching promotedAX.
AllFIVE rejected TYPEs restored; no broader audit exception.

ONEnew public exists_incidence_germs_with_full_coefficients, TWOconsumed
helpers. From ONLY actualPsi over ANYfields, derive three genuine finite
correspondence pairs over the fields generated by the displayed point
representatives; all six endpoints literal. Existing canonical descent
puts target in racl(coeffSet union source). Any containing atom would
violate the actual free clause. Existing rank-two-plane result gives
racl_k(coeffSet)=A/B/C. NoACF/ratio guard/chart/action/group/prime/basis/
rank/full-coefficient oracle. It asserts relative CLOSURE equality, not
literal equality of coefficient field and finite-generator parameter field.
Public rank facts already existed; their mathematical content is unchanged.

TWOactual59line private examples, ZEROhelpers. Canonical5-coordinate
witness DERIVES actualPsi then allthree primes/exact span ideals/full
original parameter closures. A real E_A-linear endomorphism DERIVES the
moved endpoint ideal and same canonical equation; no universalPsi
transport. FIRST2s/min35.60GiB only missing EXPLICITbase argument to old
idealOf_comp_algHom; failedtriple retained, explicitbase fixes it.
SECOND2s/min35.43GiB and THIRD2s/min36.98GiB EMPTY, normal standardlint/
defaultkernel, no weakened options or checking-budget increase.

Root prose precision distinguishes fields generated by pairs from finite
cardinality fields; private helper allows arbitrary S. Claude5965
verifies13pins, FULL168lineleaf/FULL59lineconsumer/PsiLattice3visibility
diff/NewSIG+AX/first900chars each3acceptanceJSON/oldrowcounts. NOTread:
row-by-row olderSIG/AX/proof, logs, Composition.lean. Verdict ACCEPT.
Adopt ONLY N1-N3 prose: standardStatus/source truth, arbitraryS constructor,
coefficient SETs. N4 pair versus Set.range rewrite noted, no new definition.
All math/consumer content stays exact after this review.

Exactly SIX proposedpaths: focused newleaf; PsiLattice ONLY3visibility
words plus current status clarification; rootONEimport; BookConfigurations
ONEimport/newaccount/ONEobsolete meet-status clause; sourceONEconcordance;
append-onlyCONT. Other264old Math sources, dependencies, Main public
endpoints and frozen117 unchanged. Removing ONEconcordance recovers ALL
previous source/original49active and provenance/rawhistorical statements/
44proofs/listings/literals. No source proof gap or statement is withdrawn.
Initialchart existence, C2, rationalgroupchunk, actualgroup/action bridges,
Q/Qprime/J completeness and ALL unconditional reconstruction remain OPEN.
Canonicalroot/Book/sourceviews/fullmainbook/fresh134older+FOURnewchecks,
factualappend/peer/finalfullbook AFTERappend precedecommitpush/exactCI.
The full shared goal continues, not redefined to this primitive.



Actual parameter-field checkpoint acceptance: Claude5968 verifies all11
six-path pins, mainclean8ccd. Leaf l.1-30 and docstring/declaration lines; math unchanged per
root TYPE/proof metadata. FULLPsi/root/Book/source diffs, heading/P6
grep and FULL97lineCONTappend read. Historical8092CONTlines exact.
NOTread queued/proposed JSON and acceptance bodies beyond pins. Verdict
FINAL ACCEPT. Optional standard closing-wording nit deferred; all
source/math/consumer bytes reviewed remain unchanged.

LeafFOURTH4.00s/min34.58GiB/RSS2.48GiB and metadataTHIRD8.00s/
min36.27GiB/RSS2.39GiB green after N1-N3 prose adoption. All mathTYPE/
AX/proofs/attributes unchanged; constructor/public DOC changes explicit.
LeafFIFTH4.00s/min34.29GiB/RSS2.33GiB green after Psi module-status
clarification. Canonical root standardlint/default and proper Verso
Book genre pass50.02s/min34.46GiB/RSS6.41GiB.
No checking-budget increase or weakened checking. Book does not run
the mathematical hash-command linter. ONEpublic/TWOconsumed helpers,
oldthree rank declarations visibility only, old import context retained.

FIRST source four-pass render stable83pages and aux/toc/out, NO
undefined/layout/rerun error and NO repair. ALL23 selected current
views accepted:20 prior ACTUALLY viewed PNGs byte-exact[1,2,4,5,6,
67-81], plus3/82/83 ACTUALLY inspected clear/complete/unclipped.
Removing ONE29lineconcordance restores entire prior source and all
49active/original-provenance/rawhistoric statements, all44proofs/
listings/literals. No statement or proof withdrawn/repaired here.

Exact SIX main paths integrated AFTER fresh current issue instructions,
canonical/source/peer acceptance. ALLother298-originaltracked bytes
outside five old changed paths stay exact; one newleaf is added.
First visual-comparison harness guessed page-01.png/page-1.png but
actual names are page1.png; failure before acceptance claim, then
explicit current paths checked. No source, compiler or render rerun.
Recovered terminal metrics verify prior truncated tool calls completed:
leafFIFTH and canonical actuallyEXIT0, old session handles closed.
Old #6 heartbeat session80014 was found still alive with a stale
pending-CI claim. It was stopped, its owned body GET-compared and
corrected to exactda731CIgreen/26refs; no account/otherrepo changes.
Current #27 owned watcher remains the sole live user progress report.

Full lake build passes86.57s/min31.42GiB/
RSS8.36GiB; lake exe book passes16.12s/
min34.83GiB/RSS1.51GiB. ALL711 historical
warning headers BYTEexact in BOTH logs. Hygiene267 no proof placeholder/
project axiom. HTML109 retains ALL108 old paths plus actual new
producer docstring, explicit closures/endomorphism scope and old
chart/frozen boundaries. RootONEimport, Psi oldimports/math exact
except3private keywords/status, BookONEimport/account/status clause;
dependencies/Main/frozen117 and other264oldMathsources exact.
Actual compiled main Math266/ALL1330cache and Book15/ALL75cache.
Private ownoleans retained, missing metadata links restored only.

ALL138 FIRST fresh actual-main sequential checks pass
189.14s/min33.85GiB/RSS3.18GiB.
ALL134 older INPUTbytes and268original baseline INPUT/OUTPUTfiles
retained. ALLolder TYPE/RAW/ATTR/DOC/proofs/deny records exact. ONLY
three rank declarations' visibility flags and matching3publicAX change
in Lattice/PsiGeneric SIG+AX FOURdumps; botholdProofdumps exact.
No false whole-TSV exact claim. FOURnewfixtures reproduce accepted
3SIG/3proof/1publicAX and EMPTY59line TWOactualexamples/ZEROhelpers.
Standard Lean axioms and0generated records only in NEWAUDITEDscope;
no whole-library certificate. Actual consumers standardlint/default
kernel; old diagnostic genres/options BYTEexact.

Only source rank-two field-of-definition step F6(1) is covered.
Coefficient relative CLOSURES fill A/B/C; literal generated-field
equality is not claimed. Correspondence composition/C2, group chunks,
six-point configurations, actual action/classification/initial charts,
Q/Qprime/J completeness and unconditional reconstruction remain OPEN.
Both guards, source proof gaps and frozen117 retained. #5open/#11closed.
Root sole main/compiler; peer read-only. Actualappend review plus
mandatory final full/book AFTER this append precede commit/push/CI.
The shared full-blueprint durable goal continues unchanged.


## Actual common-closed-base incidence composition (#27/#5)

Base clean48dd789d913bc22abd1e7f4db968afb8797a5a58, exactCI38450348285
BOTHjobs/EVERYstep SUCCESS; allSIXreports/bodies and27ownerrefs reconciled.
PROJECT_GOAL unchanged/read; full unconditional blueprint objective ACTIVE.
Root sole main/compiler; Claude read-only/no source/compilerGO.

READONLY16pins+7supplement, precise actual/inherited/NOTread ledger.
Root initial source1415-1535/1708-1790, Composition1-210/268-400/412-440,
Family1-155/672-744/946-1020, FamilyCover1-110/646-724, FiniteRank190-207/
225-294, PsiLattice138-174/215-256, Psi51-150 read. Supplement actual
GeometricPrimeFULL85, BaseChange929-1018, CurveEquation72-126,
CEqTransport238-282, ClosedLattice1-75, MathlibAlgClosure145-190.
Other pins/inventory not falsely counted as full reads. Guessed missing
IndependentPoints/PsiGeneric/TransferACF paths have no pins/read claims.

Claude5986/5987 confirms source orientation notation inconsistency:
historical A:YtoX requires transpose before B:YtoZ to get C:XtoZ.
Canonical model X=x,Y=ax+b,Z=cY+d gives gamma=beta alpha-transpose.
This is not a refutation of guarded completeness or a chart proof.
Root reports FIRST #27comment6153067856, original source retained.
Rank5 standalone producer is TRUE but duplicates old Composition
fiber_product_rank_count; Claude5987 REJECT adopted, no new wrapper.
FamilyMembers directly constructible; no new public family interface.
Finite-generator parameter ideals can split; shared-endpoint rfl alone
does not justify genuine coefficient/composite preservation.

Claude5989 verifies7supplementpins/precise bounded actualreads. OLD
BaseChange.idealOf_map_eq_span already supplies no-splitting overACF
base and two-way generic larger field; proposed generic wrapper dropped.
GeometricPrime is comparison-only, not imported/edited. Mathlib
algebraicClosure_eq_bot_iff plus IsRAC makes closed planes ACF.
ONE consumed private canonical-map helper reuses old monic uniqueness.
Commonfield AjoinB containsC by equalrank4; notLe clauses keep endpoints
generic. Old coefficientClosure_eq remains general and reused in same
module. No PsiLattice promotion/new import/public Prop/field definition.
Claude5991 ACCEPTS the strongest small actualPsi+ACFK commonfield
three-germ/fullcoeffclosure/correctedComposes target; root5992 PRIVATEGO.

Complete actualcurrent namespace/cache mirrored BEFOREwrite:
Math266/ALL1330cache, Book15/ALL75. Modified source/ALLcache links
unlinked BEFOREwrite. No write-through/partial namespace. Main clean.
FIRST4.03s/min36.31GiB/RSS2.59GiB fails only explicit RingHom/field
views/adjoin_self and current instance-proof style boundaries.
SECOND4.03s/min35.76GiB only missing EXPLICITbase k on adjoin_self,
longline and instance style. THIRD4.03s/min35.25GiB only final
dependent common-field rewrite; FOURTH4.03s/min35.75GiB only field
instance motive. ALLfour failed source/log/metrics triples retained.
FIFTH38.26s/min33.29GiB/RSS5.58GiB reaches defaultkernel deterministic
timeout on whole public proof after a broad field transport. Retained.
NO checking-budget increase, weakened lint/kernel or checking option.

Root factors only the new proof: exists_closed_incidencePair wraps OLD
incidencePair at the whole closed field, native type/endpoints paid once
inside a local proof motive. Consumed SIXtimes; no exported Prop/field
definition. Public proof now native A/B/C/commonF fields, no broad final
value transport. Claude5994 accepts this third consumed helper.
SIXTH2.01s/min36.19GiB and SEVENTH2.01s/min36.17GiB EMPTY standard/
default green. Three helpers: closed_isAlgClosed, native endpoint
constructor, canonical coefficient base-change. ONE new public:
Psi.exists_composing_closed_incidence_germs, actualPsi+ACFK ONLY.
No ACFk/guards/chart/group/action/prime/rank/coefficient oracle.

MetadataFIRST4.02s/min36.12GiB/RSS2.53GiB green. Old3SIG/proofs+1AX
TYPE/RAW/ATTR/DOC/axiom/normalizedproof/deny exact; add ONLYnew4SIG/
proofs and1publicAX, totals7/7/2. Old3diagnostic INPUTs/genres/options
BYTEexact, old6baseline input/output files retained. Standard Lean
axioms and0generated only in newauditedscope, not whole-library cert.
TWOreal57line privateexamples/ZEROhelpers FIRST2.01s/min35.94GiB EMPTY.
Canonical5-coordinate actualPsi derives all3commonfieldprimes/exact
span ideals/original racl{a,b},{c,d},{ac,bc+d} and composition.
Actual commonfield-linear endomorphism derives moved ideal/same
equation; no universally quantified Psi transport.

Claude5998 SOURCE ACCEPT verifies16pins/mainclean/originalcbedexact.
Reads FULLnewsource diff/l160-342, FULL57consumer, fullSIG/AX/proof
baseline-current diffs (addONLY4/1/4). NOTread acceptance JSON bodies,
diagnostic .lean drivers or rootledger (hash-only). Newhelper proof
shape/sourcehypotheses/actual coefficient derivation and corrected
composition all verified. Adopt N1module status and N2parameter-plane
wording now; N3canonical helper is a promotion candidate upon another
independent consumer, kept private. Math/consumer untouched.

Exactly FOUR proposed paths: existingParameterField newblock and
explicit module prose/ONEnewpublic doc precision; Book ONEnewaccount
and ONEscope clause, NOimport; sourceONEconcordance; append-onlyCONT.
Root/PsiLattice/dependencies/Main/frozen117 and other265Math sources
unchanged. Entire previous source/all49active/originalprovenance/raw
historic statements/44proofs/listings/literals recovered by removing
ONEconcordance. Old Gamma orientation/proof remains retained.
This covers the common-closed-base germ parameter form of(8.6).
Nonclosed-functionfield composition/C2, group chunks, actual actions/
classification, initialcharts, Q/Qprime/J completeness and unconditional
reconstruction remainOPEN. Local same-endpoint selector is not the
substantive proof: exact ideal extension and coefficient preservation
precede it. Shared fullgoal not narrowed to this source primitive.
Canonical/book/source views, fullmainbook/fresh138older+FOURnewchecks,
actualappend/peer/finalfullbook AFTERappend precede commitpush/exactCI.



Actual common-closed-germ checkpoint acceptance: Claude6003 verifies9
four-path pins/leaf351/CONT8364 with historical8264wholeprefix exact.
Reads FIRST80 changed leaf lines plus docstring/declaration grep of
rest; remaining helper/public proof lines were read FULL at5998.
Bookdiff415-471, Texdiff5848-5885, FULL100lineCONTappend read. NOTread queued/proposed/acceptanceJSON bodies
(hash-only). Math matches prior5998 read line-for-line, but peer did
NOTbytecompare overwritten95e18549; exactness rests on root metadata.
Root retains actual342line before_docs snapshot and BYTEcompares full
mathematical source by reversing ONLYdeclared prose changes.

Claude6006 corrects5989(5): pairOverIndependentExtension itself is
purely transcendental, so it does not cause splitting. Splitting caveat
is finite-generator presentation extended to CLOSEDparameter planes.
Root changes onlynewPubDOC/Booknewaccount precision; actual API name
FiniteCorrespondenceFamilyMember.pairOverIndependentExtension.
No claim that its independent extension splits. NewPubDOC explicitly
uses closed presentations; module header and status separate both
proved clauses from nonclosed composition/group/chart/completeness.
All math/57consumer BYTEexact against SOURCE-reviewed actualsnapshot.

ProducerEIGHTH/NINTH/TENTH each2.01s EMPTY normalstandardlint/default
kernel after prose changes; TENTHmin38.75GiB. MetadataSECOND/THIRD
each4.02s; THIRDmin38.32GiB/RSS2.60GiB. Only NEWpublic DOChash changes
with precision; old3SIG/proofs+1AX/attrs/docs/types/raw/deny exact,
new4SIG/proofs+1AX totals7/7/2 reproduce accepted theorem/private
helper records. No imports/math/helper/publictype changes.
Canonical FIRST36.21s/min37.53GiB/RSS5.58GiB; after precision SECOND
32.18s/min37.00GiB/RSS5.94GiB, rootstandard/default
and properVersoBook genre. No mathematical hash-command lint on Book.
No checking-budget increase or weakened checking despite retained
FIFTH kernel timeout. Native endpoint helper consumed SIXtimes.

Claude6010 bounded FINAL ACCEPT verifies ALL9finalprecision pins,
leaf352, Book57c8408f, source/CONTunchanged from6003. Actually reads
newpublicDOC/Book split/API wording diffs only; other reviewed scope
inherited. Optional further module-header phrase deferred (true under
base change as written). Actual source FIRST four stable passes84pages,
24 selected accepted views,21older ACTUALLYviewed PNGs BYTEexact
[1,2,4,5,6,67-82] plus3/83/84 ACTUALLYinspected clear/unclipped.
No render repair/undefined/overfull/rerun error. Source ONE38line
concordance; all49active/originalprovenance/rawhistoric statements,
all44proofs/listings/literals BYTEexact, historicalorientation retained.

Exactly FOUR paths integrated AFTER fresh repository issue instructions,
Source5998/Doc6003/final6010 acceptance and canonical/source green.
Full lake build passes72.40s/min36.18GiB/
RSS8.62GiB; lake exe book passes10.06s/
min37.95GiB/RSS1.63GiB. ALL711 historical
warning headers exact in BOTHlogs. Hygiene267 no proof placeholder/
projectaxiom; HTML110 retainsALL109oldpaths and first/newgerm docstrings,
explicitnonclosed/group/chart/completeness limits, chart/frozenpages.
Root/PsiLattice/Main/dependencies/frozen117/other265Math exact.
ParameterField mathematical changes ONLYnewonepublic/threeconsumed
helpers; older3mathematical blocks/imports/declarationdocs exact.
BookONEnewaccount/ONEscopeclause NOimport; CONTappend-only.
Compiled main Math266/ALL1330cache, Book15/ALL75cache; private own
oleans retained, missing metadata links restored only, no write-through.

ALL142 FIRST fresh actual-main sequential checks pass
181.02s/min37.28GiB/RSS2.94GiB.
ALL138 older INPUTbytes and276original baseline INPUT/OUTPUTfiles
retained; allolder TYPE/RAW/ATTR/DOC/AX/proof/deny records exact.
THREEold ParameterField fullmodule dumps add ONLYaccepted4newSIG/
proofs and1publicAX; no false whole-output BYTEexact claim.
FOURnew fixtures select ONLYnew4SIG/proof/1AX and EMPTY57line real
consumer, same diagnostic genres/options/imports/module selectors
with only named-row filters added; no duplicate fullmodule probes.
Standard axioms/0generated only in NEWaudited scope, not wholelibrary
certificate. Actual consumers standardlint/defaultkernel.

ActualPsi+ACFK produces commonclosedF=AjoinB germs YtoX,YtoZ,XtoZ
with coefficient CLOSURES A/B/C and correctedselectedComposes(A.swap,
B,C). Closedgerms/no-splitting/monic transport stay inside proof;
no extra public variant/Prop/fielddefinition/oracle. Original finite
presentations can split on closed extension; literalgenerated-field
equality is not claimed. Group/action/classification/initialchart,
nonclosedC2, Q/Qprime/J and unconditional reconstruction remainOPEN.
Sourceorientation report6153067856 precededconcordance; all original
proofs/gaps/frozen117 retained. #5open/#11closed. Root sole main/compiler,
peer readonly. Actualappend review and finalfull/book AFTERthisappend
precedecommitpush/exactCI. Fullsharedgoal continues unchanged.


## Joint Q′ source-route audit and direct proof plan (#12/#27)

Mathematical baseline remains clean8d01b03991aa0bf2125eef63b6751197dbb1fd7a,
exactCI38464730779 workflow and BOTHjobs completedSUCCESS. Library/book/upload/
deploy are verified by the completed archive; stale/empty step API details are
not an observed every-step certificate. Six checkpoint reports and28body-owner
references were reconciled. The full-blueprint durable goal remains ACTIVE.

This checkpoint edits ONLY PROJECT_GOAL.md and appends this handoff. It adds
ZERO mathematical declarations and changes ZERO existing source statements,
proofs, imports, dependencies, Main signatures or frozen117 files. The142
accepted mathematical probes remain the8d01 baseline; they are not rerun or
described as a fresh whole-library certificate for this documentation audit.

Root and Claude conduct the19pin read-only Qprime audit plus6supplement and
4direct-bridge API pins. Precise ledger:
/tmp/acl_geom_codex_qprime_8d0/root_read_ledger.json. A prior full cat of
PartialQuadrangle was truncated; it is explicitly NOT a full-file read.
Claude6027 AUDIT is actually read in full. Claude6031 BRIDGE_CHECK is inherited
from the message, not falsely reported as a file read. Claude6035 complete
CONVERSE_PROOF.md is actually read in full;6037 rechecks the specific steps.
Only bounded ranges and the listed inventories are claimed as actual reads.

Source proof gaps reported BEFORE any source change:
#12comment6155280744 and #27comment6155281059. The multiplication converse
invokes curve-coset before supplying its ambient connected group and actual
generic product relation. The finite group-chunk paragraph has not justified
one coherent finite lift and closure under all words. These are proof gaps,
not refutations. The square-root candidate has inverse-composition outputs
{+b,-b}, so it fails the literal identity-correspondence hypothesis. No false
statement or proved corrected finite-chunk theorem is claimed. ALL original
source bytes,49active/provenance/historical statements and44proofs/listings/
literals remain exact. Its existing84page/24view source acceptance is reused,
not rerendered or newly certified by this documentation change.

Claude6033 and root independently check the multiplication sextuple
(X,Y,V,C0,B0,A0): all16nonline triples close to allsix by the four named
rank-two lines. This is a true optional source8.3-route input over any fields.
Three private candidate attempts are retained: two default-budget timeouts
and one split-script syntax failure. The optional leaf remains UNINTEGRATED
and is deferred in favor of the direct multiplication converse. No checking
budget or transparency restriction is weakened.

Root6030 proposes fixed-prefix relocation with literal b,c,ratio; Claude6031
corrects the construction to an actual ambient automorphism fixing acl(b,c).
Root6034 supplies the D/E meet simplification. Claude6035/6037 give and recheck
a COMPLETE HAND proof, NOT yet a Lean theorem:
 - Pick a0 fresh over the actual rank-three tuple(a,b,c). An ambient automorphism
   fixing acl(b,c) sends a to a0, fixes x/y literally and yields x0*y=x*y0.
 - Over closed acl(a,a0), the actual incidences derive a real MulCorrSetup.
   A fifth fresh element supplies the existing multiplicative theorem.
 - The equal products force common exponents to sum to zero. A nonzero power
   of x0/x lies in the base; existing mem_racl_empty_of_zpow makes the ratio
   algebraic there. This avoids coprime-exponent/gcd bookkeeping entirely.
 - Over acl(a0), that ratio is interalgebraic with a. The original corners
   become interalgebraic with alpha*x and alpha*y for the SAME alpha.
 - Two independent-variable product meets put D in acl_a0(alpha*x*y) and E
   in acl_a0(x*y). Exchange removes a0, yielding the original E=[xy].
There is no separability assumption, selected-branch oracle, original curve
normalization or group-extraction conclusion supplied by the caller.

Private complete overlay at /tmp/acl_geom_codex_qprime_8d0 mirrors all266
mathematical and15book sources and ALL1330+75 current namespace artifacts.
New leaf/root outputs have no links to main. No write-through or stale
partial namespace is used. Root is sole source/compiler; Claude READONLY.
Every compiler family uses the monitored lock, two Lean threads and30GiB
available-memory stop. Actual sessions EXIT before source writes/next compile.

New private MultiplicationConverse prefix is300lines/11private lemmas and
ZEROpublic results. It checks intermediate/closed-base closure equivalences,
equal-product common ratio, literal MulDiagram incidences, two product meets,
closed-prefix independence and the ACTUAL fixed-b,c ambient automorphism.
NINTH prefix check exits0 in2.00s, minavailable38.31GiB, default kernel/standard Mathlib lint, EMPTYlog. Earlier
successful SECOND/THIRD source snapshots and all failed logs/metrics are retained.
Not every failed source version was saved; no exact failed-input replay is claimed.
Errors were field-motive/type/instance or set-order/lint fixes; FOURTH's bad
subset orientation also timed out. No weaker checking/budget increase, axiom,
sorry or admit is added. These are private prerequisite proofs only, not a
formal proof of the full multiplication converse or a library axiom audit.

Next: derive the genuine simultaneous scaling normalization from the actual
fixed-field automorphism; assemble ONE public QSem+ACTUALMulDiagram -> QprimeSem
under the genuine ACF/rank-five hypotheses; consume it to derive hQprimec
from the stillOPEN guardedhQc in the existing J assembly. Only then run the
full source/consumer/metadata/regression/book gates and integrate the result.
Geometric Q, Qprime and J completeness and unconditional reconstruction remain
OPEN. The source8.3 route and bypassed group/chunk/action statements remain owed.

PROJECT_GOAL records a shared OPEN bridge on the SOURCE group/chunk route,
not a necessity for every proof. It prioritizes the direct Qprime alternative
after joint hand review without narrowing the mathematical endpoint. Claude
review of its exact wording and this append, followed by mandatory full
lake build and lake exe book AFTER actual append, precede commit/push/CI.

Claude6040 accepts this TWO-path documentation checkpoint after verifying all
10pins. Actual reads: full goal diff and95line append; full prospective CONT
prefix/tail compared byte-exact. Other pinned artifacts are HASHONLY; unchanged
goal context is inherited from the earlier full127line read. The requested
neutral wording and recommended dependency wording/line wrap are applied.


## Direct multiplication product converse and guarded-Q reduction (#6/#27)

This checkpoint starts from785e0ca028be427cbf7835b88f6cea14f1fcb80c. It proves
one substantive new producer in Config/MultiplicationConverse.lean (693lines,
20consumed private lemmas), with two short public consumers in Correctness:
 - q'Sem_of_qSem_of_mulDiagram: ambient K algebraically closed, rank at least
   five, actual QSem and MulDiagram imply Q'Sem with the product output.
   The original base k may be arbitrary; no semantic corner, product,
   group-extraction or separability conclusion is supplied by the caller.
 - q'Sem_of_q'Geom_of_guardedQCompleteness: the actual diagram supplies both
   ratio inequalities, so the still-open GuardedQCompletenessACF gives Q′.
 - jCompletenessACF_of_guardedQCompleteness: the derived Q′ implication and
   guarded Q feed the established J assembly. No separate Q′ oracle remains.
All five old Correctness declarations retain exact scoped type, raw/normalized
proof, attribute, docstring and axiom records. Main and JCompletenessACF types,
dependencies, other265 pre-existing mathematical sources and frozen117 are exact.

The proof fixes the entire closed field of the two corners b,c, relocates a
to a fresh a0, and derives equal products from literal fixation of x/y.
A real MulCorrSetup over acl(a,a0) supplies the common ratio alpha. Exchange
and interalgebraic independence give the simultaneous corner normalization
over acl(a0). Two existing product meets yield e in acl_a0(xy); final exchange
removes a0. The original output is then the product point by its atom property.
This proves the product-output clause, NOT the full original-base auxiliary
representative classification. That stronger clause and all bypassed true
source group/chunk/action statements remain obligations. Guarded Q, unconditional
Q′/J completeness and unconditional reconstruction remain open. The full shared
goal is unchanged; its critical path now records this proved dependency.

Collaboration: Claude6035/6037 supplied and independently checked the complete
hand proof,6045 reviewed the full300line prefix,6050 accepted the extended424
prefix and full normalization plan. Root completed the Lean normalization,
product meets, public theorem and real consumers. Final full-tail/consumer and
goal/book/source reviews were requested in6063/6064, updated in6067. They have
not yet returned at this append; no final peer acceptance is claimed. Ownership
remains root sole editor/compiler and Claude read-only reviewer. The user asks
for commits at natural green checkpoints; the checked checkpoint can be recorded
while the final independent review remains an explicit follow-up, not inferred
approval. Review corrections, if any, must receive fresh affected validation.

Validation evidence: /tmp/acl_geom_codex_qprime_8d0/converse_math_acceptance.json,
converse_documentation_acceptance.json and /tmp/acl_geom_converse_shared_probes/
acceptance.json. All146 actual-main checks pass:142 exact old fixture inputs
and284 preserved old input/output baselines, plus three scoped new diagnostics
and one fixture with TWO real examples (canonical actual diagram and guarded-Q
consumer of the existing J target). Every older scoped record stays exact;
ONLY the two named new Correctness SIG/proof/AX rows enter three old Guarded
dumps. New scope has23 declarations (20private/3public), no generated records;
all three new public results use only choice, quotient soundness and propext.
This is a scoped audit, not a whole-library axiom certificate. Real behaviors
use standard Mathlib lint/default kernel; diagnostic genres/options are retained.

Full lake build110.03s/min38.17GiB, book10.00s/min40.17GiB, fresh146checks186.05s/
min40.19GiB. Both build logs preserve all711 historical warning headers exactly.
Hygiene covers268library/root files with no proof placeholders/project axioms.
HTML111 retains all110old page paths and shows all three new public docstrings.
The frozen-route visibility check now checks its actual visible phrase rather
than a raw117 substring, which could occur in unrelated tooltip identifiers.

Source proof gaps were reported before annotation (#12comment6155280744 and
#27comment6155281059). One new concordance and two current-status remarks retain
all49active statements, every historical/provenance statement and all44proofs/
listings byte-exact. Four stable source passes yield84pages;30selected views
are accepted:23previous actual PNGs byte-exact, and2/13/14/15/16/17/18 actually
viewed. One overfull URL was fixed with a linked issue label before acceptance.
The book explains the closed-base normalization and final original-base descent;
the goal records the new guarded-Q-to-J dependency without narrowing its endpoint.

Failed private normalization/public drafts and logs are preserved, including
Finset/coercion/set-order repairs and one default200000-heartbeat failure fixed
by explicit closure-parameter types. No checking limit was increased. The optional
private MultiplicationQuadrangle dead-end is unimported and not integrated.
The prior snapshot remains immutable; this continuation is appended ONCE from
current main and copied outward. Final full build and book after this append
must precede commit/push, exact CI observation and repository-issue reporting.


## Full original-base multiplication coordinates by coherent specialization (#6)

Starting from95c9e2ad24c2261ea40e51e195267b9be195d3c8, this checkpoint proves
mulDiagram_coordinates in Config/MultiplicationConverse.lean. Under ACF k/K
and ambient trdeg at least5, an ACTUAL MulDiagram with X=[x], Y=[y], V=[x/y]
admits ONE independent multiplier a with A=[a], B=[ax], C=[ay], D=[axy],
and E=[xy]. No normalization, algebraic-group or branch-choice conclusion is
supplied by the caller. This finishes the original-base auxiliary-table clause
of blueprint Lemma mul-diagram in the rank-five ACF setting. Guarded Q remains
open; the existing reductions still make it the remaining input for Q′/J
completeness. Main's conditional reconstruction inputs are unchanged. True
bypassed group/chunk/action statements remain owed, and the full shared goal
has not been narrowed. PROJECT_GOAL records only this changed frontier.

Correspondence/Specialization.lean uses Mathlib Chevalley constructibility to
find a principal open in an injective finitely presented spectrum image.
An infinite subfield supplies a parameter value there, and the ACF residue
field argument supplies an actual algebra homomorphism. The finite root
bound shows that a nonzero polynomial in T,U,V becomes identically zero in
U,V for only finitely many T-values in k. Inverting the product excluding
those values lets ONE homomorphism preserve all chosen incidence equations.
Its public finite-polynomial specialization theorem and evaluation identity
are consumed by Correspondence/MultiplierDescent.lean, which derives beta
nonzero in acl(a), b in acl(beta*x), and c in acl(beta*y). Independence keeps
the last two first coordinates transcendental. The actual diagram then forces
beta nonconstant (otherwise B=X), gives A=[beta] and independent beta,x,y by
exchange, and supplies D/E through the proved original-base product meets.

There are18 new declarations:4public and14 consumed private helpers. The
canonical actual-diagram consumer checks every row and independence. All28
older declarations in the affected converse/Correctness scope retain exact
types, attributes, docstrings and raw/normalized proofs. Eight old public axiom
rows are exact; the four new public rows use only propext, choice and quotient
soundness. This is a scoped dependency audit, not a whole-library certificate.
All other tracked sources, Main interfaces and frozen117 remain byte-exact.

The private complete overlay is /tmp/acl_geom_codex_specialization_95c; new
outputs never write through source/cache links. math_source_checks.json and
Table{Signatures,Proofs,Axioms}.tsv record private acceptance. All three producers
and the real table consumer pass default kernel/standard Mathlib lint with
empty logs in10.00s/min40.14GiB. Metadata passes in4.00s/min40.32GiB. Several
failed drafts and exact snapshots are retained. One default-heartbeat failure
was repaired by explicit closure sets and field arguments, without increasing
checking limits. The Verso module was validated with its normal configuration;
forcing Mathlib's hash-command linter merely flagged its existing #doc command.

Fresh actual-main validation: full lake build 114.04s/min38.62GiB;
lake exe book 8.00s/min40.35GiB; all150 checks 190.04s/min40.49GiB.
/tmp/acl_geom_table_shared_probes/acceptance.json records146 byte-exact old
fixture inputs and292 retained old input/output baselines. ALL older scoped
records are exact, without exceptions; four new fixtures add the three scoped
diagnostics and one canonical full-table example. Actual behavior uses default
kernel/standard Mathlib lint; historical diagnostic genres/options are retained.
Hygiene finds no proof placeholders/project axioms in270 library/root files.
Both full build and book retain all711 historical warning headers exactly.
HTML keeps all111 prior page paths and shows the three new documented results.

The source concordance retains all49 active statements, every historical
statement and all44 proofs/listings byte-exact. Four stable TeX passes give
85pages, with pages1,2,15,16,17,18,85 actually viewed and clear; evidence is
/tmp/acl_geom_table_tex/visual_acceptance.json. No whole-document visual review
is claimed. The book explains the finite bad-value set, coherent homomorphism,
nonzero specialized multiplier, and the original-base table. The original
source group-extraction proof gap remains recorded rather than silently erased.

Collaboration: root remains sole editor/compiler and Claude read-only. The
specialization truth audit and exact checked-source reviews were requested
through chit6070/6072/6076/6078/6079, and matching goal/book/source review in6080.
No reply has returned at this append; final acceptance is not inferred from
silence. The prior product-converse tail review also remains pending. Root's
kernel, real-consumer, regression and rendering gates pass. As requested,
commit and push this green mathematical checkpoint after another full build
and book AFTER this append, then observe exact CI and report on repository
issues. Address any later peer correction with fresh affected validation.
The single-family lock, two threads and30GiB available-memory stop remain in
force; actual compiler exits precede source writes and subsequent builds.


## Multiplication coordinates without an auxiliary rank bound (#6)

Starting from35e7fb4f42694d551071e968cbb8a37a2461b831, the new public
MulDiagram.exists_coordinates proves the entire original-base table over
ACF k/K with no additional transcendence-degree bound. Its caller supplies
only an actual diagram and bottom representatives x,y,x/y. One independent
a gives A=[a], B=[ax], C=[ay], D=[axy], E=[xy]. This strengthens the preceding
rank-five result to the source lemma's local hypotheses. The previous public
theorems and reductions are unchanged; guarded Q, unconditional reconstruction
and all true bypassed group/chunk/action obligations remain open. The shared
goal records this frontier change without narrowing the endpoint.

Three consumed private helpers construct the ACF of the fraction field of
K[T1,...,T5], supply its rank bound, and descend the normalized multiplier.
All original incidence memberships and independence transport to this
extension. The previous normalization and exchange put the new multiplier
in acl(original a). A nonzero polynomial with coefficients in the original
field proves it algebraic over K; since K is ACF, it belongs to K. Ambient
invariance reflects the original memberships and independence. The actual
product meets then give the final two points. The private canonical consumer
uses an actual diagram and proves every row without a rank input.

Private producer and consumer pass default kernel/standard Mathlib lint with
empty logs (6.00s/min39.99GiB and2.00s/min40.46GiB). Scoped diagnostics pass
4.00s/min40.06GiB: all46 older declarations retain exact types, attributes,
docstrings and raw/normalized proofs. The new public dependency row uses only
propext, choice and quotient soundness; this is not a whole-library dependency
certificate. The normal Verso module check passes42.01s/min39.28GiB.

Actual-main full lake build passes106.03s/min38.28GiB;
lake exe book passes10.00s/min39.89GiB; all154 fresh checks pass
196.05s/min40.13GiB. All150 older fixture inputs stay byte-exact;
all300 older input/output files and four diagnostic baselines are retained.
Every older scoped record is exact. The three unfiltered prior table diagnostics
add precisely the four checked new declarations and one public axiom row;
their original records are unchanged. The first shared harness stopped on
that expected additional axiom row; its log is retained. Correcting the
comparison preserves all old rows and checks all new rows against the private
baseline, without editing any Lean fixture or mathematical source. Four new fixtures add scoped diagnostics and the actual no-rank
consumer. Historical diagnostic options are retained, while actual mathematics
and behaviors use stock kernel/standard Mathlib lint. Hygiene is clean across
270 library/root files; all711 warning headers and111 HTML paths are retained.

Only the existing source concordance is expanded: all49 active statements,
every historical statement and44 proof/listing blocks remain exact. The85-page
PDF has four stable passes; pages1,2,16,17,18,85 were actually viewed and clear.
The book and PROJECT_GOAL agree with the new public theorem. Evidence lives in
/tmp/acl_geom_codex_unbounded_table_35e, /tmp/acl_geom_unbounded_shared_probes
and /tmp/acl_geom_unbounded_tex. Current #6 G4/G5 and #27 checklist descriptions
were reconciled to the proved multiplication results; open boxes and dated
audit text were preserved, with stale Current audit headings marked Historical.

Root remains sole editor/compiler and Claude read-only. Chit6086 coordinates
ownership,6088 requests the checked mathematical review, and6089 supplies the
exact goal/book/source review. No reply has returned at this append; acceptance
is not inferred from silence. Previous pending reviews remain pending. After
this single append, rerun full build and book, commit/push the five-path green
checkpoint, observe exact CI and report on the repository issues. The next
central mathematical obligation is still the guarded-Q initial chart. The
single-family lock, two threads and30GiB available-memory stop remain in force.


## Relational associativity of finite-correspondence germs (#5)

From e6818d94d2ebfe799fafffc69767ec9e5fd6d47c, the new focused module
Correspondence/CompositionAssociativity.lean proves
FiniteCorrespondenceGerm.composes_assoc. Over any base k in an ACF ambient,
(exists E, Composes A B E and Composes E C D) is equivalent to
(exists F, Composes B C F and Composes A F D). This is the full relational
statement for the existing represented germs, starting with independently
chosen presentations of the intermediate component. Existing strict
associativity at literal shared middles did not supply that alignment.

Equal endpoint-pair ideals give an ambient automorphism by the proved finite
generic-point theorem. Transporting the interior representative gives one
chain of four generic coordinates, which can be regrouped. Two consumed
private helpers transport a branch and preserve its ideal. The actual consumer
constructs squaring, its transpose and negation at a transcendental element,
then derives the other intermediate germ without a caller Composes oracle.
No base ACF, rank, component-selector or group/action conclusion is assumed.

The geometric identification with dominating fiber-product components remains
open, including nonclosed function-field bases. C2, group chunks, initial
charts, guarded Q and unconditional reconstruction are not closed by this
result. The book, source remark and shared-goal frontier make that boundary
explicit. All original source statements/proofs remain unchanged. No frozen
M4a source or older mathematical module was edited; the root gains one import.

Private producer/consumer checks pass with empty logs, default kernel and
standard Mathlib lint (2.00s each; minimum available 40.95/40.90 GiB).
Metadata passes in 8.00s/minimum 40.53 GiB. All 65 old signatures and 59 old
proof/axiom rows in Composition/AmbientAutomorphism are exact. There are three
new declarations (one public, two private), no generated extras, and the new
public axiom row contains only propext, choice and quotient soundness. This is
a scoped audit. The first draft's explicit-base/section-end repairs and failed
log are retained; no checking option was weakened. Private book checking
passes in 42.01s/minimum 39.59 GiB.

Actual-main full build passes in 72.02s/minimum 38.38 GiB;
book in 8.00s/minimum 40.30 GiB; four focused new checks in
6.00s/minimum 40.42 GiB. Those checks freshly compare the relevant
old/new metadata and run the real consumer. The 154 green-parent fixture inputs
and outputs are retained byte-exact, along with their four baselines; they
were not rerun because every older mathematical module is byte-exact and no
instance or simplifier attribute is added. The future corpus has 158 fixtures;
this is not a claim of 158 fresh runs. Hygiene is clean across 271 library/root
files. All 711 warning headers and 111 previous HTML paths are retained, with
one new book section. Four stable TeX passes give 85 pages; selected pages
1,2,3,18,19,20,85 were actually viewed and clear. All 49 active statements,
historical mathematical blocks and 44 proofs/listings remain exact.

Evidence: /tmp/acl_geom_codex_relational_assoc_e68,
/tmp/acl_geom_assoc_shared_probes and /tmp/acl_geom_assoc_tex. The bounded
scope was posted on #5 comment 6159595091. Claude received the target/proof
in chit6098/6100, ownership in6104, documentation/shared goal in6107 and the
focused validation plan in6110. Root remains sole editor/compiler; Claude
is read-only. No review reply has arrived, so acceptance is not inferred.
After this single append, full build/book must pass again before the six-path
commit/push, exact CI observation and issue reports. The full durable goal
remains active, with the guarded-Q initial chart still central. Keep the
single monitored family, two threads and 30 GiB available-memory stop.


## Selected function-field tensor components (#5)

From e497b353e2c5fa7b48b5cc2be875eb4f6db780f1, the focused module
Correspondence/TensorComponent.lean proves three conclusions for actual
shared-middle finite branches (x,y) and (y,z). Over E=k(y), put F=E(x), G=E(z).
The ambient multiplication map from F tensor_E G has a minimal-prime kernel;
its quotient is E-algebra equivalent to F join G; restricting that compositum
to k gives the existing chainField, k(x,y,z). Public names are
FiniteCorrespondencePair.tensor_ker_mem_minimalPrimes,
tensor_quotient_equiv_compositum and tensor_compositum_eq_chainField.

The first two consume one private generic finite-extension lemma: the tensor
is Artinian, its kernel into a field is prime and hence minimal, its range is
the compositum, and Mathlib's first isomorphism theorem identifies the quotient.
No base or ambient ACF, tensor-domain assumption, extra field definition,
instance or simp attribute is introduced. The actual squaring/transpose
consumer derives minimality, a field quotient and compositum exactly k(t).
The combined-conclusion draft exceeded default checking limits; separate
mathematical conclusions pass without changing those limits. Failed drafts,
consumer repairs and diagnostic logs are retained outside the repository.

This identifies the component selected by an actual chain. Realization of
every tensor component and the geometric coordinate-ring/localization bridge
remain open, as do group chunks, guarded-Q charts and reconstruction.
PROJECT_GOAL and the book state this boundary. The entire blueprint, every
older mathematical module and all frozen M4a files remain byte-exact.

Private producer/consumer pass default checking and standard Mathlib lint
with empty logs (8.00s each; minimum available 40.40/40.78 GiB). Scoped metadata
passes in 4.00s/minimum 40.76 GiB: exactly one private and three public
results; public dependency rows contain only the standard three axioms.
This is not a whole-library axiom certificate. Private book passes in
30.01s/minimum 39.92 GiB. Actual-main full build passes in 78.02s/minimum
38.29 GiB; book in 8.00s/minimum 40.27 GiB; four focused actual-main checks in
12.00s/minimum 40.67 GiB. The 158 prior fixture inputs/outputs and baselines
are retained byte-exact, not rerun; the future corpus is 162 fixtures.
Hygiene is clean across 272 library/root files, all 711 warning headers and
112 old HTML paths are retained, and one book section is added. Since the
entire TeX source is unchanged, no new TeX rendering is needed.

Evidence: /tmp/acl_geom_codex_tensor_component_e49 and
/tmp/acl_geom_tensor_shared_probes. Scope is on #5 comment 6160156069.
Chit6115 coordinated ownership; 6122/6123 discuss checking and scope; 6124
provides exact source/book/goal review pins. Root remains sole editor/compiler
and Claude read-only. No review reply has arrived; acceptance is not inferred.
After this single append, rerun full build/book, commit/push the five-path
checkpoint, observe exact CI and report on the repository issues. Keep the
single monitored build family, two threads and 30 GiB available-memory stop.
The durable goal remains active; the guarded-Q initial chart is still central.


## Every tensor component gives a represented composite (#5)

From 7a7b91a907997777de1eaabfd8568d88f0187c5e, the focused 181-line module
Correspondence/TensorRealization.lean proves three public results for the
existing scalar branch representation. Over arbitrary k in an ACF ambient,
FiniteCorrespondencePair.exists_tensor_component_embeddings realizes every
minimal-prime component of the shared-middle branch-field tensor by two
embeddings fixing the middle field. exists_composite_of_tensor_component
constructs an actual finite endpoint pair and Composes witness for the original
germs, retaining the exact tensor kernel and both endpoint images.
tensor_component_endpoint_ideal_eq proves that equal kernels give equal
endpoint ideals; the composite germ is independent of the chosen embeddings.
The uniqueness statement needs no ACF hypothesis. No injectivity from tensor
components to endpoint germs is asserted.

Three private helpers are consumed: embed the finite Artinian prime quotient
using IsAlgClosed.lift; transport branch data and pair ideals through a field
embedding; and compare polynomial relations through equal algebra kernels.
All actual branch, closure and ideal data are derived, not supplied as a
composition oracle. Concrete squaring/transpose consumers start from an
arbitrary minimal prime, derive both source-square identities, obtain an
actual diagonal-or-antidiagonal composite, and compare its germ with any
other realization of the same component. The source's geometric
coordinate-ring/localization bridge remains open. No group chunk, coherent
cover, initial affine chart or reconstruction-completeness input is proved.

Private producer/consumer pass default checking and standard Mathlib lint
with empty logs (2.00s each; minimum available 40.68/41.04 GiB). Scoped metadata
passes in 4.00s/minimum 40.57 GiB: six declarations, three public, with only the
standard three axioms on the public rows. This is not a whole-library axiom
certificate. Private book passes in 30.01s/minimum 39.97 GiB. Actual-main full
build passes in 76.02s/minimum 38.57 GiB; book in 8.00s/minimum 40.36 GiB; four
focused checks in 6.00s/minimum 40.61 GiB. All 162 prior fixtures and eight
baselines (332 files) remain byte-exact, not rerun; the future corpus has 166.
Hygiene is clean across 273 files. All 711 warning headers and 113 prior HTML
paths are retained, with one new section. Every older math module and the entire blueprint stay exact;
no new TeX rendering is needed. The book and PROJECT_GOAL state the exact scope.

Integration initially stopped on three new untracked source paths:
sources/group_configuration/, sources/group_configuration_blueprint.pdf and
sources/group_configuration_blueprint.tex. They were preserved, unread and
unmodified, and excluded from this five-path checkpoint. A preintegration
unchanged-head build is archived separately and not counted as new validation.
Tracked-file and explicit-stage guards then allowed integration to proceed.
Provenance/ownership is pending via chit6138 and #1 comment6160540706; do not
silently stage or delete these unrelated paths.

Evidence: /tmp/acl_geom_codex_tensor_realization_7a7 and
/tmp/acl_geom_realization_shared_probes. The original private embedding report
is #5 comment6160354051; the strengthened target and exact source/book/goal
review are in chit6133/6134/6137. Root remains sole editor/compiler and Claude
read-only; no review reply has arrived, so acceptance is not inferred.
After this single append, rerun full build/book, commit/push only the five
reviewed paths, observe exact CI and report on the repository issues. Keep
one monitored build family, two threads and the 30 GiB available-memory stop.
The full durable goal remains active; guarded-Q initial chart extraction and
unconditional reconstruction remain open.

## Group configuration theorem blueprint (#12/#1)

A second, self-contained LaTeX blueprint now lives in
`sources/group_configuration_blueprint.tex` with its thirteen parts in
`sources/group_configuration/00-scope.tex` … `12-lean.tex` (build with
`pdflatex` three times from `sources/`; the PDF is not tracked). It gives an
informal (not Lean-verified) proof of Hrushovski's group configuration theorem
for algebraically closed fields "up to interalgebraicity", in the form the
reconstruction blueprint needs: from six
tuples forming a group configuration (`def:gc`, with the canonical-base
non-degeneracy clause (GC4), which is clause (iv) of the `Ψ` witness) it
produces, over `k' = acl(k,e)` for a tuple `e` of five independent generic copies
of group points, a connected group `G` of germs of quasi-rational self-maps of a
variety `V` of dimension `m`, a transitive faithful `G`-set `S ⊇ V_gen`, and
generic `g_a, g_b ∈ G`, `y' ∈ V_gen` with the configuration pointwise
interalgebraic over `k'` with `(⌜g_a⌝, ⌜g_b⌝, ⌜g_b g_a^{-1}⌝, g_a(y'), y', g_b(y'))`
(`thm:main`). It then shows `G` and `S ≅ G/H` are constructible (definable in
`K^eq`) over `k'(t)` and `k'(t,y_0)` for fresh sampling tuples chosen in two
stages (`thm:constructible`, via a K-points form of Chevalley from Mathlib's
`PrimeSpectrum.isConstructible_comap_image` and a generic-quantifier lemma),
proves descent of independent parameters into `k` (`thm:descent`), and shows
that the `Ψ` witness of `AclGeom/Config/Psi.lean` is a group configuration with
`n = 2`, `m = 1` (`prop:psi-gc`, `cor:psi`). Every model-theoretic notion is
replaced by a field-theoretic one (types by generic points of loci, forking by
transcendence degree, canonical bases by smallest fields of definition computed
from reduced row echelon bases, definable functions by quasi-rational maps,
imaginaries by explicit codes of finite sets). Section 12 is the proposed Lean
architecture: a new `lean_lib GroupConfig` importing `AclGeom`, one module per
section.

Explicitly outside the document: Weil's theorem (algebraization of the
constructible group), the rank-two classification (blueprint Lemma
`affine-action`), multiplier identification, guarded origin/meet normalization,
and finite-ambient descent. The results are stated only for ambient fields of
infinite transcendence degree over `k` (`conv:ud`); `rem:finite-trdeg` records
why the germ definitions collapse otherwise, and `rem:psi-hyp`(c) records that
returning witnesses from an ambient extension to `K` is a separate, unproved
model-completeness step (`hasAffineGridCoordinates_of_chart` is not such a
descent theorem).

Review history (2026-10-13/14). Four independent referee passes by Claude
subagents (sections 1–4, 5–6, 7–8, 9–12 with Lean-name audit) and one
verification pass over the rewritten passages found no blocking error; their
MAJOR findings (the existence half of `lem:eval`(2), the proof of
`lem:comp-codes`(2), the invertibility clause of `lem:triple`, the (H3)
simplification via `lem:prod-indep`, the counterexample in `rem:psi-hyp`(b), the
informal/precise main-theorem mismatch, two wrong Mathlib names, the last
sentence of `lem:hw-basechange`, and the missing `y_i ∈ V_i(K)` conjuncts in the
chain relation of `lem:adm-constructible`) were all repaired in the text. codex
audited sections 09–11 and the remark `rem:connected` in 05 independently and
found three further genuine errors, each recorded on #12 and repaired: the stabiliser condition in
`thm:constructible`(2) evaluated parameter chains at the non-generic point
`y_0` (comment 6160748550; repaired with the fresh-representative argument
`g_v γ = g_{u'}`, `F(u',y_0) = F(v,y_0)`); `rem:connected` falsely claimed that
every element of `S` has a presentation `γ·ι(y)` with `y ⫝ γ` (comment
6160857201; replaced by the translation-group counterexample); and
`rem:finite-trdeg` claimed a finite transcendence degree suffices (comment
6160876868; replaced by the vacuity argument). codex accepted sections 09–11 and
the corrected remark in 05 at the pinned hashes recorded on chit (#6170, #6179),
including the staged sampling tuple, the `Adm^×` restriction of the word
relation and the descent/scope wording of 11; this is an informal mathematical
review, not Lean certification. The referee reports are not tracked; they were produced under
`/tmp/acl_geom_claude_gct_blueprint/review/`.

Agreed division for the Lean work (chit #6170): Claude owns the three source
paths above and this entry, and takes the rank calculus, loci, fields of
definition, canonical bases, germs and Hrushovski–Weil lanes; codex owns the
compiler slot, `PROJECT_GOAL.md`, and the constructibility lane
(`GroupConfig/Constructible`: K-points Chevalley and the generic quantifier,
proposed on `PrimeSpectrum.ConstructibleSetData` with
`MvPolynomial.pointToPoint`). Shared library/root ownership and the minimal
constructible-set interface are to be fixed on chit before any `lakefile.toml`
or `lean_lib` edit. The original reconstruction endpoint of `PROJECT_GOAL.md` is
unchanged; this blueprint supplies a proposed proof route for the "missing group
extraction" that the reconstruction blueprint's §8.2/8.3 route needs, not a
replacement of it, and its Lean formalization remains open (#12 is not
discharged by this source checkpoint).

## K-points Chevalley starts the GroupConfig library (#12)

From c082e7ecfb41cb900dc41f109ec9d28f1d1566ac, the dedicated `GroupConfig`
Lean library begins with `Constructible/Basic.lean`. Its three public
declarations are `IsConstructibleOver`,
`isConstructibleOver_iff_exists_polynomial_data`, and
`IsConstructibleOver.image_projection`. The definition pulls back Mathlib
constructible subsets of the polynomial prime spectrum to field-valued points;
the equivalence identifies it with finite unions of cells defined by finitely
many polynomial equations and one inequation over the base. The projection
theorem proves the supplemental blueprint's Section 9 K-points Chevalley
statement. Both coordinate blocks are finite; the base field is arbitrary,
the ambient field is algebraically closed, and no transcendence-degree
hypothesis is imposed. The definition and polynomial-data equivalence do not
require finite coordinate types or algebraic closedness.

The point-lifting argument is proved internally. A finite-type domain and an
embedding of its base into the algebraically closed ambient field give a
nonzero tensor algebra. A maximal quotient is finite over the ambient field
and embeds into it. Quotienting a common kernel and localizing a prime
quotient at the chosen nonvanishing produce a point over the specified base
point, preserving the cell's equations and inequation. Mathlib's spectral
Chevalley theorem then proves the desired equality with the actual projection
on field-valued points. Five private helpers have this named consumer; no
axiom, checking-limit change, custom instance or global simp attribute is added.

The new library is a default Lake target with the same standard Mathlib lint
setting as AclGeom. The new book chapter records only these proved results.
The generic quantifier, remaining closure/substitution interface, group
configuration, group constructibility, descent, algebraization, guarded-Q
chart and unconditional reconstruction remain open. PROJECT_GOAL is unchanged.

Before integration, the producer passed default checking and standard Mathlib
lint with an empty log (2.00s, minimum available 42.33 GiB). The actual-library
hyperbola consumer constructs the polynomial cell xy=1 and proves that its
projection is the nonzero locus; it passes without warnings (2.00s, minimum
42.31 GiB). Dependency prints for exactly the three public declarations report
only propext, Classical.choice and Quot.sound. This is a scoped check, not a
whole-library axiom certificate. The prior AclGeom fixtures and mathematical
modules are unchanged; no unchanged fixture corpus is claimed as rerun.

Ownership/interface agreement is chit6182–6184: Codex owns Constructible/*,
lakefile/root for this checkpoint and the compiler; Claude develops rank,
loci, fields of definition, germs and Hrushovski–Weil privately, asking before
any Lean invocation. Source checkpoint c082e7e and exact CI38512341939 are
fully verified; see #12 comment6161140720. Claude independently accepted the producer at its exact hash in
chit6193; documentation ownership is confirmed in chit6191. Evidence and consumer are under
/tmp/acl_geom_group_configuration_audit; full build/book must pass after this
entry and every other edit, before the checkpoint commit/push. Keep one
monitored family, two threads and the 30 GiB available-memory stop. The
untracked supplemental PDF stays excluded from the commit.


## GroupConfig rank and universal-domain foundation (#12)

After d97113a, three modules formalize the supplemental blueprint's Section 1
foundation: `GroupConfig/Rank.lean`, `Setting.lean`, and `Automorphisms.lean`.
The rank of a set over C is Mathlib's algebraic-independence matroid rank over
k(C), valued in extended natural numbers. Independence quantifies over finite
subsets, so infinite ranks are never cancelled. The proved calculus includes
finite character, the tower law, closure invariance, symmetry, transitivity,
independent closure intersection, independent base change, and a bridge from
set rank to the transcendence degree of the field it generates. These facts
hold over arbitrary fields. Locus dimension and the generic-quantifier rank
count are the next named consumers.

`UniversalDomain` explicitly requires infinite transcendence degree over the
base, with algebraic closedness kept as a separate hypothesis for later work.
`IsSmall` means finite rank. Every small set has the same relative closure as
one of its finite subsets, and every small set admits a fresh tuple of any
finite rank. Base-field automorphisms preserve the relative matroids, ranks
and independence. The book records this precise foundation scope; no locus,
canonical-base, group-extraction, algebraization, guarded-Q or unconditional
reconstruction theorem is claimed by this checkpoint. The original source
and supplemental blueprint are unchanged; PROJECT_GOAL remains unchanged.

The existing private ideal-contraction proof in
`AclGeom/Correspondence/GenericExtension.lean` is now public as
`AclGeom.comap_map_mvPolynomial_eq_self`. Its statement and proof are unchanged,
and both existing callers use the new name. Claude's next Locus module can
reuse it rather than duplicate the argument. No other AclGeom mathematics is
changed.

Claude supplied the three final producer hashes in chit6209 and released the
compiler slot. Codex independently reviewed all three, including the added
set-rank/transcendence-degree bridge and the automorphism transport proof,
and checked frozen copies in a complete independent module namespace. All
three pass default checking and explicit standard Mathlib lint with empty
logs (2.00s each; minimum available memory at least 42.05 GiB). The integrated
proofs match those pins; module status paragraphs state proved results and
remaining obligations accurately, and the universal-domain class field has
the docstring required by the book renderer. Chit6211 records this
review and the contraction API decision. Codex owns the book/root/CONT and
checkpoint integration; Claude continues Locus privately and requests the
compiler slot before checking.

Evidence and scoped consumer checks are under
`/tmp/acl_geom_group_configuration_audit/foundation_probe`. Run the full
`lake build` and `lake exe book` after this entry and all other edits before
committing. Keep the single monitored compiler family, two threads, and
30 GiB available-memory stop. The supplemental PDF remains untracked and is
excluded. Constructibility closure and the generic quantifier are separate
ongoing work; the frozen 117-item M4a chain is untouched.


## Constructibility under Boolean operations, substitution and quantifiers (#12)

After af5b6cd, `GroupConfig/Constructible/Closure.lean` adds thirteen proved
closure lemmas to the K-points interface: empty and universal sets, binary and
finite indexed unions/intersections, complements, polynomial zero/nonzero loci,
polynomial preimages, extension of the coefficient field, and existential and
universal finite-tuple quantification. Only the quantifier lemmas need finite
coordinate blocks and an algebraically closed ambient field. All coefficient
fields are arbitrary, and none of these statements needs a rank bound.

This proves the Boolean, polynomial-substitution and ordinary-quantifier
portions of the supplemental `cor:constructible-closure`. It does not yet
package general constructible partial functions or quasi-rational graphs.
The generic-quantifier majority construction is the named next consumer of
base extension, substitution and finite Boolean operations; graph and word
relations consume ordinary quantification. The book and docstrings distinguish
quantification over all ambient-field tuples from the still-open quantification
over generic points. The full group, chart and reconstruction obligations and
PROJECT_GOAL are unchanged.

Claude independently accepted the complete prototype in chit6220; the module
adds headers and scope/docstrings to the same proofs. The prototype and the
integrated module pass default checking with standard Mathlib lint. Two concrete
private consumers combine the interface: a universally quantified polynomial
implication is constructible, and sampling a relation at a tuple from an enlarged
base field is constructible over that field. The final consumer check has no
warnings and prints only the three standard axioms for the six checked closure
declarations (a scoped check, not a library-wide certificate). Its early drafts
needed explicit predicate/preimage unfolding; the final proof uses the current
Mathlib set API without deprecated aliases. Evidence is under
`/tmp/acl_geom_group_configuration_audit/ClosureConsumer.lean` and the monitored
`gct_closure_*` logs. Full build and book gates must pass after this entry and
all other edits before committing.

The preceding af5b6cd foundation checkpoint is fully green: exact CI38516836369
completed both jobs and every reported step successfully, with completed logs
verifying the 19015-job library build, book, artifact11872461521 and deployment
of that exact hash. The supplemental PDF remains excluded. Claude continues
private Dimension/Locus work under the shared compiler lease protocol; these
unintegrated modules are not claimed as public results here.


## Dimension drop and implications from genericity (#12)

After c000e0f, `GroupConfig/Dimension.lean` proves that a surjection of domains
of finite transcendence degree over a field with nonzero kernel strictly drops
transcendence degree. Lift a transcendence basis of the target; if dimensions
were equal, it would be a basis of the source, forcing a nonzero kernel element
to be algebraic over its generated polynomial ring. Mathlib's algebraic ideal
contraction lemma then contradicts the injectivity on that ring. Proper
specialization of finite tuples strictly drops rank, so equal ranks turn a
containment of their vanishing ideals into equality.

Review removed a duplicated basis proof: the generated-ring versus generated-
field dimension bridge now uses Mathlib's scoped fraction-field algebraicity
and `Algebra.trdeg_add_eq`. The direct duplicate of
`Algebra.adjoin_range_eq_range_aeval` was removed. All new declarations have the
locus dimension criterion as a named consumer. Rank adds the change-of-base-type
bridge and the finite-set converse from unchanged rank to `IndepOver`.

`GroupConfig/Locus.lean` defines the extended locus ideal and its exact
contraction, proves primality over an algebraically closed coefficient field,
and defines genericity by equality with the extended base ideal. This explicit
genericity hypothesis gives the original base ideal, preserved rank, and
independence from the enlarged field for finite tuples. It descends to a smaller
intermediate field and is invariant under automorphisms over that field; any
two finite generic tuples are conjugate when the ambient field is algebraically
closed. Generic-point existence and the converse from independence to unchanged
locus remain open. The book and statuses preserve those boundaries. No group
extraction or completeness claim follows from the definitions or implications
alone. Both TeX blueprints, PROJECT_GOAL and all AclGeom modules are unchanged.

Claude supplied frozen Rank/Dimension/Locus pins in chit6226, after the review
and simplification requests in chit6218/6221. Codex independently reviewed every
new proof and checked all five complete modules (including unchanged Setting
and Automorphisms) in a separate module namespace: standard Mathlib lint,
default limits, empty logs, all exits zero (Rank/Setting/Automorphisms/Locus
2.00s each, Dimension4.00s; minimum available memory at least41.86GiB). The
integrated proof bodies are unchanged; statuses are precise and Locus imports
are narrowed to its actual dependencies. Evidence and frozen producers are in
`/tmp/acl_geom_group_configuration_audit/locus_probe`. Full build and book must
pass after all edits before committing. Keep the single monitored compiler
family, two threads and30GiB available-memory stop. The PDF remains excluded;
Claude develops the generic-point existence/converse sequel privately.


## Generic points in the ambient universal domain and fresh conjugates (#12)

After 063e02a, Locus constructs the generic points needed for represented base
loci. With algebraically closed k and K, infinite transcendence degree of K/k,
a finite tuple a, and a finite-rank intermediate field M, `exists_isGenericOver`
constructs a tuple a' in K whose ideal over M is exactly the extended k-ideal
of a. It embeds the earlier abstract generic point: take a finite transcendence
basis of its generated field over M, relocate it to a fresh tuple in K, and
extend algebraically by `IsAlgClosed.lift`. The final ideal is preserved by the
injective field homomorphism. No genericity witness is assumed by the caller.

Dimension drop then proves `isGenericOver_self_iff`: a tuple's locus is unchanged
on extending the base to M exactly when it is independent from M, under the
same universal-domain/smallness hypotheses. `exists_algEquiv_indepOver` supplies
a conjugate over a small algebraically closed M independent from a given small
set. The two base-change smallness lemmas also apply without unnecessary
algebraic-closedness assumptions. The module, Dimension status and book are
updated together to reflect these newly proved statements.

Coverage remains precise: this supplies `lem:genexists` for a represented
base locus. Its arbitrary-prime formulation (a prime P defined over M, without
a previously supplied tuple representing P) remains a separate obligation.
The original and supplemental TeX are unchanged. These are mathematical
existence/converse results, not group extraction or a guarded chart;
PROJECT_GOAL and the full reconstruction endpoint remain unchanged.

Claude supplied final pin27470759 in chit6231. Codex independently reviewed the
entire appended construction, requested the coverage/docstring clarifications
in chit6233, and checked the frozen module against the exact committed
dependencies with default checking and standard Mathlib lint: empty log,
exit0,6.00s,minimum available41.90GiB. The integrated proof bodies are unchanged;
only the stated docstrings/coverage boundary are clarified. Frozen sources and
evidence are under `/tmp/acl_geom_group_configuration_audit/locus_exists_probe`.
Full build/book gates must pass after all edits before committing, using one
monitored family, two threads and the30GiB stop. The untracked PDF stays excluded.

Codex has also privately proved three generic-quantifier prerequisites:
a rank-drop count for a finite family of finite sets with additive total rank,
constructibility of finite cardinality thresholds, and invariance of polynomial
constructible sets under base-field automorphisms. These remain unintegrated
pending the full generic-quantifier assembly and peer review; no source claim
is marked complete by those private results.


## Reduced row echelon bases and subspace fields of definition (#12)

After 56e2129, `GroupConfig/Rref.lean` constructs a canonical pivot-indexed
basis for every subspace of a finite linearly ordered coordinate space over
an arbitrary field. Projection to intrinsic pivot coordinates is injective;
witnesses with distinct leading coordinates give the reverse dimension bound,
so projection is a linear equivalence. Its inverse constructs the reduced row
echelon basis. The module proves its pivot/leading-coordinate properties,
spanning and uniqueness, and explicitly verifies Mathlib's
`Matrix.IsReducedRowEchelon` predicate for the resulting matrix.

The subfield generated by the basis coordinates is the smallest field over
which the subspace is spanned by field-valued vectors (`definedOver_iff`).
For the reverse implication, the subspace of F-valued vectors has the same
pivots by a dimension comparison, and its reduced basis coincides with the
ambient one. An explicit finite set generates this field. Automorphisms
transport it with the subspace; an automorphism preserves the subspace exactly
when it fixes the field of definition pointwise. These are the supplemental
Section 2 subspace results, with no algebraic-closedness or universal-domain
hypotheses. Polynomial-ideal fields of definition and canonical bases remain
open. The book and module status state this scope. PROJECT_GOAL, both TeX
sources and all AclGeom modules are unchanged.

Claude's frozen474-line producer a430b640 was independently read in full by
Codex and checked with default limits and explicit standard Mathlib lint:
exit0,emptylog,4.00s,min42.11GiB. Chit6242/6244 records acceptance and root
ownership of the small integration additions. The Mathlib matrix predicate
certificate and finite-generator witness are checked separately (2.00s,
emptylog), and the leading-index helper now reuses Mathlib's existing
`row_ne_zero_iff_exists_isLeadingEntry` with its statement unchanged. All
other original producer names, statements and proofs are preserved. Evidence
and the original pin are in `/tmp/acl_geom_group_configuration_audit/rref_probe`.
Full build and book must pass after all edits before committing. Keep the
single monitored compiler family, two threads and30GiB available-memory stop.
The supplemental PDF remains untracked/excluded. Claude is developing the
ideal-filtration sequel privately and has requested the next compiler lease.


## Generic quantification and proper polynomial zero sets (#12)

After bd92603, `GroupConfig/Constructible/Generic.lean` supplies the represented-
locus forms of supplemental `lem:gen-constructible` and `lem:genquant`.
Constructible sets are invariant under automorphisms of their coefficient field;
generic-point conjugacy gives constant membership in any invariant set. A
constructible subset of a represented locus with no generic point over the
algebraic closure of its coefficient field lies in a proper polynomial zero set
over that field. For this last clause, construct a generic point, choose one
nonvanishing equation from each relevant polynomial cell, and multiply them.
Cells without such an equation are empty on the locus by specialization.

The generic quantifier is proved outright from the source's sampling hypotheses:
each sample is generic over M, and the joint rank equals the sum of the sample
ranks. Adjoining N parameter coordinates lowers rank on at most N samples. With
at least2N+1 samples, truth at every generic point over acl(M,x), truth at some
such point, and truth at at least N+1 samples are equivalent. The majority locus
is constructible over M together with all sample coordinates. The rank-count
cancellation uses a finite sum of finite ranks; no infinite-rank cancellation is
used. Genericity after parameter extension follows from the committed locus
independence converse, not from an assumed genericity conclusion.

The coefficient field M is only small, not algebraically closed. Algebraically
closed base/ambient fields and the universal-domain hypothesis are explicit.
The theorem permits dimension zero as well. Loci are represented by finite tuples;
arbitrary-prime realization remains open, as do germ/group constructibility and
the reconstruction frontier. The book and Basic/Closure module overviews are updated in
the same change; PROJECT_GOAL, both TeX sources and AclGeom remain unchanged.

The complete374-line producer is frozen at SHA5c416fcf in
`/tmp/acl_geom_group_configuration_audit/Generic.lean`. It passes default limits
and explicit standard Mathlib lint with an empty log: exit0,2.00s,min42.38GiB.
The three prerequisite proofs received peer acceptance in chit6237. Claude then
independently read the complete frozen module against both source lemmas and
accepted it without corrections in chit6257. Seven scoped axiom reports for the
public results contain only propext, Classical.choice and Quot.sound; this is
not a library-wide audit. Full library/book gates must pass after all edits
before the checkpoint.
All validation uses the single monitored compiler family, two threads and the
30GiB available-memory stop. The untracked supplemental PDF stays excluded.


## Fields of definition of polynomial ideals (#12)

After516f016, `GroupConfig/FieldOfDefinition.lean` proves the supplemental
Section2 ideal-field-of-definition theorem over arbitrary fields. Bounded-degree
coefficient spaces are finite. Coefficientwise linear projections preserve
extended ideals and degree, and finite basis decomposition recovers every
polynomial. This proves definedness of an ideal iff all its degree pieces are
defined over the field. Noetherian generators give stabilization of their
fields of definition, finite generators over the prime field, and an explicit
bounded-degree generator witness with eventual definedness equivalence.
Automorphisms transport the field of definition; an automorphism preserves the
ideal exactly when it fixes that field pointwise.

The root addition also discharges the previously bypassed filtration(2): if
I's degree-d piece is F-defined and d'≤d, compare I with the extended contraction
J=(I.comap mapF).map mapF. Their degree-d' pieces agree by the bounded-degree
membership lemma, while Mathlib's map_comap_map makes J F-defined. Hence the
lower piece is F-defined. This proves FOD monotonicity and identifies idealFod's
supremum with the source's increasing union. All three filtration clauses now
have explicit public results. The scalar-extension remark and canonical bases
remain obligations; PROJECT_GOAL and both TeX sources are unchanged.

Codex independently read all524lines of Claude's frozen88359197 producer against
source02 and checked it with default limits and standard Mathlib lint:
exit0,emptylog,2.00s,min42.07GiB. Generalized coefficient projections have named
Contraction/Descent consumers in the pending peer chain. The Mathlib polynomial
coefficient-range API replaces the old manual lift, with its statement preserved.
The producer proof bodies/statements stay unchanged in integration; the four
root additions are degSubspace_definedOver_of_le, fod_degSubspace_mono,
mem_idealFod_iff and exists_forall_idealDefinedOver_iff. Ownership6334 permits
these additions and the precise Status rewrite. Their complete default/stdlint
check passes emptylog2.00s/min42.04GiB. Peer review of these four root additions
is requested6335 and remains pending; all statements have checked proofs and the
existing producer was independently reviewed in full. Ten scoped axiom reports
contain only propext, Classical.choice and Quot.sound. Root/book/Rref status and
this guide are updated together. Full library/book validation must pass after
all edits before the checkpoint.
Use one monitored family, two threads and the30GiB stop; exclude the untracked PDF.


## Canonical bases and their six properties (#12)

After408ed4b, `GroupConfig/CanonicalBase.lean` defines the canonical base of a
finite tuple via the smallest field of definition of its locus. It lies in the
coefficient field and is small. The six supplemental Section2 properties are
proved: preservation of rank over the canonical base; the independence/
containment criterion; automorphism compatibility and the fixed-locus/conjugacy
criterion; equality over mutually independent coefficient fields; interalgebraic
canonical bases of interalgebraic tuples; and invariance on adjoining an
independent set. The original base need not be algebraically closed. Ambient
algebraic closedness, smallness, closed coefficient fields and the universal-
domain assumptions are explicit where used. No group/chart/reconstruction
conclusion is supplied as an input.

Codex independently read Claude's complete425-line frozene0cf6f33 producer
against the source and checked it against the integrated FOD module with default
limits and standard Mathlib lint: emptylog,exit0,6.00s,min41.41GiB. Cb5 is now
generalized to two different finite coordinate types, matching arbitrary finite
tuples in the source. The one-direction argument is a private helper with the
public Cb5 theorem as its sole consumer. A polymorphic local helper initially
exceeded default heartbeats; extraction into that private helper gives a clean
6.00s/min41.30GiB check, with no checking-limit increase. Frozen generalized
pin209bf30 is in `/tmp/acl_geom_group_configuration_audit/CanonicalBaseGeneralized.lean`.
Peer6344 grants this generalization and the Status rewrite; remaining producer
proof bodies/names/statements are preserved. The later Configuration integration
will replace its duplicate primed Cb5 result with this generalized theorem, as
agreed. Existing FOD/Rref status and the book are updated with the new coverage.
PROJECT_GOAL, both TeX sources and the reconstruction endpoint are unchanged.

Claude independently accepted all four previously committed FOD additions
without corrections in chit6345; the pending-review status at408ed4b is now
resolved. Root compiler ownership follows explicit terminalrelease6347. Full
library/book validation after all edits remains required before this checkpoint.
Twelve scoped public-result axiom checks contain only propext, Classical.choice
and Quot.sound; this is not a library-wide audit. The integrated module also
passes default limits and standard lint with an empty log:6.00s,min41.97GiB.
All validation uses one monitored family, two threads and the30GiB
available-memory stop. The untracked supplemental PDF stays excluded.


## Six-point configuration data and early guarded-Q input (#12/#27)

Afterc47f922, `GroupConfig/Configuration.lean` exposes the supplemental Section7
six-point predicate, its sixteen-triple constructor, pairwise independence,
equal group/space ranks, coordinate-renaming invariance of canonical bases,
the two generating relabelings, and automorphism/interalgebraic replacement.
The predicate's genuine incidence/independence/canonical-base hypotheses remain
explicit. This is configuration data and the proved conditional consequences;
it is not the group-extraction theorem or the actual Psi input construction.
Remaining rank bounds, total ranks, point/line independence and independent
base change remain obligations until their own producers integrate.

Codex independently read all661lines of frozen2f6a19a against source07. The
only integration code change is removal of the unused Germ.GenericSet import:
a complete default/stdlint check then passes emptylog18.00s/min39.70GiB.
Peer6364 grants this import/Status edit and confirms the missing dependency.
The narrowed source is frozen as ConfigurationNarrow.lean, with all existing
names/statements/proofs preserved. Canonical-base source improvements already
removed the superseded primed Cb5 helper and updated its three uses in the
peer producer before this pin. Ten scoped public-result axiom reports contain
only propext, Classical.choice and Quot.sound. Full library/book gates after
all edits are required before committing; one monitored family,
two threads and the30GiB stop; exclude the untracked supplemental PDF.

This dependency audit allows the actual Psi-to-configuration input to be
implemented before the germ chain. The proof plan in the private audit directory
uses Cb1 plus Psi's atom-freeness clauses to force each parameter plane to be
interalgebraic with the canonical base of its incidence pair. GC1/GC2 use finite
rank, and GC3 uses exactly the16 noncollinear triples. Claude independently
accepted that mathematical strategy in chit6360, flagging the finite-ambient
lift as a separate proof obligation. One finite-tuple algebraicity-capture
prerequisite is now privately checked: CanonicalBaseCapture.lean pinf04cc182,
emptylog2.00s/min40.98GiB. It is not integrated until the coherent actual input
construction assembles. No guarded-chart, group-algebraization or reconstruction
claim is discharged by this plan. PROJECT_GOAL and both TeX sources are unchanged.


## Finite codes, locus points and quasi-rational graphs (#12)

After `5efa805`, the independently reviewed producer snapshots Codes
`ba24ef10` (299 lines), Germ/Variety `ab0d31d0` (143), Contraction `9ca8d85e`
(84), and QuasiRational `c1af8e1e` (334) integrate with every original name,
statement and proof preserved. Only module documentation/status changes under
chit ownership 6366. Complete independent default-limit/standard-lint checks
pass with empty logs: Codes 2s/min38.63GiB, Variety 2s/min38.97GiB,
Contraction 2s/min38.97GiB, QuasiRational 4s/min33.72GiB. The initial three-module
full build passed 19037 jobs in44.02s/min31.60GiB; a new long documentation
line was shortened before the final gates. Root compiler reservation 6377
withdraws the unaccepted peer lease6375; the shared lock prevents overlap.

The coding polynomial retains monomial indices and is injective over domains.
Its finite scalar coefficient carrier is natural, has the pointwise-fixing/
set-stabilizing criterion, lies in the coordinate ring, and generates the same
relative algebraic closure as the coordinates. Equality of scalar carriers
alone is not asserted to recover the tuple set. The literal degree-bounded
coefficient-vector presentation and definable-closure/conjugate-set clauses
remain obligations. Represented-locus point ranks are bounded by dimension,
equality detects genericity, independence detects genericity over a larger
small field, and algebraic adjoining preserves rank. Arbitrary-prime realization
remains open. Polynomial extension/contraction commute along any injective
variable renaming, with no algebraic closedness or finite-coordinate requirement.

Quasi-rational expressions are evaluated in a perfect ambient field. Equivariance,
coefficient-field inclusion, generic agreement on represented loci and
Frobenius-twisted denominator-cleared composition are proved. The composite
is defined on the natural composition domain and agrees there; equality of
maximal expression domains is not claimed. The dcl characterization remains
separate. Codex's new `Constructible/QuasiRational.lean` proves constructibility
of finite-output domains and graphs. The graph has equations
w_j^(p^e) Q_j(u)=P_j(u) and Q_j(u)≠0; domain needs no perfection, graph needs
only ambient perfection, neither needs ACF/smallness/universal domain. Named
consumers are the Section9 admissible-parameter and germ-word relations,
whose complete construction remains open. The private producer check passed
emptylog2.00s/min35.54GiB after supplying the sum coordinate type explicitly;
no checking-limit increase. Full final library/book and scoped axiom gates
must pass after every edit before committing.

Root's actual Psi canonical-base clauses are drafted privately using the
checked finite-tuple capture argument and existing
`RankEq.eq_of_le_of_not_le_point`; they remain unvalidated at this entry.
The full16-triple input, universal-ambient lift, guarded chart, group extraction,
algebraization and unconditional reconstruction remain open. PROJECT_GOAL and
both TeX sources are unchanged. The excluded supplemental PDF stays untracked.
Use one monitored two-thread family and stop below30GiB available memory.


## Actual Ψ canonical-base clauses (#12/#27)

After `e91729d`, `AclGeom/Config/CanonicalBaseInput.lean` derives the three
GC4 identifications directly from the actual Ψ witness in an ACF universal
ambient. The public results are `QWitness.Psi.racl_canonicalBase_XY_eq_A`,
`racl_canonicalBase_YZ_eq_B`, and `racl_canonicalBase_XZ_eq_C`. Public signatures
spell out the finite representative tuples. The original base need not be ACF.
No caller-supplied canonical-base, group, chart or completeness premise is used.

Cb1/rank cancellation captures the target over the source and canonical base;
containment of that base in an atom contradicts the actual Ψ freeness clauses.
The existing `RankEq.eq_of_le_of_not_le_point` identifies the closed hull with
the rank-two plane. All new helpers are private with these three named consumers;
no chain of normalization interfaces is added. Private pin `de3f256b` checked
clean at default limits/standard lint: emptylog2.00s/min35.69GiB, after fixing
noncomputability, a closed-field coercion, and the algebraic-closure lemma's
namespace. No checking limit was increased. Peer ownership/strategy for the
root actual-Ψ lane is coordinated through chit; final code review requested6380.

This replaces the previous entry's unvalidated-draft status for these three
clauses only. The complete16-triple GroupConfiguration input and universal-
ambient lift remain open, as do guarded chart extraction, algebraization/actions
and unconditional reconstruction. Both source guards remain on the downstream
chart target. The book and root import are synchronized in this change; the
shared goal and source TeX are unchanged. Full final library/book and scoped
axiom gates must pass after all edits before committing. Use one monitored
family, two threads and the30GiB stop; exclude the supplemental PDF.


## Complete actual Ψ six-point input (#12/#27)

After `389cb3a`, `AclGeom/Config/ConfigurationInput.lean` derives the full
supplemental `GroupConfig.GroupConfiguration` predicate from an actual Ψ
witness in an ACF universal ambient, over an arbitrary original base.
`QWitness.Psi.groupConfiguration` supplies every GC1–GC5 clause, and
`groupConfiguration_with_ranks` records group rank2 and space rank1. The
six public tuple definitions are the displayed parameter pairs and singleton
space representatives; these two theorems are their named consumers.
No configuration/group/chart/action/completeness premise is supplied by the caller.

GC1/GC2 follow from equal finite ranks of comparable closed hulls. The nine
plane-pair/space triples have rank5. Finite-set independence passes to the
incidence closures to prove AYZ/BXZ/CXY; line replacement gives AXZ/BXY/CYZ;
Z independent from acl(AY), containing X,Y, proves XYZ. The actual sixteen
triples match `indep_of_sixteen` literally. Previously committed canonical-base
identifications give GC4; rank2 gives GC5. All helpers are private with this
construction as consumer. The existing Point.rankEq_one proof is exported,
and the existing private point-adjoining proof is exported as
RankEq.sup_point_of_not_le, with every proof body preserved and its old uses
renamed. No new rank-calculus chain, checking-limit change or source edit.

Frozen rootproducer `PsiConfigurationInputFrozen.lean` pin19e7a696 is276lines;
default-limit/standard-lint check passes emptylog4.00s/min37.68GiB. Initial
failures were point/field projection types, ENat normalization and the literal
CB tuple/coercion conversion; the complete predicate and rank package now
check. Peer strategy6360 accepted the mathematics and exact16 list; independent
finalcode review requested6387/6388 with an immutable snapshot. Root actual-Ψ
lane ownership and compiler reservation6386 are coordinated through chit.

CanonicalBaseInput and the book are updated in the same change to remove
stale fullinput-open wording. The previous entry's fullinput-open status is
now superseded for the ACF universal-domain input only. The universal-ambient
package, appropriate finite-ambient lift/descent, guarded chart (both output
guards), group extraction/algebraization, action classification and unconditional
reconstruction remain open. Reuse the existing QWitness.Psi.lift and lattice/
rank/atom transfer APIs for the ambient package. The shared PROJECT_GOAL
endpoint and both TeX sources are unchanged. Full final library/book and scoped
axiom gates after every edit remain mandatory before the commit. One monitored
family, two threads and the30GiB available-memory stop; exclude the PDF.


## Canonical universal-ambient actual Ψ input (#12/#27)

After `29f8ae8`, `AclGeom/Config/UniversalConfigurationInput.lean` constructs
ConfigurationAmbient K = AlgebraicClosure(FractionRing(MvPolynomial ℕ K))
and configurationBase k K = algebraicClosure k Ω. Its base is algebraically
closed via Mathlib IsAlgClosure.isAlgClosed, applied to the standard relative
algebraic-closure instance. The projection is deliberately not a general global
ACA instance; the specific base instance is registered here. Countably many
variables remain algebraically independent over the algebraic base, using
Mathlib AlgebraicIndependent.algebraicClosure, so the specific UniversalDomain
instance is proved and public. No infinitude or ACF premise is assumed of the
original caller.

QWitness.universalLift uses the canonical embedding and existing Ψ.lift,
which transfers all ranks/incidences and the actual atom-freeness. The public
Psi.groupConfiguration_universalLift returns the full configuration and its
n=2,m=1 ranks. These definitions/instances have this direct consumer and the
source group-extraction application. No generic extension oracle or duplicated
transfer calculus is added.

The first70-line coreproducer passes default/stdlint empty2s/min39.06GiB.
An additional base-instance audit found that the IsAlgClosed/AlgebraicClosure
import alone does not register ACA of the relative algebraic base. Importing
Mathlib.FieldTheory.AlgebraicClosure supplies IsAlgClosure, and projecting
IsAlgClosure.isAlgClosed k supplies the proved specific instance. Both target
instances then synthesize cleanly with the full proof:4.00s/min38.98GiB.
Final immutable producer UniversalConfigurationInputFinalFrozen.lean73lines,
SHAfdb92b723845b80edaf84c9afa64c238f1d2af3f215f5eec05cf380d70440b1f.
Peer review requested6391; root owns the actual-Ψ lane and retains compiler6386
through the final gates. No checking limit changed. Full library/book gates and
scoped axiom checks after all edits are mandatory before committing.

This closes the canonical universal-ambient package and actual witness lift;
previous fullinput/ambient-open entries are historical. Literal image-tuple
comparison and finite-ambient chart/action descent, group extraction/algebraization,
action classification and unconditional reconstruction remain open. Do not claim
semantic representatives in the original field from this lifted configuration.
Both output guards remain at the downstream chart target. PROJECT_GOAL and the
source TeX remain unchanged. Use one monitored two-thread family/30GiB stop and
exclude the untracked PDF.

## Joint goal review and revised memory policy (2026-10-14)

`PROJECT_GOAL.md` now explicitly includes the supporting group-configuration
blueprint. The two agents reviewed this additive update through chit. It
preserves the original reconstruction endpoint and keeps the original
algebraization, action, chart and reconstruction obligations. The supplemental
non-goals bind that document alone. Its weaker clause-(i)–(iv) Ψ proposition,
the main group theorem, constructibility, descent and original-field chart/action
descent remain obligations until checked proofs are integrated.

Adam replaced the available-memory rule with a maximum of **20 GB for the
combined Lean/Lake family** on
[#28](https://github.com/adamtopaz/acl_geom/issues/28#issuecomment-6174030382).
Only one family runs, with two Lean threads. On this host a temporary user
scope enforces the kernel cap; Linux rounds it down to a page boundary. For
example, with the local compiler path configured as above:

```sh
LEAN_NUM_THREADS=2 systemd-run --user --scope --expand-environment=no \
  --property=MemoryMax=20000000000 --property=MemorySwapMax=0 lake build
LEAN_NUM_THREADS=2 systemd-run --user --scope --expand-environment=no \
  --property=MemoryMax=20000000000 --property=MemorySwapMax=0 lake exe book
```

The shared monitor also holds the single-family lock, verifies the kernel cap
before launching a child and samples family RSS. It stops its own family
conservatively at 19 GB, within the 20 GB hard cap. This current policy supersedes
the 30 GiB guards quoted in earlier checkpoint records; those records describe
the measurements taken at the time. No mathematical checking limit changes.

The next reviewed private producers cover the exact Ψ core, literal image
tuples, orbit parameterization and actual admissibility. Claude's Step III and
base-change drafts are also pending checking. Their mathematical reviews are
progress evidence, not committed source coverage; see
[#12](https://github.com/adamtopaz/acl_geom/issues/12#issuecomment-6173927110) and
[#27](https://github.com/adamtopaz/acl_geom/issues/27#issuecomment-6173558980).
The durable goal remains incomplete, and the untracked supplemental PDF stays
excluded from commits.

## Exact Ψ source input (2026-10-14, #27)

The six-point proposition now takes `QWitness.PsiCore`, exactly the twelve
predicates in clauses (i)–(iv). It derives all configuration clauses with group
rank two and space rank one. The partial quadrangle and meets in clauses
(v)–(vii) are unused. Ambient algebraic closedness and a universal domain remain
explicit; the base field may be arbitrary. The source's ACF-base case follows.

The three parameter-rank proofs, three canonical-base identifications and two
configuration/rank proofs move unchanged to the core input. The full witness
record and all eight existing full-Ψ public statements are preserved, using the
proved `Psi.toCore` projection. This keeps the universal-ambient and correctness
consumers intact. An automated source comparison verifies the record, original
statements and verbatim proof bodies. Claude independently reviewed the four
diffs; the final independent standard-lint check of all four modules passed
under default project options and the 20 GB cap.

This discharges the weaker source formulation of supplemental `prop:psi-gc`.
It does not extract a group or a guarded chart. The literal image-tuple comparison,
original-field chart/action descent, group algebraization, action classification
and unconditional reconstruction remain obligations. The full-Ψ canonical lift
still returns a configuration in its chosen universal extension. The frozen M4a
chain and source TeX are untouched.

## Germ representative and automorphism foundations (2026-10-14, #12)

`GroupConfig/Germ/Basic`, `Graph`, `Code` and `Action` now contain the reviewed
representative quotient, graph ideal and canonical-base/automorphism layers.
Every pre-existing producer declaration and proof is preserved. The unchanged
`Representative.extend_equivalent` theorem moves from the later `Eval` producer
into `Basic`, where the source extension clause is introduced. Remove the
duplicate when integrating `Eval`; it is not present on main yet.

The representative relation is a proved equivalence, using generic existence
and quasi-rational agreement. Graph ideals have both coordinate projections,
generic graph-point rank and injectivity on germs. Canonical bases are small
and contained in representative fields. The chosen `codeSet` generates the
canonical base, and automorphisms transport graphs and bases, fixing the germ
exactly when they fix that base pointwise.

The finite generating carrier is not a canonical indexed code vector. Its
global naturality and injectivity are not asserted. The graph-rank theorem is
not presented as an additional abstract ideal-dimension API. Canonical RREF
codes, generic evaluation, composition, the group-theorem dependency chain and
the actual constructible quotient remain later integration slices. Mathematical
and independent standard-lint review passed for all four producer copies;
source comparisons verify all original code and the unchanged moved theorem.
The source TeX, frozen M4a chain and original reconstruction inputs are unchanged.

## Generic germ evaluation and composition (2026-10-14, #12)

The next six germ modules (`Eval` through `GenericSet`) and `IndepConj` supply
generic graph evaluation, composition, identities, associativity, inverse
uniqueness, the monoid of self-germs and its units, independent orbit members
and conjugacy. `lem:indep-conj` is proved for arbitrary finite families of
represented loci with varying coordinate types, also over a small algebraically
closed coefficient field. Finite-rank subfamily lemmas have this named consumer.
The duplicate equivalent-extension theorem is removed from `Eval`, since the
same declaration is already in `Basic`. The moved `IsGen.map` theorem now lives
beside `IsGen` in `GenericSet`, so later consumers need no duplicate.

The generic evaluation/composition statements explicitly use a common small
algebraically closed field containing the relevant canonical bases. Definable
evaluation, individually defined composition, the literal inverse-base equality,
canonical indexed orbit codes and the group-theorem chain remain later slices.
The source TeX and original reconstruction inputs are unchanged.

All 32 pinned higher integration copies (including the later admissible and
invertible-admissible candidates) passed an independent default-option,
standard-lint check in 59.31 seconds under the 20 GB family cap, with empty
diagnostics. This is Lean checking of those copies, not a blanket mathematical
or source-coverage claim for all 32. Only the seven modules above are integrated
in this checkpoint. The prior four-module checkpoint is `0bd0c7f`; its exact
CI, artifact and existing deployment passed. A source audit also distinguishes
the represented-locus base-change API, which assumes representative tuples
independent of the new field, from the arbitrary-extension source formulation.
That generality must still be packaged; no source refutation is claimed.

## Definable germ values and the generated group (2026-10-14, #12)

`DefinableClosure`, `Germ/HW`, `Difference`, `Definable` and `Triple` now supply
the next reviewed layers. Definable closure is the perfect closure and the
fixed field; finite-tuple values are quasi-rational. Under the actual `IsHW`
hypotheses the generated group consists of two orbit factors, with generic
stabilization and rank criteria. Independent differences of invertible germs
form one orbit. This does not yet derive those hypotheses from a configuration.

Germ values are definable, representatives descend to every small ACF field
containing the canonical base, and invertibility has its definable-fibre
criterion. The composition theorem permits individually defined points with
the first value in the second germ's domain. The word-evaluation clause is
explicitly stated through automorphism invariance, whose class contains the
seeds and is closed under composition and inversion; actual parameterized word
relations and their constructibility remain later work. A definable triple
constructs its unique germ, graph and canonical base, for Step I's consumer.

All five producer copies were mathematically reviewed and independently
checked under default project options and standard linters in the prior
32-module check. The integration preserves every declaration and proof, with
only the `HW` status text clarifying pending homogeneous-space and extraction
layers. The source TeX, frozen M4a chain and original reconstruction inputs
are unchanged. Full library/book gates passed after all edits (19,079 jobs in
67.76 seconds, then book in 12.63 seconds), with twenty scoped standard-axiom
checks and rendered hypotheses inspected. The checkpoint is `db74468`.
The peer's `AdmissibleWords` family released the compiler in chit6588; compiler
ownership must always be refreshed through current chit messages.

## Core lift and literal image tuples (2026-10-14, #27)

`QWitness.PsiCore.lift` now transports precisely the twelve clauses (i)–(iv),
including the universal atom-freeness clauses through the proved one-quantifier
lift. The existing full-Ψ lift is unchanged. In the canonical universal ambient,
the new core theorem supplies the configuration and ranks; the existing full-Ψ
universal theorem keeps its original statement and applies `Psi.toCore`.

The public `configurationEmbedding k K` is used by both the witness lift and
the literal-image theorem. The latter uses the original displayed six tuples
composed with that actual embedding. Single lifted-point closures agree with
the closures of their literal images; pair closures follow by unions.
`GroupConfiguration.ofRaclEq` and rank invariance then supply the literal input
with group rank two and space rank one. The original fields may be arbitrary.

The shared goal removes only the proved literal-comparison obligation and
records the already committed germ layers. Arbitrary-extension base change
remains explicit: the current represented-locus APIs need independence of the
chosen representing tuples, and a fresh-locus transport package is pending.
The chosen universal extension is still the output field. Original-field
chart/action descent, group algebraization, action classification and the
unconditional reconstruction endpoint are unchanged and open.

## Actual admissible families and word relations (2026-10-14, #12)

Six reviewed modules now provide canonical zero-padded RREF germ codes,
admissible and invertibly admissible parameters of actual expressions, typed
word relations, fresh samples and actual uniform orbit families. The six
integration copies passed an independent default-option, standard-lint check
in 7.35 seconds with empty diagnostics, under the 20 GB cap. The `Word`
constructors receive docstrings for the book; old evaluation/inverse/orbit
Status text is brought into line with the integrated modules.

The canonical code generates the base and is equivariant and injective;
generic orbit points are exactly its generic code points. The encoding fills
non-pivot RREF rows with zeros; no unpadded-list length assertion is added.
The orbit-family theorem constructs actual admissibility proofs and identifies
their germs with the conjugates. It assumes no family certificate.

Definedness remains explicit in all fibres and every word-chain step. The
literal source word relation includes invertible admissibility for forward
as well as inverse factors, and mere admissibility for the target expression.
Its constructibility takes the specified sampling hypotheses. Fresh samples
over any prescribed small field are proved for Adm and Adm×. One jointly fresh
sampling tuple also serving germ equality and all word relations is still to
be assembled. The actual group domain with the generic stabilization condition,
its surjection, quotient relations, stabilizer and action are not established
by these modules. The source TeX, frozen chain and original reconstruction
endpoint are unchanged.


## A common fresh field for actual parameter relations (2026-10-14, #12/#29)

`Constructible.JointSamples` chooses two generic sampling families over any
prescribed small field, proves their cross-independence over that field and
joint freshness from it. `Constructible.CommonSamples` uses one field generated
by the two families for the actual Adm, Adm× and parameter-germ equality sets.
The samples have size twice the number of equality parameters plus one; the
source family serves equality and the target family serves admissibility and
invertibility. The equality proof reduces the two one-letter word germs using
composition with the identity. No sampling existence certificate is an input.
This discharges the first sentence of supplemental `lem:adm-constructible`;
a common fresh field for arbitrary finite word relations remains open.

Intermediate-field monotonicity of constructibility is now public in `Closure`,
used by both `AdmissibleWords` and `CommonSamples`; the duplicate private/local
helpers are removed. The audit with Claude is tracked on #29. Automorphism and
inverse module descriptions now distinguish the proved orbit direction and
composition-code containments from their outstanding converse and heterogeneous
rank statements. The finite-set code coefficient-vector presentation is not
identified with the separate ideal/germ RREF code vector.

The actual constructible group domain, surjection, quotient relations, stabilizer
and action remain obligations. The supplemental main theorem and arbitrary-base
change drafts await integration. Original algebraization, action classification,
guarded charts and unconditional reconstruction are unchanged and open. The
source TeX and frozen M4a chain are unchanged; the untracked PDF stays excluded.


## Fresh word fields and audited closure/basis clauses (2026-10-14, #12/#29)

`Constructible.WordSamples` chooses a finite field of samples for any actual
typed word, fresh from an arbitrary prescribed small field. It chooses each
letter's required locus over the closure of that field and all preceding
samples, then jointly samples the source and target for the final quantifiers.
The source word relation retains invertible admissibility of every factor,
including forward factors, and admissibility of the target parameter. No
sampling certificate is an input. Field monotonicity and one local extension
step remove duplicated sampling arguments. Scalar-restriction equality transport
is public in `Closure`, replacing the private copy in `Admissible`; its second
consumer is the staged generic quantifier for the actual stabilizer relation.
The arbitrary-coordinate expression graph lemma is public in `AdmissibleWords`,
shared by word chains and the same actual stabilizer relation. One field for finitely many distinct
consumer relations, and actual group constructibility, remain open.

`DefinableClosure` now states transport of the entire definable closure under
automorphisms, and equality of algebraic closures from equality of definable
closures, both for intermediate fields and arbitrary generating sets. No ACF
or finiteness hypothesis is needed for these corollaries. `Rref` now proves
uniqueness for any finite ordered basis satisfying Mathlib's RREF predicate:
its leading map is strictly increasing, dimension makes it bijective onto the
canonical pivots, and pivot-coordinate uniqueness identifies the basis. The
pivot indexing is derived, not supplied as an assumption.

Claude mathematically reviewed all three producers (chit6648). They were
independently checked with default project options and standard linters before
integration. The word proof uses a local helper for both directions of letter;
final integrated module, library, book and scoped dependency gates are required
before commit. The two source-audit
items are not closed until the pushed commit and exact CI pass. Other private
GCT modules, the constructible group, original algebraization and action
classification, guarded charts and unconditional reconstruction remain open.
The source TeX and frozen M4a chain are unchanged; the supplemental PDF is excluded.


## Arbitrary loci, full configuration ranks and literal source codes (#12/#29)

The source-audit foundation slice adds arbitrary-prime realization and dimension
independence, scalar and finite-tuple orbit equivalences, heterogeneous composite
canonical bases/ranks, conjugate sets and their scalar code carriers, the full
configuration rank table, the converse configuration and the explicit triple
representative. All 25 refreshed higher-module copies passed an independent
current-main default-option standard-lint check in 50.25 seconds, with empty
diagnostics and the verified 20 GB cap. This is evidence for those pinned
copies; only the current foundation slice is integrated here.

The positive space-rank proofs move unchanged from the private Main producer
into ConfigurationRanks. Remove their old duplicate definitions before checking
or integrating that Main source against the new ranks module. The converse
producer's existing proof on finite generating code tuples is preserved. A new
public theorem transports it onto the actual canonical zero-padded RREF code
vectors, states both source ranks and the action identities, and chooses the
inverse internally. It does not assume the code bridge or an inverse certificate.

RrefBaseChange supplies the literal tensor form of a field-defined subspace:
the actual field-valued part, canonical tensor map, image equal to the defining
span, and an actual linear equivalence with its pure-tensor formula for finite
coordinates. No basis, order, ACF or isomorphism certificate is an input. Its
private producer passed default options and standard linters with empty
diagnostics after coercion/dependent-rewrite fixes and the current tensor
induction API. Scalar-carrier conjugate-code claims remain distinct from the
still-open finite indexed codePoly coefficient vector.

The remaining configuration-to-group chain, arbitrary-extension base change,
constructible group domain/quotient/stabilizer/action, original algebraization,
action classification, guarded charts and unconditional reconstruction remain
open. The actual stabilizer parameter formula is Claude's separate lane; the
primary agent owns the group domain and finite-collection sampling. The source
TeX, original shared endpoint and frozen M4a chain are unchanged. Full final
library/book and scoped dependency gates remain required before every commit;
the supplemental PDF stays excluded.


## The precise group configuration theorem and base change (#12/#29, 2026-10-15)

Sixteen reviewed producer modules now assemble the definability step at all
three space points, Steps I–III, the Hrushovski–Weil bijection theorem and faithful
transitive homogeneous space, and `GroupConfiguration.exists_main`. Its only
configuration input is the actual six-point predicate over an ACF universal
domain. The finite independent extension, germs, group and action data are
constructed internally; no open group-extraction certificate is an input.
`IsMainConclusion` records interalgebraicity through finite generating code
tuples. Canonical RREF code vectors generate the same canonical bases by the
existing code API; the carrier tuples are not described as those indexed vectors.

The arbitrary-small-ACF base-change package first transports loci to fresh
representing tuples; both inclusions for the difference set and the group/space
equivalences are proved. It does not assume that the old representative tuples
stay generic over an arbitrary new field. G6 has explicit conjugate-code and
definability-step statements at x, y and z, preserving the old z proofs.
`Descent` proves k-point density and descent of independent parameters in actual
constructible relations. `Psi` supplies the interalgebraicity part of `cor:psi`
with group rank two and space rank one over the new base.

The twenty frozen higher producer copies (including four not integrated in this
slice) passed independent default-option standard-lint checking against 8323484
in 40.28 seconds, with empty diagnostics and the verified 20 GB cap. Ten scoped
dependency/type checks passed in 1.48 seconds; the precise main and Psi statements
were rendered and inspected. Only the sixteen configuration-to-group/descent/base-
change modules are integrated here. Full library/book gates after all edits are
required before committing. The positive-rank duplicates were deleted from Main,
which uses the versions already on main in ConfigurationRanks.

The actual group-domain membership and stabilizer formulas remain private,
independently checked drafts. The primary agent's literal pair-domain and
surjection producer also passed private checking; its constructibility is not
claimed. Claude owns the finite-set coefficient-vector draft, while the primary
agent owns the domain, finite-collection sampling and quotient operations.
Constructibility of G and G/H, the remaining original group-chunk/algebraization,
action classification, guarded charts and unconditional reconstruction remain
open. PROJECT_GOAL changes only the proved frontier, preserving the complete
original endpoint. The source TeX and frozen M4a chain are unchanged, and the
untracked supplemental PDF remains excluded.


## Literal finite-set codes and FOD scalar extension (#29, 2026-10-15)

`CodeVector` gives the finite indexed coefficient vector of the actual finite-set
coding polynomial. Its indices are pairs of a T-exponent and a U-monomial of
total degree at most the chosen bound. Full homogeneity proves that all nonzero
coefficients occur in this finite range, and the vector's nonzero values recover
the scalar code carrier. Naturality, fixedness/injectivity, ring-adjoin containment,
algebraic closure and definable closure are proved. The declarations live in
`GroupConfig.FiniteSetCode`: the existing top-level `CodeIndex` and `codeVec`
already belong to the different ideal/germ RREF code. The namespace change
preserves every mathematical proof body and leaves that existing API unchanged.

`FodBaseChange` proves the literal fields-of-definition scalar-extension remark.
The actual K-span of a subspace's image has its mapped RREF basis; the actual
degree pieces of an extended ideal are scalar extensions of its original pieces,
using coefficient lifting through the field range and extension/contraction.
The field of definition is therefore the image of the original field of definition.
No ACF, universal domain or scalar-extension certificate is a hypothesis.
The producer is preserved byte for byte.

Both private producers were mathematically reviewed and independently checked;
the refreshed six peer modules plus the actual domain drafts passed in 8.61
seconds with empty default-option standard-lint diagnostics. Eleven scoped
standard-axiom/type checks passed in 1.48 seconds. Related stale Status and book
sentences are corrected here. A scan of every current module Status also found
seven remaining descriptions that still called group extraction or the canonical
code/evaluation layers pending. They now point to the proved Main, CanonicalCode
and Eval modules, retaining the constructible-presentation and reconstruction
obligations. These changes affect descriptions only. Full library/book and
independent final checks
after all integration edits remain required before committing; the two audit
boxes stay open until the pushed checkpoint's exact CI passes.

The precise main theorem checkpoint is 428b601; its exact CI38661935677,
19147-job build/book, artifact11939516767 and existing deployment7080984413
(success 00:55:04 UTC) are verified. G1–G7 and the closure/RREF audit items are
checked off with exact evidence. Claude owns the finite-collection fresh sampling
construction, exposing actual generic-point provenance and joint rank additivity,
including the admissibility restrictions for every declared expression family.
The primary agent owns the actual group domain, quotient operations and action.
The group/stabilizer formulas and pair-domain surjection remain private drafts;
the full constructible presentation is not claimed by this checkpoint. Original
algebraization, action classification, guarded charts and unconditional
reconstruction remain open. The source TeX, shared endpoint and frozen M4a chain
are unchanged; the supplemental PDF remains excluded.


## Generic group elements over the final base (#12, 2026-10-15)

`Germ/RelativeRank` proves supplemental `rem:constr-connected` in its literal
rank, orbit and product form. For any small intermediate field M, all group
elements have canonical-base rank at most the original datum's rank n, and
rank n is equivalent to original generic-set membership plus independence
from M. Every element is a product of two rank-n elements over M. Those
elements form one orbit under automorphisms over M, which preserve relative
rank. The theorem assumes neither algebraic closedness of M nor independence
of the original datum from M. Its ranks on the left are over M, including
when M is the final sampling field or its algebraic closure.

Claude supplied the 151-line producer, preserved byte for byte here. The
primary agent accepted its mathematics and independently checked the exact
copy against ebaa87e with project options and standard linters in 3.15 s.
All five rendered declaration types and scoped dependency reports were
inspected; dependencies are only the expected standard axioms. Full build,
book and final integrated checks after these edits remain required before
commit. This proves the source remark without asserting the still-open
constructible presentation or formalizing a separate finite-index notion.

The literal pair domain, its internally chosen fresh samples, kernel and
word formulas remain private checked producers. The primary agent owns the
multiplication/inverse relations and group/space presentation; Claude owns
the stabilizer preimage on the actual domain. Original algebraization,
action classification, guarded charts and unconditional reconstruction remain
open. The source TeX, shared endpoint and frozen M4a chain are unchanged;
the untracked supplemental PDF remains excluded.


## Actual constructible group and homogeneous space (#12, 2026-10-15)

Fourteen new modules and the moved pure word helpers assemble supplemental
`thm:constructible`. The literal domain contains invertibly admissible pairs
satisfying the source generic stabilization condition. No pair parameter is
assumed generic or in the code locus. Exact group membership, an actual
surjection and the kernel, multiplication and inverse relations are proved.
The definitions of constructible group and G-set quantify actual domain
membership and maps; the constructors prove them, with no presentation input
on the final theorem.

`CanonicalPresentation` chooses F on the literal indexed canonical code of
the Hrushovski–Weil datum, obtains equal dimension from its inverse, and
chooses the source/target and parameter-locus samples internally. T0 generates
L0; T1 is generic with additive rank over L0 and gives L1=k(T0,T1). The
literal domain quantifier and its coefficient field are both L1. H and the
space presentation are over L1(y0). All sample provenance, joint ranks and
freshness from any prescribed small field are retained. The point y0 is
arbitrary generic, with no independence from candidate parameters. The space
map is the total action rho(d) smul iota(y0); no nongeneric germ evaluation is
used. The actual four- and six-letter stabilizer words give its kernel and
action relations. The equivariant G/H equivalence is proved on those objects.

Pure Word.mapParams, its three transfer lemmas and stabWord move from the
stabilizer module into AdmissibleWords. The new groupWitness theorem shares
the actual pre-projection proof between the group and stabilizer formulas,
removing their duplicate construction and the CG-to-H helper dependency.
Its coordinate projection needs Sum.elim_comp_inr and definitional equality;
the group-domain module explicitly imports StabilizerParameters. PairRelations
has a narrow GroupParameters import. No mathematical hypothesis or target is
changed by these refactors.

FamilySamples also gives the literal finite-family source relation, with
invertible-admissibility restrictions for every declared expression family,
including unused families. One internally chosen fresh field serves all the
typed words, with actual locus provenance and joint rank additivity. Claude's
469-line producer 20860a39 preserves the prior bodies and adds this source
clause. The peer and primary agent mathematically accepted the full group,
stabilizer, space and canonical wrapper producers. The primary agent independently
checked the canonical full producer in 4.00 s, then the complete fifteen-module
public-path candidate and twenty-three rendered scoped dependency/type reports
in 19.08 s, with empty standard-lint diagnostics and only standard axioms in
that selected scope. All compiler families used two threads and the enforced
20 GB cap, with no limit/OOM events or safety stop. Final full library/book
and integrated checks after all edits are required before commit.

The goal update changes the proved frontier and next consumer only. Its
objective, original endpoint and completion criteria are preserved exactly.
The actual Ψ constructibility corollary is integrated in this same checkpoint;
original algebraization, action classification, guarded Q charts and
unconditional reconstruction remain open. Source TeX, the frozen M4a chain
and the excluded supplemental PDF are unchanged. The temporary handoff
question #30 was resolved when the primary agent resumed integration.


`PsiConstructible` applies those producers to the actual Ψ witness alone.
The main conclusion is unpacked with the same actual f0, ga, gb, gc and six
interalgebraicity clauses; it is an output, never a caller-supplied certificate.
The generic point y0 and all samples are chosen internally. The original-base
independence of E union all sample coordinates from the witness is proved by
base change and independence transitivity. The rank-two bound, generic iff,
two-product and one-orbit conclusions use the literal final ACF base. The
full source cor:psi is therefore packaged without algebraization, action
classification or original-field descent. The actual G/H equivalence,
faithfulness, transitivity and generic-point embedding are the existing
proofs on those same objects, with no duplicate declarations.

Claude supplied the byte-exact 233-line producer a5ca2332. The primary agent
read and accepted the complete statement/proof and independently checked it
in 6.76 s, with empty standard-lint diagnostics and its sole rendered scoped
dependency report containing only the expected standard axioms. This is
additional to the fifteen-module candidate evidence above. All final main
gates after these last source and documentation changes remain required
before committing and pushing.


## General configuration with constructibility (#12, 2026-10-15)

`GroupConfiguration.exists_main_constructible` proves supplemental
`thm:main-informal`. It retains the precise main conclusion, the same actual
Hrushovski–Weil datum and all six interalgebraicity clauses. For every generic
base point over the configuration field it chooses the canonical family and
both stages of samples internally. The combined parameters are independent
from the configuration over the original base. The actual group presentation
and all generic-point stabilizer and homogeneous-space presentations have
the source coefficient fields. Over the final algebraically closed base the
rank bound, generic characterization, two-product and one-orbit conclusions
use the rank of the input tuple over the original base.

Claude supplied the 239-line producer 381934ff. The 220-line Ψ specialization
ff2f94e6 replaces the duplicated construction with this general theorem; its
public docstring and statement are byte-identical to those of 6b76e01. The
primary agent reviewed both proofs and independently checked them in 20.88 s
with empty standard-lint diagnostics and two rendered scoped dependency/type
reports containing only the expected standard axioms. Final full build/book
and integrated checks after all edits remain required before committing.

The shared goal changes its proved frontier only; its objective, endpoint and
completion criteria are unchanged. Source TeX and the frozen M4a body are
unchanged, and the supplemental PDF remains excluded. The auxiliary source
examples and parameter bound remain obligations. The degree-only descent
usage error was reported with a counterexample on #31 before any source edit;
its formal refutation and fixed-witness correction form a separate checkpoint.
Original algebraization, action classification, original-field chart/action
descent, guarded charts and unconditional reconstruction remain open.


## Fixed-formula descent and the degree-one refutation (#31, 2026-10-15)

`ClosureCounterexample` proves that a constructible subset of the affine line
is finite or cofinite. This is a necessary condition, not an iff over an
arbitrary coefficient field. An infinite proper base field and its complement
are both infinite, so the base-field locus is not constructible. The nonzero
polynomial-witness locus of degree at most one is exactly that field, giving
the named composed refutation of the source's degree-only usage claim. The
negative results require only an infinite base field and an element outside
it, weaker than the source's ACF universal-domain setting.

The error was reported with a counterexample on #31 before source edits. The
source remark now preserves its original 6b76e01 provenance and states the
correct fixed-formula usage: retain the actual finite polynomial or
quasi-rational witness formulas, their coefficients and nonvanishings.
Existing polynomial-data, zero/nonzero, graph, Boolean and finite-tuple
quantifier theorems prove constructibility of these satisfaction relations.
The application reference is corrected at the same time. Ambient quantifiers
do not restrict coefficients to the base field. The literal degree-one
algebraicity case and the common base-field obstruction are formalized; no
new theorem about arbitrary definable-closure membership is claimed.

Claude supplied the four refutation proofs; their bodies are byte-unchanged.
The primary agent reviewed them and independently checked the doc-adjusted
149-line module bba14e89 in 2.53 s with empty standard-lint diagnostics. Nine
rendered scoped dependency/type reports (four new declarations and five
existing positive fixed-formula APIs) contain only standard Lean axioms. An
initial runner lacked dependency-artifact symlinks, and a root documentation
edit needed a line wrap; both were corrected before the clean audit. Final
full build/book and integrated checks after all edits remain required before
commit. The Chevalley docstring also now cites its already-proved source label.

The shared objective, endpoint and completion criteria and the frozen M4a
body are unchanged. The supplemental PDF remains excluded. The source
application's fixed formulas, recovery of independence, definability in
families and model-completeness descent remain obligations. Other auxiliary
examples, parameter rank, GC4 necessity, original algebraization, action
classification, guarded charts and unconditional reconstruction remain open.


## Canonical-base example, necessity and finite-ambient collapse (#12, 2026-10-15)

`CanonicalBaseCounterexample` proves the literal source example in
`rem:cb-not-acl`. For a rank-three triple s, s', t, the point (t, st+s')
has rank two; its locus over acl(s,s') is the displayed line and its actual
canonical base is k(s,s'). The element s is outside the point's algebraic
closure, so that canonical base is not contained in it. These theorems use
only arbitrary fields and the rank-three hypothesis. The affine substitution
reduces the ideal calculation to univariate transcendence. A nonzero
field-of-definition-valued degree-one vector and its coefficient ratios
recover the literal field of definition. The peer replaced a type-unification
timeout with this lighter argument, preserving the default checking options.

`ConfigurationNecessity` proves independent-base descent of all configuration
clauses. The actual main conclusion's configuration of codes and values
transfers to the original interalgebraic tuple, then descends across a finite
independent extension. Finiteness of E is explicit and supplies smallness.
The resulting .cb_a clause is the precise necessity assertion of
`rem:main-props`. Extraction still uses the genuine configuration hypotheses.

`Germ/FiniteAmbient` proves the finite-ambient warning in `rem:finite-trdeg`: a
finite-transcendence-degree ambient field is small; positive-rank loci have
no generic point over it; over an algebraically closed ambient field every
quasi-rational expression over the whole field gives a vacuous representative
equivalent to every other one. The generated equivalence relation therefore
identifies all representatives. This is a statement about representatives
and their generated equivalence relation; the existing germ definition
retains its universal-domain hypothesis. The parameter count and
model-completeness clauses of the source remark remain obligations.

Claude supplied the three exact producers: 362-line 3458ea50, 156-line
1a3b40dd and 103-line 672ddb49. The primary agent reviewed every proof and
independently checked their combined exact candidate in 6.17 s, with empty
standard-lint diagnostics and twelve rendered scoped dependency/type reports
containing only the expected standard axioms. Every compiler family used two
threads and the enforced 20 GB cap without limit/OOM events or a safety stop.
Final full build/book and integrated checks after all edits are required
before committing. The aggregate, book, shared-goal frontier and module
status agree, and the old degree-bound remark is described in the past tense.

The goal's objective, endpoint and completion criteria, source TeX and the
frozen M4a body are unchanged. The supplemental PDF remains excluded. The
translation and nonfaithful-action examples, five-copy parameter rank, base
algebraic-closure invariance and remaining descent/family assertions stay
open. Original algebraization, action classification, guarded charts and
unconditional reconstruction remain open.


## Base closure and shared affine-line computation (#12, 2026-10-15)

`BaseClosure` proves the general base-closure assertion of `rem:psi-hyp`(c).
For arbitrary fields, replacing k by its relative algebraic closure inside
the same K preserves closure carriers and matroid ranks. The constructed
closed-field order isomorphism and its inverse preserve carriers. Existing
Point.map and rankEq_map_iff apply to that actual isomorphism, preserving
points and lattice ranks. The ambient field stays fixed. When K is ACF,
the new base is ACF; returning witnesses from a larger ambient extension
remains a separate obligation. The module imports Rank only.

`CanonicalBaseCounterexample` now shares the existing affine-line ideal and
field-of-definition proof over any coefficient field L containing s,s',
with t transcendental over L. The original line-example theorems are
corollaries, and the docstrings and statements of all five old public
theorems are byte-identical to 9384cb2. The proof is moved once, not copied.
Existing canonicalBase_comp_equiv handles the Fin1-plus-Fin1 graph indices,
as checked in the actual consumer example. These shared lemmas supply the
source's forthcoming translation and nonfaithful-action computations.

Claude supplied exact producers 108-line 1d3664b5 and 381-line 8d0a1aaa.
The primary agent reviewed their complete proofs and independently checked
the combined candidate in 4.65 s, with empty standard-lint diagnostics,
twelve rendered scoped dependency/type reports containing only standard
Lean axioms, and four actual point/carrier/rank/index consumer examples.
Every family used two threads and the enforced 20 GB cap without limit/OOM
events or a safety stop. Full library/book and final integrated checks
after all edits are required before committing and pushing.

The shared goal changes its proved frontier only: objective, endpoint and
completion criteria remain exact. Source TeX and the frozen historical body
are unchanged; the supplemental PDF stays excluded. Claude owns the private
actual translation-germ and homogeneous-space example, with an explicit
stage-one terminal yield before this integration's compiler family. No
caller-supplied HW or presentation certificate is allowed. The full source
example remains open until its actual space equivalence, generic-point
image, zero class and independent-presentation obstruction are proved.
The five-copy parameter bound, nonfaithful-action example, remaining
application descent/family assertions and original reconstruction remain
obligations.


## The full translation example (#12, 2026-10-15)

`Germ/Translation` constructs the actual quasi-rational representatives and
quotient germs for translations of the affine line. Their parameters determine
the germs injectively, composition is addition, and the actual canonical base
is k(c). The generic orbit is precisely the translations by transcendental
parameters; a transcendental translation has the proved Hrushovski–Weil
structure, and its two-product group contains exactly all translations.
The three field/rank helpers have named consumers in these two modules.
The canonical-base calculation uses the shared affine-line theorem and the
existing finite-coordinate equivalence API.

`Germ/TranslationSpace` computes the actual Pair.Rel relation and constructs
the actual homogeneous-space equivalence with K. A pair (tau_a,y) maps to
a+y, with no independence imposed between its point and parameter. The
inverse uses the given transcendental base point. The generic-point embedding
has exactly the transcendental elements as image; the total action becomes
addition. The class [-t,t] maps to zero and has no presentation gamma smul
iota(y) with y independent from the canonical base of gamma. That negative
proof uses compatibility only when genuine generic-evaluation independence
is available. No caller supplies an HW or presentation certificate. Thus
all clauses of the translation example in rem:connected are proved.

Claude supplied the exact 336-line dbe321cf and 246-line e292186e producers.
The primary agent reviewed every proof and independently checked both in
4.44 s, with empty standard-lint diagnostics and all thirty-two public
rendered types and axiom reports containing only the expected standard
Lean axioms. A further 1.70 s printing-only check expands the actual proved
HW term indexing the space and group, rather than hiding it as an ellipsis.
The two threads and enforced 20 GB cap had no cap/OOM events or safety stop.
Full library/book and final integrated checks after all edits are required
before committing and pushing. The aggregate, book, goal frontier and these
module statuses describe the same proved source example.

The shared goal's objective, endpoint and completion criteria and the frozen
historical body are unchanged. Source TeX is unchanged and the supplemental
PDF remains excluded. Claude owns only the two separate private nonfaithful
example modules, with agreed compiler turns. That full source example, the
five-copy parameter rank, application descent/family assertions, original
algebraization, action classification, guarded charts and unconditional
reconstruction remain obligations.


## The nonfaithful product-group example (#12, 2026-10-15)

`Config/PsiNonfaithful` constructs the literal example of rem:psi-hyp(b)
over arbitrary fields. Five independent scalars give the displayed nine
points, with the other twelve set to the point of t as clauses (i)–(iv)
do not mention them. The product of the two groups of units acts on K
through its first factor, using Mathlib's permutation-action homomorphism
and first projection. The genuine rank-five hypothesis supplies a nonidentity
second factor acting trivially. The actual unit identities give b=c*a,
x=a*y and z=c*x. All nine rank, incidence and noncontainment assertions
of Ψ (i)–(iii) hold. The source atom A'=acl(s) violates (iv), so the
constructed witness is not PsiCore.

`Config/PsiNonfaithfulObstruction` computes the actual canonical base of
(st,t) over acl(s,u), using the shared affine-line theorem and existing
coordinate reindexing. The parameter u lies outside the closure of that
base, giving the field-only GC4 obstruction. In an algebraically closed
universal ambient, the representative tuples of the actual witness are
interalgebraic with the displayed scalar tuples. Configuration invariance
transfers the obstruction to them. Necessity from the actual main
conclusion then rules out any finite independent E carrying IsMainConclusion
over acl(k,E). This is the precise group-of-germs realization condition;
it is not a statement quantifying over arbitrary algebraic actions.
The original algebraic-group and curve-action bridges remain obligations.

Claude supplied the final 407-line fa95faff and 150-line 08a96c7f modules.
The primary agent read and accepted every proof and independently checked
the exact two-file candidate in 5.09 s, with empty standard-lint diagnostics
and all thirteen public rendered dependency/type reports containing only
the expected standard Lean axioms. Sixteen internal coordinate helpers
are private; only the two field facts consumed by the obstruction are
public. The nonfaithfulness statement uses the same genuine independence
hypothesis, with no unused coordinate lemma. All compiler families used
two threads and the enforced 20 GB cap, without cap/OOM events or a safety
stop. Full library/book and final integrated checks after all edits are
required before committing and pushing.

The aggregate, book, module statuses and shared-goal frontier describe the
same complete source example. The goal's objective, endpoint and completion
criteria, source TeX and frozen historical body are unchanged. The
supplemental PDF is excluded. The five-copy parameter bound, application
descent/family assertions, original algebraization and action classification,
guarded charts and unconditional reconstruction stay open. The primary
agent owns the private three-file parameter-rank refactor. Claude's proposed
rationality route is still in read-only truth/API review on #21; no new
classification premise is assumed. The proposed independent-generic-factor
shortcut was refuted using the translation example and is not adopted.


## The actual five-copy parameter rank (#12, 2026-10-15)

`GroupConfiguration.exists_main_with_parameterRank` proves rem:params on
its actual construction: a finite E, independent from the original six
points, has rank five times the original group-point rank over k and carries
the actual IsMainConclusion over acl(k,E). No parameter-rank certificate
or prescribed E is supplied. The universal-domain hypothesis is retained;
this does not produce a finite-ambient version of the germ theorem.

The existing producers are strengthened once. DefinabilityStep keeps
he.erk_empty_eq for its chosen generic copy, including the intermediate-base
variant. StepI retains the three successive ranks; independent base change
preserves the original group rank and the tower law gives 3n. StepIII_one
keeps the already-returned sigma*b=bprime identity, so erk_image recovers
the copy's rank without changing StepII. StepIII also uses the already-returned
sigma2*c=cdoubleprime identity; the two copies have combined relative rank
2n. Main transfers the transformed group rank back to the original input,
then combines the actual E and S by the tower law to obtain 5n over the
original base. Each old long proof is moved once into its stronger producer.
The six old public docstrings and statements are byte-identical projections,
and the relative Step III omission of IsAlgClosed k is preserved.

The primary agent owns this three-file refactor, with ownership agreed through
chit. The exact private producers are 368-line a9e1bd8b, 270-line e8a631bc
and 798-line 695e086e. Their latest standard-lint checks are empty. The
actual unchanged MainConstructible and PsiConstructible source consumers
passed in 4.49 s and 13.89 s, using the stronger producer through the old
public wrapper. Twelve new/old scoped dependency/type reports contain only
the expected standard Lean axioms. Printing-only expanded types show the
2n and 5n conclusions explicitly. An initial Main check needed an explicit
range c argument to prevent the rank proof retaining gcPoints at index two;
that inference issue was corrected. No checking option is weakened.
Every compiler family used two threads and the enforced 20 GB cap without
cap/OOM events or a safety stop. A read-only full proof review was requested
from Claude. Full public library/book gates after all six final edits are
required before committing and pushing.

The book and goal frontier describe the same actual five-copy theorem.
The shared objective, endpoint and completion criteria, source TeX and frozen
historical body are unchanged. The supplemental PDF remains excluded.
Application descent and independence recovery, model-completeness and family
definability, original algebraization and action classification, guarded
charts and unconditional reconstruction stay open. Claude's rationality
route remains in read-only truth/API review on #21; its false independent-factor
shortcut is not adopted and no new classification premise is assumed.


## Rational representatives for HW germs on curves (#21, 2026-10-15)

`Germ.IsHW.exists_rational_representative` takes an actual HW germ of a finite
rank-one tuple over the genuine ACF/universal-domain hypotheses. Every element
of its actual two-product group has an internally constructed representative
equal to that germ and with exponent zero. Both characteristics are covered;
no birationality, degree or Frobenius-index certificate is a premise.

`FunctionFieldFrobenius` proves the degree-p and pure Frobenius-layer results.
The two degree towers compute [F:F^p]=p without a separability assumption.
The intermediate-field chain argument and noncollapse give uniqueness of the
integer index. `Germ/Rationality` constructs the index of an actual unit using
its inverse representative. Two index witnesses are moved to one fresh generic
point over a common small algebraically closed field. Degree p is computed
fresh there, so extending coefficients cannot hide a collapse. Composition is
handled for arbitrary germs over that common field, with no independence
between their parameters. H3 is used only to compare the seed index d with
2d on its orbit. Index zero gives actual fractions and a representative defined
at every generic point. The two-product conclusion then follows by composing
two mapped exponent-zero representatives. The false independent-factor shortcut
reported on #21 is absent.

Claude supplied the complete 410-line 9bec224a field module and 393-line
7a0d8eeb germ module, with ownership and compiler turns agreed through chit.
The primary agent read every proof and independently compiled both exact files
against the previous main dependencies, with only its own two outputs real.
Both standard-lint logs were empty; all nineteen expanded public types and
scoped dependency reports use only the expected standard Lean axioms. The
successful independent family took 5.28 s, used two threads and an enforced
20 GB cap, and peaked at 3.32 GiB RSS without cap/OOM events or a safety stop.
The two earlier harness attempts stopped before the second module elaborated:
Lean needed an explicit private source root, then main dependency symlinks in
the fresh namespace directory. Neither changed the candidate mathematics.
Full library/book and integrated checks after all six final edits are required
before committing and pushing. Final validation and exact CI evidence are
reported on #21.

The book and shared-goal frontier describe the same bounded rationality result.
The objective, endpoint and completion criteria, source TeX and frozen M4a
history are preserved; the supplemental PDF stays excluded. The function-field
action, original group-chunk and six-point producers, normal subgroup and full
Lemma 8.4, actual application descent and independence recovery, definability in
families, guarded charts and unconditional reconstruction remain open. The
primary agent separately owns one private model-completeness module; no partial
helper chain will be integrated before its actual elementary-embedding consumer.


## Actual model completeness of algebraically closed fields (#12, 2026-10-15)

`acfElementaryEmbedding` turns a prescribed ring homomorphism between two
algebraically closed fields into an actual elementary embedding in Mathlib's
ring language, with that exact underlying map. `ringHom_realize_iff` preserves
every finite-arity formula, including arbitrary quantifiers. Its only public
mathematical inputs are the two fields, their algebraic closedness and the
prescribed homomorphism. No algebra structure, universal domain, rank bound,
elementary-embedding or formula-descent certificate is supplied by the caller.
The canonical compatible ring structures are built locally, without a global
instance loop.

The proof first extracts a base-field point from a nonempty constructible cell
by the existing locus-density theorem. This helper needs algebraic closedness
only of the base; its ambient field is arbitrary. A complete induction over
Mathlib's actual BoundedFormula constructors proves constructibility of their
realization sets in an algebraically closed ambient field. Ring terms are
interpreted as actual multivariable polynomials, using the semantics' homomorphism
naturality. Implication uses complement and union. Universal quantification uses
a polynomial snoc substitution followed by Chevalley's quantifier theorem.
The Tarski–Vaught test applies density to a polynomial fibre that fixes every
old parameter and leaves only the proposed new witness free. A point of the
whole realization set would not suffice. The prescribed underlying map is
retained definitionally. The three local helpers are private and consumed by
the actual elementary-embedding producer; no helper chain was integrated first.

The primary agent owns this one new module and the aggregate/book/goal/continuation
edits, with ownership agreed through chit. The complete private 162-line c4f09fa1
candidate passed standard lint with empty diagnostics and five expanded scoped
public type/dependency reports using only the expected standard Lean axioms.
The final private family completed in 2.53 s under two threads and an enforced
20 GB cap, peak RSS 3.36 GiB, without cap/OOM events or a safety stop. Claude
read every line and accepted the mathematical proof and exact hypotheses in
chit7121. His two documentation nits are resolved: an accurate public Status
replaces the private-candidate sentence, and actual application formulas and
independence recovery remain explicitly open. Every namespace/proof byte is
unchanged from the reviewed private candidate. Full library/book and final
integrated source/type/dependency checks after all five edits are required
before committing and pushing; final evidence is reported on #12.

This supplies model completeness itself, cited in rem:psi-hyp(c) and
rem:finite-trdeg. It does not turn algebraic independence into a finite formula
or supply the application's actual fixed formulas, independence recovery,
definability of rank/connectedness in families or original-field chart/action
descent. Those and the original group-chunk, six-point, action-classification,
guarded-chart and unconditional reconstruction obligations remain open. The
source TeX, shared endpoint/completion criteria and frozen historical M4a body
are preserved; the supplemental PDF remains excluded. Claude separately owns
only the two new private function-field/action modules and coordinates every
compiler family through chit.


## The actual faithful function-field action (#21, 2026-10-15)

`Germ.IsHW.functionFieldAction` gives a faithful homomorphism from the actual
HW two-product subgroup into the K-algebra automorphisms of its locus function
field. The field is literally FractionRing(K[X]/locusIdeal k v). The source
locus ideal is prime over the algebraically closed base, and rank one gives
the actual IsFunctionFieldOneVar K instance consumed by the curve library.
No primeness, dimension, substitution or action certificate is a premise.
The genuine finite-tuple, rank-one, ACF and universal-domain hypotheses remain.

`Germ/FunctionField` proves the generic-point dictionary and fraction-value
calculus. For coefficients in one small field, equality in the fraction field
is equivalent to equality of values at a generic point. Every fraction has
such values over a small field containing its coefficients and any prescribed
small set. A coordinate is transcendental over K by evaluating a proposed
polynomial relation at a fresh generic point over its coefficient field and
using independence. Every other coordinate is algebraic over that coordinate's
simple extension; all coordinates generate the fraction field, giving finiteness.

`Germ/FunctionFieldAction` clears denominators over common coefficients to
prove both directions of the substitution kernel equality with the locus
ideal. The map factors injectively through the quotient and lifts to the
fraction field. The value calculus proves representative invariance and
contravariant composition. Rationality supplies representatives internally;
substitution of the inverse corrects contravariance to a genuine homomorphism.
The coordinate formula applies to every equal exponent-zero inverse
representative. Trivial action on coordinates forces the identity germ,
so the homomorphism is injective. No helper chain was integrated before this
full faithful-action and one-variable-field consumer.

Claude supplied the complete 313-line 14e3f5a5 and 377-line f295272d modules,
with ownership and compiler turns agreed through chit. The primary agent read
all 690 lines and independently compiled both exact files against fresh main
a68edb2 dependencies, with only its own two outputs real. Standard-lint logs
were empty, and all twenty-six expanded scoped public type/dependency reports
use only the expected standard Lean axioms. This successful independent family
completed in 6.75 s, peak RSS 3.43 GiB, with two threads, an enforced 20 GB cap
and no cap/OOM events or safety stop. The public files retain the exact reviewed
bytes. Full library/book and final integrated lint/type/dependency gates after
all six final edits are required before committing and pushing; final evidence
is reported on #21.

The book and goal frontier describe the same actual function-field action.
The original endpoint and completion criteria, source TeX and frozen historical
M4a body are preserved; the supplemental PDF stays excluded. Curve genus,
Möbius/affine classification, the original scheme/action bridge, normal subgroup,
group-chunk and six-point producers, application formulas and independence
recovery, definability in families, chart/action descent, guarded charts and
unconditional reconstruction remain open. Claude's next genus proposal is
read-only truth/API review; no R2 implementation is assigned.


## Genus zero for the actual HW function field (#21, 2026-10-15)

`Germ.IsHW.genus_eq_zero` proves genus zero over K for the actual
`LocusFunctionField k v`, from genuine HW data, curve rank one and ordinary
canonical-base rank at least two. It derives the one-variable instance inline.
No rationality, inverse, normality, graph-stability, independent-derivation,
regularity, scalar-comparison or genus certificate is a premise. This is a
bounded auxiliary result. All eight original scheme/action classification
requirements and the full original reconstruction endpoint remain open.

The proof uses the ordinary field C = g.cb, never its algebraic or perfect
closure. The formal old field is Frac(k[X]/idealOf k v), distinct from a
compositum with the original tuple in K. Its separating parameter and
one-variable structure are derived from the actual finite-tuple rank-one
hypothesis. Canonical tensor and fraction-field comparisons identify the
formal constant extensions with C(formal coordinates) and the actual
K-function field, retaining coordinate formulas. The actual rational graph
kernel is proved equal to the contracted germ graph in both directions.

An ordinary coefficient derivation extends to a horizontal connection fixing
the old field. Conjugation by the genuine C-automorphism and subtraction gives
a C-linear curve derivation. Zero variation forces coefficient stability of
the graph kernel; differentiating its RREF code forces the derivation of the
ordinary canonical base to vanish. Finite generation and rank at least two
supply two independent coefficient derivations, hence two independent curve
variations. Normalization under arbitrary constant extension is proved from
integral equations, not assumed. The two integral-closure charts detect every
proper valuation ring over the constants and transfer regularity to K. Only
the C-linear curve variations are extended to K; coefficient derivations are
never extended to the perfect ambient field.

Two independent regular K-derivations force genus zero. Genus at least two is
excluded by the existing rigidity theorem. In genus one, a nonzero combination
has residue zero on a uniformizer at a chosen place. Writing each integral
element as x = c + pi*y proves vanishing on the whole valuation ring, so the
existing genus-one vanishing theorem applies. No uniformizer-only vanishing
condition is silently substituted for the full one.

The two agents agreed on ownership and each compiler lease through chit.
Claude supplied the normalization, independent coefficient derivations, old
field, actual graph kernel, curve-derivation and regularity base change, and
abstract genus exclusion. The primary agent read all proofs and independently
compiled the exact frozen sources. The complete private genus assembly passed
before integration; Claude accepted the full mathematical chain and final
1444-line refactor. A shared derivation API and tensor-localization comparison
replace all duplicate implementations. The focused coefficient-connection,
RREF-constants and actual-genus modules replace the private monolith. Unused
private rationality wrappers were removed; the actual producer still chooses
both rational directions from HW data and derives their ordinary-base equality.

The final nine prerequisite copies independently compile cleanly with all 65
named public expanded type/dependency reports using standard Lean axioms. The
three focused consumer modules also compile cleanly with fourteen public
reports. This scoped, two-thread 20 GB family completed in 66.29 s, peak RSS
3.96 GiB, without memory events or safety stop. These are scoped private gates,
not a whole-library axiom audit. Full library/book validation and final
integrated lint/type/dependency checks after all edits are required before a
public commit and push; final evidence is recorded on #21.

The book, module statuses and shared goal frontier describe the same bounded
genus theorem. Original source TeX, endpoint/completion criteria and frozen
historical M4a body are preserved; the supplemental PDF remains excluded.
Möbius/affine classification, original scheme/action and normal-subgroup
bridges, group/chunk and six-point producers, application formulas and
independence recovery, definability in families, original-field chart/action
descent, guarded charts and unconditional reconstruction remain obligations.


## The HW function-field action is fractional linear (#21, 2026-10-15)

`Germ.IsHW.exists_generator_moebius` chooses a transcendental generator t of
that same actual locus function field and proves K(t) = top. For every element
of the actual HW two-product group, its function-field action has the formula
sigma(t)*(c*t+d) = a*t+b, with a*d-b*c and c*t+d both nonzero. The hypotheses
are exactly the actual HW datum, finite tuple of rank one and ordinary
canonical-base rank at least two, with the genuine ambient assumptions.
The one-variable structure and genus zero are derived, not supplied.

This composes the actual genus theorem with the existing genus-zero rational
automorphism theorem and the actual function-field action. Claude supplied
the complete 48-line module; the primary agent read all its proofs and
independently compiled the exact source over fresh ee399b8 main dependencies.
The log is empty and its expanded public type/dependency report uses standard
Lean axioms. This guarded two-thread 20 GB family completed in 5.54 s, peak
3.61 GiB, without memory events. Full library/book and final integrated
lint/type/dependency gates after all edits remain mandatory before committing
and pushing; exact CI evidence is recorded on #21.

Only the individual fractional-linear formulas are asserted. Under composition
of field automorphisms, the rational expressions substitute in reverse order,
so a future map to PGL2 must account for the inverse/opposite convention. No projective group
embedding, scheme action, connected-subgroup classification, normal subgroup,
affine chart, original-field descent or reconstruction is claimed. All eight
original #21 classification requirements and other source obligations remain
open. Original goal endpoint, source TeX and frozen historical M4a body stay
unchanged; the supplemental PDF remains excluded.


## Rank-one HW data from the actual Ψ quadrangle (#12, 2026-10-15)

`IsPartialQuadrangle.groupConfiguration` derives GC1–GC5 for the actual six
points in the order (S,T,U,Tprime,Uprime,Sprime). The four dependent lines
have rank two; all sixteen noncollinear triples have rank three. Atomicity
and the canonical-base capture theorem prove GC4: a trivial closed canonical
base would force two distinct points to coincide. The full Ψ clause (vi)
supplies this quadrangle; `PsiCore` alone does not contain that clause.

`QWitness.Psi.exists_rankOne_isMainConclusion` applies the existing actual
main theorem. It returns finite E of rank five over the original base,
independent from all six quadrangle point tuples, the actual
`IsMainConclusion` over racl(k,E), and rank one for both S and Tprime over
that literal base. Algebraic closedness of k and K and the universal-domain
hypothesis are explicit. No group, configuration, canonical-base, rank or
independence certificate is supplied as an additional premise.

Claude supplied the complete 254-line private consumer; the primary agent
read every proof and independently compiled its exact source. The two agents
then reviewed shared canonical-base capture and point/tuple-rank helpers.
The final 219-line consumer removes all four duplicate private proofs;
the existing rank-two input also uses those same helpers. The primary agent
read the whole cleaned consumer and independently compiled all three exact
new modules over fresh main dependencies with empty logs. All six expanded
public type/dependency reports use standard Lean axioms. This scoped,
two-thread 20 GB family completed in 4.22 s, peak RSS 3.33 GiB, without memory
events or safety stop. Full library/book and integrated lint/type/dependency
gates after all final edits remain mandatory before every commit and push;
exact checkpoint/CI evidence is recorded on #12.

The aggregate imports, book and goal frontier match this bounded result.
Original source TeX, goal endpoint/completion criteria, frozen historical
M4a body and excluded supplemental PDF are preserved. The result asserts
independence only from the six quadrangle point tuples. The algebraic group
H over the original base in `thm:six-point-group`, Weil algebraization, the
homomorphism pi, its normal subgroup, original-field chart/action descent,
affine classification, guarded charts and unconditional reconstruction remain
obligations. All eight original classification requirements on #21 stay open.


## Actual Ψ parameters fresh from prescribed finite sets (#12, 2026-10-15)

`GroupConfiguration.exists_main_fresh_with_parameterRank` chooses the actual
five-copy parameter set E independently from the six configuration tuples
and any prescribed finite W. It retains erk(k,E) = 5*erk(k,a) and the actual
`IsMainConclusion` over racl(k,E). The generic copies are sampled over the
larger small sampling field; the configuration base is kept fixed. Relative
freshness is carried through all three Step I copies and both Step III copies.
The old public existence statements are empty-W specializations. All 38 old
public theorem statements in the four core modules and the main-conclusion
predicate remain unchanged.

`QWitness.repTuple` lists all twenty-one witness representatives in field
order. `PsiCore.exists_isMainConclusion_fresh` gives actual rank-two data
with finite E of rank ten, independent from this entire tuple and W; its
group and space input ranks remain two and one over racl(k,E).
`Psi.exists_rankOne_isMainConclusion_fresh` gives actual rank-one data from
the internally chosen partial quadrangle, finite E of rank five, and
independence from all twenty-one representatives, the three extra quadrangle
points and W. Its group and space input ranks remain one over that same base.
Both consumers derive all group/configuration and freshness conclusions;
no additional certificate is a premise. Full Ψ is needed for clause (vi).

Claude supplied the complete five-file lane and checked its scoped and full
library builds. The primary agent read all changes and both complete
consumers, independently compared the old statements, and compiled exact
frozen copies of all five modules with empty standard-lint logs and default
checking limits. All 51 selected expanded public type/dependency reports use
standard Lean axioms: the ten new declarations, 39 existing core declarations
and two existing actual Ψ consumers. This scoped audit is not a whole-library
axiom audit. The enforced 20 GB, two-thread family completed in 13.07 s,
peak RSS 3.39 GiB, without memory events or safety stop. Full library/book and
final integrated lint/type/dependency gates after all documentation edits
remain mandatory before committing and pushing; exact evidence is on #12.

The module headers, aggregate, book and shared goal frontier match this
bounded result. Original source TeX, the original goal endpoint/completion
criteria, frozen historical M4a body and excluded supplemental PDF are
preserved. These are individual existence results. A common-base realization
of both actual main conclusions still needs its base-change proof and joint
consumer. The original algebraic H/k, Weil algebraization, pi, its normal
subgroup, action classification, original-field chart/action descent,
guarded charts and unconditional reconstruction remain obligations. All eight
original #21 classification requirements remain open.


## Both actual Ψ main conclusions over one fresh base (#12, 2026-10-15)

`IsMainConclusion.baseChange_racl` preserves the actual main conclusion under
an independent finite base extension. It chooses fresh representatives for
the two loci and a fresh member of the initial HW orbit, transports the two
fixed group points, and regenerates the third through the existing HW
configuration theorem. Interalgebraicity with the input gives the necessary
independence for the fixed codes and action values. Locus-ideal equality
preserves the ranks of the new representatives. Only the original space
input requires a finite tuple; unused finiteness assumptions are absent.

`QWitness.Psi.exists_joint_isMainConclusion` consumes this producer twice.
It first chooses the actual quadrangle and E1 of rank five. It then chooses
E2 of rank ten fresh from all twenty-one representatives, the three extra
quadrangle points, E1 and prescribed finite W. Their union has rank fifteen
and is independent from the whole witness, the extra points and W. Both
actual main conclusions hold over the same literal racl(k,E1 union E2),
with the four group/space input ranks two/one and one/one. Full Ψ and the
genuine ACF/universal-domain hypotheses suffice; no Main, group or
independence certificate is an additional input.

The primary agent supplied the complete private producer and consumer.
Claude reviewed every mathematical step, including replacing the locus
representatives rather than assuming they remain fresh, lifting the old
code-closure equality before changing its base, and transporting positive
rank from the generic point to the fresh locus representative. Both exact
modules compile with empty standard-lint logs under default checking limits;
both expanded public type/dependency reports use standard Lean axioms.
The primary 20 GB, two-thread family completed in 5.48 s, peak RSS 3.31 GiB,
without memory events or safety stop. Claude independently compiled the exact
frozen sources over fresh public 96aafd1 dependencies, with only the two new
outputs real; its 5.48 s family peaked at 3.30 GiB and returned the same clean
logs and standard reports. This is a scoped audit, not a whole-library one.
Full library/book and final integrated lint/type/dependency gates after all
final edits remain mandatory before committing and pushing; exact checkpoint
and CI evidence is recorded on #12.

The module statuses, aggregate, book and goal frontier match this joint germ
realization. Original source TeX, goal endpoint/completion criteria and frozen
historical M4a body are preserved; the supplemental PDF remains excluded.
The original algebraic groups over the original base, Weil algebraization,
pi, its normal subgroup, scheme/action classification, original-field descent,
guarded charts and unconditional reconstruction remain obligations. All eight
original #21 classification requirements stay open.


## The complete constructible determinant-one HW lift (#21, 2026-10-15)

`Germ.IsHWBij.exists_constructible_slLift` starts with actual HW bijection data,
a member of its difference set, a finite rank-one source tuple and ordinary
canonical-base rank at least two. It internally chooses the function-field
generator, small algebraically closed coefficient field M, canonical
presentation, generic samples and subgroup of SL2(K). Every actual group
element has a lift; the subgroup consists of all and only these lifts.
Two lifts differ by a sign in every characteristic. Matrices for the image
of the generator compose in the reversed order. Ordinary canonical bases
and matrix entries have equal relative algebraic closures over M, giving
the actual HW rank bound with equality attained by a fresh generic element.

The uniform canonical family and actual word relation give the generic
evaluation test. Polynomial cells and ordinary projection make that test
constructible. The existing finite generic quantifier then makes the whole
lift relation constructible. Equivariance of the actual parameter and pair
germs, pair domain and surjective presentation map supplies both canonical-
base algebraicity directions, using sign uniqueness and faithfulness.
Automorphism invariance is used after constructibility has been proved.
The general coefficient-field value bridge reuses the existing substitution
lemma. Shared value calculus is moved from the graph module to FunctionField;
the graph induction stays private and no narrower evaluation proof is kept.

Claude supplied the complete six-module lane and checked the full library.
The primary agent read every proof and independently compiled exact frozen
copies of all six modules and all three committed baseline modules with
empty standard-lint logs and default checking limits. All 27 existing
expanded public declaration types are unchanged. The 18 new public
declarations and those 27 existing declarations have 45 selected expanded
type/dependency reports using standard Lean axioms; the baseline also has
27 standard reports. This scoped audit is not a whole-library axiom audit.
The enforced 20 GB, two-thread independent family took 23.21 s and peaked
at 3.75 GiB, without memory events or a safety stop. Full final library/book
and integrated lint/type/dependency gates are required after every final
edit; exact checkpoint evidence is recorded on #21.

The aggregate, module statuses, book and shared goal frontier match this
complete actual-action consumer. Original source TeX, original goal endpoint
and completion criteria, and the full historical continuation prefix are
preserved; the supplemental PDF remains excluded. M is not claimed fresh
from the original Ψ witness. Affine classification, the original scheme
action and normal-subgroup producers, Weil algebraization, original-field
descent, guarded chart extraction and unconditional reconstruction remain
obligations. All eight original #21 requirements remain open.

## The actual rank-two HW affine generator (#21, 2026-10-15)

`Germ.IsHWBij.exists_affine_generator` starts with actual HW bijection data,
a difference-set member of ordinary canonical-base rank exactly two and a
finite rank-one source locus. It internally chooses a transcendental generator
u of the original K-function field in which every actual group element sends
u to a*u+b with a nonzero. This holds in every characteristic. No classification,
eigenbasis, fixed-point, conjugation or coordinate certificate is an input.

The public constructible subgroup classifier chooses a nonbase trace, an
eigenbasis and a full torus internally. Conjugating coefficients enter a small
algebraically closed field before ranks are compared. A fresh actual matrix,
chosen using constructibility, retains rank two over that field. Two full tori
with disjoint fixed pairs force rank three; distinct tori sharing a point
generate the upper Borel, and matrix case analysis finishes the classification.
The actual lift theorem supplies all subgroup hypotheses over its own M.
The coordinate change u=phi_A(t) turns each lift m into A*m*A^-1. The existing
SL2 denominator proof is shared by the old lift consumers and the new coordinate
calculus; its former local duplicate is removed. Supporting lemmas stay private.

Claude supplied the eigenbasis, rank-three, Borel, case-analysis, rank-base-change
and coordinate ingredients. The primary agent read their proofs and assembled
the complete classifier and actual consumer. Both agents independently checked
the exact full private consumer with empty standard-lint logs at default limits;
the peer family took 5.10 s and peaked at 3.88 GiB. The split public candidate was
then checked with four fresh module outputs in 13.08 s, peaking at 3.75 GiB, with
empty standard-lint logs. All 45 existing expanded public types are unchanged;
those and the three new public declarations have 48 selected standard-axiom
reports. This is a scoped audit, not a whole-library axiom audit. Full final
library/book gates and exact CI evidence are recorded on #21 after all edits.

Rank exactly two is retained; the rank-at-least-two affine claim is not made.
The coefficient field is not claimed fresh from the original Psi witness.
The original scheme action, connected normal subgroup, algebraization,
original-field chart/action descent, guarded Q and unconditional reconstruction
remain obligations. All eight original #21 requirements remain open. Original
source TeX, goal endpoint/completion criteria and continuation history are
preserved, and the supplementary PDF stays excluded.

## Guarded ACF chart and completeness checkpoint (#27)

The actual Ψ rank-two HW action supplies the nine initial affine chart rows. An affine
generator is chosen in the original function field; rational evaluation agrees with the
actual action. A coherent automorphism moves the finite witness away from its coefficient
field. The two upper-triangular curve cosets are classified internally, yielding the S/T/U
multiplier rows. `GroupConfig.ChartAssembly` constructs every parameter and chart input.

`GroupConfig.FiniteIncidenceDescent` chooses proper finite annihilator witnesses, including
nonzero denominators and a nonzero coefficient. One constructible system specializes all
coefficient parameters at once. A base-field point of the finite fibre gives all five chart
coordinates in the original algebraically closed ambient. Closure comparison handles the
lift's arbitrary representative choices and absorbs the automorphism into the embedding.
The actual Ψ ranks force independence of these coordinates. Existing normalization gives
the full three-join/fifteen-point grid.

Public `AclGeom.guardedAffineGridExtraction` and `AclGeom.guardedQCompletenessACF` require
only an ACF pair and the actual Ψ witness with both ratio guards. Public
`AclGeom.jCompletenessACF` combines this with the proved multiplication converse and J
assembly under the source rank-five bound. The reconstruction API's explicit inputs can
now be discharged; the next checkpoint strengthens those public statements. Original
scheme/action bridges, true bypassed source lemmas and endpoint variants remain owed.
The frozen M4a log and original blueprint provenance are preserved.

Both agents independently checked the complete private proof before integration. The
checkpoint's final full library/book, selected public-type/standard-axiom and exact-head CI
results are recorded on #27; no selected check is a whole-library axiom audit.

## Unconditional lattice reconstruction checkpoint (#9/#10)

`AclGeom.exists_reconstruction` and `AclGeom.reconstruction_target` now have exactly the
blueprint hypotheses. Their conclusions are unchanged: equality of relative degrees,
compatible reconstruction of arbitrary chosen perfections, the original-field intersection
formula, the exact integral Frobenius fibre, characteristic-zero uniqueness,
positive-characteristic exponent uniqueness and the converse. There is no completeness,
chart, action or reconstruction oracle in either public statement.

A shared private producer supplies the two ACF completeness inputs of the existing generic
`Perfection.exists_induces`. Source rank five transports to each chosen perfection, using
the supplied lattice isomorphism for the target. `five_le_trdeg_algebraicClosure` gives
rank five over each perfected base's algebraic closure. Two local algebraic-closedness
proofs and the proved `jCompletenessACF` discharge the inputs. The generic internal APIs
retain their explicit parameters; no duplicate reconstruction relation is introduced.

Both agents independently checked the two proof modules with empty strict logs. The
complete conclusions and remaining binders agree with the preceding checkpoint; only the
two completeness binders are deleted. Ninety other selected public types are unchanged,
and ninety-three selected declarations use only standard Lean axioms. Full local
library/book and exact-head CI evidence is recorded on #9. These are scoped checks.

The project remains incomplete: the point-geometry, automorphism and functorial variants,
true bypassed source statements, original scheme/action bridges and remaining source
provenance obligations are still owed. The shared mathematical endpoint and acceptance
criteria, original source statements/proofs, and frozen M4a log are preserved.

## Reconstruction variants and perfect-field J correctness (#7/#10)

`Reconstruct.PointVariant` takes a point equivalence preserving full point closure and
derives its unique lattice isomorphism internally. The public theorem gives rank equality,
a compatible reconstruction, the exact Frobenius fibre for its action on points,
characteristic-zero uniqueness, positive-characteristic exponent uniqueness and converse.

`Variants` constructs the group of perfected-base-preserving automorphisms and its action
on the original closed-field lattice. The action is surjective under RAC and rank five;
its kernel is precisely the cyclic subgroup generated by Frobenius, trivial in
characteristic zero and isomorphic to the multiplicative integers in positive characteristic.

`Functorial.Literal` defines the extension groupoid with arbitrary chosen perfections and
the literal geometry functor to `Core PartOrd`. Its functor laws, Frobenius naturality,
surjectivity at rank five and exact Frobenius Hom fibres are proved. Characteristic
exponents are derived to agree along arrows. `Functorial.FrobeniusQuotient` constructs the
congruence and quotient groupoid, descends the functor and proves Hom-set bijectivity.
Full/Faithful instances are restricted to rank-five objects; the literal characteristic-zero
restriction is also full and faithful. Positive-characteristic nonfaithfulness uses only
positive transcendence degree.

`Transfer.JCorrectness` supplies the ACF completeness implication in the internal transfer
API. The four conditions of blueprint T4 are equivalent through any embedding into an
algebraically closed field, and geometric/semantic J agree over perfect ambient fields at
rank five. The original source RAC hypothesis is unnecessary.

Both agents independently checked the proofs. The first point-wrapper draft needed an
explicit unfolding of the reducible `Reconstructs` alias; the exact corrected source has
empty strict logs in both checks. Root's six fresh module outputs have empty strict logs;
141 selected declarations use standard Lean axioms and all 93 preceding selected public
types are unchanged. These checks are scoped. Full library/book and exact-head CI evidence
for the published checkpoint is recorded on #7/#10.

The shared goal remains incomplete. Perfection-choice groupoid equivalence, the complete
source validation suite, final all-public dependency audit, literal/provenance obligations,
true bypassed source results and original scheme/action bridges remain tracked. The source
mathematical statements/proofs and frozen M4a log are preserved.

## Perfection-choice equivalence and reproducible dependency audit (#10)

`Functorial.ChoiceIndependence` proves the literal §20.1 statement for two arbitrary global
choices of perfections. Each canonical comparison is the unique arrow fixing the original
field and induces the identity on its lattice. The choice-dependent groupoids are equivalent
via the identity on objects and conjugation of arrows by comparisons. Their geometry
functors agree under this transport. Arrows preserve transcendence degree.

`Test.Validation` supplies meaningful missing statements from TEST-2 and TEST-8. In positive characteristic, integral
Frobenius iterates are injectively indexed as soon as the original transcendence degree is
positive. Every base field is relatively algebraically closed in its rational function
field, whose degree is its number of variables. The actual reconstruction theorem then
gives equality of variable counts, a compatible reconstruction of arbitrary chosen
perfections and the exact Frobenius fibre. No ACF or characteristic restriction is added.

Both proof modules were independently compiled by both agents from the exact frozen
sources. Root's two fresh outputs have empty strict logs; 161 selected declarations use
standard axioms and all 141 preceding selected public types are unchanged. These checks
are scoped; the reproducible full dependency audit below covers the mathematical libraries.

Run `lake env python3 scripts/audit_axioms.py --output /tmp/acl_geom_axiom_audit` with a
new or empty output directory, under the agent memory cap when applicable. It builds both
roots to avoid stale artifacts, requires the imported module inventory to match all
mathematical source modules, selects declarations by their declaring modules and uses
Lean's `collectAxioms` (the `#print axioms` implementation). It writes source hashes, the
Git head/tree status, declaration records and a summary, and fails for project axioms or
nonstandard dependencies. Generated public declarations are included. The audit on the
preceding 6e878f4 covered all 412 modules, 12,226 public declarations and 9,161 public
theorems. Every loaded project declaration used only standard axioms. Rerun on later heads;
this is a dependency audit, not a proof of blueprint coverage.

The book's validation chapter records existing evidence and remaining obligations without
adding forwarding-only public wrappers. The literal negation detour and total nonzero
addition remain source obligations; the new mathematical negation counterexample was
reported on #23 before formal refutation work. Corrected coupled predicates remain distinct
from those literal claims. Original statements/proofs, goal endpoint/criteria and frozen
M4a are preserved. Full local library/book and exact-head CI evidence is recorded on #10.

The touched multiplication-diagram module also receives a bounded warning cleanup: four
closure helper lemmas no longer require an unrelated independence hypothesis, with all
local callers updated. Goal-changing `show` tactics use `change`, retaining their type
ascriptions. A strict independent check of all 81 public declarations has an empty log;
77 types are exact and precisely the four helper types are stronger. Failed cleanup
attempts are retained in the issue evidence.

## Literal negation and total-nonzero-addition refutations (#23)

`Counterexamples.GenericNegation` records the original §11 formulas as `BlueprintJNeg`
and `BlueprintJAddTotalNZ`, including every auxiliary Frobenius-class constraint.
Over an infinite base and at rank five, `blueprintJNeg_smul` constructs every nonzero
scalar multiple as a literal negation; `blueprintJNeg_self` gives self-negation when
`2 ≠ 0`. `blueprintJAddTotalNZ_kappa` constructs the output `j(κ*x+y,a)` for every
nonzero base scalar. The two `_not_functional` theorems prove distinct wrong outputs,
and their `_on_class` forms put all inputs and outputs in one actual Frobenius class.
No completeness input is used. Independent `x,y,a` satisfy all hypotheses of the
source total-nonzero-addition lemma. The corrected `JNegTotalRel` and `JAddTotalNZRel`
already have proved semantics; the literal full-carrier TOT and ratio-field claims
remain separate obligations.

The mathematical negation and addition counterexamples were reported on #23 before
source status edits (comments 6210013012 and 6210631348). Original theorem/lemma/
proposition/corollary/proof blocks are retained, including the literal detour proof.
The new source warning preserves commit `ee31244` provenance and distinguishes the
refuted formulas from their corrected replacements. The Verso validation chapter
now displays both actual class-level refutations.

Both agents independently compiled the exact new module with empty strict logs.
The integrated source is byte-identical to the peer's frozen `a9f90d28` artifact.
Root's independent review checks all 242 previously selected types unchanged and
nine additional definitions/theorems using standard axioms. Full library/book,
selected-type and whole-library dependency gates, plus exact-head CI, are recorded
on #23 for the committed checkpoint. These checks do not establish full source coverage.

`Interpretation.FrobSetoid` proves the separately owed equivalence-relation conclusion
of `lem:frobeq-correct` on all geometric J-tuples over perfect ambient fields at rank five,
and bundles it as `frobEqSetoid`. No RAC, infinite-base or caller-supplied completeness
hypothesis is needed. Its proof obtains semantic representatives of the three endpoints,
keeps one middle representative and composes the two integral Frobenius exponents.
It supplies the algebraic-closure completeness proof internally through the public
Mathlib `IsAlgClosure.isAlgClosed` instance and `jCompletenessACF`.
The binary semantic-characterization interface keeps its existing input explicit.
Both agents independently compiled the exact frozen `3a097fbf` module with empty strict
logs. Root's fresh two-module check verifies 253 selected types, including all previous
251 unchanged, with standard axioms. Module/book/source status descriptions now record
the global setoid while preserving the original literal and full-carrier obligations.

## Original additive and multiplicative correspondence statements (#5 C6/C7)

`Correspondence.AdditiveThreePair` proves `addcorr`: one common pair of nonzero additive
polynomials works for all three source pairs, and the two sum constants are the sums of
the original constants. The unused second-triple independence hypothesis is omitted,
so the statement is stronger than the source. `Correspondence.MultiplicativeLiteral`
proves `mulcorr` in the original orientation with both integer exponents and both
constants nonzero. Both endpoints assume the source ACF setting and impose no additional
ambient rank, freshness or universal-domain hypothesis.

`Closure.FreshExtension` supplies an algebraically closed extension with four independent
variables. Both consumers use the existing `algHom_racl_image_eq_of_racl_eq`, apply their
two-pair cores in that extension, and pull the equations back by injectivity. The additive
proof compares two translated prime generators through the same first curve's principal
prime ideal. `IsAdditive.aeval_add` extends pointwise additivity to arbitrary commutative
algebras; its named consumers are the prime-translation identity and both sum equations.
No duplicate closure-transport lemma is added.

Both agents independently compiled the exact three-module frozen bundle with empty
strict logs. Root's review checks 258 selected types with standard axioms, including all
255 previous types unchanged. The additive v2 reuses the shared extension and existing
closure transport; its two public types are unchanged from independently checked v1.
The two legacy core headers now state their exact fresh-element scopes; the only changes
to their declaration code replace two deprecated `Prime.not_unit` references with
`Prime.not_isUnit`. The original source statements/proofs, goal objective/acceptance
criteria and frozen M4a log remain unchanged. Full library/book, selected-type and
whole-library dependency gates and exact-head CI are recorded on #5 for this checkpoint.
The abstract subgroup-classification, general curve-coset, geometric fiber-product,
packaged generic-extension, group-chunk and scheme/action statements remain obligations.

## Connected additive-subgroup classification (#5 C4)

`Correspondence.AdditiveSubgroup` proves the prime-ideal curve step, with an exact ideal
and point-locus equation for two nonzero additive polynomials. Its generic Hopf/degree
argument is consumed by this source theorem. `Correspondence.AdditiveSubgroupConnected`
proves the full connected source form as `addSubgroup_classification_of_connected`.
The canonical ideal is `I(H) = vanishingIdeal k H`; closedness means `zeroLocus I(H) = H`,
connectedness is `ConnectedSpace` of its coordinate ring's prime spectrum, and dimension
one is its Krull dimension. Nonconstant projections remain explicit. There is no
caller-supplied prime-ideal premise in the connected theorem.

Primality follows from finite minimal primes. Two components meeting at any point `c`
have a translated-sum closure with prime ideal between the vanishing ideal and both
minimal primes, so they coincide. Disjoint components are comaximal by the Nullstellensatz.
The Chinese remainder theorem would supply a nontrivial coordinate-ring idempotent;
connectedness of its spectrum excludes that, leaving one minimal prime. The prime-curve
step then gives the polynomial classification. Existing additive-polynomial theorems give
the linear characteristic-zero and finite p-power-support characteristic-p clauses.
No additional scheme or tensor-product infrastructure is introduced.

Both agents independently compiled the exact two-module proof bundle with empty strict
logs. Root's review checks 263 selected types and standard axioms, including all 260
preceding types unchanged and the two existing characteristic-shape APIs. The core's
module header now points to the connected theorem; all its declaration code remains
byte-identical to the independently reviewed source. The connected module is unchanged.
Original source statement/proof blocks, goal objective/acceptance criteria and the
frozen M4a record are preserved. Full library/book, selected-type and whole-library
validation and exact-head CI are recorded on #5 for the committed checkpoint.
The torus part, general curve-coset, geometric fiber-product, packaged generic-extension,
group-chunk, six-point and original scheme/action statements remain obligations.

## Status-claim cleanup after the source subgroup checkpoint (#1/#5)

A coordinated read-only audit identified older headers that still called the guarded ACF
completeness theorem, public reconstruction, functorial packaging and existing Q/Q′
refutations open. This bounded cleanup corrects twenty-nine mathematical module headers and
two book chapters against the actual named proofs. Every mathematical import, declaration,
docstring, attribute and proof outside those module headers is byte-identical. The book
now displays the two actual arbitrary-field Q/Q′ refutations and points to the proved
literal/quotient functors and perfection-choice equivalence.

The internal interpretation/reconstruction APIs keep their ACF-completeness and carrier
inputs explicit; the corrected status text identifies the rank-five producer
`jCompletenessACF` and its use inside `Main`. Conditional carrier naturality remains
qualified. The original general R1/R2 interpretation arguments, literal construction and
provenance, general existential-witness descent and scheme/action obligations are retained.
The embedded linear-disjointness assertions in the original proof of
`lem:two-generic-intersection`, over the algebraically closed base Ē, retain a separate
[source-audit obligation on #9](https://github.com/adamtopaz/acl_geom/issues/9#issuecomment-6213314770).
The exchange proof establishes the intersection theorem but does not discharge those
assertions. This is distinct from the (8.9a) proof passage audited on #5. Closed #11's
tensor-domain theorem stays proved. The active R3 source-status annotation is aligned;
all original blueprint statements and proof blocks are preserved. Frozen M4a remains
a historical record.

The shared goal's old application paragraph now records the proved guarded chart's finite
formulas, independence recovery and original-ACF-ambient coordinate descent, while keeping
original scheme/action descent open. The objective and acceptance criteria are unchanged.
The remaining status audit is tracked on #1: five Correspondence headers
(`AffineLocusCommutation`, `AffineRelocation`, `FiniteCurveLoci`, `MultiplierCurve`,
`MultiplierPrimeCurve`); chart descriptions in `AffineGridNormalization`, `PsiLattice`,
`RemainingAffineMeets`, `ShiftedAffineMeets` and `CanonicalBaseInput`; and the HardKernel
book's chart/completeness/recovery passages. These need a follow-up; this checkpoint is
not an exhaustive correction of all historical status text.

Full library/book, selected-type comparisons, the reproducible whole-library dependency
audit and exact-head CI are recorded on #1 for the committed cleanup checkpoint. This is
a correction of progress descriptions; it does not discharge the remaining original and
supplementary source statements or complete the full project goal.

## Torus-subgroup classification and the shared connectedness bridge (#5, C5)

`mulSubgroup_classification_of_connected` proves part (b) of blueprint
`lem:subgroup-classification` over an algebraically closed field. It takes a subgroup of
`kˣ × kˣ`, closedness under the canonical embedding `(u,v) ↦ (u,v,u⁻¹,v⁻¹)` into affine
four-space, connectedness of its canonical coordinate-ring spectrum, Krull dimension one
and two nonconstant projections. It concludes the exact kernel equation `u^m = v^n` for
nonzero integers, and the equation of every coset with its nonzero unit constant. No prime
ideal is supplied by the caller. Closedness in affine two-space is not substituted.

The new `SubgroupConnectedPrime` module shares the component/minimal-prime and
CRT/idempotent argument between the additive and torus consumers. Each supplies concrete
polynomial endomorphisms for its ternary operation: translations for `u + v - c`, scalings
for `u * v * c⁻¹`. The existing additive public type is unchanged, while duplicated private
bridge proofs are removed. The shared proof reuses Mathlib's prime Nullstellensatz and
idempotent basic-open APIs. `TorusCoordinates` supplies actual denominator-clearing and
character consumers, including one general positive/negative integer-power identity.

The torus proof passes to the plane closure, derives a nonzero height-one prime ideal
and a character relation from scaling invariance, and removes the common integer factor
using primality over the algebraically closed base. Nonconstant projections exclude zero
exponents. A Bézout cocharacter parametrizes the kernel; a proper closed preimage would
be finite, contradicting infinitude. This avoids the original proof's all-support-rank
argument without changing the source theorem. Original statement and proof blocks,
the goal's objective/completion criteria and frozen M4a are preserved.

Both agents independently compiled all four exact candidate modules with empty strict
logs. Root also freshly compiled the unchanged import root and checked 283 selected
standard-axiom records, with all 263 preceding types exact. The additive endpoint keeps
its old public type. Full integrated library/book and whole-library dependency validation
and exact-head CI belong to the published checkpoint report on #5. The general
curve-coset theorem, geometric fiber-product bridge, packaged generic extension,
group-chunk, six-point and original scheme/action/provenance obligations remain open.
The shared project goal is incomplete.

The four deferred HardKernel book passages now distinguish proved guarded charts and
rank-five completeness/reconstruction from the open geometric fiber-product and original
scheme/action statements. The two matching active generic-extension source-status
annotations are aligned. The remaining mathematical-header audit still includes the
previously listed Correspondence/Config files and `Correspondence.AmbientAutomorphism`;
this checkpoint does not claim an exhaustive status cleanup.

## Original two-generic embedded-field validation (#9)

`linearDisjoint_adjoin_simple_of_transcendental` is the sole new public theorem. For any
fields `F → Ω`, intermediate field `N` and `s` transcendental over `N`, it proves actual
embedded linear disjointness of `N` and `F(s)` over `F`. It specializes the existing
`isGeneric_baseChange` to a singleton tuple with zero relation ideal. Every earlier
declaration in `GenericExtension` is unchanged; its header distinguishes the proved
guarded chart/completeness/reconstruction from the open geometric fiber-product and
original scheme/action obligations.

`Test.TwoGenericSource` has private source-validation theorems, with no public interface.
It checks A0 closure identities, A1 rational-field linear disjointness, A2 closure
intersection, A3 stronger linear disjointness and actual embedding extension fixing
the whole other rational field, A4 the algebraicity conclusion and A5 intersection
with the original field. The finite normal envelope is constructed from Mathlib's
normal closure of a simple algebraic extension in an algebraically closed ambient;
the ambient is not assumed normal over the rational field. The other fixtures allow
an arbitrary ambient extension and derive their field independence from the original
closure-independence hypotheses. No expected extension or linear-disjointness conclusion
is an input. The embedding to be extended is the source's universally quantified variable.

The original argument's extension step needs the stronger disjointness of the finite
normal extension and the other rational field. Transcendence over the algebraic extension
supplies it. This corrects the justification gap reported on #9 while retaining every
original source proof block. The algebraicity conclusion is checked using exchange;
the conjugate-comparison proof route is not transcribed. The active source annotation,
TwoGeneric and Existence headers and reconstruction book agree on that scope. Closed
#11's abstract tensor-domain theorem and the distinct (8.9a) audit on #5 are unaffected.

Both agents independently compiled the final proof bundle with empty strict logs; root
also freshly compiled its import root. All 283 preceding selected public types remain
exact, with the new theorem giving 284 standard-axiom records. All declarations of the
two proof modules, private and generated ones included, were independently checked for
standard dependencies. Full library/book, whole-library and exact-head CI evidence
belongs to the published checkpoint report on #9. Original 48 statement blocks and
44 proof blocks, the full goal and frozen M4a are preserved. The original general
R1/R2 interpretation/provenance, broader source and scheme/action obligations remain
open. This checkpoint does not complete the full shared goal.

## Tensor localization and joint versus endpoint-image fields (#5 C2)

`Correspondence.TensorFractionRing` proves
`minimalPrimes_tensorProduct_fractionRing` for domains `A → B`, `A → C` with
compatible fraction fields `K`, `L`, `M`. Under the canonical map, the minimal
primes of `L ⊗[K] M` contract exactly to the minimal primes of `B ⊗[A] C` avoiding
the nonzero elements of `A`. Injectivity of the base maps follows from the genuine
fraction-field/tower data. Two factor localizations and flatness prove the result;
there are no Noetherian, separability, reducedness or algebraic-closedness inputs.
The three private helpers are consumed by this single public theorem. Its named
consumer is the canonical-locus geometric fiber-product bridge for finite tuples,
which remains open. No scalar or rational-curve restriction discharges that bridge.

`Counterexamples.EndpointImage` proves a strict field inequality for two actual
`FiniteCorrespondencePair` branches with a shared middle coordinate. The chain
is `(t²,t,t²)` for a genuine transcendental `t`; its endpoint field `k(t²)` is
properly contained in the joint field `k(t)`, in every characteristic. The proof
uses Mathlib's rational-function degree theorem and transports through the actual
transcendental-generator equivalence. Two private lemmas are consumed by this
single public counterexample; no expected field inequality is an input.

The corrected general inclusion, its finite-extension form and the identification
of the tensor compositum with the joint field already exist in `FiniteCover` and
`TensorComponent`. They are reused rather than restated. The source wording issue
was reported on #5 (comment 6215313613) before the new annotation. The original
§8.1 paragraph, all original statement/proof blocks and frozen M4a are preserved.
The source annotation and hard-kernel book distinguish incidence components from
their endpoint images. The shared goal's C2 description records the same distinction.
Relational associativity stays proved; the tuple/nonrational geometric fiber-product
bridge and the higher-dimensional family generic-component argument remain open.
This counterexample does not close C2 or complete the shared project goal.

Both agents independently compiled the exact two proof modules with empty strict
logs. Root checks all nine new declarations, including private and generated ones,
for standard dependencies. The two new public theorems give 286 selected records,
with all 284 preceding selected public types unchanged. Full library/book, whole-library
and exact-head CI evidence belongs to the published checkpoint report on #5. The scope
of a dependency audit must still be distinguished from complete source coverage.

## Actual affine fiber-product components over canonical tuple loci (#5 C2)

`Correspondence.ComponentGeometry` proves
`dominatingComponents_tensorProduct_fractionRing`: actual irreducible components
of the tensor-product prime spectrum have dense projection image in the base
spectrum exactly when they arise from the fraction-field tensor minimal primes.
It uses the already proved domain localization theorem, Mathlib's minimal-prime
component correspondence and its image-closure formula. There is one public
theorem and no extra module helper declarations.

`Correspondence.LocusPullback` constructs the actual affine-scheme fiber product
of the canonical generated coordinate rings of `(x,y)` and `(y,z)` over that of
`y`. Its theorem `locusPullback_dominatingComponents` identifies the irreducible
components whose actual base projection has dense image. Only the tuples are
data: the inclusion algebras, scalar towers and fraction-field structures are
constructed internally. The proof transports the actual projection along
Mathlib's pullback isomorphism, as well as the irreducible components. One private
generic helper, consumed by this theorem, checks that transport with variable
instances so that concrete inclusion-instance elaboration stays within the default
checking limits. The base,
ambient and tuple-index universes are retained, and no algebraic closedness,
Noetherian, rational-curve or single-coordinate assumption is added.

The earlier private `LocusTensor` prototype is superseded by this actual scheme
consumer, which retains its canonical tuple structures. It is not added as an
unused public layer; its frozen proof evidence is retained in the issue record.
The existing `locusCoordinateRingEquiv` supplies each factor's quotient dictionary.
The relative quotient maps matching the rename-induced coordinate maps, endpoint
dominance, tuple germs/relational associativity and the family's finite-relative-
transcendence-degree generic-component argument remain open. This checkpoint does
not close C2 or complete the shared goal.

The source annotation, hard-kernel book and shared goal record this exact scope.
The original blueprint paragraphs, all 48 original statement blocks and 44 proof
blocks, the goal objective/completion criteria and frozen M4a are preserved. Full
library/book, whole-library and exact-head CI evidence belong to the published checkpoint
report on #5; dependency checks are not complete source coverage. Both agents independently
compiled the exact two proof modules with empty strict logs. Root checks all 23 new
declarations, including private and generated ones, for standard dependencies and checks
288 selected type/dependency records, with all 286 preceding public types unchanged.

## Endpoint dominance on the actual canonical fiber product (#5 C2)

`Correspondence.LocusEndDominance` proves `locusPullback_endDominance` for the
actual affine-scheme fiber product of the canonical tuple coordinate rings.
Under the four algebraicity/closure clauses of (8.1), any subset has dense
middle image if and only if it has dense image under the actual first endpoint
projection, and likewise under the second endpoint projection. The rank-one clauses are not needed for this criterion. All four
coordinate-ring algebraicity facts and injective maps are derived internally;
no algebraicity, component or density conclusion is supplied by the caller.

Two private ingredients reflect density through an injective algebraic domain
extension and derive `Algebra.IsAlgebraic k[S] k[T]` from `S ⊆ T ⊆ racl k S`.
The density lemma allows an arbitrary tensor/target ring, including nonreduced
ones, and arbitrary subsets. One further private generic scheme helper is
consumed twice by the public theorem; it pushes the subset through the actual
projections, using the pullback equation for the middle map. The proof needs
no pullback-isomorphism or component-classification calculation. Each helper
has this immediate consumer and none is published as an isolated interface.

Both agents independently compiled the exact new module with an empty strict
log. All 21 new declarations, including private/generated ones, have standard
dependencies. Root checks 289 selected type/dependency records with all 288
preceding public types unchanged. The three touched module headers now identify
the proved canonical fiber-product and endpoint results while retaining the
literal relative quotient maps, tuple germs/relational associativity and the
family generic-component argument as obligations. In those three modules, all
imports, declaration docstrings, attributes and proofs outside the headers are
unchanged.

The source annotation, hard-kernel book and shared goal record the same scope.
All original blueprint text outside its existing annotation, the 48 original
statement blocks and 44 proof blocks, the goal objective/completion criteria
and frozen M4a remain unchanged. Full library/book, whole-library dependency
and exact-head CI evidence belongs to the published checkpoint report on #5.
Those dependency checks do not establish complete source coverage. C2 and the
full shared project goal remain open.

## Literal relative quotient spectra and their projections (#5 C2)

`Correspondence.LocusQuotient` proves contraction of tuple ideals along
variable renaming and the commutation of the literal induced quotient map
with `locusCoordinateRingEquiv`. Its relative tensor theorem constructs a
base-field algebra equivalence to the generated-ring tensor, with explicit
pure-tensor and base-map formulas. The two actual middle-variable inclusions
are used; the quotient maps are not defined by transporting the desired
inclusions. One private generic heterobasic tensor helper has this immediate
consumer, using Mathlib's `mapRingHom` and its inverse.

`Correspondence.LocusQuotientComponents` consumes that equivalence. Its
`exists_locusQuotient_dominatingComponents` identifies the literal spectrum's
irreducible components with dense middle projection image by contracting
the minimal primes of the canonical fraction-field tensor. The map is
constructed internally and specified on pure tensors. Its
`locusQuotient_endDominance` compares the actual first/middle/second
projection images for every subset under the four algebraicity clauses of
(8.1). No rank-one, rationality or algebraic-closedness premise is needed.
The base, ambient and three index universes remain independent.

The existing `denseImage_iff_of_isAlgebraic` and
`isAlgebraic_adjoin_of_subset_racl` are public reusable lemmas, consumed by
both the canonical scheme criterion and the literal spectrum criterion.
Their proofs are unchanged; only visibility and docstrings change in
`LocusEndDominance`. The three older localization/component/pullback modules
have header-only scope updates, with their proofs, attributes, declaration
docstrings and imports unchanged. Both agents independently compiled the exact
mathematical proof bundle, including all public/private/generated dependency records,
and all preceding selected public types remain unchanged. Full library/book,
whole-library and exact-head CI evidence belongs to the checkpoint issue
report; dependency checking does not establish complete source coverage.

The full incidence quotient by the sum of the two extended pair ideals is
still owed. The comparison with the prime quotient of a selected joint
tuple and with the endpoint image must retain the component/minimality proof.
Tuple germs/relational associativity,
all-component realization and the higher-dimensional finite-relative-degree
family argument remain obligations. The source annotation, book and shared
goal retain that scope. All original source outside the existing annotation,
all 48 statement blocks and 44 proof blocks, the goal objective/completion
criteria and frozen M4a are preserved. C2 and the full shared goal remain open.

## The full incidence quotient and its spectrum (#5 C2)

`Correspondence.LocusIncidence` proves `exists_locusIncidence_algEquiv`:
the literal relative tensor is base-field algebra isomorphic to the joint
polynomial ring modulo the sum of the two extended pair ideals. It specifies
polynomial pure tensors and the middle base. A private generic helper proves
the polynomial-quotient universal property, with one inverse law checked on
generators and the other on pure tensors via tensor induction. The public theorem uses the actual rename-induced quotient maps;
the helper's generator facts are discharged by reflexivity. No domain,
finiteness, rank or algebraicity premise is added.

`idealOf_le_comap_rename_comp` supplies the ideal containments for the three
rename-induced projection maps into the incidence quotient. It has these three immediate
consumers in `LocusQuotientComponents`. The actual middle/endpoint maps are
rename-induced quotient maps, not maps defined by transporting a desired
projection along the isomorphism.

`exists_locusIncidence_dominatingComponents` identifies exactly the incidence
spectrum's irreducible components with dense middle projection image. Its map
to the canonical fraction-field tensor is built internally and specified on
products of renamed pair polynomials. `locusIncidence_endDominance` compares
the actual middle and both endpoint images for every subset under the four
algebraicity clauses of (8.1). All five universes remain independent.

The component transport in `LocusQuotientComponents` is extracted once into a
private generic core and consumed by both the existing tensor result and the
new incidence result, with a further private algebra-equivalence helper to
keep the incidence proof within the default elaboration limit. Density
transport is also reused. The existing public
tensor-component and endpoint statements, and all preceding selected public
types, remain unchanged. Both agents independently compiled the mathematical
proof bundle and its public/private/generated dependencies. Full library/book,
whole-library and exact-head CI evidence belongs to the checkpoint report;
dependency validation does not establish complete source coverage. The four
older localization/component/pullback/relative-quotient modules have header-only
scope updates, with their imports, declaration docstrings, attributes and
proof bodies unchanged.

The selected joint-tuple prime of the incidence ring still needs its
minimality/component proof under the source hypotheses. It must not be
identified with the incidence ideal or its endpoint image without the needed
comparison. Tuple germs, all-component realization, relational associativity
and the higher-dimensional family argument remain owed. The source annotation,
book and shared goal retain that scope. All original source outside the
existing annotation, all 48 statement blocks and 44 proof blocks, the goal
objective/completion criteria and frozen M4a are preserved. C2 and the full
shared goal remain open.

## The chosen joint tuple is a dominating incidence component (#5 C2)

`Correspondence.LocusJointComponent` proves the actual joint-point component
clause. `locusIncidence_le_idealOf` shows that joint evaluation kills the sum
of the two extended pair ideals; the evaluation therefore factors through
the actual incidence quotient. `locusIncidence_jointPrime_dominating` proves
that its kernel is minimal and its zero locus has dense image under the
actual rename-induced middle projection. Its only extra premise is the
source closure clause that each coordinate of z is algebraic over k(y).
No condition on x, rank, finiteness, rationality or algebraic closedness is
needed. All five universes remain independent.

The proof derives algebraicity of k(y,z) over k(y) internally. The tensor
k(x,y) tensor_k(y) k(y,z) is then integral over its left field. Its actual
multiplication kernel contracts to zero in that field; Mathlib's integral
extension theorem therefore makes it minimal. Polynomial generator formulas
identify multiplication after the incidence-to-function-field map with
actual joint evaluation. The proved incidence component classification
transports the kernel to the chosen joint prime and its dense middle image.
Four private lemmas support this concrete tuple producer: generic kernel
minimality, generic component contraction, field algebraicity and polynomial
evaluation compatibility. The maps from the generated fields into the
ambient field are built directly as algebra homomorphisms, and the
algebraic-closure containment is proved before installing the relative
inclusion algebra. This avoids the observed default-limit kernel timeouts
without raising checking limits. No minimality, domain, fraction-field or
projection conclusion is an input
to the public theorem. Both agents independently compiled the proof bundle
with default limits and checked its public/private/generated dependencies.

The six older localization/component/pullback/relative-quotient/incidence
modules change only in their module scope headers; imports, declaration
docstrings, attributes and mathematical code are unchanged. The book, source
annotation and shared goal now record the proved single-clause result.
Original source outside the existing annotation, all 48 statement blocks
and 44 proof blocks, the goal objective/completion criteria and frozen M4a
are preserved. Whole-library dependency checks do not establish source
coverage. Full library/book and exact-head CI evidence belongs to the issue
checkpoint report.

Tuple germs, realization of every dominating component, relational
associativity, endpoint-image comparison and the higher-dimensional family
generic-component argument remain obligations. The actual joint component
field must remain distinct from the possibly smaller endpoint-image field.
C2 and the full shared goal remain open.

## All finite-tuple incidence components are joint loci (#5 C2)

`locusIncidence_dominatingComponents_eq_jointLoci` proves an equality of
sets: the actual incidence spectrum's irreducible components with dense
image along the actual middle renaming projection are exactly the zero loci
of the images of joint vanishing ideals `I(x′,y,z′)`, where both pair
ideals equal the original ones. It proves both directions in one theorem.
The outer index types are finite, x and z are algebraic over k(y), and the
ambient field is algebraically closed. The middle tuple and its index type,
the base field and all five universes remain arbitrary. No rank-one,
rationality, component, density or finite-extension conclusion is an input.

`TensorRealization.exists_productMap_ker_of_isPrime` is now public and has
two actual consumers: the existing scalar component embedding theorem and
the new tuple classification. Its proof, imports and all old scalar public
types are unchanged. Its generated simp declaration also becomes public;
all public/private/generated declarations are included in the checks.

The proof derives both finite generated-field extensions over k(y) using
Mathlib's finiteDimensional_adjoin and a surjective map to the actual
inclusion algebra. A private generic core matches the proved component
classification with the contracted kernels of all pairs of embeddings.
Polynomial generator formulas then identify these kernels with the images
of the actual joint ideals. The embeddings preserve both pair ideals and
fix y. Conversely, the existing locusFunctionFieldEquivOfIdealEq gives
isomorphisms of the generated fields. Composing with the inclusions and
checking the middle generators produces embeddings fixing k(y); their same
polynomial comparison gives the desired joint locus. No new copy of the finite-component
embedding proof or ambient automorphism extension is introduced.

The generalized polynomial comparison has two consumers: the new set
equality and the previous chosen-joint-prime theorem. The latter and its
containment theorem retain their public statements. Supporting private
finite-dimensionality and ideal/embedding lemmas each have these concrete
uses. Both agents independently compiled the exact mathematical bundle
with default limits and checked all public/private/generated dependencies.
Six older geometric bridge modules change only in their scope headers;
imports, declaration docstrings, attributes and mathematical code are exact.

Original source outside the existing annotation, all 48 statement blocks
and 44 proof blocks, the goal objective/completion criteria and frozen M4a
are preserved. Source annotation, book and goal record this finite-tuple
classification precisely. Dependency validation does not establish source
coverage; full library/book and exact-head CI evidence belongs to the issue
checkpoint report. Tuple germs, relational associativity, endpoint-image
comparison and the higher-dimensional family generic-component argument
remain owed. The joint component field remains distinct from its possibly
smaller endpoint-image field. C2 and the full shared goal remain open.

## Actual coordinate-ring dimension of every finite tuple locus (#5 C2)

`Correspondence.LocusDimension` proves `exists_locusCoordinateRing_dimension`:
the Krull dimension of the literal quotient `MvPolynomial ι k ⧸ idealOf k a`
equals the transcendence degree of the actual generated field `k(a)` over k.
Both equal one internally chosen natural number. Only finiteness of the index
type is required; the base, ambient and index universes are independent. No
algebraic-closedness, rank-one, rationality or dimension conclusion is supplied.

The first private helper compares Krull dimensions for integral faithful
extensions, using strict contraction of prime chains in one direction and
Mathlib's going up in the other. Its named consumer is the second private
helper: Noether normalization of an actual finite-type domain yields an
integral injective polynomial algebra, whose number of variables computes
both the Krull dimension and its fraction field's transcendence degree.
The public finite-tuple producer derives finite type for the generated ring
and transfers the result along the existing `locusCoordinateRingEquiv`.
These two private helpers and one generated simp declaration are included
in the dependency inventory. No separate normalization interface is added.

Both agents independently compiled the exact mathematical source at default
strict limits and checked all four public/private/generated declarations.
The proper module header and public docstring were then added without any
change to imports or mathematical code. The new public theorem has exactly
three independent universes and type hash 2188149426. The selected audit
includes 305 standard-dependency public types, with all 304 preceding types
unchanged. Full library/book, whole-library dependency and exact-head CI
validation belong to the published checkpoint report on #5. Dependency
validation is not complete source coverage.

The root module exports the result, the loci dictionary points to it, and the
book and existing source annotation state the same scope. All original source
outside that annotation, all 48 statement blocks and 44 proof blocks, the goal
objective/completion criteria and frozen M4a remain unchanged. The function-field
module changes only in its scope header. Tuple germs, relational associativity,
endpoint-image comparison and the higher-dimensional family generic-component
argument remain obligations. C2 and the full shared goal remain open.

## Tuple germs, relational associativity and actual component images (#5 C2)

`Correspondence.TupleComposition` supplies the genuine finite-tuple germ
layer. `TupleCorrespondencePair` stores source rank one and mutual coordinatewise
closure; its ideal is joint evaluation's kernel, and presentations compose at
one literally shared middle tuple. `TupleCorrespondenceGerm` stores that ideal
with the existence of a presentation. Its `Composes` relation retains all
shared-middle presentations without selecting a binary operation.

`composes_assoc` proves both directions of relational associativity for four
finite index types in an algebraically closed ambient field, over an arbitrary
base, in six independent universes. `exists_composes_of_middle_ideal_eq` gives
a composite when the contracted middle ideals agree; only the middle index
needs to be finite. `composes_ofPair_carriers_eq` proves both directions of the actual
geometric link for fixed shared-middle presentations and three finite indices:
the set of composite carrier ideals equals the set of contractions to
endpoint variables of the vanishing ideals of middle-dominating irreducible
components of the actual incidence quotient. The component-to-carrier
implication constructs the germ and its genuine presentation internally;
it does not assume a germ with the desired carrier. Its ideal and rename-induced middle projection are the
same as in `LocusJointComponent`. The joint field is not identified with the
possibly smaller endpoint-image field.

Four private helpers have these concrete consumers. `ofIdealEq` transfers rank
using the existing generated-field isomorphism and transfers closure from equal
joint ideals. It feeds `transport` and the reverse component implication.
`idealOf_comp_elim` preserves joint ideals under ambient automorphisms and is
used throughout. `transport` feeds associativity and nonempty composition.
`idealOf_target_eq` identifies the middle ideal in every presentation and feeds
nonempty composition and the forward component implication. The component proof
keeps its incidence ideal fixed, derives containment from equal pair ideals,
proves the mapped joint ideal prime, and uses quotient contraction and variable
renaming to recover the endpoint ideal. It consumes the all-component set
equality in both directions. The source rank-one and closure hypotheses are
stored in the genuine pair. Rank and closure of transported presentations,
component classification and automorphism alignment are derived internally.

Both agents independently compiled the exact mathematical source with empty strict
logs and default limits. All 58 public/private/generated declarations use only
standard axioms. There are 18 intended user API names and 20 generated structure
API names, with no unexplained API; all 38 type hashes agree between agents.
The selected audit has 323 standard-dependency public types, retaining all 305
preceding types exactly. Scalar source modules and their public statements are
unchanged. Full library/book, whole-library and exact-head CI evidence belongs
to the published checkpoint report; dependency validation is not source coverage.

Seven older bridge modules change only in scope headers. Book, shared goal and
the existing source annotation record the same scope. An older book paragraph
that still listed finite-tuple Krull dimension as open now points to its proved
coordinate-ring theorem. Original source outside the existing annotation, all
48 statement blocks and 44 proof blocks, the goal objective/completion criteria
and frozen M4a remain unchanged. The following field module proves the general
generated-tuple field clauses. The finite-generic-fibre equivalence, component-field/compositum dictionary,
threefold incidence-component comparison, scalar specialization, higher-dimensional family argument,
packaged generic extension, general curve-coset and original group/scheme/action
obligations remain open. C2 and the full shared goal remain open.

## Rank and finite generated-field extensions in the tuple calculus (#5 C2)

`Correspondence.TupleCompositionField` derives the second rank-one clause of
(8.1) and the generated-field finiteness clauses of the same source paragraph.
`TupleCorrespondencePair.target_rank` needs no finiteness or ACF hypothesis.
Its one private generic step identifies transcendence degrees along an
algebraic extension of intermediate fields. Mathlib's canonical tower on
`extendScalars` gives a zero relative summand; an identity algebra equivalence
transfers back to the actual containing field. The target-rank proof uses this
twice, with algebraicity derived internally from the two closure clauses.

`endpointField_le_jointField` proves the actual inclusion of k(x,z) in
k(x,y,z), without extra hypotheses. `jointField_finiteDimensional` proves
finiteness over k(x,z) when the middle index is finite and y is algebraic
over that endpoint field. Both outer index types, the base and the ambient
field are arbitrary. `jointField_finiteDimensional_over_ends` proves
finiteness over each of k(x) and k(z), for finite indices and the four genuine
closure clauses of (8.1); neither rank one nor ACF is needed. The actual
inclusions are used in Mathlib's `extendScalars`, and all generator identities
and closure transitivity are derived internally. Restriction of scalars reduces
the fields to finite algebraic field adjoins, then `finiteDimensional_adjoin`
proves the conclusions. No duplicate of the incidence module's custom inclusion
algebra transfer and no new public normalization helper is introduced.

The field module has five declarations: four public source producers and one
private rank step, with no generated matcher. Both agents independently compiled
the exact tuple and field sources, with empty strict logs and default limits.
All 63 declarations in the two-module bundle use only standard axioms, and
all 63 raw type hashes agree between agents. All 58 tuple declarations and the
first three field API types are retained. The selected audit now has 327
standard-dependency public types and preserves all 323 preceding tuple-checkpoint
types exactly, including all 305 main types. The field module's five universes
are independent, and target rank uses four. Full library/book, whole-library
and exact-head CI evidence belongs to the checkpoint report on #5. Dependency
validation is not complete source coverage.

These field clauses are part of the same finite-tuple calculus checkpoint as
the carrier-set equality, relational associativity and nonempty composition.
The joint field may remain a proper finite extension of the endpoint-image
field. The finite-generic-fibre equivalence, component-function-field/compositum
dictionary, threefold incidence-component comparison, scalar specialization
and higher-dimensional family argument remain open,
as do the original packaged generic-extension, curve-coset and group/scheme/action
obligations. All original source outside its existing annotation, all 48
statement blocks and 44 proof blocks, goal objective/completion criteria and
frozen M4a are preserved. C2 and the full shared goal remain open.

The final module-scope headers of both new modules now point to the field
producers and the precise remaining §8.1 dictionary obligations. Only their
module docstrings differ from the independently compiled frozen sources;
imports, declaration docstrings, attributes, statements and proofs are exact.
This removes an earlier open-field marker without altering mathematical code.

## The finite-extension criterion for a tuple pair (#5 C2)

`pairField_finiteDimensional_iff` proves the function-field criterion of (8.1).
For two finite tuples v and w, the actual common generated field k(v,w) is
finite over each of k(v) and k(w) exactly when every coordinate of either
tuple is algebraic over the field generated by the other. Both inclusions
use Mathlib's canonical `extendScalars`. The base and ambient fields and the
two index types lie in four independent universes. No rank-one or ACF
hypothesis is used.

The forward direction takes algebraicity of an element of a finite extension
and transfers it through the actual subfield inclusion into the ambient field. The
reverse direction identifies the extension with a field adjoin of a finite
algebraic tuple. A local proof step serves both projections; no helper
declaration, generated matcher or caller-supplied field certificate is added.
All preceding declarations, imports and mathematical proofs are unchanged.

Both agents independently checked the exact mathematical source with empty
strict logs and default limits. All 64 declarations in the tuple/field bundle
use only standard axioms, all 63 preceding raw type hashes are retained, and
all 64 raw hashes agree between agents. The field module now has six
declarations: five public source producers and the existing private rank
step. The selected audit has 328 standard-dependency public types and retains
all 327 preceding types exactly. Full library/book, whole-library and exact-head
CI evidence belongs to the checkpoint report on #5. Dependency validation is
not complete source coverage.

This supplies the field criterion, not the full scheme-level generic-fibre
dictionary. That geometric packaging, the actual component-function-field and
compositum dictionary, the threefold incidence-component comparison, scalar
specialization and higher-dimensional family argument remain open. Packaged
generic extension and the original group/chunk, curve-coset and scheme/action
obligations remain separate. All source outside the existing annotation, all
48 statement blocks and 44 proof blocks, goal objective/completion criteria and
frozen M4a are preserved. C2 and the full shared goal remain open.

## Actual component coordinate rings and composita (#5 C2)

`Correspondence.LocusComponentField` proves
`exists_locusIncidence_component_algEquiv`. For every irreducible component
of the actual incidence spectrum whose actual middle projection has dense
image, it chooses x′ and z′ preserving both original pair ideals. It gives
an algebra isomorphism from the actual incidence quotient modulo that
component's vanishing ideal to the ring generated by (x′,y,z′), and an
algebra isomorphism from its actual fraction ring to k(x′,y) ⊔ k(y,z′).
Both maps send every polynomial representative to its evaluation at the
chosen joint tuple. No realization, prime/domain certificate or desired
isomorphism is supplied by the caller.

Only the outer indices must be finite and the outer coordinates algebraic
over k(y); the ambient field is algebraically closed. The base and middle
tuple remain arbitrary, and all five universes are independent. No rank-one
or rationality hypothesis is used. The component classification provides the
realization. The prime mapped joint ideal identifies the component's vanishing
ideal; the third isomorphism theorem and `locusCoordinateRingEquiv` identify
the actual double quotient. Mathlib's canonical `algebraAdjoinAdjoin` fraction
algebra supplies the fraction-ring equivalence, and the union of the two pair
coordinate sets identifies the generated joint field with their compositum.
The endpoint-image field can still be a proper subfield of this component
field. No custom inclusion algebra, extra normalization helper or foreign
namespace declaration is introduced.

The new module imports only `LocusJointComponent` and has four declarations:
one public source producer, one internal simplification theorem and two
private declarations for the incidence-ideal notation. Both agents independently
checked the exact source with empty strict logs and default limits. All four
declarations use only standard axioms, and all four raw type hashes agree.
The selected audit has 329 standard-dependency public types and retains all
328 preceding types exactly. Full library/book, whole-library and exact-head
CI evidence belongs to the checkpoint report on #5. Dependency validation is
not complete source coverage.

Nine older bridge/germ/field modules change only in module-scope headers.
They point to this component-field result and to the book and shared-goal
frontier for remaining obligations. Their imports, declaration docstrings,
attributes, statements and proofs are unchanged. The book and existing source
annotation retain the joint/endpoint distinction. All source outside that
annotation, all 48 statement blocks and 44 proof blocks, goal objective/completion
criteria and frozen M4a are preserved. The scheme-level finite-generic-fibre
dictionary, threefold incidence-component comparison, scalar specialization,
higher-dimensional family argument, packaged generic extension and original
group/chunk, curve-coset and scheme/action obligations remain open. C2 and the
full shared goal remain open.

## Generic fibres and the full finite-correspondence criterion (#5 C2 B1)

`Correspondence.LocusGenericFiber` proves `exists_pairGenericFiber_algEquiv`.
For the actual inclusion k[v] ⊆ k[v,w], its generic-fibre ring
k(v) ⊗[k[v]] k[v,w] is k(v)-isomorphic to k(v)[w], sending a ⊗ b to ab.
Only w must be finite; v and the fields are arbitrary. Both finite dimension
of this ring and finiteness of its actual spectrum projection are equivalent
to coordinatewise algebraicity of w over k(v). Mathlib's `pullbackSpecIso`
identifies this spectrum with the scheme generic fibre, and the existing
coordinate-ring map identification matches the literal quotient projection.

One private generic helper proves injectivity of the multiplication map using
flatness of the fraction field and `IsLocalization.algebraLid`. Its sole
consumer is the generic-fibre producer. The map's range is the actual algebra
adjoin; finite integral generators and the finite-affine-morphism criterion
give the two finiteness conclusions. Direct algebra maps avoid a custom
scalar tower. This module has eleven declarations: the public
producer, its consumed private helper and nine private notation declarations.

`pairLocus_finiteCorrespondence_iff`, in `TupleCompositionField`, proves the
full "(8.1) says precisely" criterion for two finite tuples. Both LITERAL
rename-induced quotient projections have dense image, proved from the
coordinate-ring equivalence and injectivity of the generated-ring inclusions.
The literal joint coordinate quotient has Krull dimension one and the two
actual generic-fibre spectrum projections are finite exactly when both
coordinatewise closure and both rank-one clauses hold. The prime joint ideal
already gives irreducibility. The reverse generic fibre uses the canonically
reordered generated ring k[w,v] = k[v,w]. Base, ambient and index types lie in
four independent universes; no ACF, rationality or extra result certificate
is assumed. The algebraicity and rank clauses occur on the appropriate side
of the equivalence, rather than as additional caller hypotheses.

The dimension theorem supplies a finite natural number for joint dimension
and transcendence degree. The EXISTING private algebraic-extension rank step
now has this second actual consumer; nothing is promoted. The two generic-fibre
criteria and rank comparisons prove both directions. All preceding field
statements, declaration docstrings, attributes and proofs are unchanged; only
two imports and this source producer are added before the scope-header update.
The field module now has seven declarations: six public producers and the
existing private rank step, with no new generated declarations.

Both agents independently checked the exact mathematical bundle with default
limits and three empty strict-module logs. All 76 declarations use only standard
axioms; all 64 preceding tuple/field and eleven generic-fibre raw type hashes
are preserved, and all 76 raw hashes agree between agents. The selected audit
has 331 standard-dependency public types and retains all 330 preceding selected
types, including all 329 previous main types, exactly. Full library/book,
whole-library and exact-head CI evidence belongs to the checkpoint report on
#5. Dependency validation is not complete source coverage.

This discharges B1 for the canonical tuple-locus model. It does not erase the
required scalar-germ specialization or the threefold incidence-component
comparison. Those, the higher-dimensional family argument, packaged generic
extension and original group/chunk, curve-coset and scheme/action obligations
remain open. All source outside the existing annotation, all 48 statement
blocks and 44 proof blocks, goal objective/completion criteria and frozen M4a
are preserved. C2 and the full shared goal remain open.

The final generic-fibre module header and its new public declaration docstring
explicitly place finiteness of w on the entire theorem, including the
isomorphism. Only these two docstrings differ from the independently checked
source; the private helper docstring, imports, attributes, statements and proofs
are exact. The field module differs from its frozen proof source only in its
module-scope header.

## Scalar correspondence germs and actual incidence components (#5 C2 B4)

`Correspondence.ScalarCompositionGeometry` proves
`FiniteCorrespondenceGerm.composes_ofPair_carriers_eq` for the ORIGINAL scalar
API. For shared-middle scalar presentations in an algebraically closed ambient
field, the carrier ideals of all scalar composites are exactly the reindexed
endpoint contractions of the vanishing ideals of all actual middle-dominating
incidence components. Every component constructs a scalar germ, and both set
inclusions are proved. The scalar carrier stays in the original two-variable
polynomial ring. The base is arbitrary and the two field universes are
independent; no rank, freshness, base-ACF or result certificate is added.

The actual cube is indexed by (Fin 1 ⊕ Fin 1) ⊕ Fin 1, with the sum of the two
extended point-pair ideals and the literal middle projection. Only its endpoint
carrier is reindexed by ![inl 0,inr 0]. No Fin 3 spectrum homeomorphism or
unconsumed coordinate-normalization interface is introduced. The joint component
field is not identified with the possibly smaller endpoint-image field.

Two private pair converters have this theorem as their sole consumer. To pass
from a scalar pair to a tuple pair, a local algebraic-independence proof makes
the one-coordinate ideal zero; the existing dimension theorem and polynomial
Krull dimension give rank one. Conversely, algebraicity over the base would make
the one-coordinate generated field algebraic and of transcendence degree zero,
contradicting rank one. Closure clauses transfer along the singleton ranges.
Local P1 reindexing in both directions then transports the STRONG tuple
carrier-set equality to the scalar calculus, including scalar-germ existence
for every component. The earlier scalar function-field tensor realization
remains proved, and now has the actual incidence-spectrum interpretation.

The new module imports only Composition, LocusDimension and TupleComposition.
It has thirteen declarations: one public source producer, the two private pair
converters, eight generated private proof auxiliaries and two private notation
declarations. Both agents independently checked its exact mathematical source
with empty strict logs and default limits. All thirteen declarations use only
standard axioms and all thirteen raw type hashes agree. The selected audit has
332 standard-dependency public types and preserves all 331 preceding main types
exactly. Full library/book, whole-library and exact-head CI evidence belongs to
the checkpoint report on #5. Dependency validation is not complete source coverage.

Only the final module-scope header clarifies the ambient ACF hypothesis and
arbitrary base; imports, declaration docstrings, attributes, statements and proofs
are byte-exact to the independently checked source. All prior mathematical
modules are unchanged. All original source outside the existing annotation,
all 48 statement blocks and 44 proof blocks, goal objective/completion criteria
and frozen M4a are preserved. This discharges B4's actual scalar bridge. The
threefold incidence-component comparison, higher-dimensional family argument,
packaged generic extension and original group/chunk, curve-coset and scheme/action
obligations remain open. C2 and the full shared goal remain open.


## Threefold incidence components and normalized generic germs (#5 C2 B3)

`TupleCorrespondenceGerm.composes_threefold_components_eq` proves the source's
threefold comparison for finite tuple correspondence presentations with literally
shared middles. BOTH parenthesizations' final carrier ideals are exactly the
endpoint contractions of the vanishing ideals of all actual four-block incidence
components whose image under the LITERAL middle-pair projection is dense.
The incidence ideal is the sum of the three extended consecutive pair ideals.
The base is arbitrary, the ambient field algebraically closed, and the four
index types and fields have six independent universes. The source closure
clauses are derived from the genuine presentations; no rank, freshness,
component, realization or field-isomorphism certificate is added.

The third conjunct also handles EVERY irreducible component, including those
not dominating the middle. For its vanishing ideal contracted to the polynomial
ring p, let A be the literal polynomial quotient by p and N the integral closure
of A in FractionRing A. It proves N integrally closed, gives a
FractionRing N equivalence with FractionRing A, fixes every original A-element,
and identifies the literal normalized generic endpoint kernel with p contracted
to the endpoint variables. This is normalization formed componentwise, without
a claim about a normalization object for the whole non-domain ring. The joint
field is still not identified with its possibly smaller endpoint-image field.

The new focused `ThreefoldIncidence` module clears denominators to obtain
polynomial annihilators with a coefficient outside the middle locus. In a prime
quotient with the correct middle contraction these coefficients survive, so
IsAlgClosed.lift realizes the prime with both middles fixed. Algebraic
incomparability gives equality of the outer pair ideals and minimality of every
realized joint prime. This avoids dimension comparison and any promotion of
private transcendence-degree lemmas. Direct quotient algebras avoid a custom
fraction-field scalar tower. Its private normalization helper specializes
Mathlib's integral-closure and localization equivalences, and has the third
public conclusion as its sole consumer.

The consumed `composes_threefold_carriers_eq` is the one public addition to
TupleComposition. Ambient automorphisms align the intermediate presentation
and then the middle pair, leaving the same fixed-middle endpoint-ideal set.
The second parenthesization reuses the existing relational associativity proof.
All preceding declarations, attributes and proofs in that module are unchanged;
its existing header only gains the accurate new producer bullet.

ThreefoldIncidence has twenty-two declarations: its public source producer,
twelve consumed private theorems and nine private notation/macro declarations,
including the generated quotient-map app unexpander. TupleComposition gains one
declaration. Both agents independently checked the exact mathematical sources
with four empty strict-module logs and default limits. All 101 bundle
declarations use only standard axioms and every raw type hash and declaring
module agrees; all 78 preceding rows are exact. The selected audit has 334
standard-dependency public types and preserves all 332 preceding main types
exactly. Root's first checker run failed only because its generated inventory
had a long line; wrapping that fixture fixed the strict style diagnostic without
changing a mathematical source or checking limit. Full library/book,
whole-library and exact-head CI evidence belongs to the checkpoint report on #5.
Dependency validation is not complete source coverage.

The book removes stale open-status descriptions of the already-proved
finite-tuple dimension, actual generic-fibre and scalar component bridges,
composition, guarded chart and public reconstruction. The shared goal compresses
its checkpoint/API catalogue into scoped capabilities, retains every genuine
open target including the general curve-function-field presentation bridge,
and corrects stale GroupConfig chart/actual-rank-two status lines. Its objective,
endpoint and completion criteria are byte-exact. The original general affine-action,
algebraization, scheme/action, normal-subgroup and witness-descent obligations
remain visible. Eleven current Lean-status passages outside the existing
annotation are corrected with an exact old/new whitelist; reversing those
status-only corrections preserves every other original source byte. All 48
statement blocks and 44 proof blocks and frozen M4a are preserved; this guide
is append-only. B3 is discharged in the canonical finite-tuple generic-component
model, including componentwise normalization. The general curve-function-field
presentation bridge, higher-dimensional family argument, packaged generic
extension and remaining original group/chunk,
curve-coset and scheme/action obligations remain open. C2 and the full shared
goal remain open.


## Rank-additive joint components (#5, source (8.4c)/(8.6))

`locusIncidence_jointPrime_dominating_of_rank` proves the chosen-point
component step for finite tuples x, y, z satisfying
rk(x,y,z) + rk(y) = rk(x,y) + rk(y,z), with ranks the generated fields'
transcendence degrees over k. Its joint evaluation kernel is a minimal prime
of the literal incidence quotient. The corresponding component has dense
image under the literal middle projection, and contracting its ideal to
endpoint variables gives exactly I(x,z). Its actual coordinate ring, the
incidence quotient further divided by that kernel, has finite Krull dimension
equal to the joint transcendence degree. The base and ambient fields are
arbitrary, in five independent universes; no ACF, algebraicity, basis or
component certificate is supplied by the caller.

A maximal independent subfamily of x over k(y) spans k(x,y) algebraically.
Finite cardinal cancellation in the actual towers makes it independent
over k(y,z). Generic base change gives linear disjointness for the smaller
purely transcendental field; integral tensor base change then makes the joint
multiplication kernel minimal. The existing incidence classification transfers
this to the literal quotient. Two quotient-to-range isomorphisms and the public
locus dimension theorem compute the selected component's dimension.

LocusJointComponent gains six declarations: the public producer, two consumed
private proofs and three private notation declarations. The existing private
kernel-transfer helper now accepts proved minimality, with its two public
callers supplying either the old algebraic proof or the new rank proof. The
old algebraic core remains for its infinite-tuple public consumer. No other
preceding declaration type changes. Both agents independently checked all six
affected modules with empty strict logs and default checking limits. All 143
bundle declarations use only standard axioms; every raw type hash and declaring
module agrees. Of the 137 preceding rows, only the agreed private helper's
type changes. The selected audit has 335 standard-dependency public types,
retaining all 334 preceding main types exactly. Full library/book,
whole-library and exact-head CI evidence belongs to the checkpoint report on #5.
Dependency validation is not complete source coverage.

The book, goal and existing blueprint annotation record precisely this
chosen-point step. Finite tuples already allow non-rational curve fields;
the remaining geometric presentation bridge constructs simultaneous joint
generic points of arbitrary irreducible correspondence curves in sufficiently
large ambient fields. It stays owed under packaged variety-level generic
extension. The vague earlier curve-field presentation phrase came from the
scalar-only checkpoint dfd0d10; no abstract-field interface is added without
a source consumer. Identifying the parameter-field family members and carrying
other finite branches in (8.4c)/(8.6), packaged generic extension and the original
group/chunk, six-point, affine-action, curve-coset and scheme/action statements
remain obligations. C2 and the full goal remain open. All original mathematical
source statements/proofs, the unchanged eleven-pair status whitelist, goal
objective/completion criteria and frozen M4a are preserved; this guide is
append-only. The mathematical module is byte-exact to the independently checked
freeze outside two clarifications in its module header.


## Generic points of arbitrary affine loci (#5, source (8.1))

`exists_idealOf_eq_iff` starts from an arbitrary prime P in a polynomial
ring over k with a finite coordinate index type. It chooses the finite
Krull dimension n of the literal quotient internally and proves that some
tuple in an algebraically closed ambient field has vanishing ideal exactly
P if and only if the ambient transcendence degree over k is at least n.
The base is arbitrary; the two fields and index type have three independent
universes. The caller supplies neither a dimension certificate nor a generic
point. The necessary size bound is proved as well as the sufficient bound.

The private embedding helper takes a finite transcendence basis of the
quotient fraction field, embeds it in an ambient transcendence basis using
explicit cardinal lifts, identifies the generated rational function fields
by evaluation, and extends across the algebraic remainder. Injectivity of
the quotient-to-fraction-field map and the resulting field embedding gives
the exact prime ideal of the coordinate tuple. The reverse direction uses
the existing locus dimension theorem and the generated field's transcendence
basis in the ambient. The original private Noether-normalization helper is
reused without promotion. The module gains exactly the public producer and
its privately consumed embedding proof; no preceding public or private type
changes and no generated public match helper remains.

Both agents independently compiled all seven affected modules with empty
strict logs and default checking limits. LocusGenericFiber does not import
LocusDimension and is not an affected consumer. All 149 bundle declarations
use only standard axioms, every raw type hash and declaring module agrees,
and all 147 preceding rows are exact. The selected audit has 336 public
standard-dependency statements, preserving all 335 preceding main statements
exactly. Full library/book, clean-commit whole-library and exact-head CI
evidence belongs to the checkpoint report on #5. Dependency validation is
not complete source coverage.

This supplies the retained variety-to-joint-generic-point presentation bridge
for arbitrary irreducible affine correspondence curves, including non-rational
function fields. Splitting a joint tuple and applying idealOf_eq_comap_rename
gives both end loci along the literal coordinate inclusions. The book now
records this existence theorem and corrects its obsolete opening description
that excluded scheme machinery despite its proved affine-scheme bridges.
Eight of the eleven existing current Lean-status passages in the source
annotation whitelist are refreshed. Every original OLD side remains exact;
normalizing parent and candidate with their respective eleven NEW sides
preserves every original byte outside the existing joint-component annotation.
All 48 mathematical statement blocks and 44 proof blocks, goal objective and
completion criteria and frozen M4a are preserved; this guide is append-only.
The mathematical module is byte-exact to both independent freezes.

The full generic-extension lemma, including its universal rank criterion over
a coefficient extension, remains owed. A producer assuming the exact extended
ideal does not itself prove that universal clause from locus membership and
rank. Parameter-field family identities and other finite branches, original
group/chunk, six-point, affine-action, curve-coset and scheme/action statements
also remain obligations. C2 and the full shared goal remain open.


## Full finite-coordinate generic extension and source coverage (#5)

`genericExtension_genericPoint` proves the original generic-extension (a)
from locus membership and the source rank, rather than an assumed exact ideal.
For an algebraically closed k, any field E/k, a prime polynomial ideal P
in finitely many variables, and any coherent E-field ambient Ω, it chooses
internally the common finite dimension n of k[ι]/P and E[ι]/Pᵉ. Every
v with P ≤ I(v/k) and trdeg_E E(v) = n satisfies I(v/E) = Pᵉ,
I(v/k) = P and linear disjointness of the E-image and k(v) over k.
The universal clause has no closedness, size or infinite-rank hypothesis on Ω.
If Ω is algebraically closed, a tuple with the extended ideal exists exactly
when n ≤ trdeg_E Ω. All four universes are independent.

The proof constructs an auxiliary algebraically closed reference field of
infinite transcendence degree over E internally. The preceding prime-realization
producer, exact-ideal field-freeness theorem and dimension theorem give a
reference tuple and both dimensions. A maximal independent coordinate subfamily
and algebraic incomparability prove that every point with the required rank
has that same ideal. Three consumed private lemmas handle the reference rank,
coordinate basis and same-rank comparison. The auxiliary reference field is not
an assumption on the ambient in the public statement.

The former private threefold-incidence lemmas H and I are moved, with identical
statements, to the focused `LocusIncomparability` module as
`exists_poly_of_mem_racl` and `idealOf_eq_of_le_of_comap_eq`. Their actual
consumers are this proof and `ThreefoldIncidence`; the target ideal in the
second lemma need not be prime. The old private coercion lemma remains because
three actual threefold-incidence proof sites consume it. The other twenty
preceding declarations in that module retain their exact types and declaring
module. The new generic-extension module has exactly one public theorem and
three consumed private lemmas; no auxiliary public interfaces are added.

Both agents independently compiled all three mathematical modules with empty
strict logs and default checking limits. All twenty-six bundle declarations
use only standard axioms and agree in raw type hash and declaring module.
The two removed private rows map to the identical types of the new public
lemmas; all other twenty preceding rows are exact. The selected dependency
audit has 339 public statements, preserving all 336 preceding main statements
exactly. Full library/book, clean-commit whole-library and exact-head CI
validation are recorded in the checkpoint report on #5. Dependency checks
are distinct from source coverage.

The two agents audited the original section-eight opening and subsection 8.1
through generic-extension (a)--(c), rather than closing obligations merely
because later reconstruction bypasses them. The coverage is:

- Locus primality and irreducibility of the literal coordinate spectrum follow
  by instances; its canonical fraction field is isomorphic to k(a) via
  `IsFractionRing.algEquivOfAlgEquiv (locusCoordinateRingEquiv a)`, including
  polynomial representatives. The finite-tuple dimension identity is
  `exists_locusCoordinateRing_dimension`.
- The finite-correspondence equivalence (8.1), both actual projection-dominance
  facts and finite generic fibres are `pairLocus_finiteCorrespondence_iff`;
  `pairField_finiteDimensional_iff` supplies the function-field formulation.
- Composition uses the actual scheme fibre product and literal incidence
  quotient. All middle-dominating components and their endpoint contractions
  are identified with tuple and original scalar germ composites. Matching
  middle loci give nonempty composition. The component fraction field is
  the realized joint compositum and is finite over both ends and over its
  endpoint-image field. The latter field can be properly smaller, as the
  proved chain (t²,t,t²) shows; the source correction retains its provenance.
- Both parenthesizations have exactly the endpoint contractions of the actual
  four-block components dominating the middle pair. Componentwise integral
  closure in the component fraction field is normal, preserves that fraction
  field and preserves the endpoint generic ideal. This completes the scoped
  normalized generic-component comparison.
- Generic-extension (a) is the new theorem. For (b), its application with
  E = k derives I(a/k) = I(b/k) = P from the two membership and rank clauses.
  `exists_ambientAutomorphism_of_idealOf_eq` extends the exact canonical
  `locusFunctionFieldEquivOfIdealEq` on every generated-field element, as
  well as mapping coordinates. Finite tuples in the source algebraically
  closed ambient require no enlargement.
- For (c), `AlgebraicIndependent.aevalEquivField` is injective, and its
  algebra-map formula together with `map_div₀` gives literal fraction
  evaluation. Algebraic independence ensures nonzero denominators stay
  nonzero. The original displayed absolute-degree identity is true by the
  tower formula; its infinite-cardinal equality alone does not imply
  independence. The existing separate freeness proof supplies independence.

Seven additional actual Lean consumer declarations were compiled under the
same strict defaults and checked for standard dependencies: the three
(b)/(c)/fraction-evaluation consumers and four prime/irreducible/function-field/
polynomial-formula consumers. These are source-coverage checks, not seven
additional project API declarations. The exact sources and logs are frozen in
`/tmp/acl_geom_codex_generic_extension_review/frozen1` and
`/tmp/acl_geom_codex_generic_extension_review/opening_frozen1`; their manifest
SHA-256 values are respectively
`812e9733d16c0a74addc407ff9fa84d246f4017eff336b396d558a610251f259` and
`bbca91a19f487197533cfbaeca9f44c9270259d8d475e58e6477426b640ae10d`.
They are also rerun against the integrated modules in the checkpoint gates.
The source-level compositions can be reproduced from these public calls:

```lean
-- (b), after obtaining the source dimension n from the new theorem:
obtain ⟨n, hn, -, hgen, -⟩ :=
  genericExtension_genericPoint (k := k) (E := k) (Ω := Ω) P
have h : idealOf k a = idealOf k b :=
  (hgen a ha hra).2.1.trans (hgen b hb hrb).2.1.symm
exact exists_ambientAutomorphism_of_idealOf_eq h
-- (c), with ha : AlgebraicIndependent k a and equality of evaluated fractions h:
exact ha.aevalEquivField.injective (Subtype.ext h)
```

After full checkpoint validation and exact-head CI, the jointly audited scope
permits marking exactly three existing #5 rows complete: loci/prime ideals/
generic points; C2 finite one-variable correspondence calculus; and generic
extension (a)--(c). Preserve all sixteen row texts and ordering, and the other
thirteen states. The issue and shared goal remain open. The inverse-correspondence
sentence occurs in the later group-chunk argument, not in this subsection's
composition definition; its group/family consumer is still owed. The parameter-field
family identities in (8.4c)/(8.6), their other finite branches, original rational
group chunk, six-point configurations, affine-action, general curve-coset,
algebraization and scheme/action/descent obligations remain separate. No bypass
or auxiliary chart closes them.

The root export, book and shared goal now describe the full finite-coordinate
lemma. Nine of the eleven current Lean-status NEW sides in the existing source
whitelist are refreshed; every original OLD side is unchanged. Normalizing
parent and candidate with their respective eleven NEW sides preserves every
original byte outside the existing joint-component annotation. All 48 original
mathematical statement blocks and 44 proof blocks, the goal's objective and
completion criteria, and frozen M4a are byte-exact. This guide is append-only.
All three mathematical sources are byte-exact to both independent freezes.


## Selected six-point incidence branches (#5, source (8.4c))

`IsPartialQuadrangle.exists_composing_closed_incidence_germs` starts only
from the literal six-point partial quadrangle in an algebraically closed
ambient. Over the closed parameter join S join T it constructs the actual
incidence germs S′ to U′, U′ to T′ and S′ to T′ with the original point
representatives. Their canonical coefficient sets have relative closures
exactly T, S and U, and the third is the selected composite of the first two.
The base field is arbitrary; its universe and the ambient universe are
independent. All pair ranks, incidences and non-incidences are derived from
the six-point rank predicate, not supplied as extra hypotheses.

Distinct atoms give pair rank two. Equal rank of a pair and dependent triple
puts the third point in the pair join; a rank-three triple excludes it.
The existing private incidence constructor supplies the finite correspondences
over their own closed parameter fields and over the common join. The existing
private exact-base-change and monic-uniqueness proof preserves coefficient
sets. A new consumed rank-one coefficient argument observes that a nonzero
closed subfield of a point is the point. A zero coefficient closure would make
the two distinct endpoints algebraically dependent over the original base.

`IsPartialQuadrangle.exists_literal_composing_incidence_germs` proves the
literal-field selected branch, again from only the partial quadrangle, now
over arbitrary base and ambient fields. Put F = k(s,t,u), where s,t,u are
the original representatives of S,T,U. The theorem constructs T and S germs
over F with a literally shared middle and the original three family germs
over k(t), k(s), k(u). Each of the first two F-ideals, and the composite
ideal, is a minimal prime of the corresponding literal family ideal extended
to F. The parameter u is algebraic over k(s,t) but need not lie in that
generated field; it is explicitly included in F. The exact relative closures
of these finite parameter sets are derived internally, not assumed. Their common closure
is S join T. The existing private `incidencePair` constructor is reused.

The new `FiniteCorrespondencePair.ideal_mem_minimalPrimes_baseChange` has
three actual uses in the literal source producer. For two finite-correspondence
presentations with the same endpoints over nested intermediate fields E ≤ F,
the larger-field ideal contains the extended smaller-field ideal. Existing
canonical curve equations make both ideals principal. The mapped equation is
nonzero, so the extended ideal has height at least one; the selected principal
prime has height at most one. Mathlib's height criterion proves minimality.
Neither coefficient field nor the ambient needs to be algebraically closed.
The extensions may split, and the theorem does not replace minimality by
an unjustified equality of ideals.

The two focused proof modules add exactly three public theorems and five
consumed private lemmas. The seven incidence/non-incidence facts are shared
privately by the closed and literal producers. No old helper is promoted or
duplicated. The previous eleven ParameterField declarations, including every
private statement and proof, are unchanged. Outside the new import and appended
section, documentation changes consist of the module header and one exactly
whitelisted old docstring correcting its stale composition/chart/completeness
status. The new closed theorem's statement also
matches the preceding independently checked geometric-only freeze exactly.
The stale header claim that initial charts and reconstruction completeness
remain open is corrected: those results are already proved elsewhere.

Both agents checked the two mathematical sources with empty strict logs and
default checking limits. Root additionally recompiled the actual importer
AclGeom.lean with an empty strict log; the peer's initial importer search had
missed that root file. All nineteen affected declarations agree in raw type
hash and declaring module and use only standard axioms. All eleven preceding
rows are exact. The selected audit has 342 public standard-dependency statements,
retaining all 339 preceding main statements and the geometric-only producer
exactly. Root's full-root inventory scans took 104.68 and 107.18 seconds;
these were completed checks, not abandoned runs. Full library/book,
clean-commit whole-library and exact-head CI evidence belongs to the checkpoint
report on #5. Dependency checks are distinct from source coverage.

Peer proof freeze: `/tmp/acl_geom_claude_literal_sixpoint/frozen1`, manifest
`1805241940b0abad16f428ed6e0d72eaa9ab3c6820c681ac517e493e6d6c1ada`.
Root independent freeze: `/tmp/acl_geom_codex_literal_sixpoint_review/frozen1`,
manifest `8d921370712f3c26df5cb3eed6a8b79636ed62bafd79e1afa982bad9b4837502`.
The helper's earlier temporary checks had explicit-map/coercion elaboration
errors and then long-line warnings; fixing these did not change checking limits.
Peer's literal attempt one failed only on three subset `simp` calls whose sets
were not yet determined; making the sets explicit gave the final empty logs.
All failed attempts, inputs, logs and metrics remain archived. Crossed compiler
messages caused one safe lock refusal before a root build started; the original
runner intervals show no overlapping families. Both agents use the canonical
inner slot in the shared capped runner, with a 20 GB cap, swap disabled and
two threads.

The root export and the configuration chapter now expose both source producers
and the helper. The correspondence chapter and shared goal state precisely
the selected-branch scope. Two obsolete book claims that the already-proved
finite-tuple geometric fibre-product/function-field bridge remains open are
corrected. The original source statements and proofs are untouched. The
existing joint-component annotation alone records the new results; every
one of the eleven status-correction OLD and NEW sides is unchanged. Reversing
that exact whitelist and removing only the existing annotation still gives
the original source byte-for-byte. All 48 original mathematical statement
blocks, 44 proof blocks, goal objective/completion criteria and frozen M4a
are exact. This guide is append-only. SelectedBaseChange differs from both
freezes only by removing one final blank line; ParameterField is byte-exact after
reversing the single exact old-docstring status correction. Every mathematical
statement and proof is unchanged.

These are the selected geometric and literal incidence steps of (8.4c).
The other finite branches, a common normal cover, the higher-dimensional
parameter-family locus forms of (8.4c) and (8.6), the source group/chunk uses and the
full six-point algebraic-group theorem remain obligations. The original
affine-action, general curve-coset, algebraization, scheme/action and descent
statements also remain owed. All sixteen #5 checklist texts/order and states
are preserved at this checkpoint; the six-point group row is not closed.
The issue and shared goal remain open. A future conjugate-branch parametrization
must preserve genericity over the coefficient field; arbitrary automorphisms
of the base extension do not define a permutation action on its fixed ideal
set. This qualifies a proposed audit interface, not the original source wording.


## Literal Ψ incidence branch over its six-generator parameter field (2026-10-16, #5)

`QWitness.Psi.exists_literal_composing_incidence_germs` now constructs the
selected germ-level (8.6) branch from only the actual Ψ witness, over arbitrary
base and ambient fields with two independent universes. The common literal
coefficient field is F₆ = k(a₁,a₂,b₁,b₂,c₁,c₂). The c-generators are included:
C ≤ A join B holds after relative closure, not necessarily in the literal
four-generator field. The proof derives that the relative closure of all six
generators is A join B. Ψ's non-incidences give generic X, Y and Z over F₆.

The theorem obtains L_A, L_B and L_C from the existing public full-coefficient
producer, over their original two-generator fields. Their endpoints are Y→X,
Y→Z and X→Z, and their canonical coefficient closures remain A, B and C.
The existing private incidence constructor gives G_A and G_B over F₆; the
transposed G_A followed by G_B shares the literal middle and gives the endpoint
X→Z composite. Three uses of the existing minimal-prime base-change theorem
compare G_A, G_B and the composite to the extensions of L_A, L_B and L_C.
These extensions may split. Coefficient closures are retained for the ORIGINAL
families; no corresponding assertion for a split larger-field factor is made.

Exactly one public theorem and no helper declarations are added. Old mathematical
statements and proofs are unchanged. Peer whole-root inventory retained all
11,098 AclGeom-owned rows and adds exactly the one new theorem, with no generated
internal row. Its 7,044 preceding API rows are exact. That inventory checks axioms
ONLY for ParameterField and SelectedBaseChange: nineteen preceding declarations
become twenty, all with standard dependencies. The other rows' empty axiom lists
are not dependency evidence. This scope is not the whole two-library audit.

Both agents independently compiled the exact ParameterField source and unchanged
actual root AclGeom.lean with empty strict logs. Root's scoped inventory preserves
all nineteen preceding rows and agrees with the peer in declaring module and raw
type hash. Its 343 selected public statements have standard dependencies, with
all 342 preceding main statements byte-exact in the pretty-type audit. The new
type hash is 3958319325. All checks use the default checking limits.

Peer freeze `/tmp/acl_geom_claude_psi_literal/frozen1` has manifest
`daa437209c9b1eca596163e40b5d6362019224319a7b8558ad3bb00c64a5f08c`.
All four attempts and logs are retained: subset simp failures; a compiled version
with a rejected generated simp row; an indentation parse error; then the final
explicit-term subset proofs with no generated row. Root freeze
`/tmp/acl_geom_codex_psi_literal_review/frozen1` has manifest
`37408af9fde0f7411da907ba87bdd9e6c059b552fd0d0dab774f77d4313a76d0`.
Root's five compiler phases all exited zero; its initial postprocessor mistakenly
expected 343 parent types instead of 342. The correction verified the exact
completed logs, old 342/new 343 types, source pins and scoped inventories without
repeating compiler work. This is recorded with the original failed runner result.
The final build/book, clean-commit whole-library audit and exact-head CI evidence
belong to the checkpoint report on #5. Both agents now iterate future syntax fixes
with strict module-only checks before repeating expensive final inventories.
The canonical inner compiler slot, 20 GB family cap, no swap and two threads apply.

The configuration chapter documents the literal Ψ consumer. The correspondence
chapter and shared frontier record its scope. Source changes are confined to the existing joint-component
annotation and three exact, separately recorded exposition corrections found in
peer review: two stale open-status passages and the ambiguous phrase "parameter
form" for a closed-field germ result. Public reconstruction is already proved
under the genuine hypotheses, as checked directly in AclGeom/Main.lean. All 48
original statement blocks, 44 proof blocks and every OLD and NEW side of the
preceding eleven-pair status whitelist remain exact. Reversing that whitelist
and the three exact exposition corrections, then removing the existing joint
annotation, gives the original source bytes. The book clarifies the closed
route's coefficient-preservation purpose and uses "selected germ form". The
shared objective/completion criteria and frozen M4a log are unchanged; this guide
is append-only. Every #5 checklist text, order and state is retained.

The parameter-family k-locus forms of (8.4c) and (8.6), the other finite branches,
their common normal cover, original group/chunk uses and full six-point
algebraic-group theorem remain owed. The original affine-action, general
curve-coset, algebraization and scheme/action/descent obligations also remain.
The full shared goal and issue stay open.


The final book-status review also corrects three pre-existing paragraphs in
Configurations that still called the finite-tuple geometric component bridge
open, and HardKernel's stale "C2 remains open" sentence. The scalar-carrier,
incidence quotient, localization and component-field APIs already prove these
bridges over arbitrary bases in an ACF ambient. The revised paragraphs retain
the precise finite-tuple/ACF scope and all higher-dimensional family, common-cover
and original group/chunk obligations. These are exposition corrections, not new
mathematical declarations or checklist changes. The initial full six-phase gates
were green and are archived as round1; full build/book and audits are repeated
on the final documentation before the checkpoint commit.


## Every literal six-point family branch is a generic conjugate (2026-10-16, #5)

`FiniteCorrespondencePair.exists_conjugate_of_mem_minimalPrimes_baseChange`
works for nested intermediate fields E ≤ F in an ACF ambient Ω, an actual
E-correspondence P, one element transcendental over F, and any minimal prime J
of P's curve ideal extended to F. It constructs an actual F-correspondence Q
with Q.ideal = J and an E-automorphism σ of Ω carrying both original endpoints
to Q's endpoints. Q's source remains transcendental over F. The automorphism
need not preserve F; this is not an action on the fixed-F ideals, and no
converse for arbitrary automorphisms is asserted.

`IsPartialQuadrangle.literal_family_branches_are_conjugates` is its actual
source consumer, with only the partial quadrangle and an ACF ambient as inputs.
Over F = k(s,t,u), it treats EVERY minimal prime of each of
I_k(t)(s′,u′), I_k(s)(u′,t′) and I_k(u)(s′,t′) after extension. Each is an
actual F-correspondence at a conjugate of its original endpoints over its own
parameter field. The proof obtains G_T and the three original families from
the PUBLIC exists_literal_composing_incidence_germs. G_T.source supplies the
needed F-transcendental element for all three calls. The obtained endpoint
equations rewrite the family ideals to the literal source expressions. No
span/rank/incidence proof is duplicated and no helper is promoted.

The core realizes J by exists_idealOf_eq_iff. A mapped nonzero canonical curve
equation bounds the quotient dimension by one. Krull's principal ideal theorem
bounds J's height by one. If its realized tuple were algebraic over F, its
coordinate quotient would be a zero-dimensional domain and hence a field;
J would then be maximal of height two, a contradiction. A transcendental
coordinate and the PUBLIC idealOf_eq_of_le_of_comap_eq recover the original
E-ideal. The ambient generic-point automorphism theorem supplies σ, and
transported mutual algebraicity derives the larger-field source genericity.

Exactly two public theorems and two consumed private lemmas are added. The
private base-monotonicity lemma has four uses; it applies the existing project
lemma isAlgebraic_of_le (Closure/Basic) through Mathlib's actual
IntermediateField.restrictScalars_adjoin_eq_sup descriptions.
The private height lemma has one consumer. It identifies the two-variable
polynomial ring with F[X][Y], uses Jacobson maximal contraction, polynomial
height additivity and PID maximal height one. Both public results have two
independent field universes. All twenty preceding affected declarations,
including private statements and proofs, are unchanged; all twenty-four
current affected declarations have standard dependencies and agree between
agents in raw type hash and declaring module. The selected audit has 345
public standard-dependency statements, retaining all 343 preceding types
exactly. Dependency checks are distinct from source coverage.

Peer freeze `/tmp/acl_geom_claude_lambda2/frozen1` has manifest
`131db6daad8e0b9e1c98311cdb183f596f66807c94d3a2511e94600ceed71f7b`.
Module-only attempts fixed an addition-order API mismatch and an incorrect
namespace for trdeg_eq_zero, then corrected an overstated "both directions"
status. The first full inventory found omega's consumed internal proof
auxiliary. Its probe identified the exact arithmetic lemma, and the simpler
Nat.le_of_lt_succ proof removed it. A module-only check preceded the final
full scoped chain. All attempts and metrics are retained; no checking limit
was weakened. Final peer strict logs for both sources and the actual root
importer are empty, with exactly four added rows and no generated row.

Root independent freeze `/tmp/acl_geom_codex_lambda2_review/frozen1` has
manifest `49184e0f3e295f97b9bfaaef99abe8df433fb4f65837706cf3ff67eabfff7c45`.
Its exact two sources and actual root importer also have empty strict logs.
Its first checker stopped on an inventory-helper line-length warning; the
next completed all six compiler phases but reported two long audit marker
lines. A final audit-only check corrected those helper marker lines and
verified all 345 statements, without repeating completed proof/inventory work.
No mathematical source changed. Raw failures, final outputs, pins and metrics
are retained. Crossed compiler messages caused one safe inner-lock refusal
before Lean started; the canonical lock prevented concurrent families. The
slot was explicitly returned to the peer, then independently retaken after
its actual release. All builds use the 20 GB cap, no swap and two threads.

The configuration chapter records the individual-branch result, its ambient
capacity and genuine source consumer. The correspondence chapter and shared
frontier match that scope. Source changes are confined to the existing joint
component annotation. Every original statement and proof, all eleven previous
status-correction pairs and all three separately recorded exposition corrections
remain exact on both OLD and NEW sides. Reversing those exact corrections and
removing the annotation recovers every original source byte. The goal core and
frozen M4a are unchanged; this guide is append-only. All sixteen #5 checklist
texts, order and states are preserved. Full build/book, clean-commit whole-library
and exact-head CI evidence belongs to the checkpoint report on #5.

This represents the three six-point families' branches INDIVIDUALLY. It does
not align a coherent triple, construct a common normal cover or close words
under multiplication. The remaining Ψ branch instantiation, the parameter-family
k-locus forms of (8.4c)/(8.6), original group/chunk uses and full six-point
algebraic-group theorem remain owed. Original affine-action, curve-coset,
algebraization and scheme/action/descent obligations also remain. The root's
temporary family-locus target/rank draft is not a proved project theorem.
The issue and full shared goal remain open.


## Every literal Ψ family branch is a generic conjugate (2026-10-16, #5)

`QWitness.Psi.literal_family_branches_are_conjugates` supplies the actual
three-family branch instantiation of (8.6). Its only inputs are Ψ and an ACF
ambient, over an arbitrary base with independent base and ambient universes.
Over F₆ = k(a₁,a₂,b₁,b₂,c₁,c₂), EVERY minimal prime of each extended original
family ideal is the ideal of an actual F₆ finite correspondence. Its endpoints
are an automorphic image of the original Y→X, Y→Z or X→Z pair over the family's
own k(a₁,a₂), k(b₁,b₂) or k(c₁,c₂). Each source remains transcendental over F₆.

The public literal-germ producer supplies G_A, L_A, L_B, L_C and their original
endpoint equations. G_A.source_generic supplies the ambient capacity for all
three applications of the existing generic-conjugate theorem. Rewriting the
obtained family ideals gives the literal source expressions. Exactly one public
theorem is added, with no helper, new core, repeated rank/span/coefficient proof,
helper promotion or checking option. The explicit subset proofs in the statement
are copied from the already compiled literal Ψ theorem. The original families
retain coefficient closures A, B and C by that theorem. No such assertion is
made for split F₆ factors. The automorphisms need not preserve F₆, and there is
no action on the fixed-F₆ ideals or converse for arbitrary automorphisms.

Peer freeze /tmp/acl_geom_claude_psi_lambda2/frozen1 has manifest
383de4f41cd71dd430d876b7b67e6ec8e1889cb1faadf2521d8c12bcac54af05 (20 pins).
Its first module-only check was strict-empty and passed; the final scoped chain
passed on its first try, with empty strict PF and actual-root logs and no
generated row. SelectedBaseChange stayed unchanged and was not recompiled.
The scoped inventory has 25 standard-dependency rows and preserves all 24
preceding rows. The only addition is the new public theorem, type hash
2932239274, with two universes.

Root independent freeze /tmp/acl_geom_codex_psi_lambda2_review/frozen1 has
manifest 7baa37aa8a037eec27c7af39b4a86c7c09d0a2501a4adc6e347d69cd29a25847
(18 pins). All five compiler phases passed on the first try: old inventory,
exact PF, unchanged actual root, new inventory and selected audit. Both strict
logs are empty; all 25 rows agree with the peer in raw type hash and declaring
module, and all 24 old rows and all 345 preceding selected types are exact.
The selected audit now has 346 public standard-dependency statements.
The run took 29.25 seconds and peaked at 7.41 GiB, with verified 20 GB cap, no
swap, two threads, no memory events and no stop. Dependency checks remain
distinct from source coverage. Full build/book, clean-commit whole-library and
exact-head CI evidence belongs to the checkpoint report on #5.

The configuration chapter documents all three Ψ branches, and the correspondence
chapter and shared frontier record the same scope. The obsolete old PF coefficient
docstring now lists coherent choices of branches as open; this is the sole exact
docstring correction relative to both proof freezes. All old mathematical
statements and proofs are unchanged. Book status passages likewise distinguish
individual branch realization from coherent triples.

Source changes consist of the existing joint-component annotation and status
updates to the NEW sides of two of the three separately recorded exposition
corrections (indices 0 and 2). Their OLD sides remain exact, the third correction
is unchanged, and every OLD and NEW side of the eleven earlier status pairs is
unchanged. Reversing the exact corrections and removing the joint annotation
recovers every original source byte; all 48 original statement blocks and 44
proof blocks are exact. The goal core and frozen M4a are unchanged, and this
guide is append-only. All sixteen #5 checklist texts/order/states are preserved.

The individual branches of both the six-point and Ψ families are now covered.
Coherent triples, the common normal cover, both parameter-family k-locus forms,
original group/chunk uses, the full six-point algebraic-group theorem, affine-action,
general curve-coset, algebraization and scheme/action/descent remain owed.
The temporary private family-rank prototype is not a public family-locus result.
The peer's next-target audit requires both dense legs of the finite function-field
cover and an explicit partial-evaluation contraction bridge before claiming the
identity of generic components. That bridge and the actual component consumer
remain separate work. The issue and full shared goal remain open.

## Selected parameter-family locus identities (2026-10-16, #5)

The chosen generic-component locus forms of (8.4c) and (8.6) are proved by
six actual source consumers. Their only mathematical inputs are the genuine
partial quadrangle or Ψ, over arbitrary base and ambient fields with independent
universes. No algebraic closure, rank, span, component, dense-image or
function-field-finiteness conclusion is supplied by the caller.

AclGeom/Config/FamilyLoci.lean contains four public theorems:
IsPartialQuadrangle.parameter_family_components and its QWitness.Psi counterpart,
and IsPartialQuadrangle.family_common_function_field_cover and its Ψ counterpart.
For six points, the source incidence x=(t,s′), y=u′, z=(s,t′) has ranks
3+1=2+2. The parameter-family incidence p=(s,t), q=u, r=(s′,t′) has the
same rank equation. For Ψ, the source x=(α,X), y=Y, z=(β,Z) has ranks
5+1=3+3; the parameter incidence p=(α,β), q=γ, r=(X,Z) has ranks
5+2=4+3. Both source and parameter joint ideals are minimal over the literal
sums of renamed pair ideals, by the existing rank-additive component theorem.
The component dimensions are 3/3 and 5/5; the parameter and original family
dimensions are respectively 2/2 and 4/3. The free S,T,S′ triple spans the
whole partial quadrangle. Equal-rank Ψ joins supply C≤A∨B and the missing
Y closure. All tuple ranks and algebraicity clauses are derived internally.

The full six- or nine-tuple W has four actual coordinate-forgetting maps, to
the two joint components, the parameter locus M and the original U- or C-family
locus. The public cover theorems return the exact tuple identifications and
density under the literal maps of polynomial coordinate quotients. Injectivity
of these quotient maps gives kernel zero and dense comap on prime spectra.
The literal generated field k(W) is finite over each component field, with
the scalar action supplied by IntermediateField.extendScalars of the actual
inclusion. Restriction of scalars identifies this with a finite algebraic
field adjunction. The missing u or γ is algebraic over the source joint,
and u′ or Y is algebraic over the parameter joint. Finiteness is asserted
for the function fields; it is not a global finite affine morphism claim.

The two new literal_composite_locus_eq_comap source consumers in ParameterField
supply the exact contraction bridge. The contracted composite ideal is the
literal B2 joint ideal of parameter_family_components, with the same nested
sum indices. The map first uses rename (Sum.map finSumFinEquiv id) to join
the two parameter index blocks, then partialAeval evaluates the full actual
parameter tuple in k(s,t,u) or k(a₁,a₂,b₁,b₂,c₁,c₂). The selected composite
is still a minimal prime of the extended original family ideal; the original
U- or C-family also has its own-field contraction. Relations among parameters
are allowed: the raw parameter polynomial map is not treated as an injective
localization. The old public literal-germ producers supply all family data.

Exactly six public theorems and fourteen consumed private lemmas are added:
thirteen private lemmas in the focused FamilyLoci module and one generic
partial-evaluation contraction lemma in ParameterField. Shared rank, minimality,
dimension, density and field-adjunction proofs are kept once; three copied
prototype helpers were removed on consolidation. There is no helper promotion,
project axiom, new generated auxiliary row or checking-limit change. All old main
ParameterField mathematical statements and proofs are unchanged. Removing the new imports
and three new declaration blocks, and reversing the one exact module-status correction,
recovers every preceding ParameterField byte. SelectedBaseChange also has one exact
docstring-status correction and no mathematical change. The actual root differs only
by the new import.

The peer's Ψ source/rank/component/cover prototypes are frozen in
/tmp/acl_geom_claude_psi_family_ranks/frozen3, manifest
a3fe58cc25ffa13edca7b0cda5bf0dd399b7c129f84a5bdc103579028ca886e3 (23 pins).
Its final inventory has eleven standard-dependency rows, preserving all eight
preceding type hashes and adding only the two copied helpers and actual cover.
The first two cover checks required explicit sets and a range-subset witness
for adjoin.mono/finite_field_cover; attempt 06 was strict-empty and green.
Those known fixes were applied to the six-point analogue before its first check.
The earlier R3 support had independent checks, but its final public types were
aligned with B2 before integration; they are not the earlier linear-index types.
The peer reviewed that composition order and exact index alignment.

Root froze the consolidated proof source in
/tmp/acl_geom_family_integration/frozen1, manifest
f7f17f9c5891cc8057c241d606fce91b7f31d7b8c90f742280676a6dfaa15a06 (32 pins).
Bundle 01 exposed two unqualified polynomial renames and consequent elaboration
timeouts; qualifying MvPolynomial.rename fixed them without weakening checking.
Its broad old-root inventory was slow, so bundle 02 used focused inventory
imports with the same declaring-module filter; the actual root remained a
separate compilation step. Bundle 02 passed all six phases: old inventory,
ParameterField, FamilyLoci, actual root, new inventory and selected audit.
All three strict module logs are empty. All forty-five affected rows have
standard dependencies and retain all twenty-five preceding rows exactly.
The selected audit has 352 public statements and retains all 346 preceding
pretty-printed types. Every new public theorem has two universes.
The run took 36.46 seconds and peaked at 7.42 GiB under the verified 20 GB
cap, no swap, two threads, no memory events or stop. Source documentation
corrections are recorded exactly and preserve every compiled proof byte.
The peer independently compiled the same three frozen final sources with empty
strict logs. Its review freeze /tmp/acl_geom_claude_family_bundle_review/frozen1
has manifest c11a7f94e729603cf18f29cd9c8c8697e322969b1a960eb1bf8b2d5ede549296
(22 pins). The final run took 229.99 seconds, peaking at 7.40 GiB under the
same cap with no events or stop. All 11,104 preceding AclGeom-module rows
(7,048 public API rows) retain their raw type hashes and declaring modules; all 45
affected rows agree with the root, and the only 20 additions are the six
public results and fourteen private lemmas. This AclGeom-module filter is
not the whole two-root library: the root found 77 of the 346 selected parent
names outside that filter, including GroupConfig declarations. A supplemental
selected audit addresses that scope separately: addendum
/tmp/acl_geom_claude_family_bundle_review/frozen2_audit, manifest
27054e36f1d85fdc8cafa7249f3efc7e8da7263f533febbee89f0d6efcf77db8,
checks all 352 pretty-printed types against the root and all 346 preceding
types exactly, with 352 standard-axiom blocks. It reused the already compiled
exact-source overlay; no mathematical compilation or broad inventory was
repeated. This 6.77-second run peaked at 7.43 GiB with no events or stop.
The root rehashed every addendum pin and verified both exact type comparisons.
The peer's first attempt
had an inventory-only parse error from using the keyword scoped as a variable;
renaming it fixed the audit without changing source.
The peer reviewed the actual source argument and the exact B2 contraction.
Its two stale-status findings in PF and SelectedBaseChange are corrected in
this candidate. The FamilyLoci scope header now distinguishes the original
coherent-branch/normal-cover obligations from stronger results not asserted;
all such source changes are exact recorded docstring corrections. No finite
morphism of entire affine loci or all-components classification is added as
a new completion requirement.

The independent final-source peer validation, exact candidate rebuild,
clean-commit whole-library audit and exact-head CI evidence are recorded on #5.
Dependency audits remain distinct from source coverage.

The book and shared frontier now record these selected locus identities.
All 48 original mathematical statement blocks, 44 proof blocks and all original
source bytes are preserved under the exact recorded annotation reversals.
Every OLD side of all eleven earlier status pairs is unchanged; only NEW
indices 0,1,2,5,8,9,10 update this frontier. All three exposition-correction OLD
sides are unchanged; only NEW indices 0 and 2 update the selected-family status.
The source joint-component annotation documents the new consumers. The goal
objective/completion criteria and frozen 117-item M4a log are unchanged;
this guide is append-only. All sixteen #5 checklist texts, order and states
stay unchanged, including the open full six-point group row.

No classification of all parameter-family components is asserted. Coherent
branch triples, their common normal cover and the original group/chunk,
six-point algebraic-group theorem, affine-action, general curve-coset,
algebraization and scheme/action/descent obligations remain. The full shared
goal and issue #5 stay open.

## Literal predicate transport, decoder obstruction and perfect-field existence (#8)

`Interpretation.CompleteNaturality` proves
`nonempty_ringEquiv_of_closedIF_orderIso_of_perfectField`: perfect ambient fields,
source transcendence degree at least five and a closed-subfield lattice order
isomorphism imply `Nonempty (K ≃+* L)`. The four field universes are independent.
Both algebraic-closure completeness proofs, the target rank bound and characteristic
exponents are supplied internally. No RAC-base hypothesis is needed for bare existence;
this statement does not assert that the isomorphism induces the given lattice map.

`blueprintRatioEq_no_decoder` in `Counterexamples.GenericArithmetic` derives a named
obstruction from the existing literal ratio counterexample: on some fixed Frobenius
class no function on pairs both respects the literal relation and sends each semantic
pair to its ratio. This prevents the advertised decoder even on the equivalence-closure
quotient. It does not refute the intended field reconstruction, which is proved through
the corrected coupled carrier. The error was reported on #8 before source annotations;
all original statements, proofs and prose remain recoverable byte for byte.

`Counterexamples.BlueprintTransport` separately proves transport of `SumPoint` and all
five literal arithmetic/ratio/negation/total-nonzero-addition predicates, together with
the class-pair `Quot` correspondence extended over zero for any raw base tuple and its
actual image. These seven public declarations need only arbitrary fields and a lattice
order isomorphism. The carrier uses equivalence closure and has no asserted field
structure or decoder. The source assertion that the literal relation itself is an
equivalence, and the transcription/transport of the two prose-defined total operation
graphs, remain open. I6b and I6c remain unchecked. Bypassed true assertions are obligations.

Both agents reviewed and independently checked the exact mathematical sources, retaining
failed audit attempts and the import-order metadata diagnosis. The checkpoint's full
library/book, strict-module, selected-type and whole-library dependency gates and exact
committed-head CI are recorded on #8. This checkpoint does not finish source validation
or the durable project goal.

## Literal ratio laws and representative graph formulas (#8)

The original three ratio-law assertions have separate dispositions. `BlueprintRatioEq.symm`
proves symmetry for arbitrary raw tuples over arbitrary fields. `blueprintRatioEq_refl`
proves reflexivity for all pairs in the class of a semantic base tuple over perfect ambient
fields at rank five, with arbitrary bases. It normalizes both endpoints through internally
supplied ACF completeness and characteristic, then uses one fresh multiplier and two honest
products. `blueprintRatioEq_not_transitive` refutes transitivity over arbitrary base and
ambient fields at rank five; no perfection or completeness is needed. Six private lemmas
are consumed by this one refutation. The source error was reported on #8 (6229602246)
before annotation changes. A setoid for the literal relation cannot be constructed.

The generic addition/multiplication scalar producers and the supplied-scalar conditional
counterexamples no longer carry stale infinite-base assumptions. Nine existing public
types are strengthened by removing exactly one unused Infinite binder; proof bodies stay
exact. The five negation/total-addition declarations use local `omit [Infinite k] in`,
while the scalar-existence declarations keep their original Infinite binder and order.
The audit verifies each changed type against its original type with that unused binder
removed, and all other scoped API records remain exact. Every mathematical import consumer
of the changed generic-arithmetic signatures is rebuilt, including GenericNegation and BPT.

`BlueprintTotalGraphs` transcribes the literal addition and multiplication recipes on
Option of raw pairs of class members. All replacement and comparison witnesses use the
literal ratio relation. Every input, output and auxiliary representative is a class member;
addition has the common denominator and negation/nonzero branches, and multiplication has
exactly its existing generic-product guards. Named-zero equalities complete the nonzero
recipes as specified by the source proof. `frobEqClassMap` and the two `_map_iff` theorems
prove geometric invariance over arbitrary fields in four independent universes. The one
internal proof constant of the class map is consumed, not a new public normalization API.
No quotient operation descent, functionality, totality or field structure is asserted here.
The source totality and decoded-operation statements retain their separate obligations.

The corrected coupled ratio setoid, decoding, total field graphs and reconstruction remain
proved. The literal equivalence-closure carrier correspondence remains a true geometric
statement with no field/decoder payload. The unproved global connectivity sketch for that
closure is not used or asserted. Original statement/proof blocks and complete source
provenance are recoverable byte for byte; the goal objective/completion criteria and frozen
M4a record remain exact. Source/TOTAL and original provenance obligations are not closed
merely by these invariance proofs. Full library/book, strict, selected-type, exhaustive
committed-head dependency and exact CI evidence are reported on #8. The durable goal remains
incomplete.

## Wrong values for both literal operation recipes (#8)

`Counterexamples.RatioGraphValues` has exactly two public theorems and no auxiliary
or private declarations. `blueprintRatioAddGraph_wrong_sum` gives semantic input pairs
`(j(x,a),j(y,a))`, `(j(y,a),j(y,a))` and output `(j(κx+y,a),j(y,a))` satisfying the
literal raw addition graph, with output ratio different from `x/y+y/y`.
`blueprintRatioMulGraph_wrong_product` gives reciprocal inputs and output
`(j(κxy,a),j(xy,a))` satisfying the literal raw multiplication graph, whose ratio is
`κ` rather than one. The statements identify every input/output pair with its actual
semantic tuples, and every numerator and denominator tuple belongs to the actual
Frobenius class of `j(x,a)`. They assume no decoder.

The hypotheses are an infinite base, a perfect ambient field and transcendence degree
at least five. A base scalar outside `{0,1}` is chosen internally; arithmetic scalar
producers provide the outputs and proved literal ratio reflexivity supplies every
replacement and output comparison. Addition uses the denominator already present in the
independent triple, with no rank-six or simultaneous freshness premise. Both agents
independently checked the exact mathematical source, preserving all 373 preceding
selected types and all 82 preceding scoped records; the expanded checks cover 375
selected declarations and 84 scoped records using standard axioms.

The forward-law error was reported on #8 (6230285952) before source annotations. All 48
original statement blocks and 44 proof blocks remain exact, and reversing the documented
annotations recovers the complete preceding source. Totality remains separately owed.
Reverse directions require careful source-domain statements: the raw addition completion
at a zero input forces equality of representatives, so equality of generator ratios
alone cannot justify replacing that output. No quotient functionality, descent or field
structure is asserted. The corrected coupled interpretation and reconstruction remain
proved. I6b/I6c and the durable project goal remain open. Full library/book, exact-head CI,
selected and exhaustive committed-head dependency evidence is reported on #8.

## True converse of literal ratio semantics (#8)

`blueprintRatioEq_of_mul_eq` in `Counterexamples.RatioConverse`
proves the true reverse implication of the source `lem:ratio-semantics`. Its base is
an actual semantic tuple `j(x₀,a)` with an independent pair, each of the four endpoints
is `j(p,a)` with its independent pair, and the hypothesis is the cross-product identity
`p₁*q₂=p₂*q₁`. The conclusion is the literal `BlueprintRatioEq` for these semantic
pairs. The base and ambient fields are arbitrary and only rank five is needed; no
perfection, infinite base, completeness, characteristic or caller freshness input occurs.

The source proof chooses `t` fresh over the at-most-four-element set `{a,p₁,p₂,q₁}`.
This closure contains `q₂=p₂*q₁/p₁`; nonzero coefficients preserve the freshness.
Four κ=1 generic products give multipliers `q₂*t`, `p₂*t` and the two common outputs.
The common-parameter bridges supply every auxiliary tuple's actual class membership.
There is one public theorem in two independent universes and no helper/private/generated
auxiliary declarations. Both agents independently checked the exact source; all 375
preceding selected types and 84 scoped records are exact, with the expanded checks
covering 376 selected standard-axiom declarations and 85 scoped records.

This is a genuine true source implication, separately recorded from the refuted forward
implication, transitivity and decoder. The literal relation still cannot provide the
advertised setoid. Raw operation totality, carefully scoped reverse operation laws and
remaining original construction/provenance obligations remain separate. All 48 original
source statement blocks and 44 proof blocks are unchanged; reversing the new annotation
recovers the entire preceding source. The shared objective/completion criteria and frozen
M4a record remain exact. Full library/book, exact-head CI and exhaustive committed-head
dependency evidence is reported on #8. I6b/I6c and the durable goal remain open.

## Literal multiplication totality and representative reverse law (#8)

`Counterexamples.RatioMulGraphLaws` has exactly two public theorems and no helpers,
private or generated auxiliary declarations. `blueprintRatioMulGraph_of_mul_ratio`
proves the NONZERO-input representative-level reverse product law, a correction of the
invalid quotient statement. Its base is an actual semantic tuple `j(x₀,a)`; all six
endpoint pair-independence proofs and the underlying tuple equalities for arbitrary raw
class pairs `r,s,t` are explicit. The cross identity
`p''*(q*q')=q''*(p*p')` implies the actual literal multiplication graph. Only arbitrary
fields and rank five are required, without perfection or completeness.

`blueprintRatioMulGraph_total` proves totality for arbitrary Option of raw class-pair
inputs, over a perfect ambient field at rank five and an arbitrary base. It supplies
characteristic and ACF completeness internally, normalizes the four input class members
inline and chooses an output denominator fresh over `{a,c*d}`, then consumes the reverse
law. Zero factors have output `none`. The reverse law chooses its replacement multipliers
fresh over `{a,c,d}` and `{a,c,d,r'}`. Two κ=1 generic products and three applications of
the true ratio-semantics converse retain every product/comparison/class witness. Fresh
choices are local; no caller normalizer, freshness oracle or joint rank-six premise occurs.

Both agents independently checked the exact source, retaining all 376 preceding selected
types and all 85 preceding scoped records byte for byte. The expanded checks cover 378
selected standard-axiom declarations and 87 scoped records, including both new public
theorems in two independent universes. The final source differs from the reviewed first
draft only in two header scope corrections and one line wrap: the equivalence-closure
quotient exists, and these two results assert no functionality theorem.

The forward literal product law remains refuted by `blueprintRatioMulGraph_wrong_product`.
No quotient functionality, operation descent, decoder or field structure is asserted.
Addition totality, its carefully scoped reverse laws and remaining original provenance
obligations remain open. The separate zero-input addition reverse refutation is checked
and reported on #8 (6230508633), awaiting integration with its corrected statement.
All 48 original source statement blocks and 44 proof blocks remain exact; reversing the
new annotations recovers the complete preceding source. The shared objective/completion
criteria and frozen M4a record are unchanged; only the goal review date and frontier are
updated. Full library/book, exhaustive committed-head dependency and exact-head CI evidence
are reported on #8. I6b/I6c and the durable project goal remain open.

## True existence half of literal total nonzero addition (#8)

`blueprintJAddTotalNZ_of_pairs` in `Counterexamples.TotalNonzeroExistence` proves the true source existence claim. Its actual semantic base has an
independent pair, and its three individual hypotheses are independent pairs `(x,a)`,
`(y,a)` and `(x+y,a)`. There is no joint independence assumption on `x,y,a`.
The literal conclusion has output `j(x+y,a)`. Arbitrary base and ambient fields and rank
five suffice; no perfection, infinite base, completeness or caller freshness is supplied.

The source detour chooses `z` outside the closure of `{x,y,a}`. Two input pair hypotheses
give the first two generic additions. The third triple `(x+z,y-z,a)` is independent
because otherwise exchange, using the given pair `(x+y,a)`, would put `z` back in that
closure. Three κ=1 additions and the literal negation at scalar minus one give all
clauses, including all four auxiliary Frobenius-class memberships. The argument works
in every characteristic within rank five. The module imports only GenericNegation and
has exactly one public theorem with no helper/private/generated auxiliary declarations.

Both agents independently checked the exact source, preserving all 378 preceding
selected types and 87 scoped records. The expanded check covers 379 selected
standard-axiom declarations and 88 scoped records, with the new theorem in two
independent universes. The mathematical source is identical to the reviewed first draft.
All 48 original source statement blocks and 44 proof blocks remain exact, and reversing
the annotation recovers the complete preceding source. The shared objective/completion
criteria and frozen M4a record are unchanged.

The unique-output/forward implication of the literal lemma remains refuted; the corrected
coupled detour has proved exact semantics. Raw addition totality, its carefully scoped
representative reverse laws and remaining original provenance obligations stay separate.
The checked zero-input reverse obstruction (#8, 6230508633) will accompany the corrected
nonzero-input statement. Full library/book, exhaustive committed-head dependency and
exact-head CI evidence is reported on #8. I6b/I6c and the durable goal remain open.

## Literal addition totality, reverse laws and zero-input obstruction (#8)

`Counterexamples.RatioAddGraphLaws` proves three public source components. For an actual
semantic base, `blueprintRatioAddGraph_of_add_ratio_eq_zero` gives the named-zero output
from the zero cross sum of two NONZERO semantic inputs. All four endpoint independent
pairs and underlying tuple identities are explicit. `blueprintRatioAddGraph_of_add_ratio`
gives any semantic nonzero output satisfying the cross identity for the sum of the two
input ratios, with all six pair hypotheses and three tuple identities explicit. The sum
is nonzero as a consequence of the cross identity and semantic output, not a caller input.
Both are representative-level corrections of the invalid quotient claim, over arbitrary
fields at rank five without perfection or completeness.

`blueprintRatioAddGraph_total` proves totality for all Option of raw class-pair inputs,
over a perfect ambient field at rank five and an arbitrary base. Normalization, ACF
completeness and characteristic are supplied internally. The literal named-zero clauses
return the other raw input exactly. For nonzero inputs, a common denominator fresh over
`{a,c,d}` gives both literal replacements. A zero sum uses negation at scalar minus one;
a nonzero sum uses the proved literal total-nonzero-addition existence result and the
true ratio converse for output comparison. There is no joint independence of the two
numerators. Totality chooses a fresh semantic target denominator over `{a,c+d}` and
consumes these branches. Every choice is local within rank five. The one private
common-denominator producer is consumed by both reverse branches; no extra internal
or generated declaration is introduced.

`blueprintRatioAddGraph_zero_reverse_counterexample` in `Counterexamples.RawZeroAddition` records the domain obstruction alongside the corrected
statements. Over arbitrary fields at rank five, two different diagonal semantic pairs
in the actual class have ratio one, but the second is not an output of zero plus the
first. The literal zero completion requires equality of raw representatives. No decoder,
perfection, infinite base or completeness is assumed. The source-domain error was reported
on #8 (6230508633) before these annotations. This does not refute totality or the proved
corrected coupled quotient operation laws.

Both agents independently checked the ADD source and the zero refutation, and the root
combined check preserves all 379 preceding selected types and 88 scoped records exactly.
The expanded audit covers 383 selected standard-axiom declarations and 93 scoped records:
four new public theorems in two independent universes and one consumed private lemma,
with no other internal/generated declarations. The ADD mathematical source equals its
reviewed first draft. The zero source has only header status/tense corrections; its
statement and entire proof are unchanged. The original two constructor-elimination type
errors and their two-line `cases` repair are retained in the proof evidence.

All 48 original source statement blocks and 44 proofs remain exact, and reversing the
new annotations recovers the complete preceding source. The shared objective/completion
criteria and frozen M4a record are unchanged. Both advertised forward operation laws
remain refuted; no literal quotient functionality, operation descent, decoder or field
structure is asserted. The remaining original construction/provenance dispositions are
separate, including the chosen-class field-map record. Full library/book, exhaustive
committed-head dependency and exact-head CI evidence is reported on #8. I6b/I6c and the
durable goal remain open; the original group/chunk and scheme/action obligations remain.


## Checkpoint: the source-setting chosen-class field map (#8)

`Interpretation.ClassFieldMap.exists_interpretedRingEquiv_ratio` proves the corrected
source-setting counterpart of the chosen-class field reconstruction proposition, retaining
the actual image base and the ratio decoding diagram. It works over arbitrary bases and
perfect ambient fields at source rank five, in four independent universes. The target
rank, characteristic exponents, both ACF completeness proofs and semantic image base are
internal. Each mapped endpoint retains its individual independent-pair hypothesis; there
is no RAC, infinite-base, target-rank, caller completeness or image-base premise.

The field map is the actual corrected `interpretedRingEquiv`. Its two public coordinate
equations cancel the same nonzero image-base factor to prove the ratio diagram. Source
class members and their images have common-parameter semantic representatives, by the
proved class descriptions and Frobenius transport; the diagram is nonvacuous. There is
one new public theorem and no helper/private/internal/generated auxiliary declaration.
This records more than bare field-isomorphism existence, but is not a new global
reconstruction endpoint. Whole-lattice compatibility and base recovery remain the
stronger RAC-base reconstruction conclusions; the literal decoder stays refuted.

Both agents independently checked the exact theorem and proof. The combined golden
retains every one of the 383 preceding selected types and 93 scoped records, adding only
the four-universe theorem (384 selected standard-axiom declarations and 94 scoped records).
The two priority stale Scalar/Base headers now distinguish their explicit internal inputs
from the proved completeness producers and Main's unconditional chosen-perfection
reconstruction. Their declarations and entire proof bodies are unchanged. The broader
Frobenius-link/chart-route header audit is retained for a separate cleanup; original
direct-link normalization, group/chunk and scheme/action obligations remain separate.

All 48 original source statement blocks and 44 proofs are exact. Reversing the recorded
progress annotations recovers the entire preceding source; the shared objective/completion
criteria and frozen M4a record are unchanged. Full library/book, clean-head exhaustive
dependency and exact-head CI evidence is reported on #8. I6b/I6c stay open pending the
clause-by-clause disposition of the original literal construction/provenance. The durable
goal and remaining true bypassed source obligations are incomplete.


## Checkpoint: the direct-link common representative (source (10.1), #23)

`Interpretation.FrobLinkRepresentative.DirectFrobLink.exists_common_representative`
proves the original common-representative claim for supplied semantic direct-link
endpoints, over arbitrary bases and perfect ambient fields, with no rank bound. For
every chosen multiplier point satisfying its first two clauses, one representative
generates that point and gives all three equalities of (10.1). The direct-link hypothesis
itself retains its existential multiplier with all three clauses. The theorem does not
remove that hypothesis. Applying it to the link's own multiplier recovers the source claim.

The proof first uses the existing incidence-rigidity Frobenius twist, chooses a power or
root representative (perfection in the inverse direction), then identifies its point
with the chosen multiplier by uniqueness on two distinct rank-two lines. The original
inference from separately chosen product representatives remains unjustified provenance;
the statement is proved by this different route. No extra rigidity wrapper is added.
Existing source-setting Frobenius characterization/setoid and completeness results stay
separate. Six stale Frobenius-family headers now reflect these proved inputs and the
common-representative result; every old declaration and entire proof body is unchanged.

Both agents independently checked the exact final leaf, one public theorem in two
independent universes, standard axioms, and no helper/private/internal/generated
auxiliary. The final source differs from the original draft only by an explicit `x ≠ 0`
have before cancellation, repairing an unreduced vector index in a rewrite. All failed
and successful peer attempts are retained. The independent root check preserves all
384 preceding selected types and 94 scoped records exactly; the expanded audit has
385 selected standard-axiom declarations and 95 scoped records, with the new full type
and record identical to the peer's. The original 48 statement blocks and 44 proofs are
exact, and reversing the recorded annotations recovers the entire preceding source.
The shared objective/completion criteria and frozen 117-item M4a record are unchanged.
Full library/book, clean committed-head exhaustive dependency and exact-head CI evidence
is reported on #23. Original literal M6 construction/provenance, group/chunk/coherent-cover
and scheme/action obligations remain separate; the durable goal stays active and incomplete.


## Checkpoint: literal addition functionality and the M6 source dispositions (#8/#23)

`Counterexamples.RatioAddQuotient.blueprintRatioAddGraph_not_functional_after_map`
refutes literal addition functionality after any identification of nonzero representative
pairs with the named zero adjoined. It works over arbitrary fields at source rank five,
with the actual semantic base pair and `2 ≠ 0` in the base. No perfection, infinite-base,
completeness or decoder input is used. The diagonal input `(j(x,a),j(x,a))` twice has
output zero by literal self-negation and nonzero output `(j(2x,a),j(x,a))` by the true
reverse sum law. Under every `Option.map f`, these outputs remain `none` and `some (f t)`.
This includes the equivalence-closure quotient and a constant identification. No assertion
is made in characteristic two or about unrelated field structures on a quotient carrier.
The error was reported on #8 (6231576509) before the source annotations.

Both agents independently checked the exact final mathematical leaf and root. There is
one new public theorem in three independent universes, standard axioms and no helper,
private, internal or generated auxiliary. The root check preserves all 385 preceding
selected types and 95 scoped records exactly, expanding to 386 selected standard-axiom
declarations and 96 scoped records. The peer's complete new type and declaration record
are identical. The first draft needed no mathematical repair; only the agreed deterministic
arithmetic tactic replaced `norm_num; ring` before the first successful check. Integration
changes only the draft Status header, with its reversal recorded. The two old mathematical
files touched in this checkpoint change only module docstrings; every old statement and
entire proof body is unchanged.

The source/book record every I6b/I6c clause: literal geometric invariance and true raw
totality/reverse components proved; the literal decoder and forward decoded laws refuted
under their documented infinite-base hypotheses; addition functionality refuted when
`2 ≠ 0`; and the corrected coupled total functional field graphs, field structure,
geometric naturality and chosen-class field isomorphism/ratio diagram proved. The
point-geometry/lattice conversion and actual-image class/carrier maps are explicit.
Multiplication functionality belongs to the refuted decoded-field theorem; no generic
any-identification multiplication claim or extra raw identity predicate is introduced.
All source characteristics remain in scope for the corrected replacement and endpoint.
Finite characteristic-two bases are allowed source instances; these refutation families
make no literal claim there. R1/R2 source-disposition work and true bypassed group/chunk,
coherent-cover and scheme/action statements remain separate obligations.

All 48 original source statement blocks and 44 proof blocks are exact. Reversing the
recorded progress annotations recovers the entire preceding source. The shared objective,
completion criteria and frozen 117-item M4a record are unchanged. Full library/book,
clean committed-head exhaustive dependency and exact-head CI evidence is reported on
#8/#23 before resolving their M6 tracker rows. The durable project goal remains active
and incomplete; these are dispositions of the original literal construction, not proofs
of its refuted predicates.


## Checkpoint: full tuple images and the R1--R4 source dispositions (#9)

`Reconstruct.TupleImage.interpretedRingEquiv_jTupleOf` exposes the first conclusion of
blueprint Prop `scalar-one`: for every `x` outside `racl_k {a}`, the actual reconstructed
`H = interpretedRingEquiv … e …` carries the canonical source tuple to `j(H(x),a')`,
and the target pair is independent. It retains every chosen semantic base and every
admissible image pair. Both perfections, rank bounds, completeness proofs, exponential
characteristics and actual image-base equality are explicit in this reusable internal API,
exactly as in Scalar. No RAC, extra target genericity, fresh/scalar oracle or new global
reconstruction endpoint is introduced. The module imports only Scalar and adds one public
theorem in four independent universes, with standard axioms and no auxiliary declarations.

The proof retains information discarded by the existing point-formula proof: Frobenius
transport and the class description produce a semantic image `j(y,a')`; the coordinate
and base-coordinate laws give `y = H(x)`, so the whole tuple is returned. The source,
book and Scalar header now name this theorem in place of uncommitted typed fixtures.
The mathematical leaf is byte-identical to the independently checked source from both
agents. All 386 preceding selected types and 96 scoped records remain exact, expanding
to 387 selected standard-axiom declarations and 97 scoped records.

The joint source audit records every remaining #9 clause for this actual H:

- R1: `interpretedRingEquiv_compatible` gives base recovery for every chosen class and
  image pair, under both genuine RAC bases.
- R2: the new tuple formula and existing `interpretedRingEquiv_point` give both source
  conclusions, without RAC. The coordinate and scalar-one laws are already proved.
- R3b: apply `congrArg` at a principal closure to `closedIFMap_interpretedRingEquiv`,
  then `CrossBase.closedIFMap_point`. The result holds for every x, including inside
  `racl_k {a}`. Both RAC bases are needed for compatibility, as in the source.
- R4: the same named actual-H equality, with `CrossBase.coe_closedIFMap`, is the image
  formula for every closed field. On the chosen perfections, use their conjugated
  lattice isomorphism, `Perfection.isRAC_basePerf`, and the proved rank/completeness
  producers. Convert the equality through `Perfection.induces_iff_eq_inducedIso`, then
  `Perfection.Induces.mem_iff`, to get the original-field intersection formula for that
  same chosen-class H. Bare existential reconstruction is not used to identify H.

In the source setting `jCompletenessACF`, lattice rank transfer, characteristic exponents
and `exists_map_jTupleOf_eq` supply every internal input. Original fields need not be
perfect; only their chosen perfections are used. No duplicate chosen-class or all-point
wrapper is added, since the existing stronger public equality exposes every needed clause.
The original RatioEq/JMul proofs and larger-freshness scalar route remain provenance;
the Lean route uses geometric transport, exchange and bijectivity. Seven old mathematical
files change module headers only; every old statement and entire proof body is unchanged.

All 48 original source statements and 44 proofs, the shared objective/completion criteria
and frozen 117-item M4a record remain exact. Full library/book, strict modules, selected
types/inventory, clean committed-head exhaustive dependency and exact-head CI evidence
are reported on #9 before its remaining four rows are resolved. The original group/chunk,
coherent-branch/common-normal-cover and scheme/action statements remain obligations.
The durable project goal stays active and incomplete.


## Checkpoint: numbered validation-suite source reconciliation (#10)

The joint source audit maps every TEST-1 through TEST-11 clause to existing named Lean
evidence or a direct instance, at its precise hypotheses. This checkpoint changes only
the book, source progress annotations, shared frontier and this guide. Every mathematical
source file and public declaration is byte-identical to the preceding green 3437a9f head.
No new declaration, weaker checking, predicate or reconstruction endpoint is introduced.

Three book paragraphs understated true source clauses. TEST-2 now cites the direct
`point_frobeniusZPow` identity on every point of a perfect field, without RAC; the original
lattice identity still uses RAC. TEST-3's intended literal coordinates are proved by
`blueprintJAdd_kappa` and `blueprintJMul_kappa` at κ=1 over arbitrary fields at rank five
for independent x,y,a. Their uniqueness is refuted when a nonzero κ≠1 is supplied.
TEST-5's true literal reverse is `blueprintRatioEq_of_mul_eq`, using exactly c₁=s₂t and
c₂=r₂t with one fresh t, over arbitrary fields at rank five on semantic representatives
with a common parameter. Its forward semantics is refuted over infinite bases at rank five.
The corrected coupled iff laws retain their exact carrier/completeness APIs.

TEST-6 now names its true literal zero-sum reverse and the 2≠0 self-negation witness
refuting the converse; the latter outputs stay distinct under every identification
retaining the named zero. This witness makes no characteristic-two assertion, while
the corrected zero-addition iff covers every source characteristic. The other tests retain
their exact established scopes: both Frobenius directions, lattice dimension transport,
rational-function-field reconstruction with arbitrary bases/perfections, the rank-five
reconstruction and characteristic-zero uniqueness boundaries, modified-composite
congruence/quotient unit laws, and literal Hom surjectivity/exact fibres/quotient injectivity.

The source records the complete eleven-item ledger without changing any original TEST
clause. Its transcription-table preamble no longer calls proved completeness, corrected
field operations or public reconstruction open. Every original 48 statement block and
44 proof block, the shared objective/completion criteria and frozen 117-item M4a record
remain exact. Full library/book, mathematical source identity, clean-head exhaustive
dependency and exact-head CI evidence are reported on #10 before its two final rows
are resolved. Dependency auditing is not source-coverage certification.

The full original/supplementary disposition audit remains open. In particular, #7/#25's
corrected arbitrary-field Q/Q′ and general witness-descent scope, the original group/chunk,
coherent-branch/common-normal-cover and scheme/action statements remain obligations.
The durable project goal stays active and incomplete.


## Checkpoint: the multiplication-diagram product point over arbitrary fields (#25)

`MulDiagram.product_point` in `Transfer.MulDiagramProduct` proves the product clause of
source `mul-diagram` over arbitrary base and ambient fields. For an actual nondegenerate
diagram and supplied actual representatives X=[x], Y=[y], V=[x/y], it returns E=[xy].
No closedness, perfection, rank, RAC, infinite-base or freshness hypothesis is needed.
The two field universes are independent. The module imports only MultiplicationConverse
and LiftConfig, with one public theorem, standard axioms and no auxiliary declarations.

The diagram lifts to the algebraic closure of K over the algebraic closure of k there.
Lifted principal points retain x,y and x/y. The existing rank-free full coordinate theorem
gives E=[xy] in that ACF pair; injectivity of the closed-field lift reflects the equality.
Only the product point is reflected. The auxiliary corner need not lie in K, so no full
table or general existential configuration-witness descent is claimed over arbitrary K.
The existing full table remains proved for ACF base and ambient fields without rank.

Both agents independently checked the exact mathematical leaf and root on 4e43a83.
The draft needed no repair. The public type hash is 3813660894 in two universes.
Integration changes only the leaf's header provenance wording: the source section first
discusses ACF pairs, so this is described as a strengthening of its product clause,
without asserting that the original section lacked an implicit ACF setting. The entire
statement and proof body are exact. The one old mathematical file changes only its
module header; all old statements and entire proof bodies remain exact.

The selected scope expands to 388 standard-axiom declarations and 98 scoped records,
preserving all 387 preceding types and 97 declaration records exactly. Both agents' full
new type and declaration record agree. The original source lemma and proof remain exact;
the source/book distinguish the stronger product point from the full ACF coordinate table,
the still-open Q/Q′ correction and witness-descent scope, and original curve-coset/group
proof provenance. A stale source paragraph no longer calls the proved four-way J theorem
or ACF completeness open; the literal M6 defects retain their recorded dispositions.

All 48 original source statements and 44 proofs, the shared objective/completion criteria
and frozen 117-item M4a record are unchanged. Full library/book, three strict modules,
selected types/inventory, clean-head exhaustive dependency and exact-head CI evidence
are reported on #25 before this checkpoint is final. #7/#25 and the durable project goal
remain open. Corrected arbitrary-field Q/Q′, general existential-witness descent and true
group/chunk, coherent-cover and scheme/action obligations are not discharged here.


## Checkpoint: corrected projected configurations and the M5 source audit (#25, #7)

`Transfer.ProjectedConfigurations` proves `qSem_iff_exists_jGeom` and
`q'Sem_iff_exists_jGeom_mulDiagram`. Over arbitrary base fields and perfect ambient fields
of transcendence degree at least five, semantic Q is exactly `∃ P, JGeom X P Y S V`;
semantic Q′ is exactly `∃ V P A B C D, JGeom X P Y S V ∧ MulDiagram X Y V E A B C D`.
Every existential is a point over K. Both public types retain perfection and rank five;
there is no RAC, ACF, infinite-base, caller completeness or freshness premise.

The first proof composes semantic J projection with the proved perfect-field J theorem.
The second chooses a parameter fresh over only the two semantic representatives, uses
the explicit multiplication table, and reads the reverse product via
`MulDiagram.product_point`. The old raw predicates are unchanged. The formulas are finite
and nonrecursive: geometric J was defined with the original raw predicates and proved
correct before these projections. No arbitrary-witness descent or arbitrary-field full
auxiliary coordinate table is claimed.

Peer and independent checks agree on the exact leaf (SHA-256
`6ecf791ad8ba2c54cd657bc853ad7de7d5891e23294ad7b412a343153e3047ae`), all full public
types and scoped records. Both new declarations have two independent universe levels
and standard axioms; their type hashes are 1565943284 and 1306459126. The peer's first
proof passed mathematics/type checking but an inventory guard caught one generated
auxiliary from an omega cardinality proof. Replacing only that finite-set bound with
`Finset.card_le_two.trans (by decide)` removed the auxiliary; both statements and full
types stayed exact. The final leaf required no repair in the independent check.
The selected scope is 390 standard-axiom declarations and 100 records, preserving every
preceding 388 type and 98 record exactly, with exactly two new public declarations and
no helper, private, internal or generated addition.

The source-scope audit compared the original J-descent statement and proof with T1--T4.
Its only arbitrary-field Q/Q′ assertion was the false consequence already refuted with
provenance. No separate general raw existential-witness descent theorem is stated.
J descent lifts supplied witnesses in one direction and descends the semantic pair before
constructing K-witnesses in the other; it never needs descent of arbitrary lifted raw
witnesses. That question stays explicitly unknown and exploratory, not proved or refuted.
The source's §10 alignment clauses have their separate common-representative/global
Frobenius/M6 dispositions. This scope correction does not narrow the project endpoint.

Only headers change in four old mathematical modules: LiftConfig, OneQuantifier,
Correctness and Multiplication. All their statements and proof bodies stay exact.
Original source statements/proofs and TEST clauses, the shared objective/completion
criteria and frozen 117-item M4a record remain exact. The source/book/goal distinguish
raw refutations, proved projected replacements and the unresolved exploratory question.
Full build/book, strict checks, selected and exhaustive dependency audits and exact-head
CI are reported on #25 before this checkpoint is final. #7/#25 may close after these
gates and the recorded dispositions; the full durable goal remains active. Original
and supplementary group/chunk, coherent-cover, curve/scheme/action, algebraization and
descent obligations remain open.


## Checkpoint: the source j-rigidity exponent and characteristic-zero correction (#32, #5)

The source's literal unique-integer clause in `thm:jrigidity` is false in characteristic
zero. Its explicit convention is exponential characteristic one and all integer Frobenius
iterates. Even a self-pair of an independent j-tuple has distinct valid exponents zero
and one. The source's nonzero-polynomial inference uses a polynomial that is zero at p=1.
This was reported on #32 before source edits, and independently confirmed by the peer.
Two downstream original proof steps repeat the same slip: J descent's orbit argument
and the coordinate bijection's fixed-parameter polynomial argument. Their statements are
true. Adjacent annotations provide the direct characteristic-zero pair-equality branch;
the original theorem statements and all proof blocks are retained verbatim.

`Transfer.JRigidityStatement` proves the corrected source-facing
`existsUnique_normalized_frobeniusZPow_of_jTupleOf_eq`: actual equal j-tuples of two
independent pairs over a perfect ambient K have a unique common exponent n with
(q=1 → n=0). The base k is arbitrary. There is no ACF, RAC, ambient rank, supplied
freshness or completeness premise. All five actual point equalities lift to
`FreshAmbient K`; its four added variables supply the existing core's two fresh elements.
The equalities of natural powers reflect by injectivity, perfection gives an integral
iterate, and the existing exponent separator is used only at q≥2. At q=1 the pair is
equal and normalization selects zero. Both field universes are independent.

`jTupleOf_eq_charZero_and_exponent_not_unique` proves the source's characteristic-zero
pair equality for every actual equal tuple pair and refutes the literal integer
uniqueness, using zero and one. Both new declarations have standard axioms; their type
hashes are 2189296325 and 3571323396. There are no helper, private, internal or generated
additions. The selected scope is 392 declarations/102 records, preserving every preceding
390 type and 100 record exactly.

The original 110-line mathematical draft passed its first strict leaf/root check.
A verification inventory initially forgot the new import and saw exactly the 100 old
rows; the import-only driver fix passed without any proof change. After peer reading,
the separate self/reflexive-conjunct counterexample was strengthened to the universal
actual equal-tuple statement, also passing its first strict check. The normalized theorem's
statement and full proof body stayed exact. The checked 116-line mathematical leaf changes at integration
only in its proved-status and docstring wording. Two existing auxiliary mixed-relation lemmas lose four unused premises, and their five
caller sites are adjusted. Seven deprecated aliases and three Prop-valued haveI bindings
are updated to Mathlib's preferred forms. The two full old modules retain all 108
declaration names, universes, axioms and private/internal flags; 106 raw type hashes stay
exact and only the two deliberately strengthened helper types change. Four strict logs
are empty. All thirteen inherited rigidity warnings are removed, with every other parent
warning header required exact. The earlier clear-based cleanup and the intermediate
newly-unused-premise warning remain recorded; no checking option was weakened.

The source/book/goal distinguish normalized integer uniqueness, positive-characteristic
raw exponent uniqueness and characteristic-zero pair equality. The book's stale R1/R2
scope is also corrected to the actual-H results already proved on closed #9. The main
reconstruction endpoint and all 48 original statement blocks, 44 proofs, eleven TEST
clauses and frozen 117-item M4a record remain exact. The original-statement inventory
includes archived variants; it is not full source-coverage certification.
Full library/book, four strict modules, selected and whole-library dependency checks,
independent peer review and exact-head CI are reported on #32 before this checkpoint is
final. The full durable goal and original/supplementary group/chunk, coherent-cover,
general curve-coset, curve/scheme/action, algebraization and descent obligations stay open.


## Checkpoint: additive finite-correspondence curve cosets (#5)

`Correspondence.CurveCosetAdditive` proves
`curveCoset_additive_of_finiteCorrespondence`, the additive finite-correspondence instance
of source `lem:curve-coset`. Its inputs are actual pairs `(x₁,y₁)`, `(x₂,y₂)` with equal
coordinate points, independent `x₁,x₂` and equal points of their sums, over ACF k and Ω.
It needs no ambient-rank, caller freshness or completeness premise. The two field
universes are independent. This proves the source additive-correspondence proof
step followed by `addSubgroup_classification_of_connected`; Lean `addcorr` uses a
different route.

The theorem constructs an actual `AddSubgroup (Fin 2 → k)`, a prime generator F and
base-field vectors g₁,g₂. It gives the canonical ideal I(H)=span{F}, exact closedness,
connected prime spectrum of the canonical coordinate quotient, Krull dimension one,
and both nonconstant projection witnesses. The three original generic curve ideals
are exactly span{translate(-g₁) F}, span{translate(-g₂) F} and
span{translate(-(g₁+g₂)) F}. Their base-field point loci are the three corresponding
cosets. FreshAmbient supplies the additive core's two fresh elements internally;
injectivity reflects the constant-value equations. Algebraically closed base-field
roots choose the translations. Prime association, Nullstellensatz and Krull dimension
then provide the actual subgroup data; no private declaration is promoted.

The peer wrote the mathematical leaf a1d5939b. Its initial elaboration failure and the
two intermediate inventory guard failures are retained in the peer evidence. The latter
had three ordinary simp-generated equality lemmas, all with standard axioms, consumed
only by the theorem. An explicit diagnostic checked their complete proof terms and
consumers. The final proof replaces those simp arguments by direct rewrites/membership
proofs; its full theorem type remains byte-identical to both intermediate versions.
It has exactly one public declaration, two universes, type hash 3687643288 and no helper,
private, internal or generated additions. No checking option was weakened.

The final peer family passed under the canonical 20 GB cap. Root independently compiled
that exact leaf and its shadow root import; all five Lean phases passed on their first
try. A final Python path-parenthesization typo was corrected offline without repeating
any passed phase. The final inventory and complete type agree exactly with the peer;
all 392 preceding selected types and 102 preceding scoped declaration records stay exact.
Integration copies that mathematical leaf verbatim. The source note is outside the
original lemma/proof, and all original statement/proof blocks, TEST clauses, shared goal
objective/completion core and frozen 117-item M4a history are preserved.

Full library/book, strict leaf/root, selected and exhaustive dependency checks, peer
review and exact-head CI are recorded on #5 before this checkpoint is final. The general
connected-algebraic-group lemma, including the noncommutative g₁H/Hg₂ conclusion, its
torus instance and constant-coordinate curves remain open. The curve-coset checklist
row stays unchecked. Original group/chunk, coherent-cover, six-point, affine-action,
scheme/action, algebraization and descent obligations and the full durable goal remain
open. This restricted additive theorem does not complete the project.


## Checkpoint: general algebraic-group curve cosets (#5)

`Correspondence.CurveCoset.curveCoset_of_genericProduct` proves the main clause of
`lem:curve-coset` in the scheme language of closed irreducible curves over an ACF base.
Its genuine input consists of the three closed/irreducible/dimension-one curves and one
jointly generic point of their actual reduced scheme product whose product lies in D.
The source's genericity in D is stronger. The ambient algebraic group need not be connected.
`CurveCosetCommutative.curveCoset_of_genericProduct_commutative` spells out the final source
sentence, with all three left cosets and the third translation g₁*g₂.

The theorem constructs H : ConnectedAlgebraicGroup, its actual group morphism into G,
closed immersion, dimension one and all three noncommutative coset identities. There is
no supplied subgroup, product integrality, restricted operation, ambient rank, freshness
or completeness oracle. Abstract torus and constant-coordinate cases are permitted once the
ambient group is presented as an AlgebraicGroup; no concrete additive-plane or torus object
is constructed here. The earlier
additive finite-correspondence theorem retains its stronger explicit polynomial ideals,
projection witnesses and original field-tuple interface.

`ClosedCurveDimension` proves equality of nested closed curves by the finite topological
dimension chain argument. `GroupSchemePoints` gives actual translations and the closed-point
equivalence. `CurveCosetGroup` proves the translation/sandwich argument at closed points.
`IntegralProduct` proves integrality of products of arbitrary integral schemes over ACF,
using the already proved field-tensor theorem and scheme-theoretic dominance under flat
base change. `ReducedSubscheme` proves reduced induced schemes and their factorization.
`CurveCosetGeneric` and `CurveCosetSource` supply the genuine generic-product input internally.
`GroupSubobject` checks the group laws through a monomorphism. `ClosedSubgroup` restricts
the actual unit, multiplication and inverse to the reduced scheme; Jacobson density,
reducedness and product integrality supply every restriction. Finite type, separatedness,
quasi-compactness and geometric integrality are derived.

Both agents reviewed the mathematical route and checked the exact proof sources.
Integration changes only module-status/bridge prose in these mathematical files. The
original source statement/proof blocks, TEST clauses, shared objective/completion core
and frozen M4a history remain exact. The source annotations distinguish this theorem from
the separate missing producer of an ambient algebraic group in earlier source arguments.

The issue report records strict module checks, complete types and declaration records,
the generated definition proof fields and their actual consumers, full library/book,
whole-library standard-dependency audit and exact-head CI. These are dependency and finite
source-inventory checks, not a certificate of complete source coverage. Group/chunk,
six-point, affine-action, coherent-cover, algebraization and scheme/action/descent remain
open. The full durable goal remains active and incomplete.


## Checkpoint: concrete group schemes and the affine action on the line (#21)

Nine focused modules now construct the actual target model in source (8.4a).
`SymmetricHopf` adds the antipode to Mathlib's existing primitive-generator bialgebra.
`HopfSpecPoints` identifies unit-over-Spec points with convolution characters, including
the actual Spec-of-evaluation formula. `AdditiveGroupScheme` constructs Gaⁿ and its
additive coordinate group; `MultiplicativeGroupScheme` constructs Gm with unit coordinates.
`AlgebraicGroupProduct` constructs products, including Gm² with its pair-of-units point
group. These are concrete commutative ambient algebraic groups for the general curve-coset
theorem; the tuple-locus-to-scheme-curves and jointly generic product bridge remains owed.

`AffineCoordinateRing` proves the universal property of k[a,a⁻¹,b]. `AffineGroupScheme`
checks the semidirect comultiplication, counit and antipode, constructs the actual finite-type
group scheme and identifies its base-field points with `AffineTransformation k`.
`AffineGroupGeometry` proves dimension(Gaⁿ)=n, dimension(Gm)=1 and dimension(Aff)=2.
It uses Laurent localization of k[X] to obtain a nonfield PID and a polynomial-ring
presentation of the affine coordinate ring. Over an ACF base, geometric integrality
supplies the actual connected algebraic-group package internally.

`AffineSchemeAction` constructs the action by the coaction X↦a⊗X+b⊗1. Mathlib's ModObj
records the actual scheme morphism's unit and associativity laws. Those are proved by
cancelling affine Spec isomorphisms and checking on all commutative coefficient-algebra
points. The action formula is literally ax+b, and fixing 0 and 1 proves faithfulness
for every such algebra C in the base universe. Pure coordinate-ring formulas allow an
independent coefficient universe; C requires no bialgebra or Hopf structure.

Both agents checked the exact mathematical sources and independently compiled each
other's modules. The primary agent owns integration and all tracked files. Two unused
generated unfolding equations were avoided by direct definitional proof steps; the remaining internal
rows, including structure-proof fields and one simp auxiliary lemma, all have consumers. The checkpoint report records
the full types, standard-dependency inventory, parent declaration preservation, strict
module checks, full library/book gates and exact-head CI.

This is the concrete model of (8.4a), not the classification of an arbitrary curve action.
All eight original #21 requirements remain open, including the source action/function-field
and normal-subgroup bridges, group/chunk and six-point producers, algebraization and
descent. The original source statement/proof blocks, TEST clauses, shared objective and
completion core, and frozen M4a history remain exact. The full durable goal is active
and incomplete.


## Checkpoint: actual scheme curves and function-field actions (#21)

`Correspondence.ActionFunctionField` constructs the function-field action of an actual
regular scheme action. Mathlib's Hom.mulAction gives global points acting by scheme
automorphisms over Spec k. Dominant morphisms induce contravariant function-field maps,
with identity and composition proved from the existing FunctionFieldEquivalence API.
The base algebra is the structure morphism's pullback from the function field of Spec k;
explicit local instances avoid a global algebra diamond. The actual homomorphism lands
in the opposite group of k-algebra automorphisms. For a scheme separated over k, its
injectivity follows from the genuine point-action kernel criterion and the dominant
generic-stalk inclusion. This is not a scheme-faithfulness equivalence in characteristic p.

`CurveFunctionFieldAlgebra` proves that an essentially finite-type field of transcendence
degree one is a one-variable function field, without perfectness. It also chooses a
nonempty affine open of dimension one in any dimension-one scheme. A point of the bottom
member of a strict irreducible-closed chain chooses the open; Mathlib's open-embedding
order isomorphism preserves the chain. Subspace dimension supplies the other inequality.
No general cover-dimension API is added.

`SchemeFunctionFieldBase` identifies the pullback algebra with the canonical map through
global sections and their generic germ. Its proof postcomposes the generic-point morphism
with toSpecΓ and uses Spec.map injectivity and naturality. `SchemeCurveFunctionField`
then proves the one-variable class for the ACTUAL generic-stalk field of an integral,
locally finite-type curve scheme of dimension one. Its base algebra is exactly the one
used by ActionFunctionField. The proof constructs the affine section algebra and scalar
tower internally, uses Mathlib's fraction-ring theorem, and derives both dimension and
transcendence degree from the same natural number. A single public access theorem in
LocusDimension exposes its existing private Noether-normalization proof; no implementation
is copied and all previous declarations remain unchanged.

Both agents read the complete proofs and independently checked each other's modules.
The original source statement/proof blocks and TEST clauses, shared objective/completion
core and frozen M4a history remain exact. The checkpoint report records strict checks,
complete selected types, declaration/axiom inventories, parent preservation, actual book
content, full library/book gates and exact-head CI. A finite dependency inventory is not
a whole-source coverage certificate.

The bridge takes a regular action; source Lemma affine-action takes a rational action.
Rational-action regularization, the original completion/points bridge, the normal-subgroup and original
group/chunk/six-point producers, arbitrary-action classification, algebraization and
descent remain owed. All eight original #21 work items stay open. The complete durable
goal remains active and incomplete.


## Checkpoint: places of actual curves and their affine boundary (#21)

`Curves.PlaceAction` transports a place along a k-field automorphism by preimage of its
valuation ring. The opposite automorphism group acts on places. The boundary of a
finitely generated subalgebra of a one-variable function field over an ACF base is finite:
every boundary place is a pole of a nonzero generator. An automorphism preserving the
subalgebra preserves this boundary. The generic field and the base have independent universes.

`Correspondence.SchemePlaceAction` uses exactly ActionFunctionField.functionFieldAlgebra V.
It derives the DVR instance for every place of an actual integral locally finite-type
curve of scheme dimension one over an ACF base, using the actual curve field theorem.
For an actual regular scheme action, the contravariant field map and the valuation-ring
preimage reverse composition twice, giving a genuine left action of G(k) on places as an
explicit homomorphism to permutations. No global scheme-recovery instance is introduced.

The global-section model is the range of the actual generic-germ map, as a k-subalgebra
via the existing base-algebra comparison. Germ naturality and the inverse scheme
automorphism prove that every automorphism over Spec k preserves this range. Thus a
regular action preserves its boundary for any integral scheme. For an affine curve,
local finite type supplies finite generation of the model; dimension one supplies the
one-variable function-field hypothesis. The resulting finite-boundary theorem has no
caller-supplied preservation, finite-generation or field-finiteness oracle.

`Correspondence.SchemePlaceBoundary` proves that an actual affine integral locally
finite-type curve of dimension one has a NONEMPTY boundary, over arbitrary fields. It
chooses a transcendental element of the actual stalk field and writes it as a fraction
of global sections. If both generic germs were algebraic, their fraction would be
algebraic. A transcendental section therefore has a pole place outside the model.

The two agents independently read the proofs and strictly checked each other's modules.
The checkpoint report records complete expanded types, axioms/internal consumers, parent
preservation, actual book content and full library/book gates with exact-head CI. Source
statements, proofs and TEST clauses, the goal objective/completion core and frozen M4a
history retain their provenance. A finite inventory is not a source-coverage certificate.

This is the valuation-place bridge for REGULAR actions. It does not identify places with
points, construct a projective completion, extend scheme automorphisms to it, prove their
uniqueness, or regularize a rational action. The next checkpoint proves the fixed-boundary
step for connected regular actions on affine curves using the algebraic action and
irreducibility; an abstract finite-index argument would fail in positive characteristic. There is no field/place-faithfulness equivalence. The original
group/chunk, six-point and normal-subgroup producers, arbitrary-action classification,
algebraization and descent remain owed. All eight original #21 rows stay open, and the
full durable goal remains active and incomplete.


## Checkpoint: a connected regular action fixes the affine boundary (#21)

`Correspondence.SchemePlaceFixed` proves `SchemePlaceAction.placeAction_eq_of_mem_boundary`.
The theorem takes an actual connected algebraic group, its regular ModObj action on an integral affine locally finite-type curve,
scheme dimension one and a boundary place, over an ACF base. It proves that every k-point
fixes that place. `exists_fixed_boundary_place` also chooses a genuine fixed boundary place
internally from the existing nonempty-boundary theorem. There is no caller closedness,
finite-generation, one-variable, finite-boundary, faithfulness or fixed-point oracle.
The literal Lean namespace is `AclGeom.SchemePlaceAction`.

`GroupPointTopology` transports the closed-point subspace topology to actual k-points as
an explicit/local definition. The integral carrier and Jacobson density give an irreducible
point space. Existing scheme translations supply the left homeomorphisms. No global Hom-set
topology or joint continuity for the product of the point-space topologies is claimed.

`Curves.PlaceTransport` proves normalized-order transport. Nonnegative sets agree; the
uniformizer comparison factor is positive and divides one, hence is one. The theorem
includes zero using its junk order. The zero-including order threshold is a k-subspace.
`PlaceProfiles` chooses finite nonzero section samples distinguishing any finite family of
places of a genuine fraction field, with three independent universes. Different valuation
rings give different order signs for some nonzero fraction; a numerator or denominator
then distinguishes their orders.

`SchemeActionSections` gives the action on actual global sections as a finite tensor sum,
uniform in every acting point of an affine group open. Its algebras are the explicit base
maps through Gamma/Spec, not a silent identification with the range model. Generic-germ
naturality turns the section formula into the actual function-field pullback formula.
`ActionSemicontinuity` derives closedness of every order threshold for a nonzero section.
At a point outside the threshold, algebraic dual separation of the zero-including order
subspace supplies a linear form. The finite coefficient formula gives a genuine section
whose basic open is a complement neighborhood. No finite-dimensionality of the function
field or the order subspace is required.

A private scheme gluing lemma uses those internally supplied closed conditions and finite
profiles to express each orbit fiber as a closed intersection minus a finite closed union.
`FiniteActionIrreducible` proves the finite-action argument: a finite locally closed cover
of an irreducible space has an open member; translate its fiber to an open stabilizer and
intersect two nonempty open translates. This uses the algebraic action in every
characteristic, with no abstract finite-index argument. The public scheme theorem derives
every premise of this private gluing step from the actual connected group/action/curve.

Both agents read all proofs and independently checked the other's modules. Strict source
checks, full expanded API types, declaration/axiom/internal-consumer inventories, parent
preservation, actual book main content, full library/book gates and exact-head CI are
recorded in the issue report. All original source statements/proofs/TEST clauses, the
shared objective/completion core and frozen M4a history retain their provenance. A finite
inventory is not a source-coverage certificate. The stale places-open module prose in
ActionFunctionField is corrected without changing its mathematics.

The result concerns valuation places for REGULAR actions on AFFINE curves. The original
rational-action regularization, non-affine completion/points bridge and extension/uniqueness,
original group/chunk/six-point/normal-subgroup producers, arbitrary-action classification,
algebraization and descent remain owed. No field/place-faithfulness equivalence is asserted.
All eight original #21 work items remain open; the full durable goal stays active and incomplete.


## Checkpoint: faithful point parameters and coefficient-field algebraicity (#21)

`Correspondence.PointwiseFaithfulness` proves
`isAlgebraic_fractionRing_of_injective_points`. Over an ACF base k, let A be a finite-type
domain, B a coefficient ring and E its fraction field. For a compatible field C containing
the coefficient image, injectivity of Hom_k(A,k) -> Hom_k(B,k) restriction implies that E/C
is algebraic. All scalar maps and both compatibility towers remain explicit. The coefficient
ring need not be a domain or finite type; k,B,A,C,E have independent universes. Purely
inseparable extensions are permitted. No derivative, variation or genus premise is used.

The proof first makes every tensor diagonal in A tensor_B A nilpotent: each k-point is a
pair agreeing on B, hence equal, and the Jacobson/Nullstellensatz argument detects the
nilradical of any finite-type k-algebra, including nonreduced ones. Powers of a transcendental
element stay linearly independent after flat extension of constants; consequently its
field-tensor diagonal is not nilpotent. Mapping the coordinate diagonal to E tensor_C E
shows that every element of A is algebraic over C. Fractions finish the argument.

The new module has five public API theorems and one consumed internal proof field, with no
private declarations or generated public equations. The checkpoint report records strict
checks, full types/dependencies/consumers, parent preservation, rendered book content and full
library/book validation with exact-head CI. All original source statement/proof/TEST blocks,
shared objective/completion core and frozen M4a history retain their provenance. A finite
inventory is not a source-coverage certificate.

This is the algebraic input for retaining the actual generic-action coefficient rank.
The coefficient map and its faithfulness still have to be constructed from the actual scheme
action. The generic-translate construction was isolated at this checkpoint; the next
checkpoint below integrates its completed actual function-field comparison. Coefficient variation,
the genus producer and constant-field rationality/genus-zero descent remain open. The source
rational-action regularization, completion/points bridge, original normal-subgroup and
arbitrary-action classifier, group/chunk/six-point producers, algebraization and descent
remain obligations. All eight original #21 rows stay open; the durable goal is active
and incomplete.


## Checkpoint: the actual generic parameter acts on the curve field (#21)

`Correspondence.SchemeGenericTranslate.exists_functionField_genericTranslate` now constructs
the actual generic action on Frac(k(G) tensor_k k(V)). Its hypotheses are an algebraically
closed base field, an integral group scheme, and its given regular action on an integral
affine scheme. It derives the canonical base algebras, the generic parameter, the tensor-domain
fact and the literal global-section/function-field comparison internally. No dimension,
finite-type, faithfulness, derivative, coefficient-variation or genus premise is supplied.
The conjugation formula identifies the resulting field automorphism with the actual action
on Frac(k(G) tensor_k Gamma(V)). No genus or classification conclusion is proved here.

`Correspondence.ParameterAction` constructs the parameter-preserving automorphism of T times X
in any cartesian monoidal category. `SchemeParameterAction` pulls it back to an A-algebra
automorphism of A tensor_k R and records the literal Spec formula and inverse-parameter law.
It uses Mathlib's tensor-product spectrum isomorphism directly, without importing the concrete
affine-group action. The generic consumer transports the given action through the actual
affine spectrum presentation and extends it to fractions. Its canonical coordinate fraction
field is compared with the actual generic stalk as a k-algebra; flatness and the ACF tensor
domain theorem supply the constant-extension comparison and its literal generic-germ formula.

The three modules have twenty public API declarations, three consumed private declarations
(including one compiler proof field) and twenty-nine consumed internal fields. Their complete
types, axioms and consumers are checked with strict flags; the report records full library/book
validation, the whole-library dependency audit, preservation of all parent declarations and
exact-head CI. Original source statement/proof/TEST blocks, the shared objective/completion core
and frozen M4a history retain their provenance. A declaration inventory is not source coverage.

Next is the finite actual coaction coefficient field C0, using both the action and its inverse,
and the proof that its coefficients give faithful variation. The pointwise-faithfulness
algebraicity theorem must then be applied to the actual coefficient map to retain group rank.
The actual finite-type integral-group dimension/function-field-rank bridge is still required.
Constant-field rationality and genus-zero descent remain the peer's separate source-only task.
A formal Frobenius-twist refutation must accompany the corrected variation producer: faithfulness
on field-valued points alone does not imply injective infinitesimal variation. This is a rejected
proof target, not a refutation of the original genus/classification claim.

The source rational-action regularization, completion/points identification, original
normal-subgroup and arbitrary-action classifier, group/chunk/six-point producers, algebraization
and descent remain obligations. All eight original #21 work items stay open. The full durable
goal remains active and incomplete; the issue report records the continuing ownership and next
mathematical consumers.


## Checkpoint: common finite coefficients for the actual parameter action (#21)

`Correspondence.ParameterCoefficients.exists_generating_sectionsCoefficients` internally
constructs finite algebra generators of Gamma(V) and a common finite k-linearly independent
section family for a given Spec A-family of group points acting regularly on an affine
locally finite-type scheme V over any field k. One finite matrix of A-coefficients describes
the images of all chosen generators in both parameter directions. It evaluates correctly for
every map A -> B of commutative k-algebras in the base universe, including nonreduced B.
No ACF, integrality or faithfulness premise is needed for this construction. The actual
Spec A-family is an input; the group chart and its effective coefficient field are not yet
chosen here. No generator, basis, coefficient matrix or coordinate-action certificate is
supplied by the caller. The scheme's structural morphism supplies finite generation, and
its actual affine spectrum presentation supplies the coordinate action.

`ParameterActionNaturality.parameterAct_natural` proves parameter naturality categorically.
`SchemeParameterBaseChange.tensorAut_baseChange` transfers it to the actual coordinate
automorphism, using Mathlib algSpec and its product-comparison naturality directly. The
finite coefficient proof chooses a k-basis of the coordinate ring and takes the finite union
of the supports of all generator images in both directions. Its restricted basis is the
common independent section family. The base-change theorem supplies all evaluation formulas.

The three new modules have four public theorems, one consumed private helper and one consumed
internal proof field. Complete public types, dependencies and consumers are checked with
strict flags, with no generated public equation or congruence wrappers. The checkpoint
report records full library/book gates, parent preservation, the whole-library dependency
audit, rendered book content and exact-head CI. Original source statement/proof/TEST blocks,
the shared objective/completion core and frozen M4a history retain their provenance.

Next is the actual effective field generated by these finite coefficients, together with
descent of the coordinate automorphism and its inverse. The coefficient map's actual
point-faithfulness and rank, faithful coefficient variation, the required dimension/rank
input, the genus producer and constant-field rationality/genus-zero descent remain open.
Uniform compatibility over all parameter algebras is not infinitesimal faithfulness.
The formal Frobenius-twist refutation remains due alongside the corrected variation producer.
Rational-action regularization, completion/points identification, the original normal
subgroup and arbitrary-action classifier, group/chunk/six-point producers, algebraization
and descent remain obligations. All eight original #21 work items stay open; the full durable
goal remains active and incomplete.


## Checkpoint: the actual effective coefficient field and tensor-ring descent (#21)

`SchemeGenericTranslate.exists_effective_sectionsTensorAut` constructs the effective
coefficient field C0 inside any field C receiving a parameter-algebra map A -> C, for a
G-action on an affine locally finite-type V over any field k and an actual Spec A-family g.
It retains the same internally chosen algebra generators, k-independent sections and raw
A-coefficients, together with every parameter-algebra evaluation formula from the previous
checkpoint. C0 is exactly the field adjoin of the evaluated forward and inverse coefficients.
The coefficient lifts generate C0 over k; essential finite type is derived internally.
The actual tensor-coordinate automorphism and its inverse descend to C0 tensor Gamma(V),
with their matrix formulas and literal comparison after the canonical injection into
C tensor Gamma(V). No coefficient model, invariant-image, finite-generation or coordinate-
action certificate is supplied by the caller. The given family g and field evaluation remain
explicit inputs; this checkpoint does not select the actual group chart or parameter field.

`TensorCoefficientDescent.exists_effective_tensorAut` constructs this field, its coefficient
lifts and both descended matrix formulas from any such finite matrix. Its consumed restriction
criterion `exists_tensorAut_of_generator_images` uses flatness to inject C0 tensor R into
C tensor R, finite algebra generation to prove invariance of its image in both directions,
and existing Mathlib range equivalences to restrict the automorphism. Both finite-image
hypotheses of the criterion are discharged by the actual matrix in the scheme consumer.
No ACF, domain, integrality or faithfulness hypothesis is used for this tensor-ring descent.

Exactly three new module declarations are public theorems, with no private/internal or
public equation/congruence wrappers. The restriction criterion is consumed by the finite-matrix
constructor, which is consumed by the actual scheme producer. All three expanded public
types were read in full; their dependencies are standard Lean axioms. The checkpoint issue
report records full library/book checks, parent preservation and exact-head CI evidence.
Original source statements/proofs/TEST blocks and the shared objective/completion core retain
their provenance; source scope has not been narrowed.

Next are the fraction-field lift and actual function-field comparison, choosing the actual
group chart and parameter field, point-map faithfulness/rank, faithful coefficient variation
and the genus producer. These must use the same raw matrix and effective field, with their
needed hypotheses derived internally. Constant-field rationality/genus-zero descent remains
separate. The formal Frobenius-twist refutation remains due alongside the corrected variation
producer; ordinary infinitesimal faithfulness does not follow from field-point faithfulness.
Rational regularization, completion/points identification, the original normal subgroup and
arbitrary-action classifier, group/chunk/six-point producers, algebraization and descent remain
obligations. All eight original #21 items stay open; the full durable goal remains active.


## Checkpoint: actual effective-field action and faithful coefficient variation (#21)

`SchemeGenericTranslate.exists_effective_functionFieldAut` internally constructs the action
on Frac(C0 tensor k(V)) for a regular group-scheme action on integral affine locally finite-
type V over an ACF base, with a given actual Spec A-family and field evaluation A -> C.
It retains the same finite algebra generators, k-independent sections, raw A-coefficients,
every parameter-algebra evaluation formula, effective C0, coefficient lifts, field-generation
and essential-finite-type proofs from the previous model. Three tensor domains are derived
and returned; canonical fraction embeddings and the actual Gamma(V)/function-field comparison
are internal. Both directions have literal germ-matrix formulas, and the field action compares
to the original C-action through the canonical fraction injection. No coefficient, domain,
field-comparison, variation or genus certificate is supplied by the caller. The given family
and field evaluation remain explicit inputs; no group chart or parameter field is chosen here.

The ordinary C0-coefficient variation map is injective. The consumed finite-matrix criterion
`coefficientVariationLinear_injective_of_generating_coefficients` takes the explicit domain,
independent sections, field generation and both matrix formulas; the actual producer derives
them. A zero variation commutes with the horizontal coefficient connection in both directions.
Differentiating the formulas and using independence after flat extension and fraction injection
kills every lifted coefficient. Their field-generation property then kills the derivation,
including inverses. No one-variable hypothesis or point-action faithfulness is needed for
this construction; it does not yet produce independent regular variations from group rank.

`TensorCoefficientDescent.exists_fractionTensorAut_comparison` derives the smaller tensor
domain by flatness, extends the descended ring action and retains the literal embedding and
comparison. Its returned domain witness and the actual producer's three returned witnesses
are bound as instances in the result. This makes the field structures reusable and fixes the
otherwise failing field/Galois-notation reconstruction in public type printing. No domain
hypothesis was added to the actual producer. One commented, finite maxHeartbeats600000 budget
supports its dependent elaboration; kernel, lint and synthesis checking are unchanged.

The formal companion
`field_point_faithfulness_does_not_detect_coefficient_derivations` works in every prime positive
characteristic. Every map x -> a^p*x+b^p is bijective, and the family is faithful on parameters
over every field extension. Every ordinary coefficient derivation kills both coefficients;
a nonzero derivation on Frac(k[X0,X1]) is constructed internally. This refutes the attempted
coefficient-detection inference, not the source genus or affine-action lemma. The corrected
variation producer differentiates the field generated by the coefficients, allowing the
original parameter field to be a purely inseparable extension of it.

The four new modules contain exactly five declarations: four public theorems and one consumed
private Frobenius-family theorem, no internal or public equation/congruence wrappers. The
fraction helper and generic variation criterion are consumed by the actual producer; the
private family theorem is consumed by the counterexample. All expanded public types are
reviewed, with only standard axioms. The actual type preserves the fully read field-action
statement modulo whitespace/binder naming and adds only variation injectivity. The hardened
audit rejects printer-failure sentinels. Lean omission metadata checks all fifty-one inherited
signatures with ellipses and the four new signatures: every omission is an embedded proof term,
with no depth/step truncation of public binders or conclusions. The issue report records full
library/book checks, parent preservation, fresh whole-library dependencies and exact-head CI.
Original statements/proofs/TEST blocks, goal core and frozen M4a provenance remain unchanged.

Next: choose the actual affine group chart/parameter field; prove point-map faithfulness and
rank from the same raw coefficient map, allowing inseparability; derive the dimension/rank
input, two independent regular variations and genus. Constant-field rationality/genus-zero
descent remains separate. Rational regularization, completion/points identification, the
normal subgroup and arbitrary-action classifier, group/chunk/six-point results, algebraization
and descent remain obligations. All eight original #21 items and the full durable goal stay open.


## Checkpoint: actual regular-affine action genus zero after constants (#21)

`SchemeGenericTranslate.exists_constantExtension_genus_eq_zero` takes only an ACF base k,
an integral locally finite-type group object G of dimension at least two, an integral affine
locally finite-type curve V of dimension one, its actual regular action and the genuine
global-point kernel criterion. It internally chooses an algebraically closed constant
extension K and proves genus zero for Frac(K tensor_k actual k(V)). The actual generic-stalk
base algebra is retained. The tensor domain and one-variable witnesses are returned and
bound in the conclusion. No chart, parameter-field, coefficient model, rank, separating-
parameter, variation, regularity, domain, one-variable or genus certificate is supplied.
This is the regular-affine case after constants; original-base genus descent and the
non-affine, rational-action and arbitrary-classification obligations remain open.

A finite chain of irreducible closed subsets gives a nonempty affine group chart retaining
the required dimension bound. Its actual section algebra is finite type and integral, and
its fraction field has the same lower rank bound. The chart inclusion and canonical map
from its section algebra to its fraction field supply the actual family and evaluation.
The original effective function-field producer is called once: the same s, independent v,
raw cA, C0, lifted c0, field generation, essential finite type, both matrices, actual field
comparisons and faithful ordinary variation are retained.

Equal restrictions of chart points to the raw coefficient algebra imply equal evaluated
matrices. Finite algebra generation gives equal tensor-coordinate automorphisms. Their
literal spectrum pullbacks give equal parameter actions. Transport along the actual affine
presentation and the terminal-parameter comparison reduces to the point-action kernel.
The chart monomorphism gives equality of chart points. The coefficient-ring map into C0 and
all scalar towers are constructed internally. The existing tensor-diagonal theorem then
makes the parameter field algebraic over C0, allowing pure inseparability. The transcendence
rank bound passes to C0 and its finite generation gives two independent ordinary derivations.

The actual curve field's dimension and finite generation supply a separating parameter.
The same faithful variation map sends the two coefficient derivations to independent
coefficient-linear curve derivations, regular at every proper valuation subring containing
C0. Only these curve derivations extend to the algebraic closure K of C0, using Mathlib's
canonical algebra/tower structures. The ordinary coefficient derivations are never extended
to a perfect or algebraically closed field. The canonical larger tensor fraction field is
one-variable and its two independent regular derivations give genus zero.

The generic matrix/containment criteria expose their premises; the actual genus consumer
derives them. The shared finite-type section lemma is also used by the existing coefficient-
family producer. The new source module split preserves the independently checked mathematical
bodies, with literal extraction of that shared lemma. Six complete public signatures have
been read in full. The independent audit finds four consumed private lemmas and three
consumed generated internal proofs, all using standard axioms. Two unused generated public
exports found during review were eliminated by explicit proof rewrites; none is retained.
The issue report records full repository/book gates, the selected-scope and fresh whole-library
checks, committed-head validation and exact CI. A finite inventory is not a coverage certificate.
Original statement/proof/TEST blocks, the goal completion core and frozen M4a history are exact.

Next: descend genus/rationality from the internally chosen constant extension to the original
k(V), then continue the original normal-subgroup and arbitrary-action classifier. Non-affine
and rational-action cases, regularization, completion/points identification, original group/
chunk/six-point results, algebraization/descent and all true bypassed auxiliaries remain owed.
`aclgeom.claude` retains the separately coordinated source-only constant-field descent task;
no fresh peer proof approval is claimed. All eight original #21 items stay open and the full
durable goal remains active and incomplete. Earlier checkpoint sections record their then-
current frontiers; this checkpoint supplies their regular-affine genus consumer after constants.


## Checkpoint: original-base genus and rational coordinates for actual affine actions (#21)

`SchemeCurveGenus.genus_eq_zero` and `SchemeCurveGenus.exists_generator` prove genus zero
and choose a transcendental generator over the ORIGINAL algebraically closed base for the
actual generic-stalk field of V. Genuine hypotheses: integral locally finite-type group G of
dimension at least two, integral AFFINE locally finite-type dimension-one V, actual REGULAR
action and the global k-point kernel criterion. The public curve theorem supplies the original
one-variable instance. The preceding actual producer internally chooses K and supplies its
tensor domain, larger one-variable instance and genus zero. Rationality descent removes that
constant extension. No chart, coefficient model, rank, constants, one-variable, genus or
rationality certificate is a caller premise. The project's connected group package supplies
integrality; bare connected nonreduced groups are not silently treated as integral.

`RationalityDescent.exists_generator_of_tensor_generator` works with k/F/K in three independent
universes, with ACF k, arbitrary field K/k and a one-variable F/k. The rational generator of
canonical Frac(K tensor_k F) is the explicit mathematical premise. K need not be ACF. All
finite models, common denominators, nonvanishing and specializations are internal. The generic
genus-zero criterion has both one-variable instances explicit and K ACF; the actual scheme
consumer supplies every instance and rationality premise internally. No arbitrary-genus
base-change invariance is asserted.

The proof chooses finite field generators of F and polynomial fractions for their images.
A common nonzero tensor denominator clears u and every inverse polynomial denominator.
A tensor basis selects a finite-type constant subalgebra containing all coefficients and
cleared numerators. Injectivity gives an embedded common localization in the canonical
fraction field. A nonzero basis coordinate and the Jacobson/residue-field theorem choose
a k-point preserving the denominator. The actual localization map to F fixes all of F and
sends selected K-coefficients into k. The inverse table forces specialized denominators to
be units. Every original field generator lies in k(t), so this is F; the one-variable
hypothesis rules out algebraic t.

The two new modules preserve the independently checked mathematical bodies literally. All
four expanded public types have been read in full, with zero printer omissions. The nine
new declaration records contain four public theorems, four explicit consumed private proofs
and one consumed private simp proof. Only standard axioms occur; no unsafe declarations or
unused generated exports are present. The proof chain is specialization -> rationality
descent -> genus-zero descent -> actual original-base genus -> actual rational coordinate.
Validation evidence for the committed checkpoint is recorded on #21. Original source
statements/proofs/TEST blocks, the shared completion core and frozen M4a history are preserved.

Next: combine the original-base coordinate with the actual field/place action and fixed
boundary place for the fractional-linear and affine-coordinate description. Non-affine and
rational-action cases, regularization, completion/points identification, the normal subgroup
and arbitrary-action classifier, original group/chunk/six-point results, algebraization and
descent and all true bypassed auxiliaries remain owed. Peer source ownership, review requests
and serial compiler leases were coordinated through chit; no fresh peer proof approval was
received. All eight original #21 items and the full durable goal remain open. Earlier
checkpoint sections retain their then-current frontiers; this checkpoint supplies their
regular-affine original-base genus/rationality descent consumer.


## Checkpoint: faithful affine coordinates for the actual k-point action (#21)

`SchemeAffinePointAction.exists_faithful_affine_coordinates` gives a transcendental original-
base generator of the actual generic-stalk field and an injective group homomorphism from
G(k) into `AffineTransformation k`, with the literal pullback formula for every actual point.
G is the connected algebraic-group package, of dimension at least two; V is integral,
affine, locally finite type and dimension one over an ACF base. Its actual regular action
and genuine global k-point kernel criterion are the only action inputs. The package supplies
integrality. The fixed boundary place, one-variable field, genus and faithful field action
are all chosen or proved internally. No coordinate or classification certificate is supplied.

`FixedPlaceAffine.exists_affine_of_fixed_pole` eliminates the nonconstant Möbius denominator
coefficient by orders at the fixed simple pole. In the nonzero-coefficient case, the
transformed generator and denominator have order minus one, whereas the numerator has order
zero or minus one; their crossed identity is impossible. Its generic representation consumer
chooses a generator at the given place using genus zero. Transcendence makes affine evaluation
injective. Pullback's reversed composition gives exactly the existing affine multiplication.
Equality on the generator gives equality of field automorphisms, then faithfulness of the
point representation. The scheme consumer derives every generic criterion premise.

The two focused mathematical bodies are literal to the independently checked frozen source,
up to trailing blank-line normalization at splitting. The eight new declarations consist of
three public APIs, two explicit private helpers, one consumed private proof and two consumed
public internal proofs. Every non-API declaration has a named consumer; unused simplifier
exports found in the first prototype were removed with explicit quotient identities. All
three expanded public types were read in full, with zero printer omissions and only standard
axioms. The issue report records the full library/book gates, parent preservation, fresh
whole-library dependencies, committed-head checks and exact CI. The original statement/proof/
TEST blocks, shared completion core and frozen 117-item M4a history retain their provenance.

This is a k-point/function-field theorem. Next are rational or regular coefficient functions
on the actual group, their scheme-group morphism and finite-cover parameter coordinates.
Non-affine and rational-action cases, regularization, completion/points identification,
the normal subgroup and full classifier, original group/chunk/six-point producers,
algebraization/descent and every true bypassed auxiliary remain owed. Peer ownership and
compiler leases were coordinated through chit; no fresh peer proof approval was received.
All eight original #21 items stay open; the full durable goal remains active and incomplete.
Earlier checkpoint sections record their then-current frontiers.


## Checkpoint: actual rational affine coefficients and finite parameter field (#21)

`SchemeAffineParameters.exists_affine_parameters` starts from a connected algebraic-group
package of dimension at least two, an integral affine locally finite-type dimension-one
curve V over an ACF base, its actual regular action and the genuine global k-point kernel
criterion. It retains the same original-base transcendental generator of the actual generic-
stalk field and global injective affine point homomorphism. It internally chooses an actual
affine group chart and two rational coefficients. Their literal point specializations and
actual generic-translate comparison are proved. The actual chart fraction field is finite
over their field and they form a transcendence basis. Pure inseparability is allowed. No
chart, coordinate, coefficient, specialization, rank or finiteness certificate is supplied.

The common-denominator proof uses tensor coordinates and Cramer identities. Transcendence
supplies a nonzero minor at one actual point; Jacobson density proves the cleared identities
at every coefficient, including points where the minor vanishes. The actual section coaction
specializes to the point action on generic germs and commutes with parameter base change.
Thus the same coefficients describe the actual generic translate, with its canonical
section/function-field comparison. Localizing the parameter ring only at the denominator,
agreement on the two coefficients gives equal field actions, then equal group points by
the global kernel criterion and equal chart points by its monomorphism. The two-coefficient
algebra includes no unrelated inverse of the denominator. Point injectivity proves algebraicity
over the coefficient field. Actual chart rank and essential finite type give independence
and a finite field extension, without a separability claim.

The five focused mathematical modules preserve the independently checked prototype bodies
literally, with concatenation and trailing blank-line normalization. Their seventeen new
records comprise eleven public APIs, three consumed public internal proofs and three consumed
private proofs. Every helper has a named consumer. Two unused generated equation/congruence
exports found during audit were removed by explicit rewrites; every retained type stayed
exact. A broader fresh-meta signature check caught two fraction-field printing failures.
Both tensor-domain witnesses are now proved internally and bound in the generic and actual
conclusions, adding no caller premise. Both full strengthened statements and the unchanged
remaining types were read in full; the fresh-meta and direct-type printing paths succeed.
All eleven public types and six private/internal types and consumers have zero printer
omissions and only standard axioms. The issue report
records full library/book gates, selected statement preservation, fresh whole-library
checks, committed-head validation and exact CI. A finite inventory is not a source-coverage
certificate. Original statements/proofs/TEST blocks, goal completion core and frozen M4a
history are exact.

Next: global regular coefficient maps, the scheme-group morphism and multiplication law,
and scheme finite-cover coordinate maps. The finite field extension alone is not that
scheme theorem. Non-affine and rational-action cases, regularization, completion/points
identification, the normal subgroup and full classifier, original group/chunk/six-point
producers, algebraization/descent and every true bypassed auxiliary remain owed. Peer source
ownership, review requests and serial compiler leases were coordinated through chit;
no fresh peer proof approval was received. All eight original #21 items stay open; the full
durable goal stays active and incomplete. Earlier checkpoint sections retain their then-
current frontiers; this one supplies the actual regular-affine rational coefficient and
parameter-field consumer.


## Checkpoint: the global regular affine-group morphism (#21)

`SchemeAffineMorphism.exists_affine_morphism` constructs an actual group-scheme morphism
from the connected algebraic-group package to the standard affine group, with injective
k-point map. Its only inputs are the genuine ACF base, group dimension at least two,
integral AFFINE locally finite-type dimension-one curve, actual REGULAR action and global
k-point kernel criterion. The preceding parameter producer is called ONCE. The SAME original
generic-stalk generator, faithful affine point homomorphism, chart, rational coefficients,
finite parameter-field extension, transcendence basis and actual generic/specialized formulas
are retained, including both internally proved bound tensor-domain witnesses. No coordinate,
local regular model, gluing, extension or scheme morphism is supplied by the caller.

On the principal open obtained by inverting the product of multiplier numerator and
denominator, the rational multiplier is a unit and the shift is regular. The existing
coordinate algebra's universal property constructs the actual affine-group Spec map.
Jacobson density chooses a point on that open. Transcendental affine evaluation identifies
its point map with the same global representation. The elementary evaluation-injectivity
proof was moved literally from its old consumed private fixed-place helper into the common
`AffineTransformation.eval_injective` API; both old and new consumers use it. Its type hash,
universes and axioms are exact, and no duplicate local proof remains.

Translates of the open cover every closed point. Jacobson density applied to the closed
complement proves that they cover the whole group. On actual pullback overlaps, the local
point formulas and Mathlib's reduced-source morphism extensionality give compatibility.
Mathlib gluing constructs the global scheme map and local checks give its base compatibility.
The chosen original point gives the formula at every group point. The actual group product
is integral; point extensionality there and the point homomorphism's laws prove the actual
unit and multiplication diagrams. The map is packaged as a genuine group-scheme homomorphism.

The three focused mathematical modules and the promoted common proof preserve the checked
prototype bodies literally. The nine added records comprise four public APIs (one promoted),
four consumed explicit private helpers and one consumed public internal proof. Fourteen
generated normalization facts, including twelve unused ones, were eliminated by replacing
two group-tactic calls with explicit cancellation. All nine retained types stayed exact.
All four expanded public statements and all five private/internal types and consumers were
read in full; fresh-meta and direct-type printing succeed with zero omissions. Only standard
axioms and zero unsafe declarations occur. One commented finite600000-heartbeat budget
supports the actual producer's dependent data; strict synthesis, lint and kernel checking
remain enabled. The issue report records full library/book checks, declaration promotion,
parent preservation, fresh whole-library staged/committed audits and exact-head CI.
Original statements/proofs/TEST blocks, goal completion core and frozen M4a history are exact.
A finite inventory is not a source-coverage certificate.

No scheme monomorphism is asserted and inseparability is allowed. Scheme finite-cover
coordinate maps, non-affine and rational-action cases, regularization, completion/points
identification, the normal subgroup and full classifier, original group/chunk/six-point
producers, algebraization/descent and every true bypassed auxiliary remain owed. Peer
ownership, review requests and serial compiler leases were coordinated through chit; no
fresh peer proof approval was received or claimed. All eight original #21 items stay open;
the full durable goal remains active and incomplete. Earlier checkpoint sections retain
their then-current frontiers.


## Checkpoint: the actual finite affine-group parameter cover (#21)

`SchemeAffineParameterCover.exists_finite_parameter_cover` constructs a finite surjective
scheme map between internally chosen nonempty opens of the original group and the standard
affine group. Its actual square commutes with the SAME global group-scheme morphism. The
only inputs are the genuine ACF base, connected algebraic-group package of dimension at
least two, integral AFFINE locally finite-type dimension-one curve, actual REGULAR action
and global k-point kernel criterion. The preceding actual morphism producer is called ONCE.
The original generic-stalk generator, faithful affine point homomorphism, actual group
morphism, chart, rational coefficients, finite parameter field, transcendence basis and all
generic/specialized formulas are retained, with both internal tensor domains bound. No
coordinate, dominance, algebraicity or finite-cover certificate is a premise.

Full faithfulness of algebraic Spec gives the regular pullback coordinate map on the same
actual chart. Its point evaluations agree with the same faithful affine representation.
The original field formula and transcendence identify the multiplier and shift where the
denominator is nonzero. Multiplying the cleared difference by that denominator makes it
vanish at every point. Jacobson density and the chart domain give the cleared identities,
including the original rational coefficients in its fraction field. Their independence
makes the affine coordinate-algebra map injective. That injectivity is proved via the
existing affine universal property and polynomial localization, not assumed as dominance.

Agreement on the coordinate algebra identifies the affine transformation, then the actual
group point by global faithfulness and the chart point by its open immersion. The existing
tensor-diagonal criterion makes the chart fraction field algebraic over the coefficient
fraction field. Algebraicity reflects to the chart ring. Mathlib chooses one common nonzero
multiple making its finite algebra generators integral. Inverting it gives an integral
finite-type algebra, hence a finite map. Its actual Spec map is surjective by injectivity
and lying-over. Both localization maps are open immersions into the actual source chart
and affine group. Localization compatibility proves the actual commuting square.

Four focused modules preserve all seven independently checked prototype bodies literally,
with concatenation and trailing blank-line normalization. Exactly seven declaration records
are added: all public theorems, every supporting API consumed on the path to the actual
producer, with no private, internal or generated extras. All seven expanded public types
have been read in full; both fresh-meta and direct-type printing pass with zero omissions.
Only standard axioms and zero unsafe declarations occur. Narrowing a helper import to the
affine-group target model preserves all seven type hashes, universes, types and consumers;
the actual consumer imports its parent producer explicitly. One commented finite budget of 600000 heartbeats supports its retained dependent
fields/chart and literal comparison;
kernel, lint and strict synthesis checking remain enabled. The issue report records full
library/book gates, exact parent preservation, fresh whole-library staged/committed audits
and exact-head CI. Original source statements/proofs/TEST blocks, the shared completion
core and frozen M4a history retain their provenance. A finite inventory is not a coverage
certificate.

This is the GROUP PARAMETER finite cover, not a global finiteness or degree-one assertion.
Inseparability remains allowed and no scheme monomorphism is asserted. Curve-coordinate
scheme/action diagrams, the remaining source finite-cover constructions, non-affine and
rational-action cases, regularization, completion/points identification, the normal subgroup
and full classifier, original group/chunk/six-point results, algebraization/descent and every
true bypassed auxiliary remain owed. Source ownership, review requests and serial compiler
leases were coordinated through chit; no fresh peer proof approval is claimed. All eight
original #21 items stay open and the full durable goal remains active and incomplete.
Earlier checkpoint sections retain their then-current frontiers.


## Checkpoint: the same curve coordinate and joint scheme action diagram (#21)

`SchemeAffineCurveDiagram.exists_curve_action_diagram` adds an actual nonempty curve open,
a regular line coordinate with the SAME literal generic-point value, and an actual joint
scheme action diagram on a nonempty open of the original group times the curve. Its only
inputs are the genuine ACF base, connected algebraic-group package of dimension at least
two, integral AFFINE locally finite-type dimension-one curve, actual REGULAR action and
global k-point kernel criterion. The parent finite group-parameter producer is called ONCE.
The SAME original generic-stalk generator, faithful affine point homomorphism, global group
morphism, finite group-parameter cover, chart, rational coefficients, transcendence basis,
finite parameter field and every generic/specialized formula are retained, with both internal
tensor-domain witnesses bound. No coordinate, generic lift, normality or intertwining
certificate is a caller premise.

Mathlib spreads the actual line point at the original generator to a dense curve open.
The actual generic point lifts to this open and has precisely the required coordinate.
For each curve automorphism, its function-field pullback lifts that point to the actual
common pullback open. This makes the open nonempty. The lifted generic morphism is dominant,
because composing with the open immersion to the original curve gives its generic point.
The affine field formula and actual standard point-action computation therefore prove the
slice identity as actual scheme morphisms into the separated line, by reduced-source
extensionality. No normalization or scheme completion is used.

For the joint identity, pull the curve coordinate open back along the actual action on the
product of the group and coordinate open. This is an actual open in G times V; the unit
action gives a point over the original generic field, proving nonemptiness. The slice
identity handles every base-field point. Product integrality over the ACF base gives a
reduced joint open, and Mathlib point extensionality proves the actual joint scheme diagram.
The SAME global group morphism provides its affine coordinates. The curve need not be normal.

Three focused modules preserve four independently checked prototype bodies literally, with
concatenation and trailing blank-line normalization. Exactly five public theorems are added;
each supporting API has a named consumer ending at the actual action theorem. Two generated
exports in the first prototype were eliminated by explicit instance/association identities;
all five public types stayed exact. All five complete expanded public types were read;
both printing paths succeed without omissions and use only standard axioms. One commented
finite600000-heartbeat budget supports the actual consumer's retained dependent chart and
fields; the default200000 budget timed out. Kernel, lint and strict synthesis checking remain
enabled. Full library/book gates, fresh whole-library and committed-head dependency checks
and exact-head CI are recorded on #21. Original statements/proofs/TEST blocks, shared goal
completion core and frozen117-item M4a history retain their provenance. A finite declaration
inventory is not a whole-source coverage certificate. Ownership, source review requests and
serial compiler leases were coordinated with aclgeom.claude; no fresh peer proof approval is
claimed.

The curve coordinate's finiteness or open-immersion property has not yet been proved.
Remaining source finite covers, non-affine and rational-action cases, regularization,
completion/points identification, the normal subgroup and full classifier, original group/
chunk/six-point results, algebraization/descent and every true bypassed auxiliary remain owed.
All eight original #21 items stay open and the full durable goal remains active/incomplete.
Earlier checkpoints retain their then-current frontiers.


## Checkpoint: the given curve coordinate restricts to an open isomorphism (#21)

`SchemeAffineCurveCover.exists_curve_coordinate_cover` calls the previous actual action
producer ONCE and retains every old datum. The GIVEN old coordinate x restricts to an
isomorphism between internally chosen nonempty curve and standard-line opens, finite and
surjective onto its target open. The new generic lift factors the GIVEN old lift; the
restriction square is literal. The SAME original t and global group morphism satisfy the
joint scheme action diagram on the restricted coordinate. Inputs remain exactly the genuine
ACF/connected-group/regular-action/affine-curve/dimension/global-point-kernel hypotheses.
No normality, birationality, coordinate or generic-lift certificate is supplied by the caller.

Transcendence gives injective evaluation on the actual standard-line coordinate algebra.
Extending to its actual generic-stalk field and using k(t)=k(V) gives a field equivalence,
compatible with the actual base algebra and generic Spec map. The old curve open immersion
identifies the original and open-curve function fields. Transporting t along that map and
using the old generic identities proves that the GIVEN x induces an isomorphism of function
fields. The existing mutual-inverse-rational-map construction then supplies an isomorphism
of nonempty opens. Its new forward-map law proves the actual restriction square. The generic
point lifts to the new curve open, and mono cancellation gives the required factorization.

Four focused new modules supply the field, birational-morphism, coordinate-restriction and
actual-action layers. The old joint-diagram proof is factored for a GIVEN coordinate/lift;
its previous public theorem keeps its exact type and delegates after choosing its coordinate.
The moved joint proof is reused, and every supporting API has a named consumer ending at the
actual cover. There are eleven new named public APIs; generated proof dependencies are
included in the declaration audit. A finite600000-heartbeat budget supports the actual
consumer's retained dependent data and two curve opens; no checking is weakened. Full
build/book, strict touched-module checks, dependency/signature/source-fidelity checks and
exact-head CI evidence are recorded on #21. Ownership and source review were coordinated
through chit with aclgeom.claude; no fresh peer proof approval is claimed.

Finiteness is onto the chosen line OPEN. The group parameter cover may remain inseparable;
no scheme monomorphism or degree-one group field extension is asserted. Remaining source
finite covers, non-affine and rational-action cases, regularization, completion/points
identification, the normal subgroup and full classifier, original group/chunk/six-point
results, algebraization/descent and every true bypassed auxiliary remain owed. All eight
original #21 work items stay open, and the full durable goal remains active/incomplete.
Earlier checkpoints retain their then-current frontiers.


## Checkpoint: actual normal multiplicative subgroups are central (#21)

`MultiplicativeRigidity.normal_multiplicativeGroup_conj` proves the torus alternative in the
original proof of Lemma 8.4: a normal multiplicative-subgroup morphism into a connected
algebraic group over an ACF base is central as an actual morphism G times Gm to G. Its only
inputs are that actual group, actual group morphism and genuine normal-subgroup property.
No exponent, regular conjugation lift, constancy or action certificate is supplied by the
caller. All characteristics, including two, are covered; no group-dimension hypothesis is
needed for this auxiliary statement.

Hopf-Spec full faithfulness lifts every actual Gm group-scheme automorphism to the actual
coordinate Hopf algebra. Mathlib's group-algebra bialgebra-map classification gives an
endomorphism of the integers, and the inverse forces its value at one to be one or minus
one. Thus the scheme automorphism is identity or inversion over any field. This theorem
concerns group-scheme automorphisms, rather than arbitrary abstract automorphisms of k-points.

Normality supplies the regular conjugation lift internally. In a general cartesian monoidal
category, restricting such a lift at a group point gives an actual group-object isomorphism;
monic cancellation proves its group law and inverse. For the actual connected algebraic
group, choose a multiplicative point distinct from its inverse. Closed orbit fibers and
Jacobson density cover the group by two closed sets; irreducibility and the unit select the
identity alternative. The integral product is reduced, so point extensionality proves the
actual joint conjugation identity. No smoothness, completion or characteristic-zero argument
is used.

Three focused modules preserve four checked prototype bodies by concatenation. Every helper
has a named consumer ending at the actual centrality theorem. Unused generated simplification
artifacts in the first generic group-normalization proof were removed using explicit group
identities. All generated dependencies retained in the final inventory have consumers.
No checking option is weakened. Full build/book, strict touched-module checks, expanded
signature/dependency/source-fidelity audit and exact-head CI evidence are recorded on #21.
Ownership, truth/API review requests and serial compiler leases were coordinated through
chit with aclgeom.claude; no fresh peer proof approval is claimed.

This proves the torus alternative for a normal subgroup already presented as Gm. It does
not classify arbitrary one-dimensional normal subgroups or their finite isogenies. Remaining
source finite covers, non-affine/rational actions, regularization, completion/points,
the full classifier, original group/chunk/six-point results, algebraization/descent and every
true bypassed auxiliary remain owed. All eight original #21 items stay open; the full durable
goal remains active/incomplete. Earlier checkpoints retain their then-current frontiers.


## Checkpoint: the actual normal additive-subgroup character (#21)

`AdditiveRigidity.normal_additiveGroup_conj` proves the normal-Ga case of (8.4b). From a
connected algebraic group over an ACF base, an actual Ga group morphism into it and genuine
normality, it constructs a regular group character to Gm and proves the actual joint scheme
conjugation diagram. Coefficient, regularity, global invertibility and group laws are all
internal. Every characteristic is covered; no group-dimension hypothesis is needed for this
auxiliary statement. This does not identify arbitrary one-dimensional normal subgroups.

Every actual Ga group-scheme automorphism over a field is multiplication by a nonzero
scalar. Hopf-Spec full faithfulness gives a coordinate-algebra automorphism. Polynomial
inverse degrees force degree one and the actual Hopf counit removes the constant. This is
not a classification over arbitrary nonreduced coefficient rings. The parameter group in
the regular-family consumer is reduced.

Normality gives the regular conjugation lift. Evaluation at one gives a regular line map
whose value at each base-field point is nonzero. Its pullback coordinate is a global
section; Jacobson closed points make its basic open the whole group, so it is a global unit.
The actual Laurent-algebra and spectrum maps give the regular Gm morphism, without assuming
the parameter group affine. Monic cancellation proves multiplicativity of the conjugation
slices; the scalar point formula gives the coefficient law. Reduced-product point
extensionality proves the actual character's group laws and joint scheme diagram.

Nine focused production modules preserve eleven independently checked prototype bodies.
Every helper has a named consumer ending at the actual theorem; all generated proof
dependencies have consumers. The expanded intrinsic types and direct signatures have zero
omissions. No checking option is weakened. Full build/book, strict module checks, whole-
library dependency/source fidelity and exact-head CI evidence are recorded on #21. Ownership,
source review requests and serial compiler leases were coordinated through chit with
aclgeom.claude; no fresh peer proof approval is claimed.

The normal-Ga character and normal-Gm centrality are now actual source auxiliaries. Arbitrary
one-dimensional normal-subgroup/isogeny classification, the dense-orbit curve coordinate,
remaining source finite covers, non-affine/rational actions, regularization, completion/points,
the full classifier, original group/chunk/six-point statements, algebraization/descent and
every true bypassed auxiliary remain owed. All eight original #21 items and the full durable
goal remain active/incomplete. Earlier checkpoints retain their then-current frontiers.
