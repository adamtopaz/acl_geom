# Shared project goal

Last reviewed: 2026-10-15.
Jointly maintained by `aclgeom.codex` and `aclgeom.claude`.

## Objective

Complete the Lean 4/Mathlib formalization of the mathematical content of
[sources/blueprint.tex](sources/blueprint.tex): the Evans–Hrushovski–Gismatullin
reconstruction theorem, its auxiliary results, and its stated variants and
functorial consequences. Produce unconditional public theorems under the
blueprint's genuine hypotheses, a matching Verso exposition, and reproducible
validation. Preserve the provenance and justified corrections of source errors.

The project also formalizes, in the `GroupConfig` library, the group
configuration theorem of
[sources/group_configuration_blueprint.tex](sources/group_configuration_blueprint.tex),
whose parts are in [sources/group_configuration/](sources/group_configuration/).
That supplementary blueprint was written for this project to supply the group
extraction that the source route needs. It adds obligations and removes none
from the original blueprint; see
[Group configuration theorem](#group-configuration-theorem) below.

The shared goal is the mathematical result, rather than a particular proof
route or a collection of interfaces. Alternative proofs are welcome; true
blueprint statements bypassed by a route remain obligations.

## Mathematical endpoint

For relatively algebraically closed extensions $K/k$ and $L/l$, with
$\operatorname{trdeg}(K/k)\geq5$, every order isomorphism
$\phi:\mathcal G(K/k)\simeq\mathcal G(L/l)$ must:

- imply equality of the two transcendence degrees;
- arise from an isomorphism $\Phi:K^{\mathrm{perf}}\simeq L^{\mathrm{perf}}$
  carrying the perfected base onto the perfected base and inducing $\phi$ on
  every relatively closed intermediate field;
- have exactly integral Frobenius twists as its possible reconstructions:
  literal uniqueness in characteristic zero, and a unique twist exponent
  between any two reconstructions in positive characteristic.

Prove the converse and the point-geometry formulation, automorphism exact
sequence, literal functor laws and exact Hom fibres, and the fully faithful
Frobenius-quotient formulation. The literal geometry functor is fully faithful
in characteristic zero; positive characteristic requires the Frobenius quotient.
Cover arbitrary chosen perfections and the blueprint's universe generality.

## When the project is complete

All of the following must hold:

1. The public reconstruction theorem has only the mathematical hypotheses above.
   Open completeness, chart, action or reconstruction conclusions are proved
   internally, rather than supplied by the caller. In particular, the current
   `JCompletenessACF` inputs in [AclGeom/Main.lean](AclGeom/Main.lean) are discharged.
2. Every intended blueprint statement has a recorded disposition and Lean
   evidence: proved with its precise hypotheses, or refuted with original
   provenance and a justified, proved corrected replacement. A source error or
   a bypass does not silently erase an obligation or narrow the final theorem.
   If a correction remains unresolved, the associated obligation remains open.
   The same holds for the group configuration blueprint. Its main theorem
   (`thm:main`), the constructible group (`thm:constructible`), descent
   (`thm:descent`), the Ψ application (`prop:psi-gc`, `cor:psi`) and their
   prerequisites must each be proved in the project or refuted with provenance.
   Proofs may live in `GroupConfig` or in project bridges such as `AclGeom/Config`.
3. The endpoint's variants and consequences above are proved. No conditional
   configuration or reconstruction theorem is presented as unconditional.
4. No `sorry`, `admit` or project axiom occurs on main. Final public theorem
   dependency checks report only the expected standard Lean axioms
   (`propext`, `Classical.choice`, `Quot.sound`); checking a selected scope is
   never described as checking the whole library.
5. Full `lake build`, `lake exe book` and CI pass for the final committed head.
   Source coverage, theorem statements, docstrings, book, README, issues and
   continuation guide agree. A final report on the repository's issues links
   the theorem and coverage evidence.

A theorem with named open hypotheses proves only the implication from those
hypotheses (AGENTS rule 4). It is progress; it does not discharge the corresponding
unconditional obligation.
Green builds or the existence of a public wrapper alone do not mean completion.

## Current frontier and critical path

The library already contains substantial foundations, hard-kernel results,
generic-point field clauses, semantic configuration assembly, transfer and
conditional reconstruction. The public reconstruction theorem still assumes
two perfected ACF completeness inputs. The central open work is:

| Work | Required result and tracker |
|---|---|
| Guarded geometric Q | Derive an independent initial chart from the actual guarded Ψ witness; the full grid follows from the existing chart theorem. Both necessary guards remain visible. [#27](https://github.com/adamtopaz/acl_geom/issues/27), [#6 G3](https://github.com/adamtopaz/acl_geom/issues/6). |
| Geometric Q′ | The product-output converse is proved under its stated ACF/rank-five hypotheses; the full original-base auxiliary table over ACF k/K now needs no rank bound. Q′ completeness reduces to guarded Q completeness. [#6 G4](https://github.com/adamtopaz/acl_geom/issues/6). |
| Geometric J and transfer | The new public reduction derives `JCompletenessACF` from guarded Q completeness alone. Prove that remaining input and complete arbitrary-field descent obligations. [#6 G5](https://github.com/adamtopaz/acl_geom/issues/6), [#7](https://github.com/adamtopaz/acl_geom/issues/7). |
| Reconstruction and variants | Remove open completeness inputs from reconstruction and finish the endpoint's public variants and functorial consequences. [#8](https://github.com/adamtopaz/acl_geom/issues/8), [#9](https://github.com/adamtopaz/acl_geom/issues/9), [#10](https://github.com/adamtopaz/acl_geom/issues/10). |
| Group configuration theorem | The precise and informal main theorems, the canonical-code constructible group/stabilizer/homogeneous-space presentations, arbitrary-small-ACF base change, parameter descent and the full `cor:psi` are proved. Complete the auxiliary source obligations and turn the actual constructible Ψ data into the algebraic group/curve action needed for classification and the guarded Q chart. [#12](https://github.com/adamtopaz/acl_geom/issues/12), [#27](https://github.com/adamtopaz/acl_geom/issues/27). |
| Remaining source mathematics | Complete the coordinate-ring/localization bridge to geometric fiber products. In an ACF ambient over an arbitrary base, the existing scalar branch calculus realizes all minimal-prime tensor components as composite germs independent of the chosen embeddings, and relational germ composition is associative. Packaged generic extension, group chunks, six-point configurations, affine actions and the remaining subgroup/correspondence results remain owed. [#5](https://github.com/adamtopaz/acl_geom/issues/5), [#12](https://github.com/adamtopaz/acl_geom/issues/12), [#13](https://github.com/adamtopaz/acl_geom/issues/13), [#21](https://github.com/adamtopaz/acl_geom/issues/21). |

The existing Q/Q′-to-J assembly is an established dependency. On the source's
group/chunk route, the two-dimensional Q chart and the one-dimensional Q′
six-point argument share an open bridge: extract an algebraic group from an
actual finite-correspondence configuration, up to interalgebraicity. The source
multiplication converse has not supplied the ambient group required by its
curve-coset invocation. The finite group-chunk variant has not proved the
coherent lift and closure under words required by its proposed finite cover.
These are proof gaps, not verified refutations; the original wording remains.
The joint audit is recorded on
[#12](https://github.com/adamtopaz/acl_geom/issues/12#issuecomment-6155280744) and
[#27](https://github.com/adamtopaz/acl_geom/issues/27#issuecomment-6155281059).

This describes a dependency of the source route, not a necessity for every
proof. The direct Q′ route is now proved in
[AclGeom/Config/MultiplicationConverse.lean](AclGeom/Config/MultiplicationConverse.lean):
a literal semantic ratio, a fixed-field ambient automorphism and the proved
multiplicative correspondence theorem force the product output. Its consumers in
[AclGeom/Config/Correctness.lean](AclGeom/Config/Correctness.lean) derive Q′ and J
completeness from guarded Q completeness alone. Coherent specialization now
proves the full original-base auxiliary coordinate table over an ACF base:
one homomorphism preserves the finite incidence equations and the common
nonzero multiplier. An auxiliary extension and descent remove the table
theorem’s ambient rank bound over algebraically closed fields. This bypasses
group extraction for both multiplication conclusions; the true bypassed group/chunk statements remain obligations.
Audit the needed targets and dependencies before investing in group, chunk or
action infrastructure. No route is declared sufficient without proofs.
The frozen 117-item M4a chain is historical, not a list of deliverables. Related
source statements remain owed; revisiting frozen code requires a concrete
mathematical purpose and agreed ownership.

## Group configuration theorem

[sources/group_configuration_blueprint.tex](sources/group_configuration_blueprint.tex)
was committed in c082e7e and is tracked on
[#12](https://github.com/adamtopaz/acl_geom/issues/12). It gives an informal proof
of Hrushovski's group configuration theorem in the language of fields. The fields
are algebraically closed, $k\subseteq K$, and $K$ has infinite transcendence
degree over $k$. The theorem says that, after a finite independent
base extension, a six-point configuration is interalgebraic with the standard
configuration of a group of germs of quasi-rational maps acting on a variety.
Over a further generic extension that group is constructible
(`thm:constructible`), and the descent theorem (`thm:descent`) controls the base
fields. The application (`prop:psi-gc`, `cor:psi`) takes the actual Ψ witness
with $n=2$ and $m=1$. Its output is a rank-two constructible group acting on a rank-one homogeneous
space. Algebraization must turn these quotient presentations into the algebraic
group and curve action required by the original blueprint's Lemma `affine-action`
([#21](https://github.com/adamtopaz/acl_geom/issues/21)).

Part [12](sources/group_configuration/12-lean.tex) of the supplementary blueprint
proposes the Lean architecture: a `lean_lib GroupConfig` in this package.

Its scope section states three non-goals:

- Weil's algebraization of constructible groups;
- the classification of the resulting group;
- elimination of imaginaries beyond the codes it constructs.

These are non-goals of the supplementary blueprint alone. Weil algebraization and
the group classification remain obligations of the original reconstruction
blueprint and the shared endpoint. Those include the original group-chunk,
six-point and action statements (`thm:rational-group-chunk`,
`thm:six-point-group`, `lem:affine-action`) and the chart and reconstruction
steps built on them. The supplementary non-goals cannot erase
these obligations. Completing `GroupConfig` does not by itself make the original
group, chunk, action, chart or reconstruction results complete, and it must not
be described as doing so.

On main are the following established layers. This lists layers; it does not
certify every auxiliary statement in the corresponding source sections.

- the universal-domain, rank, automorphism, locus and dimension foundations;
- fields of definition and canonical bases;
- codes, quasi-rational expressions and germ varieties;
- germ representatives, graph ideals, automorphisms, evaluation and composition;
- independent generic conjugacy, definable values and triple germs;
- the Hrushovski–Weil group and faithful transitive homogeneous space;
- the final-base rank, one-orbit and two-product properties of its generic elements;
- constructible group, stabilizer and homogeneous-space presentations on the actual canonical
  code, after internally chosen two-stage generic sampling;
- extraction of those data from a configuration after finite independent base extension;
- arbitrary small ACF base change, with the group and homogeneous space preserved;
- descent of independent parameters in constructible relations;
- the configuration predicate and its invariance;
- constructible sets, with Chevalley's theorem and generic quantification;
- the clause-(i)–(iv) form of `prop:psi-gc` and full `cor:psi`, including the actual
  constructible presentations, original-base freshness and final-base rank/orbit conclusions.

For the last item, all configuration clauses with group rank two and space rank
one are derived from `QWitness.PsiCore`, precisely clauses (i)–(iv), in a
universal ACF ambient
([AclGeom/Config/ConfigurationInput.lean](AclGeom/Config/ConfigurationInput.lean)).
A canonical universal ACF lift
([AclGeom/Config/UniversalConfigurationInput.lean](AclGeom/Config/UniversalConfigurationInput.lean))
applies to a Ψ witness over arbitrary original fields. It produces the
configuration in its chosen universal extension, not in the original $K$.
The core clauses also lift, and the configuration is proved on the literal
images of the original six displayed tuples under the canonical embedding
([AclGeom/Config/UniversalImageConfigurationInput.lean](AclGeom/Config/UniversalImageConfigurationInput.lean)).

The precise `thm:main` of part 08 is proved in
[GroupConfig/Main.lean](GroupConfig/Main.lean). Its conclusion constructs actual
Hrushovski–Weil data, three difference germs and their action values, with the
six points interalgebraic with the input over a finite independent extension.
The homogeneous space has a faithful transitive action. The arbitrary-small-ACF
base-change package transports the actual loci to fresh representing tuples;
it preserves the generic and difference sets, group and homogeneous space.
[GroupConfig/Descent.lean](GroupConfig/Descent.lean) proves the parameter-descent
theorem for constructible relations. The stronger degree-only usage claim is refuted in
[GroupConfig/ClosureCounterexample.lean](GroupConfig/ClosureCounterexample.lean), with original
provenance and the fixed-formula correction on [#31](https://github.com/adamtopaz/acl_geom/issues/31).
Fixed finite polynomial and quasi-rational witness formulas, with their coefficients and
nonvanishing conditions retained, have constructible satisfaction predicates by the existing
polynomial, graph and quantifier theorems. This does not by itself descend the application
witnesses or recover their independence.
[GroupConfig/MainConstructible.lean](GroupConfig/MainConstructible.lean) proves the combined
`thm:main-informal` on those same data: for every generic base point it chooses the canonical
family and fresh samples internally, proves combined-parameter independence over the original
base, and obtains the actual group, stabilizer and homogeneous-space presentations. The
final-base rank, orbit and two-product conclusions use the rank of the original input tuple.
The finite supporting audit on #29 is complete; these results do not certify every auxiliary
statement in the sources.

[GroupConfig/Constructible/CanonicalPresentation.lean](GroupConfig/Constructible/CanonicalPresentation.lean)
proves `thm:constructible` for every Hrushovski–Weil datum of bijections, in particular
the one supplied by the main theorem. It chooses the family on its literal canonical code, derives equal dimension
from invertibility, and chooses both sampling stages internally. The actual group, stabilizer
and homogeneous-space presentations have the source coefficient fields and retain the
generic-point provenance, joint ranks and freshness from any prescribed small field. These
are constructible quotient presentations in the source sense. Original algebraization, action
classification and original-field chart/action descent remain obligations.

[GroupConfig/Psi.lean](GroupConfig/Psi.lean) applies the precise main theorem to
`QWitness.PsiCore` over an ACF universal domain, obtaining the rank-two group of
germs acting on a curve up to interalgebraicity.
[GroupConfig/PsiConstructible.lean](GroupConfig/PsiConstructible.lean) specializes the
general configuration theorem with constructibility on the same actual data. It chooses a
generic base point and both sampling stages internally, proves freshness of the combined
parameters over the original base, and states the rank-two, one-orbit and two-product
conclusions over the literal
final algebraically closed base. The group, stabilizer and homogeneous-space presentations
have the source fields. These theorems do not algebraize the group or descend the chart/action
to the original fields.

Open:

- auxiliary source statements outside the completed finite #29 audit, including the canonical-base,
  translation and nonfaithful-action examples, the five-copy parameter rank, GC4 necessity, the
  finite-ambient germ-collapse assertion and general base-algebraic-closure invariance;
- the fixed formulas and independence argument needed for the application's descent,
  and the source's definability-in-families assertions for rank and connectedness;
- descending the chart and action to the original fields.

The proved Q′ route bypasses group extraction, but the group configuration
statements remain obligations under the rules above.

## Fidelity and collaboration

Preserve the refutations and corrections in [#22](https://github.com/adamtopaz/acl_geom/issues/22),
[#23](https://github.com/adamtopaz/acl_geom/issues/23),
[#25](https://github.com/adamtopaz/acl_geom/issues/25),
[#27](https://github.com/adamtopaz/acl_geom/issues/27) and
[#31](https://github.com/adamtopaz/acl_geom/issues/31). Keep recorded proof gaps
distinct from false statements: the tensor-domain sketch
([#11](https://github.com/adamtopaz/acl_geom/issues/11)), the inference from infinite
absolute degree to independence ([#5](https://github.com/adamtopaz/acl_geom/issues/5)),
and the generic evaluation-map dimension argument
([#21](https://github.com/adamtopaz/acl_geom/issues/21)) do not themselves supply
their advertised conclusions.
Report an error with evidence on an issue before changing the source.

Follow [AGENTS.md](AGENTS.md). Both agents coordinate through chit, agree on
ownership before editing, and use one monitored Lean/Lake family at a time.
Prefer existing Mathlib APIs and prove only source results or reusable lemmas
with named mathematical consumers. Commit and push at natural green
checkpoints, after full library/book validation, and report on the relevant
issues. All communication with Adam is through issues on this repository;
GitHub activity stays within the repository.

## Keeping this goal current

Either agent may update this entire document as the project evolves. Coordinate
the editor through chit, keep changes reviewable, and record the review date
and the issue or evidence behind a genuine change in targets, dependencies,
critical path or completion criteria. Routine progress belongs in issues and
[CONTINUATION.md](CONTINUATION.md); do not grow a checkpoint diary here.

Read this goal and the current issues when resuming work. Adam's instructions
take precedence; `AGENTS.md` governs working rules, this file the shared
objective and completion criteria, and `CONTINUATION.md` the detailed handoff.
Changing a plan must not silently weaken the intended mathematical result.
Any proposed narrowing must be justified on a repository issue in the same
change; editing this file cannot make an unresolved obligation complete.
