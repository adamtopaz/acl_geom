# Shared project goal

Last reviewed: 2026-10-13. Mathematical baseline:
[8d01b03](https://github.com/adamtopaz/acl_geom/commit/8d01b03991aa0bf2125eef63b6751197dbb1fd7a),
with [exact green CI](https://github.com/adamtopaz/acl_geom/actions/runs/38464730779).
Jointly maintained by `aclgeom.codex` and `aclgeom.claude`.

## Objective

Complete the Lean 4/Mathlib formalization of the mathematical content of
[sources/blueprint.tex](sources/blueprint.tex): the Evans–Hrushovski–Gismatullin
reconstruction theorem, its auxiliary results, and its stated variants and
functorial consequences. Produce unconditional public theorems under the
blueprint's genuine hypotheses, a matching Verso exposition, and reproducible
validation. Preserve the provenance and justified corrections of source errors.

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
| Geometric Q′ | Prove the ACF multiplication-diagram converse/completeness, rather than supply semantic representatives. [#6 G4](https://github.com/adamtopaz/acl_geom/issues/6). |
| Geometric J and transfer | Use the proved Q/Q′ assembly to discharge `JCompletenessACF`, then complete the arbitrary-field descent obligations. [#6 G5](https://github.com/adamtopaz/acl_geom/issues/6), [#7](https://github.com/adamtopaz/acl_geom/issues/7). |
| Reconstruction and variants | Remove open completeness inputs from reconstruction and finish the endpoint's public variants and functorial consequences. [#8](https://github.com/adamtopaz/acl_geom/issues/8), [#9](https://github.com/adamtopaz/acl_geom/issues/9), [#10](https://github.com/adamtopaz/acl_geom/issues/10). |
| Remaining source mathematics | Resolve correspondence composition over nonclosed function fields, packaged generic extension, group chunks, six-point configurations, affine actions and the remaining subgroup/correspondence results. [#5](https://github.com/adamtopaz/acl_geom/issues/5), [#12](https://github.com/adamtopaz/acl_geom/issues/12), [#13](https://github.com/adamtopaz/acl_geom/issues/13), [#21](https://github.com/adamtopaz/acl_geom/issues/21). |

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
proof. A direct Q′ route using the literal semantic ratio, a fixed-field
ambient automorphism and the proved multiplicative correspondence theorem
would derive Q′ completeness from guarded Q completeness, bypassing group
extraction for Q′; it is not yet proved in Lean. Audit the needed targets and
dependencies before investing in group, chunk or action infrastructure. No
route is declared sufficient without proofs.
The frozen 117-item M4a chain is historical, not a list of deliverables. Related
source statements remain owed; revisiting frozen code requires a concrete
mathematical purpose and agreed ownership.

## Fidelity and collaboration

Preserve the refutations and corrections in [#22](https://github.com/adamtopaz/acl_geom/issues/22),
[#23](https://github.com/adamtopaz/acl_geom/issues/23),
[#25](https://github.com/adamtopaz/acl_geom/issues/25) and
[#27](https://github.com/adamtopaz/acl_geom/issues/27). Keep recorded proof gaps
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
