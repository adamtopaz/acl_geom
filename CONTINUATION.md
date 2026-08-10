# Continuation guide

This document lets a fresh agent (or human) pick up the formalization
with no prior context and carry it to completion. Read this file, then
the issue tracker, then start working.

## What this project is

A Lean 4 formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem. The mathematical source of truth is
`sources/blueprint.tex`. The library lives in `AclGeom/`, a Verso book
documenting it lives in `AclGeomBook/` (built with `lake exe book`).
Toolchain: see `lean-toolchain`; verso is pinned to the nearest minor
tag of the toolchain (currently v4.32.0 for toolchain v4.32.2).

## How work is coordinated

- **All coordination happens on GitHub issues** of `adamtopaz/acl_geom`.
  Adam reads the issues, the code, and the generated Verso page; he
  steers by commenting on issues. Check for new comments from Adam at
  the start of every work session and treat them as top priority.
- Issue map: #1 coordination, #2–#10 milestones M0–M8, #11 M3a
  regularity brick, **#12 M4a design — the active issue**, and #13
  M4b function-field curve theory (completed).
- Do not add a Claude signature or Claude attribution to issue comments.
  Current Codex progress comments are left unsigned.
- Post a progress comment on the relevant milestone issue after each
  substantive push.

## Hard policies

- **Never leave `sorry` on `main`** outside files whose module
  docstring marks them WIP. (Currently no file contains sorries.)
- **Never axiomatize blueprint theorems.** Everything is proved.
- Verify with `lake build` (or `lake build <module>`); never trust
  `lake env lean` alone. Run a full `lake build` before every commit.
- Keep `lake exe book` building; grow the book alongside the code.
- Never `cd` into `.lake/packages/*` — lake builds whatever package
  the cwd is in.
- Commit and push in small verifiable increments, always green.

## State of the library (all built, CI green)

### Foundations (earlier milestones)
- M0 skeleton/CI done; M1–M3 lattice/pregeometry layers done through
  the "hard kernel" (see issues #3–#5, #11); M4 partially done (#6).
  The curve theory below is M4b (#13), the completeness half of the
  configuration layer, targeting blueprint Lemma 8.4.

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

## THE ACTIVE TASK: M4a — finite-cover field action and algebraization

P6 and P7 are complete in the library: regular-derivation rigidity,
infinitesimal automorphisms, genus-zero rationality, rational-function-field
automorphisms, Möbius normalization, and the algebraic affine-action
endgame all compile and are documented.  Issue #12 is active again.

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

**Next exact step:** turn the selected relational multiplication and inverse
into dominant rational maps on one common positive-dimensional normalized
parameter cover.  Items 25--27 put the four normalized based projections on
one literal source and target and identify every generic-point map with an
explicit field embedding.  Item 28 provides the faithful semantic
field-equivalence target and one strict selected composition triangle.
Items 29--34 give four strict finite-normal-cover curve triangles, the exact
semantic target for aligning them, and one formal curve source shared by all
four embedded loci over one eight-input coefficient field.  Enlarge their
four source covers to one common finite normal compositum and transport it
through the four actions.  Use equality of the repeated branch loci and
canonical-curve-coefficient faithfulness to identify the resulting middle
and target covers coefficient-compatibly.  This constructs the Ψ-specific
`ReferenceAlignment` with
coefficient-compatible equivalences to three reference fields.  Then apply
its literal cancellation theorem
and canonical-curve-coefficient faithfulness to identify the four displayed
parameter field embeddings.  Use that equality to prove that
`toReferenceC` factors through `toReferenceE`, `toReferenceA`, and
`toReferenceB`.  This is the precise auxiliary-`s` independence statement:
the factorization must descend to the intrinsic two-input germ chart, not
merely hold on the eight-input relational source.  Then extract
multiplication and inverse on that single chart with strict rational
identities.
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

- **M4** (#6, #12): algebraize the finite-normal-cover rank-two group and
  its rank-one normal kernel; apply affine-action classification; prove
  affine-grid extraction and both directions of Q/Q'/J correctness.
- **M5** (#7): T1--T3 and the main descent direction are present.  Finish
  the four-way T4 wiring after M4 supplies the ACF correctness theorems.
- **M6–M8** (#8--#10): Frobenius classes and generic arithmetic, ratio
  field interpretation, base/point recovery, Frobenius kernel, public
  theorem variants, and the functorial quotient formulation.
- **Book**: the curves chapter covers P1--P7 through infinitesimal
  rigidity, and the configurations chapter follows the current M4a
  boundary.  Keep both synchronized.  Verso requires docstrings on every
  referenced declaration *and its structure fields*.

## Lean gotchas (hard-won; read before writing proofs)

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

If running as a self-paced loop: each iteration (1) check
`gh issue list` / recent comments on adamtopaz/acl_geom for steering,
(2) do one small verifiable increment, (3) full `lake build`, commit,
push, (4) leave an unsigned progress comment on the active issue, (5)
keep the book building. CI runs on push (build + Pages deploy;
back-to-back pushes can race the Pages deployment — harmless, next
push redeploys).
