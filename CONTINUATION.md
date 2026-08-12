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

**Next exact step:** turn the selected relational multiplication and inverse
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
