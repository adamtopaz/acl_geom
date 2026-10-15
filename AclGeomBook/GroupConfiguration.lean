/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import VersoManual
import GroupConfig
import AclGeom.Config.CanonicalBaseInput
import AclGeom.Config.ConfigurationInput
import AclGeom.Config.PsiNonfaithfulObstruction
import AclGeom.Config.UniversalConfigurationInput
import AclGeom.Config.UniversalImageConfigurationInput

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Group configuration: foundations" =>

%%%
tag := "group-configuration-constructibility"
%%%

The separate `GroupConfig` library follows the supplemental
`sources/group_configuration_blueprint.tex`. That document gives an informal
group-configuration proof and records the remaining algebraization and
application boundaries. Its full Lean formalization remains open (#12).

The library proves the following rank, universal-domain, dimension, locus and constructibility
foundations, and extracts a group of germs and its faithful transitive
homogeneous space from a six-point configuration after finite independent
base extension. A further generic extension gives constructible group and
homogeneous-space presentations, constructed below.

# Rank, independence and fresh tuples
%%%
tag := "group-configuration-rank"
%%%

Over a base set $`C`, rank is the extended natural-number rank in the
algebraic-independence matroid over $`k(C)`. Independence of sets means that
every finite subset preserves its rank on adjoining the other set to the base.
The tower law, finite character, closure invariance, symmetry, transitivity,
independent closure intersection and independent base change are proved for
arbitrary fields. Cancellation in extended natural numbers uses finite ranks.

{docstring GroupConfig.erk}

{docstring GroupConfig.IndepOver}

{docstring GroupConfig.erk_union_eq}

{docstring GroupConfig.IndepOver.racl_inter_eq}

{docstring AlgebraicIndependent.matroid_eRk_eq_toENat_trdeg}

A small set has finite rank. The universal-domain hypothesis explicitly
requires infinite transcendence degree over the base. It gives fresh tuples
of every finite rank over any small set, using finite generators for its
algebraic closure. Algebraic closedness is unnecessary for these lemmas.

{docstring GroupConfig.UniversalDomain}

{docstring GroupConfig.IsSmall.exists_finite_racl_eq}

{docstring GroupConfig.exists_erk_range_eq}

Automorphisms preserve the relative matroids, ranks and independence.

{docstring GroupConfig.erk_image}

{docstring GroupConfig.IndepOver.image}

# Dimension and generic loci
%%%
tag := "group-configuration-locus"
%%%

A surjection of domains over a field with a nonzero kernel strictly decreases
finite transcendence degree. Lifting a transcendence basis from the target and
using algebraicity forces the kernel to meet the polynomial ring on that basis,
contradicting its injectivity there. For finite tuples this proves that proper
containment of vanishing ideals strictly lowers rank. Equal ranks therefore turn
a containment of their vanishing ideals into equality.

{docstring Algebra.trdeg_lt_of_surjective_of_ker_ne_bot}

{docstring GroupConfig.erk_lt_of_idealOf_lt}

The locus ideal extends a tuple's vanishing ideal to ambient-field coefficients.
It contracts back to the original ideal, and is prime when its coefficient field
is algebraically closed. Genericity over an intermediate field means that the
vanishing ideal is exactly the extension of the original base ideal.

{docstring GroupConfig.locusIdeal}

{docstring GroupConfig.IsGenericOver}

This exact-ideal premise implies equality of the base ideals, preservation of
rank, and independence from the larger coefficient field for finite tuples.
Genericity descends to smaller intermediate fields. In an algebraically closed
ambient field, any two finite generic tuples are conjugate over their common
coefficient field.

{docstring GroupConfig.IsGenericOver.erk_coe_eq}

{docstring GroupConfig.IsGenericOver.indepOver}

{docstring GroupConfig.IsGenericOver.exists_algEquiv}

For finite tuples, the locus of an existing tuple over an algebraically closed
base has a generic point over every finite-rank intermediate field in an
algebraically closed universal domain. The proof embeds the abstract generic
point into the ambient field: relocate a finite transcendence basis to fresh
elements and extend the resulting embedding algebraically. Combining this witness
with dimension drop proves that independence is equivalent to an unchanged locus.

{docstring GroupConfig.exists_isGenericOver}

{docstring GroupConfig.isGenericOver_self_iff}

Every finite tuple also has a conjugate over a small algebraically closed subfield
that is independent from any specified small set.

{docstring GroupConfig.exists_algEquiv_indepOver}

The theorem above constructs points of represented base loci. The arbitrary-prime
formulation is proved below in `PrimeLocus`. Universal-domain and smallness
hypotheses remain explicit. These results do not extract a group from a configuration.

# Points of represented loci
%%%
tag := "group-configuration-locus-points"
%%%

A point of a represented locus satisfies every polynomial in its locus ideal.
For a finite tuple over an algebraically closed base, its rank over a small
intermediate field is at most the dimension of that locus; equality is
precisely genericity. The ambient field is an algebraically closed universal
domain. For a generic point over a small algebraically closed field,
genericity over a larger small field is equivalent to independence from it.
Adjoining coordinates algebraic over that field and the generic point does
not change rank. Arbitrary prime ideals are realized by the following theorems.

{docstring GroupConfig.InLocus}

{docstring GroupConfig.erk_le_of_inLocus}

{docstring GroupConfig.isGenericOver_iff_erk_eq}

{docstring GroupConfig.IsGenericOver.isGenericOver_iff_indepOver}

{docstring GroupConfig.erk_union_eq_of_subset_racl_of_isGenericOver}

Every prime polynomial ideal over a field in a universal ACF domain is realized
by an actual generic tuple. Extending a prime ideal defined over a small
coefficient field gives the source's arbitrary-variety form. Genericity descends
to a smaller field over which the ideal is defined. To compare dimensions over
two small fields, a new generic point is chosen over their common closure;
the old points need not remain generic there.

{docstring GroupConfig.exists_idealOf_eq_of_isPrime}

{docstring GroupConfig.exists_locusIdeal_eq_of_isSmall}

{docstring GroupConfig.locusIdeal_eq_of_le}

{docstring GroupConfig.erk_eq_of_locusIdeal_eq}

# Fields of definition of subspaces
%%%
tag := "group-configuration-subspace-field-of-definition"
%%%

In a finite coordinate space over any field, the pivot indices of a subspace
are the possible first nonzero coordinates of its vectors. Projection to these
coordinates is injective and has the same dimension as the subspace. Its inverse
constructs a unique reduced row echelon basis. The resulting matrix satisfies
Mathlib's reduced-row-echelon predicate.

{docstring GroupConfig.pivotEquiv}

{docstring GroupConfig.rref_isReducedRowEchelon}

Any finite ordered basis satisfying the reduced-row-echelon predicate is this
canonical basis under the increasing bijection with its pivot indices. Its
pivot set is derived from the basis and the dimension, rather than supplied.

{docstring GroupConfig.eq_rref_of_basis_isReducedRowEchelon}

The field-valued part is the actual intersection with the coordinate space over
that field. Its tensor product maps canonically into the ambient coordinate
space. The image is precisely the span in the definition of field-definedness;
for finite coordinates the map is injective and gives the literal scalar
extension isomorphism, with its value on pure tensors.

{docstring GroupConfig.coefficientFieldPart}

{docstring GroupConfig.definedOver_iff_coefficientExtension_range}

{docstring GroupConfig.DefinedOver.exists_coefficientExtensionEquiv}

The field generated by the finitely many coordinates of this basis is the
smallest field over which the subspace is defined. Here defined over a subfield
means spanned by vectors whose coordinates lie in that subfield. No algebraic
closedness or universal-domain hypothesis is needed.

{docstring GroupConfig.fod}

{docstring GroupConfig.definedOver_iff}

{docstring GroupConfig.exists_finset_closure_eq_fod}

A field automorphism transports this field of definition along with the subspace.
It preserves the subspace exactly when it fixes the field of definition pointwise.

{docstring GroupConfig.map_eq_self_iff}

Fields of definition of polynomial ideals and canonical bases are constructed below.

# Fields of definition of polynomial ideals
%%%
tag := "group-configuration-ideal-field-of-definition"
%%%

An ideal in a finite-variable polynomial ring is defined over a subfield when
its polynomials with coefficients in that subfield generate the ideal. Its
bounded-degree pieces are finite-coordinate subspaces. The ideal is defined
over a field exactly when every such subspace is defined over that field.
Coefficientwise linear projections along a basis of the ambient field recover
the original polynomial, preserve degree, and preserve extended ideals.

{docstring GroupConfig.IdealDefinedOver}

{docstring GroupConfig.idealDefinedOver_iff_forall_degSubspace}

Definedness of a degree piece implies definedness of every lower degree piece,
and their fields of definition increase with degree. This holds even though
the coordinate spaces have different sizes. Noetherianity supplies a bounded
degree piece generating the ideal, and every larger piece detects exactly the
fields defining the ideal.

{docstring GroupConfig.degSubspace_definedOver_of_le}

{docstring GroupConfig.fod_degSubspace_mono}

{docstring GroupConfig.exists_forall_idealDefinedOver_iff}

The increasing union of these fields is the smallest field defining the ideal.
The union stabilizes at a bounded degree piece, so it has a finite set of
generators over the prime field. Automorphisms transport this field together
with the ideal; an automorphism preserves the ideal exactly when it fixes the
field of definition pointwise. These results hold over arbitrary fields.

{docstring GroupConfig.idealFod}

{docstring GroupConfig.mem_idealFod_iff}

{docstring GroupConfig.idealDefinedOver_iff}

{docstring GroupConfig.exists_forall_idealFod_eq}

{docstring GroupConfig.exists_finset_closure_eq_idealFod}

{docstring GroupConfig.idealFod_map}

{docstring GroupConfig.ideal_map_eq_self_iff}

Scalar extension preserves the field of definition, transported along the
coefficient embedding. The actual scalar-extended subspace has the mapped
RREF basis, and every degree piece of an extended ideal is the scalar
extension of the original piece. This holds for arbitrary fields.

{docstring GroupConfig.exists_rref_spanMap}

{docstring GroupConfig.degSubspace_map_algebraMap}

{docstring GroupConfig.idealFod_map_algebraMap}

# Dropping polynomial variables
%%%
tag := "group-configuration-contraction"
%%%

For any field extension, contracting an extended polynomial ideal along an
injective renaming of variables gives the extension of its contraction.
Coefficient projections along a basis of the field extension commute with
that renaming. This includes dropping a group of variables, and supplies the
projection step for the later germ graph ideals. Neither algebraic closedness
nor a universal domain is needed.

{docstring GroupConfig.coordPoly_rename}

{docstring GroupConfig.comap_rename_map_eq}

# Canonical bases
%%%
tag := "group-configuration-canonical-base"
%%%

The canonical base of a finite tuple over a subfield is the field generated
over the original base by the field of definition of its locus ideal. It lies
in the coefficient field and has finite rank, because the ideal's field of
definition has a finite generating set.

{docstring GroupConfig.canonicalBase}

{docstring GroupConfig.canonicalBase_le}

{docstring GroupConfig.isSmall_canonicalBase}

Over a small algebraically closed coefficient field, the tuple has the same
rank over its canonical base as over that coefficient field. For a smaller
algebraically closed field, independence from the coefficient field is
therefore equivalent to containment of the canonical base in the smaller field.
The proof compares locus ideals over the algebraic closure of the canonical
base and uses the proved generic-point independence criterion.

{docstring GroupConfig.erk_canonicalBase_eq}

{docstring GroupConfig.indepOver_iff_canonicalBase_le}

Canonical bases commute with automorphisms. An automorphism over the coefficient
field fixes the canonical base exactly when it preserves the locus, equivalently
when the image tuple is conjugate to the original tuple over that field.

{docstring GroupConfig.canonicalBase_map}

{docstring GroupConfig.fixes_canonicalBase_iff_exists_algEquiv}

The remaining properties identify canonical bases under independent field
extensions, give equality under mutual independence over two fields, and show
that interalgebraic tuples have interalgebraic canonical bases. The two tuples
may have different finite coordinate types. Adjoining an independent set to
the coefficient field also preserves the canonical base.

{docstring GroupConfig.canonicalBase_eq_of_indepOver_of_indepOver}

{docstring GroupConfig.racl_canonicalBase_eq_of_racl_eq}

{docstring GroupConfig.canonicalBase_racl_union_eq}

The ambient field is algebraically closed and the rank/independence properties
use a universal domain and small algebraically closed coefficient fields. The
original base field need not be algebraically closed. These results supply the
canonical-base hypotheses of the configuration route, whose actual group
extraction is proved below. Original algebraization, chart/action descent and
unconditional reconstruction remain open.

# A canonical base outside the point's algebraic closure
%%%
tag := "group-configuration-canonical-base-example"
%%%

The affine-line computation is proved once over any intermediate coefficient
field $`L` containing $`s,s'`, provided $`t` is transcendental over $`L`.
It computes the actual locus ideal and canonical base. The original source
example below is a corollary. Existing finite-coordinate reindexing transports
this calculation to the two-block graph coordinates used by germs; the
$`\mathrm{Fin}\,1 \oplus \mathrm{Fin}\,1` consumer is checked with that API.

{docstring GroupConfig.locusIdeal_affineLine}

{docstring GroupConfig.canonicalBase_affineLine}

For independent $`s,s',t`, the point $`a=(t,st+s')` has rank two. Its locus over
$`L=\operatorname{acl}(s,s')` is the line $`X_2=sX_1+s'`, with canonical base
$`k(s,s')`. But $`s` is outside the algebraic closure of $`a`. Thus a canonical
base need not lie in the algebraic closure of the point. This proves the
source's explicit example in `rem:cb-not-acl`, including the actual locus ideal
and field of definition. The Lean coordinates are numbered zero and one.
Only rank three of the displayed triple is assumed; algebraic closedness and
a universal domain are unnecessary.

{docstring GroupConfig.locusIdeal_line}

{docstring GroupConfig.canonicalBase_line}

{docstring GroupConfig.erk_line}

{docstring GroupConfig.not_mem_racl_line}

{docstring GroupConfig.canonicalBase_line_not_subset_racl}

# Canonical bases of the actual Ψ incidences
%%%
tag := "group-configuration-psi-canonical-bases"
%%%

In an algebraically closed universal domain, clauses (i)–(iv) of the actual
$`\Psi` witness, through its atom-freeness clauses, force the canonical bases of
the incidence pairs to
recover the full parameter planes. The relative algebraic closures of
$`\operatorname{Cb}(X,Y/A)`, $`\operatorname{Cb}(Y,Z/B)` and
$`\operatorname{Cb}(X,Z/C)` are respectively $`A`, $`B` and $`C`.

Cb1 and the finite-rank tower law first make the target point algebraic over
the source point and the canonical base. A canonical base contained in an
atom would then contradict the witness's freeness clause. The proved
rank-two lattice criterion identifies its closure with the whole plane.
The canonical-base containments are derived from $`\Psi`; they are not extra
hypotheses supplied by the caller.

{docstring AclGeom.QWitness.PsiCore.racl_canonicalBase_XY_eq_A}

{docstring AclGeom.QWitness.PsiCore.racl_canonicalBase_YZ_eq_B}

{docstring AclGeom.QWitness.PsiCore.racl_canonicalBase_XZ_eq_C}

These are the three GC4 clauses for the proposed actual six-point input.
The theorem statements retain ambient algebraic closedness and a universal
domain; the original base field may be arbitrary. The complete sixteen-triple
input and its canonical universal ambient are constructed below, including the
literal image tuples. Finite-ambient chart/action descent remains open. These
identifications do not extract the guarded chart, a group or its action.

# Representatives, graph ideals and germ automorphisms
%%%
tag := "group-configuration-germ-foundations"
%%%

A representative is a quasi-rational expression over a small algebraically
closed coefficient field, defined on every generic source point and sending
it to a generic target point. Representatives are equivalent when they agree
over the closure of both fields. Generic existence and polynomial agreement
prove transitivity; their quotient is the type of germs. Enlarging the
coefficient field gives an equivalent representative.

{docstring GroupConfig.Representative}

{docstring GroupConfig.Representative.Equivalent}

{docstring GroupConfig.Representative.extend_equivalent}

{docstring GroupConfig.Germ}

The graph ideal is independent of the representative. Its contractions to the
source and target variables are the corresponding locus ideals. Its generic
graph point has the source dimension as its rank. Equality of graph ideals
forces equality of germs, by a conjugation fixing the shared source point.
These statements concern represented loci; a separate abstract ideal-dimension
interface is not asserted.

{docstring GroupConfig.Germ.graphIdeal}

{docstring GroupConfig.Representative.erk_graphPoint}

{docstring GroupConfig.Germ.graphIdeal_injective}

The canonical base is the field generated over the base by the graph's field
of definition. A chosen finite generating carrier gives rank and closure
calculations. This carrier preserves the generated field; it is not the
canonical indexed RREF vector and has no claimed global coordinate naturality
or injectivity. The canonical indexed representation is constructed below.

{docstring GroupConfig.Germ.cb}

{docstring GroupConfig.Germ.codeSet}

{docstring GroupConfig.Germ.adjoin_codeSet}

Automorphisms genuinely transport representatives, graph ideals and canonical
bases. They fix a germ exactly when they fix its canonical base pointwise.
Evaluation and composition are developed next. The Hrushovski–Weil group and
extraction from an actual configuration remain subsequent integration layers.

{docstring GroupConfig.Germ.map}

{docstring GroupConfig.Germ.cb_map}

{docstring GroupConfig.Germ.map_eq_self_iff}

# Why the universal domain is essential for germs
%%%
tag := "group-configuration-finite-ambient"
%%%

If the ambient extension has finite transcendence degree, the whole ambient
field is small. A locus of positive rank has no generic point over that
whole field. In an algebraically closed ambient field, every quasi-rational
expression over the whole field therefore gives a vacuous representative,
equivalent to every other representative. The equivalence relation generated
by these comparisons identifies all representatives. This proves the
finite-ambient collapse warning in `rem:finite-trdeg`.

{docstring GroupConfig.isSmall_univ_of_trdeg_lt}

{docstring GroupConfig.not_isGenericOver_of_top_le}

{docstring GroupConfig.Representative.top}

{docstring GroupConfig.Representative.top_equivalent}

{docstring GroupConfig.Representative.eqvGen_equivalent}

This statement concerns the generated equivalence relation. The existing
germ type retains its universal-domain hypothesis, which supplies the generic
points used to prove transitivity of the comparison relation.

# Generic evaluation, composition and independent conjugacy
%%%
tag := "group-configuration-germ-evaluation"
%%%

A germ's value at a generic source point is the unique target coordinate making
a generic point of its graph. A fresh representative proves existence; graph
genericity proves uniqueness. The coefficient field is small and algebraically
closed and contains the canonical base. Evaluation is independent of enlarging
that field and commutes with ambient automorphisms. Equality of values at one
jointly generic source point determines the germ.

{docstring GroupConfig.Germ.eval}

{docstring GroupConfig.Germ.exists_rep}

{docstring GroupConfig.Germ.eval_eq_of_le}

{docstring GroupConfig.Germ.eq_of_eval_eq}

Representatives compose over a common field. This descends to germs, and
evaluation there respects composition. Identities and associativity give a
monoid of self-germs; its units are exactly the germs with two-sided inverses.
Inverse germs are unique, have interalgebraic canonical bases, and preserve
dimension. Definable evaluation and composition at points individually in the
relevant domains are developed below. Literal equality of inverse canonical
bases awaits a later integration layer.

{docstring GroupConfig.Germ.comp}

{docstring GroupConfig.Germ.comp_eval}

{docstring GroupConfig.Germ.comp_assoc}

{docstring GroupConfig.Germ.IsInverse.unique}

{docstring GroupConfig.Germ.IsInverse.racl_cb_eq}

{docstring GroupConfig.Germ.IsInverse.erk_eq}

An orbit of germs has independent members over every small set, unique up to
conjugacy over that set's closure. Their values at independent generic source
points are generic and independent from their canonical bases. The chosen finite
carriers generate those bases; canonical indexed orbit codes are constructed next.

{docstring GroupConfig.Germ.orbit}

{docstring GroupConfig.Germ.exists_mem_orbit_indepOver}

{docstring GroupConfig.Germ.exists_algEquiv_of_mem_orbit}

{docstring GroupConfig.Germ.evalGen}

The independent-conjugacy lemma also holds for arbitrary finite families of
represented loci, including varying coordinate types. Additivity of joint rank
gives independence block by block. Inductively, a conjugation matching the next
block fixes every block already matched. The second statement works over any
small algebraically closed coefficient field.

{docstring GroupConfig.exists_algEquiv_of_erk_iUnion_eq}

{docstring GroupConfig.exists_algEquiv_of_erk_iUnion_eq_of_isGenericOver}

# Definable values and the group generated by a generic orbit
%%%
tag := "group-configuration-definable-germs"
%%%

Definable closure is the perfect closure of a coefficient field inside the
ambient field. Its elements are exactly those fixed by every automorphism
over that field. For a finite tuple, definability is equivalent to being a
quasi-rational value at that tuple.

{docstring GroupConfig.dcl}

{docstring GroupConfig.mem_dcl_iff_forall_fixed}

Automorphisms transport the whole definable closure. Equal definable closures
of arbitrary generating sets give equal algebraic closures. These corollaries
hold for arbitrary fields and sets, with no finiteness or ACF assumption.

{docstring GroupConfig.dcl_adjoin_image}

{docstring GroupConfig.racl_eq_of_dcl_adjoin_eq}

{docstring GroupConfig.exists_quasiRational_of_mem_dclAdjoin}

A Hrushovski–Weil datum is an invertible germ whose orbit is generically
transitive and closed under inversion and independent composition. These
hypotheses give the subgroup of units generated by that orbit: every element
is a product of two orbit members. Generic stabilization, the rank bound and
the maximal-rank criterion follow from the same hypotheses. The quotient
homogeneous space carries a faithful transitive action, and its embedding of
generic points agrees with the generic action of germs.

{docstring GroupConfig.Germ.IsHW}

{docstring GroupConfig.Germ.IsHW.threetwo}

{docstring GroupConfig.Germ.IsHW.prodSubgroup}

{docstring GroupConfig.Germ.IsHW.closure_eq}

{docstring GroupConfig.Germ.IsHW.keyrank}

On a rank-one locus, every member of the actual HW two-product group has a
rational representative: its quasi-rational exponent is zero. In characteristic
zero inverse Frobenius is the identity. In positive characteristic the field of
a generic image is an integral Frobenius twist of the source function field.
The index is independent of representatives and coefficient fields, and adds
under arbitrary composition over a common coefficient field. Independence is
used only for the HW orbit product, forcing its index to satisfy $`d=2d`.
The seed index is therefore zero; products of its conjugates remain rational.

{docstring GroupConfig.relfinrank_map_frobenius_eq}

{docstring GroupConfig.Germ.HasFrobIndex.unique}

{docstring GroupConfig.Germ.HasFrobIndex.mul}

{docstring GroupConfig.Germ.IsHW.exists_rational_representative}

These are actual equal representatives, constructed internally in both
characteristics. The universal-domain hypothesis is retained.

The fraction field of the actual prime locus quotient over the universal
domain is a function field of one variable. A coordinate transcendental over
the original base remains transcendental in this abstract function field over
K. Every other coordinate is algebraic over its simple extension, and the
finitely many coordinates generate the field.

{docstring GroupConfig.LocusFunctionField}

{docstring GroupConfig.LocusFunctionField.isFunctionFieldOneVar}

An exponent-zero representative substitutes its rational fractions into the
coordinates. Evaluation at a point generic over a common coefficient field
proves both directions of the kernel equality with the actual locus ideal.
This gives a field endomorphism, independent of the equal representative.
Substitution reverses composition. Substituting a representative of the inverse
therefore gives a homomorphism from the actual HW group into the K-algebra
automorphisms of this field.

{docstring GroupConfig.Representative.subst_comp}

{docstring GroupConfig.Germ.IsHW.functionFieldAction}

The coordinate formula holds for every equal rational representative of the
inverse. If the field automorphism is the identity, these coordinates force
identity values at all generic points, hence the identity germ. The action
is therefore faithful.

{docstring GroupConfig.Germ.IsHW.functionFieldAction_coord}

{docstring GroupConfig.Germ.IsHW.functionFieldAction_injective}

When the ordinary canonical base of the HW germ has rank at least two, this
actual function field has genus zero over K. The proof works over the ordinary
coefficient field C, not its algebraic or perfect closure. The old function
field is the formal fraction field of the locus over k; extending constants
gives `Frac(C ⊗[k] F)` and `Frac(K ⊗[k] F)`, with the actual coordinate formulas.

{docstring GroupConfig.BaseFunctionField.exists_separating_transcendental}

{docstring GroupConfig.Representative.ker_aeval_graph}

Coefficient derivations extend horizontally, fixing the old function field.
Conjugating by the actual C-automorphism and subtracting gives C-linear curve
variations. Zero variation makes the graph ideal coefficient-stable. Its RREF
field-of-definition code then forces the coefficient derivation to vanish.
Two independent coefficient derivations therefore give two independent regular
curve derivations. Normalization under constant extension and the two affine
charts transfer their regularity to K. Positive genus is excluded by the
regular-derivation rigidity theorems.

{docstring AclGeom.exists_regular_derivations_baseChange}

{docstring GroupConfig.Germ.IsHW.genus_eq_zero}

All comparison, inverse, independence, regularity and one-variable data in
this theorem are derived from the actual HW, curve-rank-one and ordinary
canonical-base-rank-at-least-two hypotheses. Coefficient derivations are never
extended to the perfect ambient field; only the C-linear curve variations are.

Genus-zero rationality now gives one transcendental generator of the same
K-function field in which every element of the HW action is fractional linear.
The formula includes a nonzero determinant and a nonzero denominator. The
one-variable structure and genus zero are supplied by the actual HW data;
no coordinate or rationality certificate is assumed.

{docstring GroupConfig.Germ.IsHW.exists_generator_moebius}

This states the formula for each field automorphism. It does not construct a
scheme action or classify the connected subgroup of projective transformations.
That classification, the affine coordinates, original scheme/action bridge,
normal-subgroup producer, group algebraization and original-field chart/action
descent remain obligations of the original blueprint.

For an orbit of invertible germs between two loci, independent pairs give
difference germs. These form one orbit. The difference and either member of
the pair are interalgebraic over the other member, yielding its rank and
independence criteria. The hypotheses making this difference orbit a
Hrushovski–Weil datum are derived from a configuration in Steps I and II below.

{docstring GroupConfig.Germ.diffSet}

{docstring GroupConfig.Germ.diffSet_eq_orbit}

Generic evaluation lies in the definable closure of the canonical base and
the source point. Every small algebraically closed field containing that base
admits a representative of the germ. Invertibility is equivalent to recovering
the generic source point definably from its value. Composition also evaluates
correctly whenever the point is individually in the domains of the first germ
and the composite, and its first value is in the second germ's domain.

{docstring GroupConfig.Germ.eval_mem_dclAdjoin}

{docstring GroupConfig.Germ.exists_rep_M_eq}

{docstring GroupConfig.Germ.isInvertible_iff_mem_dclAdjoin}

Canonical bases of composites satisfy all three algebraic containments for
germs between different loci. Over the base of either invertible factor, the
composite has the same relative rank as the other factor. The inverse has
exactly the original canonical base and its graph is the coordinate swap.

{docstring GroupConfig.Germ.erk_cb_comp_eq_of_isInverse}

{docstring GroupConfig.Germ.erk_cb_comp_eq_of_isInverse_left}

{docstring GroupConfig.Germ.IsInverse.cb_eq}

{docstring GroupConfig.Germ.IsInverse.graphIdeal_eq}

{docstring GroupConfig.Germ.evalGen_comp_of_indepOver}

For words, invariance under the parameter-field automorphisms gives definable
evaluation; seed germs, composition and inversion preserve this invariance.
The actual parameterized word relations and their constructibility are developed
below, with definedness at every intermediate step.

{docstring GroupConfig.Germ.evalGen_mem_dclAdjoin_of_forall_map_eq}

Finally, a definable triple of a parameter and two generic points gives a
unique germ with the required value and canonical-base bound. Its graph and
canonical base are the locus and canonical base of that pair. This is the
producer needed by the subsequent configuration argument.

{docstring GroupConfig.IsTriple}

{docstring GroupConfig.IsTriple.germ}

An actual expression taking the triple's source to its target is admissible at
the original parameter, and at every conjugate parameter it gives the
corresponding conjugate germ. The expression is supplied as actual data, with
its definedness and value, rather than a representation certificate.

{docstring GroupConfig.IsTriple.exists_parameterGerm_eq}

{docstring GroupConfig.IsTriple.germ_cb}

{docstring GroupConfig.IsTriple.isInvertible_iff}

# The full translation example
%%%
tag := "group-configuration-translation-example"
%%%

Supplemental `rem:connected` gives an example in which the homogeneous space
contains points outside the embedded generic locus. Work over algebraically
closed fields in a universal domain, with a transcendental base point and a
transcendental translation parameter. The following construction proves the
Hrushovski–Weil structure on actual translation germs. Their canonical bases
are the fields generated by their parameters. The generic orbit consists of
translations by transcendental elements, and its two-product group contains
all translations.

{docstring GroupConfig.Germ.translation}

{docstring GroupConfig.Germ.cb_translation}

{docstring GroupConfig.Germ.isHW_translation}

{docstring GroupConfig.Germ.prodSet_translation}

The actual homogeneous space is equivalent to the ambient field. A pair
consisting of a translation by $`a` and a generic point $`y` maps to $`a+y`.
Two pairs are identified precisely when these sums agree. The inverse
equivalence uses the given transcendental base point and allows dependent
point and translation parameters, as required by the definition of a pair.

{docstring GroupConfig.Germ.Translation.rel_iff_pairValue_eq}

{docstring GroupConfig.Germ.Translation.spaceEquiv}

{docstring GroupConfig.Germ.Translation.ofPair_eq_ofPair_iff_add}

The embedding of generic points becomes the inclusion of the transcendental
elements. The total group action becomes addition by the translation
parameter. This action is defined on the whole homogeneous space, including
points at which the corresponding generic germ evaluation is unavailable.

{docstring GroupConfig.Germ.Translation.spaceEquiv_iota}

{docstring GroupConfig.Germ.Translation.range_spaceEquiv_iota}

{docstring GroupConfig.Germ.Translation.spaceEquiv_smul}

For transcendental $`t`, the class $`[-t,t]` maps to zero. If it had a
presentation $`\gamma\cdot\iota(y)` with $`y` independent from the acting
element, compatibility with generic evaluation would make its image
transcendental. Thus the independence requirement cannot be imposed on
presentations of arbitrary homogeneous-space points.

{docstring GroupConfig.Germ.Translation.spaceEquiv_zeroClass}

{docstring GroupConfig.Germ.Translation.zeroClass_ne_smul_iota}

# Canonical codes and actual orbit families
%%%
tag := "group-configuration-canonical-germ-codes"
%%%

A canonical finite code records the RREF coordinates of the graph ideal's
degree pieces, up to its least generating degree. Non-pivot rows are filled
with zeros, giving one index type throughout an orbit. The vector determines
the ideal and generates its field of definition. Its coordinates commute
with automorphisms, and its degree bound is invariant. The code generates a
germ's canonical base and identifies its orbit with the generic points of
the code locus. This is an explicit zero-padded encoding of the source code.

{docstring GroupConfig.codeVec}

{docstring GroupConfig.Germ.code}

{docstring GroupConfig.Germ.adjoin_range_code}

{docstring GroupConfig.Germ.exists_mem_orbit_codeVec_eq}

Transporting a fixed generating tuple of the canonical base distinguishes
exactly the orbit germs. Definability gives one quasi-rational expression over
the base field. Joint conjugation proves that every transported parameter is
actually admissible and that its parameter germ is the corresponding orbit
germ. No family or evaluation identity is supplied as a hypothesis.

{docstring GroupConfig.Germ.exists_orbit_uniformExpression}

{docstring GroupConfig.Germ.exists_orbit_admissibleFamily}

# Admissible parameters, words and fresh samples
%%%
tag := "group-configuration-admissible-parameters"
%%%

Specializing a quasi-rational expression at a parameter gives coefficients in
the algebraic closure of that parameter field. Admissibility means it is
defined at every generic source point and sends those points to generic target
points. It constructs an actual representative and germ. For equal-dimensional
loci, admissibility is equivalent to the defined graph covering every generic
target point. Invertibility is equivalent to uniqueness of each such defined
source-locus fibre. Definedness is present in every fibre condition.

{docstring GroupConfig.QuasiRational.IsAdmissible}

{docstring GroupConfig.QuasiRational.parameterGerm}

{docstring GroupConfig.QuasiRational.isAdmissible_iff_generic_surjective}

{docstring GroupConfig.QuasiRational.isInvertible_parameterGerm_iff}

Ordinary constructible fibres and the proved generic quantifier make both
parameter sets constructible over a finite sampling field. A rank induction
chooses those samples jointly independently from any prescribed small field;
they need not be supplied by the caller.

{docstring GroupConfig.QuasiRational.isConstructibleOver_admissible}

{docstring GroupConfig.QuasiRational.isConstructibleOver_invertibleAdmissible}

{docstring GroupConfig.exists_fresh_genericSamples}

{docstring GroupConfig.QuasiRational.exists_fresh_constructible_admissible_samples}

One field generated by jointly fresh samples from both loci also makes
equality of the actual parameter germs constructible. The source samples
serve the equality quantifier, whose parameter tuple has twice the original
number of coordinates; the target samples serve admissibility and invertibility.
Both families and their cross-independence are produced internally.

{docstring GroupConfig.exists_joint_fresh_genericSamples}

{docstring GroupConfig.QuasiRational.exists_fresh_constructible_parameterRelations}

A typed word uses actual forward and inverse expressions, reading its
parameters from a shared tuple. Its chain relation requires every intermediate
point to lie on its prescribed locus and every expression to be defined at its
argument. At generic source points the chain is unique and evaluates the actual
composite germ. Generic chain agreement is therefore equivalent to germ equality.

{docstring GroupConfig.Word}

{docstring GroupConfig.Word.Chain}

{docstring GroupConfig.Word.IsGerm.chain_iff}

{docstring GroupConfig.Word.IsGerm.eq_iff}

The resulting word relations are constructible over a field containing the
specified generic samples. The source form requires every factor, including
forward factors, to be invertibly admissible, while the target expression is
merely admissible. That full restriction appears in the following theorem.

{docstring GroupConfig.Word.isConstructibleOver_eq_parameterGerm}

The samples for a whole typed word can now be chosen internally, fresh from any
prescribed small field. At each letter, its required locus is sampled over the
closure of the field and all preceding samples. Joint source and target samples
then serve the final equality relation. The caller supplies no sampling certificate.

{docstring GroupConfig.Word.exists_fresh_samples}

{docstring GroupConfig.Word.exists_fresh_constructible_eq_parameterGerm}

One internally chosen field now serves finitely many heterogeneous typed word
relations. Its generators are coordinates of actual generic points of the
listed loci, with joint rank additivity and freshness from the prescribed
small field. The full source relation restricts every declared expression
family to its invertibly admissible parameters, including families unused
by the word. That restriction is retained in the following theorem.

{docstring GroupConfig.Word.exists_fresh_constructible_sourceRelation_family}

A second stage chooses parameter-locus points generic and independent over
the first sampling field. Both stages remain jointly fresh from the
prescribed field; they serve the group and action relations constructed below.

{docstring GroupConfig.exists_groupSamples}

# Finite tuple codes
%%%
tag := "group-configuration-finite-codes"
%%%

A finite set of tuples is encoded by the monic polynomial whose roots are
the linear forms attached to those tuples. Over a domain this indexed
polynomial determines the set, and injective ring maps transport it naturally.
The scalar coefficient carrier is finite and natural. Fixing its elements
pointwise is equivalent to stabilizing the original tuple set.

{docstring GroupConfig.codePoly}

{docstring GroupConfig.codePoly_injective}

{docstring GroupConfig.codePoly_map}

{docstring GroupConfig.fixes_code_iff}

Over a field, the scalar coefficients lie in the ring generated by the tuple
coordinates. Conversely, each tuple coordinate is algebraic over the field
generated by those coefficients: specialize the variables in the coding
polynomial to a unit vector to obtain a monic polynomial for that coordinate.
Thus both sets generate the same relatively algebraically closed field.
No algebraic closedness or universal-domain assumption is needed.

{docstring GroupConfig.code_subset_adjoin}

{docstring GroupConfig.mem_racl_code}

{docstring GroupConfig.racl_code_eq}

The scalar coefficient carrier discards the monomial indices. Its equality
alone is not asserted to determine the tuple set; that injectivity belongs to
the indexed polynomial and to its finite coefficient vector. That vector uses
the actual pairs of exponents of $`T` and monomials in $`U`, of total degree at
most the cardinality of the tuple set. Homogeneity puts every nonzero
coefficient within that finite index. The nonzero vector entries recover
the scalar carrier, while their positions retain the injective encoding.

{docstring GroupConfig.FiniteSetCode.CodeIndex}

{docstring GroupConfig.FiniteSetCode.codeVec}

{docstring GroupConfig.FiniteSetCode.coeff_coeff_codePoly_eq_zero}

{docstring GroupConfig.FiniteSetCode.range_codeVec_diff_zero}

{docstring GroupConfig.FiniteSetCode.codeVec_injective}

The vector is natural under injective ring maps. Over fields it lies in the
ring generated by the original coordinates, has their same algebraic closure,
and is fixed by an automorphism exactly when the finite tuple set is stable.
The invariant-set hypothesis also puts all entries in the definable closure.
These coefficient indices are distinct from the germ RREF indices.

{docstring GroupConfig.FiniteSetCode.codeVec_map}

{docstring GroupConfig.FiniteSetCode.fixes_codeVec_iff}

{docstring GroupConfig.FiniteSetCode.racl_range_codeVec}

{docstring GroupConfig.FiniteSetCode.range_codeVec_subset_dcl}

# Quasi-rational expressions
%%%
tag := "group-configuration-quasi-rational"
%%%

An expression consists of polynomial numerators and denominators and one
Frobenius-root exponent. It is defined where every denominator is nonzero.
In a perfect ambient field its value is the unique root of the resulting
fraction. In characteristic zero the exponential characteristic is one,
so the root operator is the identity. Evaluation commutes with coefficient-field
automorphisms and with enlarging the coefficient field.

{docstring GroupConfig.QuasiRational}

{docstring GroupConfig.QuasiRational.IsDefinedAt}

{docstring GroupConfig.QuasiRational.eval}

{docstring GroupConfig.QuasiRational.eval_comp}

Two expressions agreeing at a generic point over a common coefficient field
agree on every point of the represented locus where both are defined. A
polynomial obtained by clearing denominators lies in the generic point's
vanishing ideal and hence vanishes throughout the locus.

{docstring GroupConfig.QuasiRational.eval_eq_of_eval_eq}

Frobenius-twisting coefficients and clearing denominators constructs a
composite expression. It is defined on the natural composition domain and
there evaluates to the composed values. Its expression domain may be larger;
no equality with the natural composition domain is claimed.

{docstring GroupConfig.QuasiRational.comp}

{docstring GroupConfig.QuasiRational.isDefinedAt_comp}

{docstring GroupConfig.QuasiRational.comp_eval}

For finitely many output coordinates, the domain is constructible over the
coefficient field. The graph is constructible as well: its equations are
$`w_j^{p^e}Q_j(u)=P_j(u)`, together with $`Q_j(u)\ne0`. Graph evaluation
uses perfection of the ambient field; neither result needs algebraic
closedness, a universal domain or smallness. These are building blocks for
the admissible-parameter and typed germ-word relations proved above, with their
explicit sample hypotheses and fresh-field producers. The definable-closure
characterization is proved in `DefinableClosure`.

{docstring GroupConfig.QuasiRational.isConstructibleOver_domain}

{docstring GroupConfig.QuasiRational.isConstructibleOver_graph}

For any coefficient subfield of an ACF ambient, a scalar orbit is finite exactly
when the element is algebraic. All transcendental elements form one orbit. The
finite-tuple criterion holds coordinate by coordinate. Algebraic conjugate sets
are finite, their scalar coefficient carriers lie in definable closure, and the
carriers have the required algebraic-closure and definable-value properties.
The finite coefficient-vector forms are proved in `FiniteSetCode`. They retain
coefficient positions; the scalar carrier discards them, and the germ RREF
vector uses different indices.

{docstring GroupConfig.finite_orbit_iff}

{docstring GroupConfig.orbit_eq_of_transcendental}

{docstring GroupConfig.finite_orbit_tuple_iff}

{docstring GroupConfig.conjCode_subset_dcl}

{docstring GroupConfig.mem_dclAdjoin_conjCode}

# Six-point configuration data
%%%
tag := "group-configuration-six-point-data"
%%%

A configuration consists of six tuples with four specified lines. The group
points are $`a,b,c`, the space points are $`x,y,z`, and the lines are
$`abc`, $`axy`, $`byz` and $`czx`. Its hypotheses give algebraic-closure
incidences, independence of each noncollinear triple, the three canonical-base
containments, and positive group rank.

{docstring GroupConfig.GroupConfiguration}

The incidence table has exactly sixteen sorted noncollinear triples. Checking
those triples gives the full independence clause. Pairwise independence and
equality of the three group ranks and of the three space ranks follow from
the configuration hypotheses.

{docstring GroupConfig.indep_of_sixteen}

{docstring GroupConfig.GroupConfiguration.indepOver_pts}

{docstring GroupConfig.GroupConfiguration.erk_b_eq}

{docstring GroupConfig.GroupConfiguration.erk_y_eq}

Canonical bases are invariant under permuting coordinate variables. This
makes the configuration stable under the two generating relabelings of its
space lines, under base-field automorphisms, and under interalgebraic replacement
of the six tuples. Coordinate types may differ after replacement.

{docstring GroupConfig.canonicalBase_comp_equiv}

{docstring GroupConfig.GroupConfiguration.swapAB}

{docstring GroupConfig.GroupConfiguration.swapBC}

{docstring GroupConfig.GroupConfiguration.map}

{docstring GroupConfig.GroupConfiguration.ofRaclEq}

The full rank table now includes positive space rank, $`m \le n`, the three
line ranks, the total rank $`2n+m`, and all twelve point-versus-line
independence statements. The positive-rank proof lives beside this table,
without a dependency on the main group-extraction theorem.

{docstring GroupConfig.GroupConfiguration.one_le_erk_x}

{docstring GroupConfig.GroupConfiguration.erk_x_le_erk_a}

{docstring GroupConfig.GroupConfiguration.erk_abcxyz}

{docstring GroupConfig.GroupConfiguration.indepOver_x_abc}

Conversely, actual Hrushovski–Weil data produce the six-point configuration
on the canonical zero-padded RREF code vectors, with both ranks and the action
identities. Its inverse and third germ are chosen internally. This constructs
a configuration from existing group data; extraction of the group from an
arbitrary configuration is proved below.

{docstring GroupConfig.Germ.IsHW.groupConfiguration_code}

Independent base change preserves configurations. The definability step
constructs a new configuration, pointwise interalgebraic over a finite
independent extension, with the selected incidence definable. The conjugate-code
and definability-step conclusions are stated at all three space points.

{docstring GroupConfig.GroupConfiguration.baseChange}

{docstring GroupConfig.GroupConfiguration.racl_conjCode_x}

{docstring GroupConfig.GroupConfiguration.racl_conjCode_y}

{docstring GroupConfig.GroupConfiguration.exists_defStep}

{docstring GroupConfig.GroupConfiguration.exists_defStep_x}

{docstring GroupConfig.GroupConfiguration.exists_defStep_y}

# From a configuration to a group of germs
%%%
tag := "group-configuration-main"
%%%

Step I iterates the definability step over fresh independent extensions.
Step II constructs the actual germ from a definable incidence and proves the
Hrushovski–Weil bijection hypotheses. Step III constructs three difference
germs and a generic point whose standard configuration is interalgebraic
with the original six points. The finite independent extension and all
germs are conclusions of the theorem.

The construction also proves the parameter count in supplemental `rem:params`.
Write $`n` for the rank of the original group tuple $`a` over $`k`.
Step I chooses three generic copies of group points. Independence and
preservation of group ranks under each base change give total parameter
rank $`3n` over $`k`.

{docstring GroupConfig.GroupConfiguration.exists_stepI_with_parameterRank}

{docstring GroupConfig.GroupConfiguration.exists_isHWBij}

{docstring GroupConfig.IsMainConclusion}

Step III chooses two further copies over the base obtained in Step I.
Their automorphisms preserve the ranks of the copied group points, so
these new parameters have relative rank $`2n`. The tower law gives a
finite set $`E`, independent from the original six points, with rank
$`5n` over the original base $`k` and the actual main conclusion over
$`\operatorname{acl}(k,E)`.

{docstring GroupConfig.GroupConfiguration.exists_stepIII_with_parameterRank}

{docstring GroupConfig.GroupConfiguration.exists_main_with_parameterRank}

This is the rank of the parameters chosen by the construction. The
universal-domain hypothesis is retained. The count supplies no version
over an ambient field of finite transcendence degree, where the germ
representative collapse described above still applies.

The configuration hypotheses also follow from the actual conclusion over a
finite independent base extension. First the configuration of codes and
values transfers to the original interalgebraic tuples. Independent-base
descent then brings every configuration clause back to the original base.
In particular, its GC4 clause for $`a` proves the necessity assertion of
`rem:main-props`. Finiteness of the adjoined set explicitly supplies the
smallness needed for descent.

{docstring GroupConfig.GroupConfiguration.descend}

{docstring GroupConfig.GroupConfiguration.of_isMainConclusion}

The displayed code tuples are finite generators of the canonical bases.
The canonical RREF code vectors generate the same fields; the two tuple
presentations are interalgebraic. The homogeneous space constructed from
the actual germs has a faithful transitive action, and the action identities
of the main theorem follow from its compatibility with generic evaluation.

{docstring GroupConfig.Germ.IsHW.Space}

{docstring GroupConfig.Germ.IsHW.iota}

{docstring GroupConfig.Germ.IsHW.exists_smul_eq}

{docstring GroupConfig.Germ.IsHW.eq_one_of_forall_smul_eq}

{docstring GroupConfig.Germ.IsHWBij.iota_eq_smul}

# Generic group elements over a larger base
%%%
tag := "group-configuration-relative-rank"
%%%

The source's connectedness remark is proved in its stated rank and orbit form.
Let $`n` be the original rank of the canonical base of the Hrushovski–Weil
datum. Over any small intermediate field $`M`, every group element has
canonical-base rank at most $`n`. Equality holds precisely for elements of
the original generic set that are independent from $`M`.

{docstring GroupConfig.Germ.IsHW.erk_base_cb_le}

{docstring GroupConfig.Germ.IsHW.erk_base_cb_eq_iff}

Every group element is a product of two elements of rank $`n` over $`M`,
and any two such elements are conjugate by an automorphism fixing $`M`.
Automorphisms over $`M` preserve this relative rank. These statements apply
to the final sampling field and its algebraic closure; $`M` need not be
algebraically closed, and the originally chosen datum need not be independent
from $`M`. These properties apply to the constructible presentation below.

{docstring GroupConfig.Germ.IsHW.exists_mul_eq_of_mem_prodSet}

{docstring GroupConfig.Germ.erk_cb_map_restrictScalars}

{docstring GroupConfig.Germ.IsHW.exists_algEquiv_of_erk_base_eq}

# Base change and independent parameter descent
%%%
tag := "group-configuration-base-change-descent"
%%%

For an arbitrary small ACF extension, fresh tuples represent the original
loci. Transport to these tuples and base change preserve the generic and
difference sets, with both inclusions proved. The resulting group and
homogeneous space are equivariantly isomorphic to the originals. Old tuples
are not assumed to stay generic over the new field.

{docstring GroupConfig.Germ.baseChange_transport_mem_diffSet}

{docstring GroupConfig.Germ.exists_of_mem_diffSet_baseChange_transport}

{docstring GroupConfig.Germ.IsHW.baseChangeTransportGroupEquiv}

{docstring GroupConfig.Germ.IsHW.baseChangeTransportSpaceEquiv}

A polynomial nonzero on a locus is nonzero at a base-field point. This
density statement descends an actual constructible relation satisfied by
a parameter tuple independent from its other arguments to a tuple in the
algebraically closed base field.

{docstring GroupConfig.exists_kpoint_of_notMem_locusIdeal}

{docstring GroupConfig.descent}

More generally, any nonempty constructible set over an algebraically closed
base has a base-field point. The ambient field can be arbitrary. This follows
by choosing one polynomial cell and applying the same locus-density theorem.

{docstring GroupConfig.IsConstructibleOver.exists_kpoint}

Every actual bounded formula in Mathlib's ring language has a constructible
realization set in an algebraically closed ambient field. Terms are polynomial
expressions; Boolean operations and Chevalley handle implication and universal
quantification. This covers all constructors of the actual syntax.

{docstring GroupConfig.isConstructibleOver_realize}

Consequently, a prescribed embedding between algebraically closed fields is
an elementary embedding with exactly that underlying map. The Tarski–Vaught
proof fixes the old parameters in a polynomial fibre before finding a
base-field point for the new witness. It preserves every finite-arity
first-order ring formula, including arbitrary quantifiers. No universal-domain
or transcendence-degree hypothesis is used.

{docstring GroupConfig.acfElementaryEmbedding}

{docstring GroupConfig.ringHom_realize_iff}

This proves model completeness itself, the logical input cited in
`rem:psi-hyp`(c) and `rem:finite-trdeg`. The application's actual formulas,
independence recovery and original-field chart/action descent remain open.

The source usage remark's original degree-bound claim is refuted on #31, with
provenance in `6b76e01`. A constructible subset of the line is finite or cofinite.
The degree-one polynomial-witness locus over an infinite proper base field is
exactly that field, whose complement contains a translate of the field. It is
therefore not constructible. Constant rational-function witnesses give the same
base-field obstruction. The following Lean statements prove the base-field and
degree-one polynomial cases; the finite/cofinite statement is only a necessary
condition over an arbitrary coefficient field.

{docstring GroupConfig.IsConstructibleOver.finite_or_finite_compl}

{docstring GroupConfig.not_isConstructibleOver_range_algebraMap}

{docstring GroupConfig.setOf_exists_natDegree_le_one_aeval_eq_zero}

{docstring GroupConfig.not_isConstructibleOver_setOf_exists_natDegree_le_one}

The corrected usage fixes actual finite polynomial or quasi-rational formulas,
including their coefficients and nonvanishing conditions. Their satisfaction
relations are constructible by the polynomial-data characterization, polynomial
zero and nonzero loci, quasi-rational graphs, finite Boolean operations and
finite-tuple existential closure below. The existential step requires an
algebraically closed ambient field. Quantifying coefficients over the ambient
field does not restrict them to the base field. The application still needs
its actual fixed formulas and the proof of independence after descent, together
with original-field chart/action descent.

The group and homogeneous-space presentations are constructed below.
Original-field chart/action descent, group algebraization, action
classification and unconditional reconstruction remain obligations.

# The complete actual Ψ six-point input
%%%
tag := "group-configuration-psi-input"
%%%

The actual twenty-one-point $`\Psi` witness now supplies the entire six-point
configuration predicate using only clauses (i)–(iv), packaged as
`QWitness.PsiCore`. The partial quadrangle and meet equations in clauses (v)–(vii)
are unused. This proves the precise source input of supplemental `prop:psi-gc`.
Its three parameter tuples use the displayed pairs
of point representatives, and its three space tuples use representatives of
$`X,Y,Z`. Equal finite ranks give the two parameter-plane incidences and the
three space-line incidences. The rank and freeness clauses force each pair
of space points to have rank two.

Nine noncollinear triples contain two parameter planes and one space point;
they have rank five. Independence from an incidence closure gives the
$`AYZ`, $`BXZ` and $`CXY` triples. The three line equalities give
$`AXZ`, $`BXY` and $`CYZ`. Finally, $`Z` is independent from the closure
of $`A,Y`, which contains $`X,Y`, giving the $`XYZ` triple. These are exactly
the sixteen triples required by the predicate. The canonical-base
identifications above give all three GC4 clauses.

{docstring AclGeom.QWitness.PsiCore}

{docstring AclGeom.QWitness.PsiCore.groupConfiguration}

The resulting group rank is two and the space rank is one; the following
package records those precise values along with the configuration.

{docstring AclGeom.QWitness.PsiCore.groupConfiguration_with_ranks}

The full-witness theorems retain their original statements and apply the core
result through the proved projection.

{docstring AclGeom.QWitness.Psi.toCore}

Only the actual witness is supplied. Ambient algebraic closedness and a
universal domain are explicit; the original base may be arbitrary. The
canonical ambient package below proves those ambient hypotheses internally.
Literal image-tuple comparison is proved below; finite-ambient chart/action
descent remains open. The
initial chart still needs both output guards. The precise main theorem now
applies to this configuration in an ACF universal domain, giving the
interalgebraicity part of the application with group rank two and curve rank one.

{docstring AclGeom.QWitness.PsiCore.exists_isMainConclusion}

The full Ψ application chooses a generic base point and both sampling stages
internally. It proves the combined parameters fresh from the witness over the
original base, and gives the actual constructible group, stabilizer and
homogeneous-space presentations. Its rank-two, one-orbit and two-product
conclusions use the literal final algebraically closed base. All six original
interalgebraicity clauses refer to the same extracted data.

{docstring AclGeom.QWitness.PsiCore.exists_constructibleGroupSpace}

Algebraization, action classification, original-field chart/action descent
and unconditional reconstruction remain separate targets.

# The nonfaithful product-group example
%%%
tag := "group-configuration-nonfaithful-example"
%%%

Supplemental `rem:psi-hyp`(b) shows why the freeness clause (iv) is needed.
For five independent elements $`s,s',t,u,u'`, take the parameter pairs
$`a=(s,u)`, $`b=(s',u')`, $`c=(s'/s,u'/u)` and the space points
$`y=t`, $`x=st`, $`z=s't`. The product of the two multiplicative groups
acts on the line through its first factor. The second factor supplies
nonidentity elements acting trivially. The displayed units satisfy the
literal group identity $`b=c*a` and action identities $`x=a\cdot y`,
$`z=c\cdot x`.

{docstring AclGeom.QWitness.Nonfaithful.firstFactorAction}

{docstring AclGeom.QWitness.Nonfaithful.not_injective_firstFactorAction}

{docstring AclGeom.QWitness.Nonfaithful.model}

The constructed twenty-one-point witness uses the displayed elements for
the nine relevant points. Its other twelve points are all the point of
$`t`; clauses (i)–(iv) do not mention them. All nine rank, incidence and
noncontainment assertions in (i)–(iii) hold over arbitrary fields. The atom
$`A'=\operatorname{acl}(s)` lies in $`A`, and $`X\leq A'\vee Y`, so
clause (iv) fails.

{docstring AclGeom.QWitness.Nonfaithful.witness}

{docstring AclGeom.QWitness.Nonfaithful.witness_psi_i_iii}

{docstring AclGeom.QWitness.Nonfaithful.witness_not_iv}

{docstring AclGeom.QWitness.Nonfaithful.not_psiCore}

Over $`\operatorname{acl}(s,u)`, the pair $`(st,t)` has the line locus
$`X=sY` and canonical base $`k(s)`. Its algebraic closure does not contain
$`u`, which violates GC4 for the first parameter pair. This computation
also holds over arbitrary fields and reuses the shared affine-line proof.

{docstring AclGeom.QWitness.Nonfaithful.not_cb_a}

In an algebraically closed universal ambient field, the actual witness
tuples therefore fail the configuration predicate. Necessity of that
predicate from the main conclusion rules out any finite independent base
extension realizing these tuples in the precise sense of `thm:main`.
This statement concerns the actual group-of-germs conclusion; the original
algebraic-group and curve-action bridges remain obligations.

{docstring AclGeom.QWitness.Nonfaithful.not_groupConfiguration}

{docstring AclGeom.QWitness.Nonfaithful.not_exists_isMainConclusion}

# Replacing the base by its relative algebraic closure
%%%
tag := "group-configuration-base-closure"
%%%

Let $`\bar k=\operatorname{acl}_k(\varnothing)` inside the same ambient field
$`K`. Relative algebraic closures over $`k` and $`\bar k` have the same
carriers. Ranks over these two bases agree for every set of coordinates.
The closed-field lattices are order isomorphic, with exactly the same
carriers in both directions.

{docstring AclGeom.racl_baseClosure_coe}

{docstring GroupConfig.erk_baseClosure}

{docstring AclGeom.ClosedIF.baseClosureEquiv}

{docstring AclGeom.ClosedIF.coe_baseClosureEquiv}

{docstring AclGeom.ClosedIF.coe_baseClosureEquiv_symm}

The existing `Point.map` applied to this actual order isomorphism gives the
point bijection with the same carriers, and `rankEq_map_iff` preserves every
lattice-rank statement. These applications are checked on the constructed
isomorphism. The order and rank results hold over arbitrary fields. When
$`K` is algebraically closed, $`\bar k` is algebraically closed, giving the
source's reduction in `rem:psi-hyp`(c). Original-field witness descent from a
larger ambient extension remains open.

# A canonical universal ambient
%%%
tag := "group-configuration-universal-ambient"
%%%

For any original field extension, adjoin countably many variables to the
ambient field and take the algebraic closure of the resulting fraction field.
The algebraic closure of the original base inside this chosen ambient is
itself algebraically closed. Mathlib supplies this from its algebraic-closure
structure. The independent variables remain independent over that enlarged
algebraic base, proving the universal-domain hypothesis there.

{docstring AclGeom.ConfigurationAmbient}

{docstring AclGeom.configurationBase}

The geometric lift transfers the point record. The core lifting lemma needs
only clauses (i)–(iv), including atom-freeness. Applying the complete input theorem
gives the six-point configuration, with group rank two and space rank one.
The caller supplies the actual core witness. Original ambient algebraic
closedness and a universal-domain hypothesis are unnecessary for this lift.

{docstring AclGeom.QWitness.universalLift}

{docstring AclGeom.configurationEmbedding}

{docstring AclGeom.QWitness.PsiCore.lift}

{docstring AclGeom.QWitness.PsiCore.groupConfiguration_universalLift}

The same configuration is obtained on the literal images of the original
displayed six tuples under this embedding. The lifted point and the literal
image of its representative have equal relatively algebraic closures, so
configuration invariance and rank invariance transport the result. This needs
only clauses (i)–(iv). The existing full-Ψ theorem retains its original statement
and applies the proved core projection.

{docstring AclGeom.QWitness.PsiCore.groupConfiguration_universalImages}

The configuration lives in the chosen extension over its algebraic base.
Finite-ambient chart/action descent remains open. This construction supplies
the input for group extraction; it produces no original-field semantic representatives,
group, action or guarded
initial chart. Algebraization, action classification and unconditional
reconstruction remain separate targets.

# Constructible sets
%%%
tag := "group-configuration-constructible-sets"
%%%

Section 9 starts with a polynomial definition. A set of
points is constructible over a field $`k` when it is a finite union of cells,
each cut out by finitely many polynomial equations and one polynomial
inequation with coefficients in $`k`. The implementation uses the pullback of
a constructible subset of the polynomial prime spectrum; the following
equivalence proves that this is exactly the stated polynomial definition.

{docstring GroupConfig.IsConstructibleOver}

{docstring GroupConfig.isConstructibleOver_iff_exists_polynomial_data}

# Chevalley on points
%%%
tag := "group-configuration-chevalley-points"
%%%

A finite coordinate projection preserves constructibility over $`k` when
the ambient field $`K` is algebraically closed. The base $`k` may be arbitrary,
and this theorem needs no transcendence-degree bound.

{docstring GroupConfig.IsConstructibleOver.image_projection}

Mathlib's Chevalley theorem first gives a constructible image in the prime
spectrum. To obtain an actual $`K`-valued point over a specified base point,
the proof localizes a prime quotient at the polynomial required to stay
nonzero. Its tensor product with $`K` is a nonzero algebra of finite type.
A maximal quotient embeds into $`K`, preserving the base point, all equations,
and the required nonvanishing. This proves equality with the image on points.

# Boolean operations, substitution and quantifiers
%%%
tag := "group-configuration-closure-operations"
%%%

Constructible sets are closed under finite unions, intersections and complements.
Polynomial zero sets and nonzero loci are constructible. Polynomial substitution
preserves the coefficient field, and enlarging that field preserves constructibility.
These statements hold over arbitrary fields, without a transcendence-degree bound.

{docstring GroupConfig.IsConstructibleOver.polynomial_zero}

{docstring GroupConfig.IsConstructibleOver.polynomial_ne_zero}

{docstring GroupConfig.IsConstructibleOver.preimage_polynomial}

{docstring GroupConfig.IsConstructibleOver.extend_base}

Chevalley and complementation give existential and universal quantifiers over all
ambient-field tuples. Both coordinate blocks are finite and the ambient field is
algebraically closed. These operations also supply the generic quantifier below,
whose quantifiers range over generic points of a represented irreducible locus.

{docstring GroupConfig.IsConstructibleOver.exists}

{docstring GroupConfig.IsConstructibleOver.forall}

# Generic points and finite sampling
%%%
tag := "group-configuration-generic-quantifier"
%%%

An automorphism over the coefficient field preserves constructible membership.
Generic points of a represented base locus form a single orbit, so an invariant
set contains either all such points or none. If a constructible subset of the
locus contains no generic point over the algebraic closure of its coefficient
field, it lies in a proper polynomial zero set over that field. The proof chooses
one equation from each nonempty polynomial cell and multiplies them.

{docstring GroupConfig.IsConstructibleOver.mem_comp_algEquiv_iff}

{docstring GroupConfig.IsGenericOver.mem_iff_of_invariant}

{docstring GroupConfig.exists_polynomial_zero_of_no_generic}

For $`N` parameter coordinates, adjoining a parameter tuple can lower rank on at
most $`N` members of a finite family whose joint rank is the sum of its members'
ranks. Thus among at least $`2N+1` generic samples, at least $`N+1` remain generic
over the parameter field. A predicate true at $`N+1` samples is true at one of
these generic samples, hence at all generic points by orbit invariance. Conversely,
truth at every generic point gives truth at all the remaining generic samples.
This also proves that existential and universal generic quantification agree;
the rank count supplies a generic witness, so the equivalence is not vacuous.

{docstring GroupConfig.card_rank_drop_le}

{docstring GroupConfig.generic_quantifier_iff}

The majority condition is a finite Boolean combination of sampled polynomial
predicates. Its locus is therefore constructible over the field generated by all
sample coordinates over the original coefficient field.

{docstring GroupConfig.IsConstructibleOver.card_le}

{docstring GroupConfig.constructible_generic_quantifier}

The base and ambient fields are algebraically closed, the ambient field is a
universal domain, and the intermediate coefficient field is small; that
coefficient field need not be algebraically closed. The loci are represented by
finite tuples, and the sampling theorem also covers dimension zero. The
arbitrary-prime realization formulation is proved in `PrimeLocus`. The precise
group-of-germs extraction and independent parameter descent are proved above.
The actual constructible presentations follow below. Original-field chart/action
descent, algebraization and the guarded initial affine chart remain separate
obligations. The public reconstruction theorem still has its open completeness inputs.


# The constructible group and homogeneous space
%%%
tag := "group-configuration-constructible-presentations"
%%%

A constructible group in the source sense is an actual group $`G` with a
surjection $`ρ : D_G → G` from a constructible parameter set. Its equality,
multiplication and inverse relations on parameters must be constructible.
For a constructible $`G`-set, the same is required of a surjection onto the
space, its equality relation and its action relation.

{docstring GroupConfig.ConstructibleGroupPresentation}

{docstring GroupConfig.ConstructibleGSetPresentation}

The group domain is the literal set of invertibly admissible pairs
$`d = (u_1,u_2)` satisfying the source stabilization condition. For every
parameter $`v` generic over the field and $`d`, some invertibly admissible
$`u'` in the parameter locus represents $`g_v g_{u_1}^{-1}g_{u_2}`.
Neither $`u_1` nor $`u_2` is assumed generic or in that locus.
This condition is equivalent to membership of the actual pair germ in $`G`.
The resulting map onto $`G` is surjective, using its two orbit factors.

{docstring GroupConfig.QuasiRational.pairDomain}

{docstring GroupConfig.QuasiRational.mem_pairDomain_iff}

{docstring GroupConfig.QuasiRational.pairDomainMap_surjective}

The samples are chosen in two stages. Actual generic points of the source
and target loci generate $`L_0`; they make the finite inner word relations
constructible. Parameter-locus samples are then generic and jointly independent
over $`L_0`, and generate $`L_1 = k(t_0,t_1)`. The generic quantifier gives
constructibility over $`L_1`. The literal domain uses that same $`L_1` in its
quantifier; its equality with the earlier quantified domain is proved.
All the samples remain jointly fresh from the prescribed small field.

The shared witness relation before existential projection supplies both the
group and stabilizer inner formulas. Actual pair words prove the group kernel,
multiplication and inverse relations constructible over the common field.
The source definition is then a conclusion of the group constructor.

{docstring GroupConfig.isConstructibleOver_groupWitness}

{docstring GroupConfig.QuasiRational.constructibleGroupPresentation_pairDomain}

For any generic point $`y_0`, the total orbit map is
$`ρ_X(d) = ρ(d) • ι(y_0)`. Transitivity makes it surjective. The point need
not be independent from candidate parameters. The stabilizer formula therefore
uses the actual group action, with defined values of the expression family in
its witnesses. The four-letter word $`ρ(d)^{-1}ρ(d')` gives the space kernel;
the six-letter word $`ρ(t)^{-1}ρ(g)ρ(x)` gives its action relation.
Every letter retains its invertible-admissibility restriction.

{docstring GroupConfig.QuasiRational.pairDomainSpaceMap}

{docstring GroupConfig.QuasiRational.isConstructibleOver_pairSpaceKernel}

{docstring GroupConfig.QuasiRational.isConstructibleOver_pairSpaceAction}

For $`H = \operatorname{Stab}(ι(y_0))`, the orbit map is a
$`G`-equivariant bijection $`G/H ≃ S`. The stabilizer preimage and the full
space presentation are constructible over $`L_1(y_0)`.

{docstring GroupConfig.Germ.IsHW.quotientStabilizerEquiv}

{docstring GroupConfig.Germ.IsHW.quotientStabilizerEquiv_smul}

Finally the canonical wrapper chooses the family internally on the literal
indexed RREF code $`f_0.code`, derives equal dimension from invertibility,
and chooses both sampling stages. It preserves their actual provenance,
joint ranks and freshness. The group is presented over $`k(t_0,t_1)`;
every generic-point stabilizer and the homogeneous space are presented over
$`k(t_0,t_1,y_0)`. No family, sampling or presentation certificate is an input.
The producer applies to every Hrushovski–Weil datum of bijections, including
the data supplied by the precise main theorem.

{docstring GroupConfig.Germ.IsHWBij.exists_fresh_canonicalGroupSpacePresentation}

The general configuration theorem composes the precise main conclusion and this
canonical producer on the same actual data. For every generic base point over
the configuration field it chooses the samples internally. Their union with
the original finite extension is independent from the configuration over the
original base. The final-base rank bound, generic characterization, two-product
and one-orbit conclusions use the rank of the original input tuple. The full
Ψ application above specializes this theorem to group rank two and space rank
one; its public statement is unchanged.

{docstring GroupConfig.GroupConfiguration.exists_main_constructible}

These are constructible quotient presentations. Original algebraization,
action classification, original-field chart/action descent, guarded charts
and unconditional reconstruction remain obligations of the shared project goal.
