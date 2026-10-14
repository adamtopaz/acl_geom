/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import VersoManual
import GroupConfig
import AclGeom.Config.CanonicalBaseInput
import AclGeom.Config.ConfigurationInput
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
foundations. These results do not extract a group from a configuration.

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

The arbitrary-prime formulation of the supplemental generic-point existence lemma
remains an obligation; the theorem above constructs points of represented base
loci. All universal-domain and smallness hypotheses are explicit. These results
do not yet extract a group from a configuration.

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
not change rank. The arbitrary-prime realization obligation remains open.

{docstring GroupConfig.InLocus}

{docstring GroupConfig.erk_le_of_inLocus}

{docstring GroupConfig.isGenericOver_iff_erk_eq}

{docstring GroupConfig.IsGenericOver.isGenericOver_iff_indepOver}

{docstring GroupConfig.erk_union_eq_of_subset_racl_of_isGenericOver}

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

The scalar-extension remark for fields of definition remains an obligation.

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
canonical-base hypotheses of the configuration route; group extraction and
unconditional reconstruction remain open.

# Canonical bases of the actual Ψ incidences
%%%
tag := "group-configuration-psi-canonical-bases"
%%%

In an algebraically closed universal domain, clauses (i)–(iv) of the actual
$`\Psi` witness, through its atom-freeness clauses, force the canonical bases of the incidence pairs to
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

{docstring GroupConfig.exists_quasiRational_of_mem_dclAdjoin}

A Hrushovski–Weil datum is an invertible germ whose orbit is generically
transitive and closed under inversion and independent composition. These
hypotheses give the subgroup of units generated by that orbit: every element
is a product of two orbit members. Generic stabilization, the rank bound and
the maximal-rank criterion follow from the same hypotheses. The quotient
homogeneous space and extraction of the datum from a six-point configuration
are later integration layers.

{docstring GroupConfig.Germ.IsHW}

{docstring GroupConfig.Germ.IsHW.threetwo}

{docstring GroupConfig.Germ.IsHW.prodSubgroup}

{docstring GroupConfig.Germ.IsHW.closure_eq}

{docstring GroupConfig.Germ.IsHW.keyrank}

For an orbit of invertible germs between two loci, independent pairs give
difference germs. These form one orbit. The difference and either member of
the pair are interalgebraic over the other member, yielding its rank and
independence criteria. The hypotheses making this difference orbit a
Hrushovski–Weil datum are still to be supplied by the configuration argument.

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

{docstring GroupConfig.IsTriple.germ_cb}

{docstring GroupConfig.IsTriple.isInvertible_iff}

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

A single jointly fresh sampling tuple serving arbitrary finite word relations
still requires assembly. The constructible-group domain, its surjection onto
the generated group, the quotient relations and the stabilizer action remain
separate obligations.

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
the indexed polynomial. The literal finite degree-bounded coefficient-vector
presentation and the definable-closure and conjugate-set clauses remain separate.

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
the later admissible-parameter and germ-word relations. Those relations and
the definable-closure characterization remain separate obligations.

{docstring GroupConfig.QuasiRational.isConstructibleOver_domain}

{docstring GroupConfig.QuasiRational.isConstructibleOver_graph}

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

This module imports the canonical-base layer directly. It proves the stated
consequences and invariances of the configuration predicate. The remaining
rank bounds, total-rank and point/line clauses, independent base change,
literal image-tuple comparison and finite-ambient chart/action descent for the
actual $`\Psi` input, and extraction of a group remain obligations. The actual input
in a universal domain is constructed below.

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
Literal image-tuple comparison is proved below; finite-ambient chart/action descent remains open. The
initial chart still needs both output guards. Group extraction, algebraization,
action classification and unconditional reconstruction remain separate targets.

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
arbitrary-prime realization formulation remains open. Extraction and
constructibility of the group, parameter and witness descent, algebraization,
and the guarded initial affine chart remain separate obligations. The public
reconstruction theorem still has its open completeness inputs.
