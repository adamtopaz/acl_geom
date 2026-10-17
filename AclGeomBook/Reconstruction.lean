/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import VersoManual
import AclGeom.Counterexamples.KernelRank
import AclGeom.Correspondence.GenericExtension
import AclGeom.Reconstruct.Base
import AclGeom.Reconstruct.Scalar
import AclGeom.Reconstruct.TupleImage
import AclGeom.Reconstruct.Existence
import AclGeom.Reconstruct.Target
import AclGeom.Main
import AclGeom.Reconstruct.Kernel
import AclGeom.Reconstruct.Points
import AclGeom.Reconstruct.TwoGeneric
import AclGeom.Reconstruct.Uniqueness
import AclGeom.Reconstruct.PointVariant
import AclGeom.Variants

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Reconstruction: generic intersections and the Frobenius kernel" =>

%%%
tag := "reconstruction"
%%%

The lattice reconstruction theorem is proved under the blueprint's hypotheses: two
relatively algebraically closed bases, source transcendence degree at least five, arbitrary
chosen perfections and a lattice isomorphism. `Main` supplies its two ACF completeness
proofs internally. The result includes rank equality, base compatibility, the original-field
intersection formula, the exact Frobenius fibre and the converse.

The internal existence and interpretation APIs below retain explicit completeness
parameters. Those parameters are proved by `Config.Completeness` at the transported
rank-five bounds. The point-geometry formulation and the automorphism exact sequence are
proved below, and the functorial formulation is the next chapter. True bypassed source
statements remain separate obligations ([issue
#9](https://github.com/adamtopaz/acl_geom/issues/9),
[issue #10](https://github.com/adamtopaz/acl_geom/issues/10)).

# Relative base ratios
%%%
tag := "relative-base-ratio"
%%%

The base-ratio corollary supplies the prerequisite for base recovery.
Suppose `u₁,t` are independent over an arbitrary base `k`, `u₂` is nonzero,
and both the elements and their products with `t` are interalgebraic.
The ratio is algebraic over `k`, with no fresh element in the original field:

{docstring AclGeom.base_ratio_rel}

The proof embeds the ambient field into the algebraic closure of `K(X)`.
The image of the variable is transcendental over all of `K` and provides
the fresh third element for the existing algebraically closed correspondence
lemma. The pairs are `(u₁,u₂)` and the degenerate correspondence `(t,t)`.
Algebraicity of the enlarged base preserves closure membership, and the
embedding pulls the ratio's algebraicity back. All algebra/tower instances
are the existing global instances; no local algebra structure is installed.

If the original base is relatively algebraically closed, the inverse ratio
lies in its actual algebra-map image, in the original corollary's orientation:

{docstring AclGeom.base_ratio_mem_range}

Neither theorem assumes rank, freshness, perfection, completeness or an
exponential characteristic. Base membership names `IsRAC` explicitly. The
statements include finite bases and characteristics zero/two, and the
algebraically closed-base case needs no ambient closure assumption.
This completes the base-ratio corollary prerequisite (R1a/C7b).

The next section proves the named R1b consumer: base-element membership and
`CrossBase.Compatible` for the actual `interpretedRingEquiv` under explicit
carrier and RAC inputs. Conditional scalar one is proved after it without RAC.
The internal `Induces` existence API retains both perfected completeness parameters.
The public target below supplies them internally, giving original-field reconstruction
under the blueprint hypotheses. The broader group/geometric-fiber-product obligations
and frozen M4a scope are preserved. The original source proof is retained;
its incorrect correspondence-pair ordering was reported on issue #5.

# Conditional base recovery
%%%
tag := "conditional-base-recovery"
%%%

For the actual decoded geometric ring equivalence, the forward base
inclusion needs only the target base to be relatively algebraically closed:

{docstring AclGeom.interpretedRingEquiv_algebraMap_mem}

The zero case uses explicit zero-preservation identities. A nonzero base
element is represented by the ratio of `j(c x₀,a)` and the canonical
`j(x₀,a)`. The supplied image-tuple equality fixes the denominator as
`j(x₀',a')`. Target fixed-class correctness supplies `j(y,a')` for the
numerator. Only point coordinates zero and two are used: base scaling
fixes the points of `x₀` and `x₀ a`, so the relative base-ratio
corollary puts the decoded ratio `y/x₀'` in the actual target base.

The actual inverse agrees with the swapped construction:

{docstring AclGeom.interpretedRingEquiv_symm}

This theorem needs no RAC hypothesis. It takes the redundant inverse
image-tuple equality explicitly; pointwise values of the two inverse
composites agree by reflexivity. Compatible assembly derives that equality
inline and applies forward inclusion in both directions:

{docstring AclGeom.interpretedRingEquiv_compatible}

The conclusion is the actual equality of base-field ranges
`CrossBase.Compatible (interpretedRingEquiv …)`. Both RAC bases and all
existing carrier inputs remain explicit: both perfections/rank-five bounds,
separate exponential characteristics, both explicit ACF J-completeness
hypotheses and the canonical image-base equality. Forward inclusion uses
target RAC only. The statements include independent universes, finite bases
and characteristics zero/two. The two accepted no-fresh ratio declarations
are unchanged, and no helper, generated declaration or global instance is added.

This accepts corrected conditional R1b. In the source setting the proved producers supply
every explicit input, so Prop `base-recovery` holds for the actual reconstruction, for every
chosen class and image pair. The next section proves scalar elimination for this same map
without RAC. Original-field inducing existence
is a reusable conditional API. The public target below supplies the completeness inputs
and proves lattice reconstruction under the blueprint hypotheses. The original literal
RatioEq proof, broader group/geometric-fiber-product obligations and frozen
M4a scope remain preserved.

# Conditional scalar one and outside points
%%%
tag := "conditional-scalar-one"
%%%

Write `H = interpretedRingEquiv … e …` for the same decoded geometric
ring equivalence. For an actual tuple image `e(j(x,a)) = j(y,a')`,
the ratio class of `(j(x,a),j(x₀,a))` decodes to `x/x₀` and its image
to `y/x₀'`. Division preservation gives the multiplied coordinate formula:

{docstring AclGeom.interpretedRingEquiv_coord}

There is a single scalar `x₀'/H(x₀)`, and it is one:

{docstring AclGeom.interpretedRingEquiv_base_coord}

Choose two fresh source elements over `a`. Their target genericity is
proved geometrically: point-triple independence is preserved by the lattice
isomorphism, and tuple-image coordinates zero, zero and four identify the
target triple. The coupled product is preserved, so its image coordinate
is the product of the two image coordinates. Combining the three multiplied
coordinate identities with multiplication preservation and nonzero
cancellation yields `H(x₀)=x₀'`.

This route replaces the original blueprint choice over `acl(a,x₀,t₀)`
by geometric transport of target genericity. The original proposition and
proof remain preserved exactly; their literal RatioEq/JMul argument retains its provenance.
The corrected proof supplies the public reconstruction below.

The first tuple coordinate then gives the outside-point formula:

{docstring AclGeom.interpretedRingEquiv_point}

The same steps give the full tuple formula, the first displayed conclusion of
Prop `scalar-one`: for `x` outside `acl_k(a)`, the pair `(H(x),a')` is independent and
`e(j(x,a)) = j(H(x),a')`.

{docstring AclGeom.interpretedRingEquiv_jTupleOf}

It is stated for the actual `H`, with the same explicit inputs and no RAC. In the source
setting `jCompletenessACF` supplies both completeness inputs, the lattice isomorphism the
target rank and `exists_map_jTupleOf_eq` the image pair.

The three Scalar statements and the tuple formula need no RAC hypothesis. Both
perfections/rank-five bounds, separate exponential characteristics, both explicit ACF
J-completeness inputs and the actual canonical image-base equality remain explicit. No extra
target genericity, freshness witness, scalar oracle, helper, global instance or generated
declaration is introduced. `Reconstruct.Scalar` imports Base only, and
`Reconstruct.TupleImage` imports Scalar only. This accepts corrected R2a/b/c and the tuple
formula: with base recovery above, Props `base-recovery` and `scalar-one` hold for the actual
reconstruction. The public theorem supplies completeness internally. The original literal
RatioEq/JMul proofs keep their provenance. The canonical finite-tuple geometric fibre-product
bridge is proved; coherent branches/common normal covers and the original group/chunk and
scheme/action statements remain obligations. The frozen M4a record is historical. The named
next section proves its actual inducing direction under explicit RAC bases.

# Conditional inducing equality and existence
%%%
tag := "conditional-inducing-existence"
%%%

The same actual `interpretedRingEquiv` carries the base ranges onto each
other and satisfies the outside-point formula. Applying the general
all-point and atomistic propagation theorem gives equality with the
supplied lattice isomorphism:

{docstring AclGeom.closedIFMap_interpretedRingEquiv}

This is the corrected counterpart of Prop `all-points` and the atomistic
extension for the actual reconstruction. `CrossBase.closedIFMap_point` turns it into
`e([x]) = [H(x)]` for every `x`, and `CrossBase.coe_closedIFMap` into `e(M) = H(M)` for
every closed `M`. Both RAC bases and the exact carrier inputs remain explicit, and the
proved producers supply them in the source setting. There is no supplied point or scalar
oracle. The full inverse point formula also follows from this actual equality. For the
original fields, the same equality on the chosen perfections, with the conjugated lattice
isomorphism, gives `φ(M) = H(M^perf) ∩ L` for that actual `H` through
`Perfection.induces_iff_eq_inducedIso` and `Perfection.Induces.mem_iff`. The source proof's
two-generic intersection route is replaced by exchange and bijectivity of point maps; the
original proof is retained.

Choosing the source pair and its actual target image gives existence:

{docstring AclGeom.exists_ringEquiv_closedIFMap_eq}

Only the source rank-five bound is supplied. The source pair is chosen
fresh over the empty set and then its parameter; target rank is derived
from the lattice isomorphism, and target completeness gives the image
pair. No source/target pair, target rank, image equality, point/scalar
oracle or inducing endpoint is assumed. Both perfect ambient fields,
separate exponential characteristics, both RAC bases and both explicit
ACF J-completeness hypotheses remain explicit across independent universes.

This proves compatible inducing RingEquiv existence in the perfected RAC
setting. Independent typed behaviors check all points/closed-field images,
inverse points, the induced base-field RingEquiv, finite bases and
characteristics zero/two. Extension to arbitrary chosen perfections of
these already-perfect input fields is also checked; it does not prove
the original nonperfect-field statement.

The next section proves original-field inducing existence through chosen
perfection lattices, deriving RAC of the perfected base from original RAC.
The following public target section assembles Frobenius uniqueness.
The public theorem supplies completeness internally. The original literal RatioEq/scalar
proofs keep their provenance on #23, and the literal TOT theorem is refuted (#8). The
embedded-field assertions of the original two-generic
proof are checked separately below; frozen M4a remains historical. The original
larger-freshness scalar argument is preserved. Exactly two public results
are added in a focused module importing Points and Scalar only, with no
helper, generated declaration, global instance or duplicate RingEquiv.

# Conditional existence through chosen perfections
%%%
tag := "conditional-chosen-perfection-existence"
%%%

The original ambient fields need not be perfect. Choose arbitrary bundles
`π` and `ρ`, and conjugate the supplied lattice map by their `latticeIso`.
The perfected base is RAC by `Perfection.isRAC_basePerf` from original-base
RAC, as displayed in the perfection chapter. The perfected source rank is
derived from original source rank five. The perfect-field endpoint then
constructs a compatible field isomorphism of the chosen perfections that
actually induces the original map:

{docstring AclGeom.Perfection.exists_induces}

Both ORIGINAL bases are RAC, and both exact perfected ACF J-completeness
hypotheses remain explicit in this internal API. No original ambient perfection, perfected RAC,
target rank, pair, image equality, point/scalar oracle or inducing endpoint
is supplied. The bundles supply separate characteristic parameters; two
local Prop-valued PerfectField witnesses add no global or local Algebra
instance. The focused Target module imports Induces and Existence only.

Independent typed behaviors check literal perfected-subfield equality,
every intersection membership formula, the actual compatible perfected
base RingEquiv, equality with the conjugated inducing map, Frobenius twists
and the exact fibre for this constructed witness, finite original bases
and characteristics zero/two across independent universes. The fibre is
a private consumer check of the landed uniqueness API; no extra public
assembler is added. Exactly two public results, with no helper, generated
declaration, global instance or duplicate RingEquiv, are added.

This proves the reusable internal original-field inducing theorem. The next section
supplies its completeness parameters internally and derives the public target with rank,
base/intersection formulas, Frobenius uniqueness and the converse. The literal RatioEq/scalar
proofs keep their provenance and the literal TOT theorem is refuted; broader
group/chunk, coherent-cover and scheme/action source obligations remain tracked.
The original two-generic embedded-field assertions are checked below; frozen M4a remains
historical. Every original source statement and proof is preserved.

# Public reconstruction theorem
%%%
tag := "public-conditional-target"
%%%

The public relation reuses the actual equality of perfected subfields through the
reducible alias `Perfection.Induces`:

{docstring AclGeom.Reconstructs}

Public existence requires only the two original RAC bases, source rank at least five,
the arbitrary chosen perfections and the supplied lattice isomorphism. The original
fields need not be perfect:

{docstring AclGeom.exists_reconstruction}

The perfected source retains rank five by the perfection lattice isomorphism. Transport
along the supplied lattice isomorphism gives the target rank bound. Passing to each
perfected base's algebraic closure retains that bound, and the proved ACF J-completeness
theorem supplies both inputs of the internal existence lemma. Algebraic closedness of
these bases is proved locally. A shared private producer supplies the inducing map to
both public statements; the caller supplies no completeness, chart or reconstruction
oracle.

The assembled lattice-form target gives rank equality and a compatible reconstruction.
For the same witness it gives every original-field intersection formula, the full
Frobenius fibre, literal uniqueness in characteristic zero and uniqueness of the integral
exponent in positive characteristic. Conversely every compatible isomorphism of chosen
perfections reconstructs its transported lattice map:

{docstring AclGeom.reconstruction_target}

The two characteristic parameters stay separate, and the ambient universes are
independent. The conclusions of the former conditional statements are unchanged; only
the two completeness parameters have been removed. The point-geometry and automorphism
variants follow; the functorial variants are in the next chapter. Original literal
formulas and proofs retain their provenance; true bypassed source statements remain obligations.
The original theorem,
assembly sketch and proof retain their provenance and wording.

# Point-geometry reconstruction
%%%
tag := "point-geometry-reconstruction"
%%%

A bijection of points that preserves the full point closure is a geometry isomorphism in the
sense of blueprint (20.2). The closure condition determines a lattice isomorphism whose
restriction to atoms is the bijection (`latticeIsoOfPointEquiv`). The lattice-form theorem then
gives a compatible reconstruction whose action on points is the bijection, with the exact
Frobenius fibre among compatible maps and the converse:

{docstring AclGeom.point_reconstruction_target}

# The automorphism exact sequence
%%%
tag := "automorphism-exact-sequence"
%%%

The automorphisms of the chosen perfection carrying the perfected base onto itself form a
subgroup. Each one acts on `𝒢(K/k)` by its transported lattice map, and this is a group
homomorphism:

{docstring AclGeom.Perfection.pairAut}

{docstring AclGeom.Perfection.pairAutAction}

For a relatively algebraically closed base and transcendence degree at least five, the action
is surjective by existence. Its kernel is the subgroup generated by Frobenius, by the kernel
theorem. The kernel is trivial in characteristic zero and infinite cyclic in positive
characteristic (blueprint Thm `target`, closing paragraph of the proof):

{docstring AclGeom.Perfection.pairAutAction_surjective}

{docstring AclGeom.Perfection.frobZPow_mem_pairAut}

{docstring AclGeom.Perfection.ker_pairAutAction}

{docstring AclGeom.Perfection.ker_pairAutAction_eq_bot}

{docstring AclGeom.Perfection.kerPairAutActionEquivInt}

# Two generic intersections
%%%
tag := "two-generic-intersection"
%%%

If `t` is transcendental over the closure of `X ∪ {s}`, the closures of
`X ∪ {t}` and `X ∪ {s}` meet exactly in the closure of `X`. This is a direct
consequence of the existing exchange membership lemma. The set `X` may be infinite:

{docstring AclGeom.racl_insert_inf_racl_insert}

For nonzero generic `s,t` over the closure of `x`, division identifies
`acl(t,tx)` with `acl(x,t)` and `acl(s,sx)` with `acl(x,s)`. Their
intersection is the principal closure generated by `x`:

{docstring AclGeom.racl_pair_mul_inf_racl_pair_mul}

This proves the blueprint's two-generic intersection lemma. The conditional
point-propagation theorem below uses bijectivity instead of that meet argument.
The original proof's separate embedded-field assertions are validated next.

# Embedded fields in the original proof
%%%
tag := "two-generic-source-validation"
%%%

The original argument uses the fields `Ē(t)` and `Ē(s)` inside the same ambient field.
The field `F(s)` generated by `s` transcendental over an intermediate field `N` of `Ω/F`
is linearly disjoint from `N` over `F`. Neither the base nor the ambient needs to be
algebraically closed:

{docstring AclGeom.linearDisjoint_adjoin_simple_of_transcendental}

The proof specializes the existing generic-point base-change theorem to one variable
with zero relation ideal. Its consumers are both the rational fields and an algebraic
extension of one of them: `s` remains transcendental over such an extension.

`Test.TwoGenericSource` checks the original assertions from the two closure-independence
conditions in `K`, transported through the original embedding into `Ω`:

* The closures of `k(t,tx)` and `E(t)` agree, and the closure `Ē` meets `K` in `E`.
* The embedded fields `Ē(t)` and `Ē(s)` are linearly disjoint, and their closures meet in `Ē`.
* An algebraic element over `Ē(t)` lies in a finite normal extension inside an algebraically
  closed `Ω`. This uses Mathlib's normal closure of the simple extension and its finiteness.
* For a normal extension `N` of `Ē(t)`, every `Ē(t)`-embedding of `N` extends to `N(s)`,
  agrees with it on `N`, and fixes the whole of `Ē(s)` pointwise. Transcendence over `N`
  permits the rational-function extension; the fixed elements form a subfield containing
  `Ē` and `s`.
* An element algebraic over both rational fields belongs to `Ē`. This conclusion follows
  from the checked intersection theorem; the original conjugate-comparison route is retained
  without being transcribed.

The source's embedding-extension step needs the stronger disjointness of `N` and `Ē(s)`.
Linear disjointness of the two rational fields alone does not give that premise. The
justification gap and its correction are recorded on
[issue #9](https://github.com/adamtopaz/acl_geom/issues/9#issuecomment-6213953033), with the
original proof preserved. Closed [#11](https://github.com/adamtopaz/acl_geom/issues/11)
proves the separate abstract tensor-domain theorem. The distinct (8.9a) audit on #5 and
the remaining true source auxiliary obligations stay separate. The actual-H R1--R4
statements are proved with their original literal proof routes retained as provenance.

# Integral Frobenius powers
%%%
tag := "integral-frobenius-powers"
%%%

For a perfect field of exponential characteristic `q`, Frobenius is a field
automorphism.  Its integer powers include inverse powers; for `q = 1` they
all equal the identity.  Every such power fixes every closed point of the
algebraic-dependence geometry:

{docstring AclGeom.frobeniusZPow}

{docstring AclGeom.frobeniusZPow_natCast_apply}

{docstring AclGeom.frobeniusZPow_eq_one_of_eq_one}

{docstring AclGeom.point_frobeniusZPow}

# The kernel theorem
%%%
tag := "frobenius-kernel-theorem"
%%%

If `K` is perfect, has transcendence degree at least five over `k`, and a
field automorphism fixes every transcendental point, one integer Frobenius
power describes its action on the whole field:

{docstring AclGeom.exists_eq_frobeniusZPow_of_point_fixed}

The proof transports j-rigidity to arbitrary fields through algebraic
closures, applies it to independent pairs, and joins those pairs through a
fresh transcendental element.  Agreement on that shared element determines
the same Frobenius automorphism.  An algebraic element is recovered by
adding it to a transcendental element and cancelling the latter.

{docstring AclGeom.j_rigidity_field}

{docstring AclGeom.exists_frobeniusZPow_pair}

# Uniqueness
%%%
tag := "frobenius-kernel-uniqueness"
%%%

In positive characteristic, different integer exponents give different
automorphisms as soon as a transcendental element exists.  In characteristic
zero, point-fixing forces the identity:

{docstring AclGeom.frobeniusZPow_injective}

{docstring AclGeom.eq_refl_of_point_fixed}


# Why the rank hypothesis is needed
%%%
tag := "kernel-rank-hypothesis"
%%%

The original displayed blueprint kernel theorem omitted its rank hypothesis.
Its proof and the main reconstruction theorem require transcendence degree at
least five. Read without that qualification, the kernel claim is false even
in characteristic zero: in `ℚ(t)/ℚ`, translation `t ↦ t + 1` fixes the single
point of the geometry but moves `t`. The coefficient field is relatively
algebraically closed. The corrected statement keeps rank five explicitly,
and the source preserves the original wording and audit provenance:

{docstring AclGeom.not_forall_eq_refl_of_point_fixed}


# The fibre of supplied inducing maps
%%%
tag := "supplied-inducing-map-fibre"
%%%

Suppose two isomorphisms of chosen perfections induce the same closed-lattice
map. Their composite `Φ₂ ∘ Φ₁⁻¹` fixes every principal closure of the
perfected target, without a rank or relatively closed base assumption:

{docstring AclGeom.Perfection.Induces.point_symm_trans}

When the original source has transcendence degree at least five, rank
transport along the supplied lattice isomorphism and the perfection lattice
isomorphism gives the kernel's target rank. Thus the two supplied inducing
maps differ by an integral power of target Frobenius:

{docstring AclGeom.Perfection.Induces.exists_eq_trans_frobZPow}

Combined with the forward Frobenius-invariance law, this describes the
entire fibre once one inducing isomorphism is supplied:

{docstring AclGeom.Perfection.Induces.iff_exists_eq_trans_frobZPow}

The exponent is unique in positive characteristic, and the inducing
isomorphism is literally unique in characteristic zero:

{docstring AclGeom.Perfection.trans_frobZPow_injective}

{docstring AclGeom.Perfection.Induces.eq_of_p_eq_one}

These theorems require no agreement of the two recorded exponential
characteristics and no relatively closed base hypotheses. They take the
inducing maps as explicit inputs. Existence of a map inducing an arbitrary
lattice isomorphism is proved by the public theorem above. The point-geometry formulation
and the automorphism exact sequence are proved above; the functorial formulation is in the
next chapter ([issues #9](https://github.com/adamtopaz/acl_geom/issues/9) and
[#10](https://github.com/adamtopaz/acl_geom/issues/10)).


# Conditional recovery of all points
%%%
tag := "conditional-point-recovery"
%%%

Suppose a field isomorphism carries the source base onto the target base
and agrees with the prescribed lattice map on the principal closures of
every element outside the closure of one parameter. These are explicit
outputs of base recovery and scalar elimination. Conditional base recovery
and outside-point recovery are proved above under explicit carrier inputs.
The actual perfect-field inducing/existence assembly is proved above.
The original-field chosen-perfection existence consumer is also proved above
through the internal conditional API. The public target above supplies its completeness
proofs internally and reconstructs the original lattice map.
The agreement then extends to every closed intermediate field:

{docstring AclGeom.eq_closedIFMap_of_point_eq}

A point with a representative inside the exceptional closure must equal
the parameter's point, by exchange. Thus the two bijections of atoms agree
away from at most one atom; bijectivity forces agreement there too.
The existing uniqueness theorem for the atomistic lattice extension
finishes the proof. No rank, freshness or relatively closed base assumption
is needed, and the parameter may be algebraic.

The compatible transport of a principal closure gives the all-point
formula, including elements inside the exceptional closure:

{docstring AclGeom.CrossBase.closedIFMap_point}

This conditional propagation also supplies the whole-lattice image
formula. Its inputs for the actual interpreted ring equivalence are now
proved under explicit completeness/carrier hypotheses, with RAC for
compatibility. On perfected lattices the existing conjugacy and inducing-map
APIs transport it back to the original fields. The public target supplies the internal
chosen-perfection API's two completeness proofs, giving reconstruction under the genuine
hypotheses ([issue #9](https://github.com/adamtopaz/acl_geom/issues/9)).
The two-generic intersection remains a proved blueprint statement. The original
embedded-field assertions have the separate source validation described above;
closed [#11](https://github.com/adamtopaz/acl_geom/issues/11) stays proved.
Original general interpretation/provenance obligations remain on #9/#23.
