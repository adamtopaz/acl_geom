/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import VersoManual
import AclGeom.Counterexamples.KernelRank
import AclGeom.Reconstruct.Base
import AclGeom.Reconstruct.Scalar
import AclGeom.Reconstruct.Existence
import AclGeom.Reconstruct.Target
import AclGeom.Reconstruct.Kernel
import AclGeom.Reconstruct.Points
import AclGeom.Reconstruct.TwoGeneric
import AclGeom.Reconstruct.Uniqueness

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Reconstruction: generic intersections and the Frobenius kernel" =>

%%%
tag := "reconstruction"
%%%

The Frobenius kernel theorem supplies the kernel input to the blueprint's
uniqueness argument.  The existence of a field isomorphism inducing a
geometry isomorphism is proved conditionally for perfect ambient fields with
RAC bases and explicit ACF completeness. Actual original-field existence through
arbitrary chosen perfections is also proved with original-base RAC, source rank
five and both perfected completeness inputs explicit. Final target assembly
remains open. Base recovery, scalar one, outside-point recovery
and both actual inducing/existence consumers are proved below ([issue #9](https://github.com/adamtopaz/acl_geom/issues/9)).

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
General unconditional R1/R2 and original-field `Induces` assembly remain open. The broader C7/group/three-pair/tensor obligations
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
separate exponential characteristics, both still-open ACF J-completeness
hypotheses and the canonical image-base equality. Forward inclusion uses
target RAC only. The statements include independent universes, finite bases
and characteristics zero/two. The two accepted no-fresh ratio declarations
are unchanged, and no helper, generated declaration or global instance is added.

This accepts corrected conditional R1b. The next section proves scalar
elimination for this same map without RAC. General unconditional R1/R2,
original-field inducing assembly, `Induces`, unconditional completeness and
full reconstruction remain open. The original literal
RatioEq proof, broader C7/group/three-pair/tensor obligations and frozen
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
proof remain preserved exactly; their literal RatioEq/JMul argument and
unconditional completeness remain obligations.

The first tuple coordinate then gives the outside-point formula:

{docstring AclGeom.interpretedRingEquiv_point}

B1 plus the coordinate and scalar-one laws also give the full tuple-image
consequence: an independent `(x,a)` maps to the independent target pair
`(H(x),a')` and its canonical tuple. This consequence, actual inverse/base
coordinates, and feeding compatibility plus this point law to the existing
whole-lattice propagation API are checked by independent typed interfaces.

All three statements need no RAC hypothesis. Both perfections/rank-five
bounds, separate exponential characteristics, both still-open ACF
J-completeness inputs and the actual canonical image-base equality remain
explicit. No extra target genericity, freshness witness, scalar oracle,
helper, global instance or generated declaration is introduced. The new
module imports Base only. This accepts corrected conditional R2a/b/c;
general unconditional R1/R2, final target assembly,
unconditional completeness and global,
literal/TOT/three-pair/tensor/frozen M4a obligations remain open. The named
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

This is the corrected conditional counterpart of all-point recovery and
the atomistic extension. Both RAC bases and the exact carrier inputs
remain explicit. There is no supplied point or scalar oracle. Every
principal point, every closed-field set image and the full inverse point
formula follow from this actual equality.

Choosing the source pair and its actual target image gives existence:

{docstring AclGeom.exists_ringEquiv_closedIFMap_eq}

Only the source rank-five bound is supplied. The source pair is chosen
fresh over the empty set and then its parameter; target rank is derived
from the lattice isomorphism, and target completeness gives the image
pair. No source/target pair, target rank, image equality, point/scalar
oracle or inducing endpoint is assumed. Both perfect ambient fields,
separate exponential characteristics, both RAC bases and both still-open
ACF J-completeness hypotheses remain explicit across independent universes.

This proves compatible inducing RingEquiv existence in the perfected RAC
setting. Independent typed behaviors check all points/closed-field images,
inverse points, the induced base-field RingEquiv, finite bases and
characteristics zero/two. Extension to arbitrary chosen perfections of
these already-perfect input fields is also checked; it does not prove
the original nonperfect-field statement.

The next section proves original-field inducing existence through chosen
perfection lattices, deriving RAC of the perfected base from original RAC.
Final target assembly with Frobenius uniqueness remains open, as do
unconditional completeness, general
R1/R2/R3/R4, literal RatioEq/TOT/scalar arguments, bypassed
linear-disjointness and the frozen M4a obligations. The original
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
hypotheses remain explicit. No original ambient perfection, perfected RAC,
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

This accepts only conditional original-field inducing existence. The next
named consumer is a public conditional target assembly combining rank,
the base and intersection formulas, Frobenius uniqueness and the converse.
Final Reconstructs/target assembly, general unconditional R1/R2/R3/R4,
both completeness obligations, literal RatioEq/TOT/scalar arguments,
bypassed linear-disjointness and broader group/three-pair/tensor/frozen M4a
obligations remain open. Every original source statement and proof is preserved.

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
The exchange proof does not
discharge the separate linear-disjointness obligations tracked in
[issue #11](https://github.com/adamtopaz/acl_geom/issues/11).

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
lattice isomorphism, unconditional base/point recovery and full functorial
assembly remain open ([issues #9](https://github.com/adamtopaz/acl_geom/issues/9) and
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
with both perfected completeness hypotheses explicit. Final target assembly remains open.
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
APIs transport it back to the original fields in the conditional chosen-perfection
existence consumer above. Both perfected completeness hypotheses stay explicit.
General unconditional R1/R2, final target assembly and unconditional
completeness remain open ([issue #9](https://github.com/adamtopaz/acl_geom/issues/9)).
The two-generic intersection remains a proved blueprint statement; the
separate linear-disjointness obligations on
[issue #11](https://github.com/adamtopaz/acl_geom/issues/11) remain open.
