/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import VersoManual
import AclGeom

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Curves: function fields of one variable" =>

%%%
tag := "curves"
%%%

The completeness half of the configuration layer classifies group actions
on curves (blueprint Lemma 8.4), and by the design decision recorded on
the project tracker the supporting theory is built as a classical
function-field library — places, divisors, Riemann–Roch spaces, genus —
with no scheme theory, over mathlib's valuation and Dedekind stacks. The
base field is algebraically closed throughout the application, which
keeps every place of degree one.

# The setting
%%%
tag := "function-field-setting"
%%%

A function field of one variable is a field extension admitting a
transcendental element over whose simple extension it is finite. The
pregeometry developed for the foundation layers immediately upgrades the
single witness to every transcendental element — this is the exchange
property doing curve-theoretic work:

{docstring AclGeom.IsFunctionFieldOneVar}

{docstring AclGeom.finiteDimensional_adjoin_of_transcendental}

# Places are discrete valuation rings
%%%
tag := "places-dvr"
%%%

A place is a nontrivial valuation subring containing the base field:

{docstring AclGeom.Place}

The chapter's main theorem is Stichtenoth's Theorem 1.1.6: places of
one-variable function fields are discrete valuation rings. The proof runs
through the value group. Constants are units, so a polynomial with
nonzero constant term is a unit at any maximal-ideal element, and every
nonzero element of `k(z)` has value an integer power of `v z`:

{docstring AclGeom.valuation_aeval_eq_one}

{docstring AclGeom.exists_valuation_eq_zpow_of_mem_adjoin}

Elements whose values occupy distinct cosets of `⟨v z⟩` are linearly
independent over `k(z)` — the ultrametric dominant-term argument — so the
coset count is bounded by `[F : k(z)]`:

{docstring AclGeom.valuation_sum_eq_of_forall_lt}

{docstring AclGeom.linearIndependent_of_pairwise_valuation_ne}

Pigeonhole then puts a bounded positive power of every value in `⟨v z⟩`,
uniformized through the factorial exponent; the least attained exponent
supplies a maximal small value — a uniformizer — and every small value is
one of its powers:

{docstring AclGeom.exists_pow_valuation_eq_zpow}

{docstring AclGeom.exists_valuation_uniformizer}

{docstring AclGeom.valuation_eq_pow_uniformizer}

Principality of ideals follows by taking a generator of least exponent,
and the theorem assembles, with the finiteness hypothesis discharged from
the function-field axioms and transcendence of maximal-ideal elements
from relative algebraic closedness of the base:

{docstring AclGeom.isDiscreteValuationRing_of_valuationSubring}

{docstring AclGeom.Place.isDiscreteValuationRing}

# Approximation
%%%
tag := "approximation"
%%%

Distinct places are incomparable as valuation subrings — an overring of
a discrete valuation ring inside a one-dimensional situation collapses —
and incomparability yields an element large at one place and small at
finitely many others. Powering sharpens this into indicator elements and
a full weak-approximation theorem with prescribed orders:

{docstring AclGeom.Place.exists_one_lt_forall_lt_one}

{docstring AclGeom.Place.exists_forall_sub_valuation_le}

{docstring AclGeom.Place.exists_forall_ord_eq}

# Orders and divisors
%%%
tag := "divisors"
%%%

Each place carries a uniformizer, and every nonzero element has a unique
integer order at each place — positive at zeros, negative at poles. An
element of the function field has only finitely many zeros and poles,
because a uniform exponent computation reduces finiteness to the degree
bound over `k(f)`:

{docstring AclGeom.Place.ord}

{docstring AclGeom.finite_setOf_valuation_lt_one}

A divisor is a finitely supported integer combination of places; the
principal divisor of a nonzero element records its orders everywhere,
and the degree sums the coefficients:

{docstring AclGeom.Divisor}

{docstring AclGeom.divisorOf}

{docstring AclGeom.Divisor.deg}

# Riemann–Roch spaces
%%%
tag := "riemann-roch-spaces"
%%%

The space `L(D)` collects the elements whose principal divisor is
bounded below by `-D`; it is a `k`-submodule, monotone in `D`, and at
`D = 0` it is exactly the constants — the no-poles-implies-constant
theorem in module form:

{docstring AclGeom.RiemannSpace}

{docstring AclGeom.riemannSpace_zero}

Removing one point from the divisor drops the dimension by at most one:
the quotient is gauged by the residue of a ratio of extremal elements,
using the residue-field computation at algebraically closed base. By
induction, `ℓ(D) ≤ deg D + 1` for effective `D`, and every `L(D)` is
finite-dimensional:

{docstring AclGeom.riemannSpace_eq_or_eq_sup}

{docstring AclGeom.finiteDimensional_riemannSpace_of_nonneg}

# Principal divisors have degree zero
%%%
tag := "deg-div-zero"
%%%

Stichtenoth's Theorem 1.4.11, in both directions. The pole side: for
finitely many poles of `f`, witnesses with prescribed order `-j` at one
pole and `1` at the others are linearly independent over `k(f)` by a
dominant-term argument, bounding the total pole order by `[F : k(f)]`.
The dimension side: products of a `k(f)`-basis of `F` with powers of `f`
live in `L(N·(f)_∞ + C)` and are `k`-linearly independent, so counting
against `ℓ ≤ deg + 1` and letting `N → ∞` gives the reverse bound:

{docstring AclGeom.sum_pole_orders_le_finrank}

{docstring AclGeom.finrank_le_deg_poleDivisor}

{docstring AclGeom.deg_poleDivisor_eq_finrank}

Since the zeros of `f` are the poles of `f⁻¹` and `k(f) = k(f⁻¹)`, the
zero and pole degrees agree, and principal divisors have degree zero:

{docstring AclGeom.deg_divisorOf_eq_zero}

# Riemann's inequality and the genus
%%%
tag := "genus"
%%%

The defect `deg D + 1 − ℓ(D)` of a divisor is monotone — enlarging a
divisor grows the dimension by at most the added degree, iterating the
one-point decomposition — and invariant under adding principal
divisors, since `div z` has degree zero and multiplication by `z`
identifies the Riemann–Roch spaces:

{docstring AclGeom.Divisor.defect}

{docstring AclGeom.finrank_riemannSpace_le_of_le}

{docstring AclGeom.finrank_riemannSpace_add_divisorOf}

The defect is bounded uniformly: any divisor is dominated, up to a
principal divisor, by a high multiple of the pole divisor of a fixed
transcendental element, and on those multiples the counting family from
the degree theorem pins the defect down. The genus is the supremum of
the defect, and Riemann's inequality holds by construction:

{docstring AclGeom.exists_forall_defect_le}

{docstring AclGeom.genus}

{docstring AclGeom.riemann_inequality}

{docstring AclGeom.genus_nonneg}

# The genus-zero checkpoint
%%%
tag := "genus-zero"
%%%

At genus zero the theory pays off: Riemann's inequality at a single
place gives `ℓ(P) ≥ 2`, so some element of `L(P)` is not constant; its
one and only pole is `P`, of order one, so the degree theorem forces
`[F : k(t)] = 1` — the function field is rational, with a generator
whose pole sits at any prescribed place:

{docstring AclGeom.exists_generator_of_genus_eq_zero}

The converse holds as well: on a rational function field every
degree-zero divisor is principal — partial fractions in divisor form,
products of shifts of the generator — so every defect reduces to a
multiple of the pole place, where the powers of the generator fill the
Riemann–Roch space. Genus zero characterizes rationality:

{docstring AclGeom.exists_divisorOf_eq_of_deg_eq_zero}

{docstring AclGeom.genus_eq_zero_iff_exists_generator}

# Adeles and the index of specialty
%%%
tag := "adeles"
%%%

The correction term in Riemann's inequality is computed adelically. The
adele space collects place-indexed families that are integral almost
everywhere, filtered by divisor bounds whose diagonal slice is exactly
the Riemann–Roch space; unlike `L(D)`, the bounded adele spaces grow by
exactly a line per point — the spanning monomial always exists — and
the dichotomy trades that line against the growth of `L`:

{docstring AclGeom.adeleSubmodule}

{docstring AclGeom.adeleSpace_add_single}

{docstring AclGeom.adeleMonomial_mem_sup_iff}

The genus is attained and stays attained upward — the stabilized form
of Riemann's theorem — which yields adelic surjectivity with no
dimension bookkeeping, and then the index of specialty turns Riemann's
inequality into an identity:

{docstring AclGeom.defect_eq_genus_of_le}

{docstring AclGeom.adeleSubmodule_eq_sup_of_defect_eq_genus}

{docstring AclGeom.finiteDimensional_finrank_specialtyQuotient}

{docstring AclGeom.finrank_riemannSpace_eq_add_specialtyIndex}

# Weil differentials and the canonical class
%%%
tag := "canonical"
%%%

A Weil differential of level `D` is a functional on the adeles killing
`A(D) + F`; the space of them is the dual of the specialty quotient, of
dimension `i(D)`. Multiplication by a field element shifts levels by
principal divisors, injectively — so the levels of a fixed nonzero
differential are degree-bounded, and being join-closed they admit a
maximum: the divisor of the differential.

{docstring AclGeom.weilDifferentialsAt}

{docstring AclGeom.deg_le_of_mem_weilDifferentialsAt}

{docstring AclGeom.exists_isGreatest_level}

Any two nonzero differentials are proportional over the function field
— the two-parameter double-count against `Ω(−B)` collapses for large
`deg B` — and proportionality plus the maximal-level shift make the
multiplication pairing `L(W − D) → Ω(D)` bijective. This is the
duality theorem, and evaluating it at `D = 0` and `D = W` pins the
canonical class:

{docstring AclGeom.exists_eq_comp_adeleSMul}

{docstring AclGeom.specialtyIndex_eq_finrank_riemannSpace}

{docstring AclGeom.exists_canonicalDivisor}

# Tate's abstract trace
%%%
tag := "tate-trace"
%%%

The residue theory that connects differentials to orders of functions
is built on Tate's linear algebra of *finite-potent* endomorphisms: on
an arbitrary vector space, an operator some power of which has
finite-dimensional range carries a well-defined trace, computed on any
*core* — a finite-dimensional invariant subspace absorbing a power —
because the induced action beyond a core is nilpotent:

{docstring AclGeom.IsFinitePotent}

{docstring AclGeom.IsTateCore}

{docstring AclGeom.tateTrace}

The calculus of this trace runs through squared ranges: symmetry
`tr(αβ) = tr(βα)` and additivity hold as soon as the relevant
length-two words have finite-dimensional range, and commutators of
such pairs are traceless — no finiteness is needed on the factors
themselves:

{docstring AclGeom.tateTrace_comp_comm_of_sq}

{docstring AclGeom.tateTrace_add_of_sq}

{docstring AclGeom.tateTrace_comp_sub_comp_comm_of_sq}

{docstring AclGeom.tateTrace_of_isIdempotentElem}

Tate's commensurability order compares subspaces up to
finite-dimensional error, and the operators whose ranges are almost
inside a fixed subspace and which almost kill it form the trace class
of that subspace:

{docstring AclGeom.AlmostLE}

{docstring AclGeom.IsTraceClass}

# The residue
%%%
tag := "residue"
%%%

At a place, the valuation ring is commensurable with all its
uniformizer shifts — each filtration step is gauged by one residue —
and multiplication operators respect the commensurability class:

{docstring AclGeom.Place.filtration_almostLE}

Choosing a linear projection `ε` onto the valuation ring, the
commutator `c(h) = [ε, mult h]` is trace-class, and the residue of
`f dg` is the Tate trace of the commutator `[ε ∘ mult f, mult g]`:

{docstring AclGeom.Place.commutatorProj}

{docstring AclGeom.Place.isTraceClass_commutatorProj}

{docstring AclGeom.Place.residue}

The residue is bilinear, vanishes on integral pairs, and — the anchor
identity — counts the order of a function on the logarithmic
differential `dg/g`: the residue commutator at `(g⁻¹, g)` is the
difference of the projections onto `O_P` and `g O_P`, the trace flips
to an idempotent projecting onto a transversal of `g O_P` in `O_P`,
and the transversal has dimension exactly `ord g` by the finite Taylor
expansion and dominant-term independence:

{docstring AclGeom.Place.residue_add_left}

{docstring AclGeom.Place.residue_eq_zero_of_mem}

{docstring AclGeom.Place.finrank_map_id_sub_conjProj}

{docstring AclGeom.Place.residue_inv_self}

The residue does not depend on the chosen projection — the difference
of two projections onto commensurable targets has finite-rank
composites against all words in the multiplication operators, so the
commutators differ by a traceless commutator. In particular the
residue reads off any filtration stage:

{docstring AclGeom.tateTrace_commutator_eq_of_projection}

{docstring AclGeom.Place.residue_eq_of_projection_filtration}

# The residue theorem
%%%
tag := "residue-theorem"
%%%

Globally, the bounded adele spaces inside the adele module are
pairwise commensurable, multiplication almost-stabilizes each of
them, and the residue commutator of a projection onto a bounded space
is trace-class:

{docstring AclGeom.almostLE_adeleSpaceIn}

{docstring AclGeom.isTraceClass_adeleSMul_commutator}

Two traces are computed for the same commutator. Against the diagonal
decomposition `𝔸 = A(D₀) + F` at an effective genus-attaining divisor
— the stabilized Riemann theorem — the compatible projection pair
splits the commutator into the vanishing commutator of
multiplications, a finite-rank piece on the diagonal Riemann–Roch
space, and a square-zero piece on the invariant diagonal, so the
trace is zero:

{docstring AclGeom.exists_projection_pair}

{docstring AclGeom.tateTrace_adeleSMul_commutator_eq_zero}

Against the componentwise projection onto local filtration stages,
the commutator acts blockwise; it is the sum of its single-place
blocks over the bad set plus a square-zero remainder, blocks at
distinct places compose to zero, and the Tate trace is additive over
such families — so the same trace is the sum of the local residues:

{docstring AclGeom.tateTrace_finset_sum}

{docstring AclGeom.tateTrace_blockOp}

{docstring AclGeom.tateTrace_adeleProj_commutator}

The two computations combine into the residue theorem:

{docstring AclGeom.sum_residue_eq_zero}

Next in this library: local vanishing thresholds for the residue,
the differentials attached to field elements, and automorphism
rigidity via vector fields against the canonical degree `2g − 2`,
tracked on the curve-theory issue.
