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

Next in this library: Riemann's inequality and the genus, then the
genus-zero checkpoint `F ≃ k(t)` — tracked on the curve-theory issue.
