/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.Naturality
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Recovery of the base field

The blueprint base-recovery target is that the reconstructed field equivalence carries `k`
onto `l` (Prop `base-recovery`). The base-ratio corollary proved here is its prerequisite.

This module proves the base-ratio corollary (blueprint Corollary `base-ratio`) over an arbitrary
base.  Let `u₁, t` be independent over `k` and `u₂ ≠ 0`.  Suppose `[u₁] = [u₂]` and
`[u₁ t] = [u₂ t]` (interalgebraicity over `k`).  Then `u₂ / u₁` is algebraic over `k`
(`base_ratio_rel`). The inverse ratio `u₁ / u₂` lies in the actual image of `k` when that base
is relatively algebraically closed in `K` (`base_ratio_mem_range`).

The proof embeds `K` into the algebraic closure `Ω` of the rational function field `K(X)`.  It
applies the base-ratio lemma `base_ratio` there, over the algebraic closure `K₀` of `k` in `Ω`.
The image of the variable `X` is transcendental over `K`, so it supplies the fresh third element
that `base_ratio` needs.  No rank hypothesis on `K` is required.  Closures over `k` and over `K₀`
agree because `K₀` is algebraic over `k` (`mem_racl_base_iff_of_algebraic`).  Closure membership
is insensitive to the ambient field (`algHom_mem_racl_image_iff`).

**Status:** the no-fresh relative base-ratio corollary and its actual base-membership form are
complete (#5/#9, R1a). No rank, freshness, perfection, completeness or exponential-characteristic
input is assumed; base membership names `IsRAC` explicitly. Recovery of the base by the actual
`interpretedRingEquiv`, scalar one, `Induces` and full reconstruction remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **The base-ratio corollary over an arbitrary base** (blueprint Corollary `base-ratio`): if
`u₁, t` are independent over `k`, `u₂ ≠ 0`, and both `[u₁] = [u₂]` and `[u₁ t] = [u₂ t]`, then
`u₂ / u₁` is algebraic over `k`.  No fresh element in `K` is needed: the image of the variable of
`K(X)` in its algebraic closure serves as one. -/
theorem base_ratio_rel {u₁ u₂ t : K} (hind : AlgebraicIndependent k ![u₁, t]) (hu₂0 : u₂ ≠ 0)
    (hu₂ : u₂ ∈ racl k ({u₁} : Set K)) (hu₁ : u₁ ∈ racl k ({u₂} : Set K))
    (hmul : u₂ * t ∈ racl k ({u₁ * t} : Set K)) (hmul' : u₁ * t ∈ racl k ({u₂ * t} : Set K)) :
    u₂ / u₁ ∈ racl k (∅ : Set K) := by
  -- Work in the algebraic closure `Ω` of `K(X)`, over the algebraic closure `K₀` of `k` in `Ω`.
  let ι : K →ₐ[k] AlgebraicClosure (RatFunc K) :=
    IsScalarTower.toAlgHom k K (AlgebraicClosure (RatFunc K))
  let K₀ := algebraicClosure k (AlgebraicClosure (RatFunc K))
  have : IsAlgClosed ↥K₀ := IsAlgClosure.isAlgClosed k
  have halg : ∀ z ∈ K₀, IsAlgebraic k z := fun z hz ↦ mem_algebraicClosure_iff.1 hz
  have key : ∀ {S : Set K} {z : K}, ι z ∈ racl (↥K₀) (⇑ι '' S) ↔ z ∈ racl k S :=
    (mem_racl_base_iff_of_algebraic halg).trans (algHom_mem_racl_image_iff ι)
  have hinj : Function.Injective ι := ι.toRingHom.injective
  have hind' : AlgebraicIndependent (↥K₀) ![ι u₁, ι t] := by
    have h := AlgebraicIndependent.extendScalars (↥K₀) (hind.map' hinj)
    convert h using 1
    ext i
    fin_cases i <;> rfl
  -- The image of the variable `X` is fresh over `ι u₁, ι t`: it is transcendental over `K`.
  have hs : algebraMap (RatFunc K) (AlgebraicClosure (RatFunc K)) RatFunc.X ∉
      racl (↥K₀) ({ι u₁, ι t} : Set (AlgebraicClosure (RatFunc K))) := by
    rw [mem_racl_base_iff_of_algebraic halg]
    have hle : adjoin k ({ι u₁, ι t} : Set (AlgebraicClosure (RatFunc K))) ≤ ι.fieldRange := by
      refine adjoin_le_iff.2 ?_
      rintro z (rfl | rfl)
      · exact ⟨u₁, rfl⟩
      · exact ⟨t, rfl⟩
    have hX : Transcendental K
        (algebraMap (RatFunc K) (AlgebraicClosure (RatFunc K)) RatFunc.X) :=
      (transcendental_algebraMap_iff
        (algebraMap (RatFunc K) (AlgebraicClosure (RatFunc K))).injective).2
        (RatFunc.transcendental_X (K := K))
    have hX' : Transcendental ι.fieldRange
        (algebraMap (RatFunc K) (AlgebraicClosure (RatFunc K)) RatFunc.X) :=
      hX.ringHom_of_comp_eq ι.equivFieldRange.toRingHom
        (RingHom.id (AlgebraicClosure (RatFunc K)))
        ι.equivFieldRange.surjective Function.injective_id rfl
    exact fun hx ↦ hX' (isAlgebraic_of_le hle ((mem_racl_iff k).1 hx))
  -- The base-ratio lemma over `K₀` gives `ι u₂ = e * ι u₁` with `e` algebraic over `k`.
  have hu₁0 : u₁ ≠ 0 := AlgebraicIndependent.ne_zero hind 0
  obtain ⟨e, -, he⟩ := base_ratio hind' ((map_ne_zero_iff ι hinj).2 hu₂0)
    (by simpa using key.2 hu₂) (by simpa using key.2 hu₁) (by simpa using key.2 hmul)
    (by simpa using key.2 hmul') hs
  have hdiv : ι (u₂ / u₁) = algebraMap (↥K₀) (AlgebraicClosure (RatFunc K)) e := by
    rw [map_div₀, he, mul_div_cancel_right₀ _ ((map_ne_zero_iff ι hinj).2 hu₁0)]
  refine (algHom_mem_racl_empty_iff ι).1 ?_
  rw [hdiv]
  exact mem_racl_empty_of_isAlgebraic (halg _ e.2)

/-- **The base-ratio corollary over a relatively algebraically closed base** (blueprint
Corollary `base-ratio`, final clause): if moreover `k` is relatively algebraically closed in `K`,
then `u₁ / u₂` lies in `k`. -/
theorem base_ratio_mem_range (hRAC : IsRAC (⊥ : IntermediateField k K)) {u₁ u₂ t : K}
    (hind : AlgebraicIndependent k ![u₁, t]) (hu₂0 : u₂ ≠ 0)
    (hu₂ : u₂ ∈ racl k ({u₁} : Set K)) (hu₁ : u₁ ∈ racl k ({u₂} : Set K))
    (hmul : u₂ * t ∈ racl k ({u₁ * t} : Set K)) (hmul' : u₁ * t ∈ racl k ({u₂ * t} : Set K)) :
    u₁ / u₂ ∈ Set.range (algebraMap k K) := by
  have hratio : u₁ / u₂ ∈ racl k (∅ : Set K) := by
    rw [← inv_div]
    exact inv_mem (base_ratio_rel hind hu₂0 hu₂ hu₁ hmul hmul')
  apply IntermediateField.mem_bot.1
  have h : u₁ / u₂ ∈ racl k ((⊥ : IntermediateField k K) : Set K) :=
    racl_mono (Set.empty_subset _) hratio
  rwa [isRAC_iff_racl_eq.1 hRAC] at h

end

end AclGeom
