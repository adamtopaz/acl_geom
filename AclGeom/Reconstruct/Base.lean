/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Closure.CrossBase
import AclGeom.Interpretation.Naturality
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Recovery of the base field

The corrected conditional base-recovery target is proved: the actual `interpretedRingEquiv`
carries the image of `k` onto the image of `l` (Prop `base-recovery`), under its explicit carrier
inputs and both relatively closed bases. The base-ratio corollary below is its prerequisite.

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

For the actual interpreted ring equivalence, `interpretedRingEquiv_algebraMap_mem` proves the
forward base inclusion under target `IsRAC` only. The ratio representation uses the canonical
base element as denominator, so its image is fixed by the supplied tuple equality; only the
zero and product point coordinates are needed. `interpretedRingEquiv_symm` identifies the actual
inverse with the swapped construction pointwise by reflexivity, without any RAC hypothesis.
It takes the redundant inverse tuple equality explicitly. `interpretedRingEquiv_compatible`
derives that equality inline and proves `CrossBase.Compatible` under both RAC bases.

**Status:** the no-fresh relative base-ratio corollary and its actual base-membership form are
complete (#5/#9, R1a/C7b), without rank, freshness, perfection, completeness or an exponential
characteristic; base membership names `IsRAC` explicitly. Corrected base recovery for the actual
`interpretedRingEquiv` is complete (#9, conditional R1b) under both perfections/rank-five bounds,
separate exponential characteristics, both still-open ACF J-completeness inputs and the canonical
image-base equality, with both `IsRAC` hypotheses for compatibility. Corrected conditional scalar
one and outside-point recovery are proved in `Reconstruct.Scalar` under the same carrier inputs,
without RAC. General unconditional R1/R2, public `Induces` assembly, unconditional completeness,
full reconstruction and literal source obligations remain open. The two ratio declarations are
unchanged.

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

open ClosedIF

variable {l L : Type*} [Field l] [Field L] [Algebra l L]

/-- **The reconstructed isomorphism carries the base into the base** (blueprint Prop
`base-recovery`, forward inclusion): if `l` is relatively algebraically closed in `L`, the
corrected interpreted reconstruction sends `k` into `l`.  For `c ≠ 0`, the class of
`(j(c x₀, a), j(x₀, a))` decodes to `c`, and its image is the class of `(j(y, a'), j(x₀', a'))`.
Scaling by `c` fixes the points `[x₀]` and `[x₀ a]`, so `[y] = [x₀']` and `[y a'] = [x₀' a']`,
and the base-ratio corollary puts `y / x₀'` in `l`. -/
theorem interpretedRingEquiv_algebraMap_mem [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    [PerfectField L] (q' : ℕ) [ExpChar L q']
    (htr' : (5 : Cardinal) ≤ Algebra.trdeg l L)
    (hcomp' : JCompletenessACF (↥(algebraicClosure l (AlgebraicClosure L))) (AlgebraicClosure L))
    (e : ClosedIF k K ≃o ClosedIF l L) {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    {x₀' a' : L} (h₀' : AlgebraicIndependent l ![x₀', a'])
    (hφ : Point.map e ∘ jTupleOf x₀ a h₀ = jTupleOf x₀' a' h₀')
    (hl : IsRAC (⊥ : IntermediateField l L)) (c : k) :
    interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ (algebraMap k K c) ∈
      Set.range (algebraMap l L) := by
  rcases eq_or_ne c 0 with rfl | hc
  · let σ := interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ
    exact ⟨0, (map_zero (algebraMap l L)).trans
      ((map_zero σ).symm.trans ((congrArg σ (map_zero (algebraMap k K))).symm))⟩
  -- The class of `(j(c x₀, a), j(x₀, a))` decodes to `c`.
  have hx₀0 : x₀ ≠ 0 := AlgebraicIndependent.ne_zero h₀ 0
  have hcx : AlgebraicIndependent k ![algebraMap k K c * x₀, a] :=
    algebraicIndependent_pair_congr (racl_algebraMap_mul hc x₀).symm rfl h₀
  have hu : FrobEq (jTupleOf x₀ a h₀) (jTupleOf (algebraMap k K c * x₀) a hcx) :=
    frobEq_jTupleOf_of_common htr h₀ hcx
  have hv : FrobEq (jTupleOf x₀ a h₀) (jTupleOf x₀ a h₀) := frobEq_jTupleOf_of_common htr h₀ h₀
  have hD : ratioInterpDecode q htr hcomp h₀
      ((Quotient.mk (ratioSetoid q htr hcomp h₀)
        (⟨jTupleOf (algebraMap k K c * x₀) a hcx, hu⟩, ⟨jTupleOf x₀ a h₀, hv⟩) : Quotient _) :
        RatioInterp q htr hcomp h₀) = algebraMap k K c := by
    rw [ratioInterpDecode_coe, jClassEquiv_jTupleOf, jClassEquiv_jTupleOf]
    exact mul_div_cancel_right₀ _ hx₀0
  -- Its image is the class of `(j(y, a'), j(x₀', a'))`, which decodes to `y / x₀'`.
  obtain ⟨y, hy, hyu⟩ := (frobEq_jTupleOf_iff q' htr' hcomp' h₀').1
    (ratioClassMap e h₀ h₀' hφ ⟨jTupleOf (algebraMap k K c * x₀) a hcx, hu⟩).2
  have hCu : ratioClassMap e h₀ h₀' hφ ⟨jTupleOf (algebraMap k K c * x₀) a hcx, hu⟩ =
      ⟨jTupleOf y a' hy, frobEq_jTupleOf_of_common htr' h₀' hy⟩ := Subtype.ext hyu
  have hCv : ratioClassMap e h₀ h₀' hφ ⟨jTupleOf x₀ a h₀, hv⟩ =
      ⟨jTupleOf x₀' a' h₀', frobEq_jTupleOf_of_common htr' h₀' h₀'⟩ := Subtype.ext hφ
  have hval : interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ (algebraMap k K c) =
      y / x₀' := by
    change ratioInterpDecode q' htr' hcomp' h₀'
      (ratioInterpMap q htr hcomp q' htr' hcomp' e h₀ h₀' hφ
        ((ratioInterpDecode q htr hcomp h₀).symm (algebraMap k K c))) = y / x₀'
    rw [(Equiv.symm_apply_eq _).2 hD.symm]
    change ratioInterpDecode q' htr' hcomp' h₀'
      ((Quotient.mk (ratioSetoid q' htr' hcomp' h₀')
        (ratioClassMap e h₀ h₀' hφ ⟨jTupleOf (algebraMap k K c * x₀) a hcx, hu⟩,
          ratioClassMap e h₀ h₀' hφ ⟨jTupleOf x₀ a h₀, hv⟩) : Quotient _) :
        RatioInterp q' htr' hcomp' h₀') = y / x₀'
    rw [hCu, hCv, ratioInterpDecode_coe, jClassEquiv_jTupleOf, jClassEquiv_jTupleOf]
  -- Scaling by `c` fixes the points `[x₀]` and `[x₀ a]`; push them along `e`.
  have hpt : ∀ z : K, point k (algebraMap k K c * z) = point k z := fun z ↦ by
    have hr := racl_algebraMap_mul hc z
    refine point_eq_point_iff.2 ⟨?_, ?_⟩
    · rw [mem_point, ← hr]
      exact subset_racl k _ rfl
    · rw [mem_point, hr]
      exact subset_racl k _ rfl
  have hpt2 : point k (algebraMap k K c * x₀ * a) = point k (x₀ * a) := by
    rw [mul_assoc]
    exact hpt (x₀ * a)
  have h0 : point l y = point l x₀' := congrArg Subtype.val
    ((congrFun hyu 0).symm.trans ((congrArg (Point.map e) (Subtype.ext (hpt x₀) :
      jTupleOf (algebraMap k K c * x₀) a hcx 0 = jTupleOf x₀ a h₀ 0)).trans (congrFun hφ 0)))
  have h2 : point l (y * a') = point l (x₀' * a') := congrArg Subtype.val
    ((congrFun hyu 2).symm.trans ((congrArg (Point.map e) (Subtype.ext hpt2 :
      jTupleOf (algebraMap k K c * x₀) a hcx 2 = jTupleOf x₀ a h₀ 2)).trans (congrFun hφ 2)))
  -- The base-ratio corollary in `L`.
  have hy0 : y ≠ 0 := AlgebraicIndependent.ne_zero hy 0
  obtain ⟨hy₁, hy₂⟩ := point_eq_point_iff.1 h0
  obtain ⟨hm₁, hm₂⟩ := point_eq_point_iff.1 h2
  obtain ⟨d, hd⟩ := base_ratio_mem_range hl h₀' hy0 hy₁ hy₂ hm₁ hm₂
  refine ⟨d⁻¹, ?_⟩
  rw [hval, map_inv₀, hd, inv_div]

/-- **The inverse of the reconstructed isomorphism is the reconstruction for the inverse lattice
isomorphism**: the geometric carrier maps of `e` and `e.symm` are mutually inverse, so the two
composites through the decodings are inverse. -/
theorem interpretedRingEquiv_symm [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    [PerfectField L] (q' : ℕ) [ExpChar L q']
    (htr' : (5 : Cardinal) ≤ Algebra.trdeg l L)
    (hcomp' : JCompletenessACF (↥(algebraicClosure l (AlgebraicClosure L))) (AlgebraicClosure L))
    (e : ClosedIF k K ≃o ClosedIF l L) {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    {x₀' a' : L} (h₀' : AlgebraicIndependent l ![x₀', a'])
    (hφ : Point.map e ∘ jTupleOf x₀ a h₀ = jTupleOf x₀' a' h₀')
    (hφ' : Point.map e.symm ∘ jTupleOf x₀' a' h₀' = jTupleOf x₀ a h₀) :
    (interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ).symm =
      interpretedRingEquiv q' htr' hcomp' q htr hcomp e.symm h₀' h₀ hφ' := by
  exact RingEquiv.ext fun _ ↦ rfl

/-- **Base recovery for the corrected interpreted reconstruction** (blueprint Prop
`base-recovery`): if `k` and `l` are relatively algebraically closed in `K` and `L`, the
reconstructed isomorphism carries the image of `k` onto the image of `l`.  The reverse inclusion
is the forward one for `e.symm`, through `interpretedRingEquiv_symm`. -/
theorem interpretedRingEquiv_compatible [PerfectField K] (q : ℕ) [ExpChar K q]
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    (hcomp : JCompletenessACF (↥(algebraicClosure k (AlgebraicClosure K))) (AlgebraicClosure K))
    [PerfectField L] (q' : ℕ) [ExpChar L q']
    (htr' : (5 : Cardinal) ≤ Algebra.trdeg l L)
    (hcomp' : JCompletenessACF (↥(algebraicClosure l (AlgebraicClosure L))) (AlgebraicClosure L))
    (e : ClosedIF k K ≃o ClosedIF l L) {x₀ a : K} (h₀ : AlgebraicIndependent k ![x₀, a])
    {x₀' a' : L} (h₀' : AlgebraicIndependent l ![x₀', a'])
    (hφ : Point.map e ∘ jTupleOf x₀ a h₀ = jTupleOf x₀' a' h₀')
    (hk : IsRAC (⊥ : IntermediateField k K)) (hl : IsRAC (⊥ : IntermediateField l L)) :
    CrossBase.Compatible (k := k) (l := l)
      (interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ) := by
  -- The inverse lattice isomorphism carries the target base tuple back.
  have hφ' : Point.map e.symm ∘ jTupleOf x₀' a' h₀' = jTupleOf x₀ a h₀ := by
    rw [← hφ]
    funext i
    exact Subtype.ext (e.symm_apply_apply _)
  unfold CrossBase.Compatible
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subfield.mem_map.1 hy
    obtain ⟨c, rfl⟩ := RingHom.mem_fieldRange.1 hx
    obtain ⟨d, hd⟩ :=
      interpretedRingEquiv_algebraMap_mem q htr hcomp q' htr' hcomp' e h₀ h₀' hφ hl c
    exact RingHom.mem_fieldRange.2 ⟨d, hd⟩
  · intro y hy
    obtain ⟨d, rfl⟩ := RingHom.mem_fieldRange.1 hy
    refine Subfield.mem_map.2 ⟨(interpretedRingEquiv q htr hcomp q' htr' hcomp' e h₀ h₀' hφ).symm
      (algebraMap l L d), ?_, RingEquiv.apply_symm_apply _ _⟩
    rw [interpretedRingEquiv_symm q htr hcomp q' htr' hcomp' e h₀ h₀' hφ hφ']
    obtain ⟨c, hc⟩ :=
      interpretedRingEquiv_algebraMap_mem q' htr' hcomp' q htr hcomp e.symm h₀' h₀ hφ' hk d
    exact RingHom.mem_fieldRange.2 ⟨c, hc⟩

end

end AclGeom
