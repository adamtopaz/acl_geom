/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.PolynomialFrobeniusFactor
import AclGeom.Correspondence.FinitePointInjectivity
import AclGeom.Correspondence.AdditiveOrbitCover
import AclGeom.Correspondence.AffineGroupGeometry

/-!
# The actual finite line cover of an affine curve over Ga

**Status:** for an actual integral affine locally finite-type curve of dimension one over
an ACF base, a finite surjective point-injective map to Ga internally gives a finite
surjective Ga cover whose composite is relative Frobenius. Its formula holds over every
commutative coefficient algebra in the base universe. Zero/one separation proves actual
finiteness and surjectivity. The original curve need not be normal. Named consumer:
`FiniteGaCover.exists_group_cover` for the actual connected normal subgroup (#21).
-/

namespace AclGeom.FiniteGaCover
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
attribute [local instance] SchemeGenericTranslate.sectionsAlgebra

/-- Named consumer: the actual normal subgroup has a finite Ga cover. Finite point-
injectivity of its map to Ga supplies all polynomial and Frobenius data internally. -/
theorem exists_line_cover
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] (hdim : topologicalKrullDim V.left = 1)
    (β : V ⟶ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X)
    [IsFinite β.left] [Surjective β.left]
    (hinj : Function.Injective (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ V ↦ q ≫ β))
    (p : ℕ) [ExpChar k p] :
    ∃ (n : ℕ) (a : (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ⟶ V),
      IsFinite a.left ∧ Surjective a.left ∧
      a ≫ β = AffineSchemeAction.linePoint k (AffineSchemeAction.lineCoordinate k ^ p ^ n) ∧
      ∀ (C : Type u) [CommRing C] [Algebra k C] (c : C),
        AffineSchemeAction.linePoint k c ≫ a ≫ β =
          AffineSchemeAction.linePoint k (c ^ p ^ n) := by
  classical
  let A : Type u := Γ(V.left, ⊤)
  let R := AdditiveGroupScheme.CoordinateRing k 1
  let P := AdditiveTranslation.polynomialCoordinates k
  let e : V ≅ (Spec (.of A)).asOver (Spec (.of k)) :=
    SchemeGenericTranslate.sectionsSpecIso V
  let e₀ : V.left ≅ Spec (.of A) := (Over.forget (Spec (.of k))).mapIso e
  let βraw : V.left ⟶ Spec (.of R) := β.left
  have : IsFinite βraw := ‹IsFinite β.left›
  have : Surjective βraw := ‹Surjective β.left›
  have : IsDomain A := inferInstance
  obtain ⟨β₀, hβ₀⟩ := AdditiveOrbit.exists_algHom_of_spec_hom R A (e.inv ≫ β)
  have hβleft := congrArg Over.Hom.left hβ₀
  change Spec.map (CommRingCat.ofHom β₀.toRingHom) = e₀.inv ≫ βraw at hβleft
  have : IsFinite e₀.inv := inferInstance
  have : IsFinite (Spec.map (CommRingCat.ofHom β₀.toRingHom)) := by
    rw [hβleft]
    exact CategoryTheory.MorphismProperty.IsStableUnderComposition.comp_mem
      e₀.inv βraw inferInstance inferInstance
  have hβfin : β₀.toRingHom.Finite :=
    (IsFinite.SpecMap_iff (CommRingCat.ofHom β₀.toRingHom)).mp inferInstance
  have hβsurj : Surjective (Spec.map (CommRingCat.ofHom β₀.toRingHom)) := by
    rw [hβleft]
    exact ⟨βraw.surjective.comp e₀.inv.surjective⟩
  have hβinj : Function.Injective β₀ := by
    obtain ⟨Q, hQ⟩ := hβsurj.1 (⟨⊥, inferInstance⟩ : PrimeSpectrum R)
    have hcomap : Ideal.comap β₀.toRingHom Q.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal hQ
    apply (RingHom.injective_iff_ker_eq_bot β₀.toRingHom).mpr
    apply le_antisymm ?_ bot_le
    intro r hr
    rw [RingHom.mem_ker] at hr
    change β₀ r = 0 at hr
    rw [← hcomap]
    change β₀ r ∈ Q.asIdeal
    rw [hr]
    exact Q.asIdeal.zero_mem
  have hβuniv : UniversallyInjective β.left :=
    GroupFinite.universallyInjective_of_point_injective β hinj
  have : UniversallyInjective βraw := hβuniv
  have : UniversallyInjective (Spec.map (CommRingCat.ofHom β₀.toRingHom)) := by
    rw [hβleft]
    exact CategoryTheory.MorphismProperty.IsStableUnderComposition.comp_mem
      e₀.inv βraw inferInstance inferInstance
  let δ : Polynomial k →ₐ[k] A := β₀.comp P.symm.toAlgHom
  have hδinj : Function.Injective δ := hβinj.comp P.symm.injective
  have hδfin : δ.toRingHom.Finite := hβfin.comp P.symm.toRingEquiv.finite
  have hδleft : Spec.map (CommRingCat.ofHom δ.toRingHom) =
      Spec.map (CommRingCat.ofHom β₀.toRingHom) ≫
        Spec.map (CommRingCat.ofHom P.symm.toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  have : IsIso (CommRingCat.ofHom P.symm.toRingHom) :=
    P.symm.toRingEquiv.toCommRingCatIso.isIso_hom
  have : IsIso (Spec.map (CommRingCat.ofHom P.symm.toRingHom)) := inferInstance
  have : UniversallyInjective (Spec.map (CommRingCat.ofHom P.symm.toRingHom)) := inferInstance
  have : UniversallyInjective (Spec.map (CommRingCat.ofHom δ.toRingHom)) := by
    rw [hδleft]
    exact CategoryTheory.MorphismProperty.IsStableUnderComposition.comp_mem
      (Spec.map (CommRingCat.ofHom β₀.toRingHom))
      (Spec.map (CommRingCat.ofHom P.symm.toRingHom)) inferInstance inferInstance
  obtain ⟨n, θ, _, hθ⟩ := exists_polynomial_frobenius_factor p δ hδinj hδfin
  let σ : A →ₐ[k] R := P.symm.toAlgHom.comp θ
  let a : (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ⟶ V :=
    (algSpec (.of k)).map (CommAlgCat.ofHom σ).op ≫ e.inv
  have hθX : θ (δ Polynomial.X) = Polynomial.X ^ p ^ n := by
    have h := AlgHom.congr_fun hθ Polynomial.X
    simpa only [AlgHom.comp_apply, Polynomial.aeval_X] using h
  have hcompAlg : σ.comp β₀ = AffineSchemeAction.lineEval
      (k := k) (AffineSchemeAction.lineCoordinate k ^ p ^ n) := by
    apply AffineSchemeAction.lineHom_ext
    rw [AffineSchemeAction.lineEval_lineCoordinate]
    change P.symm (θ (β₀ (AffineSchemeAction.lineCoordinate k))) = _
    have hx : δ Polynomial.X = β₀ (AffineSchemeAction.lineCoordinate k) := by
      change β₀ (P.symm Polynomial.X) = _
      rw [← AdditiveTranslation.polynomialCoordinates_coordinate k, AlgEquiv.symm_apply_apply]
    rw [← hx, hθX, map_pow]
    rw [← AdditiveTranslation.polynomialCoordinates_coordinate k, AlgEquiv.symm_apply_apply]
  have hcomp : a ≫ β = AffineSchemeAction.linePoint k
      (AffineSchemeAction.lineCoordinate k ^ p ^ n) := by
    apply Over.OverMorphism.ext
    change (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ e₀.inv) ≫ βraw =
      Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval
        (k := k) (AffineSchemeAction.lineCoordinate k ^ p ^ n)).toRingHom)
    rw [Category.assoc, ← hβleft, ← Spec.map_comp]
    exact congrArg Spec.map (congrArg (fun f : R →ₐ[k] R ↦
      CommRingCat.ofHom f.toRingHom) hcompAlg)
  have hformula (C : Type u) [CommRing C] [Algebra k C] (c : C) :
      AffineSchemeAction.linePoint k c ≫ a ≫ β =
        AffineSchemeAction.linePoint k (c ^ p ^ n) := by
    rw [hcomp, AdditiveTranslation.linePoint_comp_linePoint, map_pow,
      AffineSchemeAction.lineEval_lineCoordinate]
  have hne : AffineSchemeAction.linePoint k (0 : k) ≫ a ≠
      AffineSchemeAction.linePoint k (1 : k) ≫ a := by
    intro h
    have hh := congrArg (fun z ↦ z ≫ β) h
    rw [Category.assoc, Category.assoc, hformula, hformula,
      zero_pow (Nat.ne_of_gt (expChar_pow_pos k p n)), one_pow] at hh
    exact zero_ne_one (AffineSchemeAction.linePoint_injective k hh)
  have hcover := AdditiveOrbit.finite_surjective_of_separates_zero_one V hdim a hne
  exact ⟨n, a, hcover.1, hcover.2, hcomp, hformula⟩

end
end AclGeom.FiniteGaCover
