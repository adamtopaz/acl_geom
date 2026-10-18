/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AdditivePolynomialMaps
import AclGeom.Correspondence.SchemeGenericTranslate
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# A nonconstant actual line map onto an integral affine curve is finite surjective

**Status:** a regular map from the actual additive line to an integral affine curve of
dimension one, separating zero and one, is finite and surjective over any field (#21).
Recover its actual algebra map from ordinary Spec full faithfulness and the over-base
identity. A nonconstant polynomial image gives finiteness. A nonzero prime kernel in the
dimension-one domain would be maximal; integrality would then make the polynomial ring a
field. Thus the map is injective, and integral lying-over gives scheme surjectivity.
Named consumer: `AdditiveOrbit.exists_finite_orbit_cover`, which constructs the actual
orbit and separating points internally. No finiteness or dominance certificate is supplied.
-/

namespace AclGeom.AdditiveOrbit
noncomputable section
open Polynomial
universe u
variable {k A : Type u} [Field k] [CommRing A]

/-- Named consumer: an actual nonconstant regular line map into an affine curve is finite. -/
theorem finite_of_nonconstant_polynomial_image [Algebra k A] (φ : A →ₐ[k] k[X]) (a : A)
    (ha : (φ a).natDegree ≠ 0) : φ.toRingHom.Finite := by
  have hcomp : φ.toRingHom.comp (aeval (R := k) a).toRingHom =
      (aeval (R := k) (φ a)).toRingHom :=
    congrArg AlgHom.toRingHom (Polynomial.aeval_algHom φ a).symm
  apply RingHom.Finite.of_comp_finite (f := (aeval (R := k) a).toRingHom)
  rw [hcomp]
  exact AdditiveTranslation.polynomial_aeval_finite (φ a) ha

/-- Named consumer: surjectivity of the actual finite line-to-curve map by lying-over. -/
theorem injective_finite_to_polynomial [IsDomain A] [Ring.KrullDimLE 1 A]
    (φ : A →+* k[X]) (hφ : φ.Finite) : Function.Injective φ := by
  by_contra hinj
  have hker : RingHom.ker φ ≠ ⊥ := fun h ↦ hinj ((RingHom.injective_iff_ker_eq_bot φ).mpr h)
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hm : (RingHom.ker φ).IsMaximal :=
    Ideal.isMaximal_of_isPrime_of_ne_bot _ hker
  have hbot : (⊥ : Ideal k[X]).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap φ hφ.to_isIntegral ⊥ (by
      rw [← RingHom.ker_eq_comap_bot]
      exact hm)
  exact Polynomial.not_isField k (Ring.isField_iff_maximal_bot.mpr hbot)
end
end AclGeom.AdditiveOrbit

namespace AclGeom.AdditiveOrbit
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {k : Type u} [Field k]

/-- Named consumers: actual affine point separation and finite line-to-curve orbit maps. -/
theorem exists_algHom_of_spec_hom (A B : Type u) [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B]
    (f : (Spec (.of B)).asOver (Spec (.of k)) ⟶ (Spec (.of A)).asOver (Spec (.of k))) :
    ∃ φ : A →ₐ[k] B, (algSpec (.of k)).map (CommAlgCat.ofHom φ).op = f := by
  let f₀ : Spec (.of B) ⟶ Spec (.of A) := f.left
  obtain ⟨φ, hφ⟩ := Spec.map_surjective f₀
  have hcomp : CommRingCat.ofHom (algebraMap k A) ≫ φ =
      CommRingCat.ofHom (algebraMap k B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ]
    exact Over.w f
  let ψ : A →ₐ[k] B :=
    { φ.hom with
      commutes' := fun a ↦ congrArg (fun h : CommRingCat.of k ⟶ CommRingCat.of B ↦ h a) hcomp }
  refine ⟨ψ, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map φ = f₀
  exact hφ
end
end AclGeom.AdditiveOrbit

namespace AclGeom.AdditiveOrbit
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
universe u
variable {k : Type u} [Field k]
attribute [local instance] SchemeGenericTranslate.sectionsAlgebra

/-- A regular line map separating zero and one is an actual finite surjective map onto an
integral affine curve. Named consumer: the actual Ga orbit cover. -/
theorem finite_surjective_of_separates_zero_one
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    (hdim : topologicalKrullDim V.left = 1)
    (f : (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ⟶ V)
    (hne : AffineSchemeAction.linePoint k (0 : k) ≫ f ≠
      AffineSchemeAction.linePoint k (1 : k) ≫ f) :
    IsFinite f.left ∧ Surjective f.left := by
  classical
  let A : Type u := Γ(V.left, ⊤)
  let R := AdditiveGroupScheme.CoordinateRing k 1
  let e : V ≅ (Spec (.of A)).asOver (Spec (.of k)) :=
    SchemeGenericTranslate.sectionsSpecIso V
  let e₀ : V.left ≅ Spec (.of A) := (Over.forget (Spec (.of k))).mapIso e
  let f₁ : Spec (.of R) ⟶ V.left := f.left
  let f₀ : (Spec (.of R)).asOver (Spec (.of k)) ⟶
      (Spec (.of A)).asOver (Spec (.of k)) := f ≫ e.hom
  obtain ⟨σ, hσ⟩ := exists_algHom_of_spec_hom A R f₀
  have hσleft := congrArg Over.Hom.left hσ
  change Spec.map (CommRingCat.ofHom σ.toRingHom) = f₁ ≫ e₀.hom at hσleft
  let P := AdditiveTranslation.polynomialCoordinates k
  let η₀ : A →ₐ[k] Polynomial k := P.toAlgHom.comp σ
  have hex : ∃ a : A, (η₀ a).natDegree ≠ 0 := by
    by_contra! h
    have hcompare : (AffineSchemeAction.lineEval (k := k) (0 : k)).comp σ =
        (AffineSchemeAction.lineEval (k := k) (1 : k)).comp σ := by
      apply AlgHom.ext
      intro a
      simp only [AlgHom.comp_apply, AdditiveTranslation.lineEval_polynomialCoordinates]
      have ha : P (σ a) = Polynomial.C ((P (σ a)).coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero (h a)
      rw [ha, Polynomial.aeval_C, Polynomial.aeval_C]
    apply hne
    apply Over.OverMorphism.ext
    apply (cancel_mono e₀.hom).mp
    change (Spec.map (CommRingCat.ofHom
        (AffineSchemeAction.lineEval (k := k) (0 : k)).toRingHom) ≫ f₁) ≫ e₀.hom =
      (Spec.map (CommRingCat.ofHom
        (AffineSchemeAction.lineEval (k := k) (1 : k)).toRingHom) ≫ f₁) ≫ e₀.hom
    rw [Category.assoc, Category.assoc, ← hσleft]
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    change ((AffineSchemeAction.lineEval (k := k) (0 : k)).comp σ).toRingHom =
      ((AffineSchemeAction.lineEval (k := k) (1 : k)).comp σ).toRingHom
    exact congrArg AlgHom.toRingHom hcompare
  obtain ⟨a, ha⟩ := hex
  have hη : η₀.toRingHom.Finite := finite_of_nonconstant_polynomial_image η₀ a ha
  have hdimA : ringKrullDim A = 1 := by
    have he := IsHomeomorph.topologicalKrullDim_eq _
      e₀.hom.homeomorph.isHomeomorph
    change topologicalKrullDim V.left = topologicalKrullDim (PrimeSpectrum A) at he
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at he
    exact he.symm.trans hdim
  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hdimA.le
  have hinjη : Function.Injective η₀ := injective_finite_to_polynomial η₀.toRingHom hη
  have hinjσ : Function.Injective σ := fun x y h ↦ hinjη (congrArg P h)
  have hσeq : P.symm.toRingHom.comp η₀.toRingHom = σ.toRingHom := by
    apply RingHom.ext
    intro a
    exact P.symm_apply_apply (σ a)
  have hσfin : σ.toRingHom.Finite := by
    rw [← hσeq]
    exact P.symm.toRingEquiv.finite.comp hη
  have hf : f₁ = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ e₀.inv := by
    apply (cancel_mono e₀.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact hσleft.symm
  have : IsFinite (Spec.map (CommRingCat.ofHom σ.toRingHom)) :=
    (IsFinite.SpecMap_iff _).mpr hσfin
  have : Surjective (Spec.map (CommRingCat.ofHom σ.toRingHom)) := by
    constructor
    exact hσfin.to_isIntegral.comap_surjective hinjσ
  have : IsFinite e₀.inv := inferInstance
  have : Surjective e₀.inv := inferInstance
  change IsFinite f₁ ∧ Surjective f₁
  rw [hf]
  exact ⟨inferInstance, inferInstance⟩
end
end AclGeom.AdditiveOrbit
