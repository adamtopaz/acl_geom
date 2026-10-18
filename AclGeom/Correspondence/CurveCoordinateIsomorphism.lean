/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AdditiveOrbitCover
import AclGeom.Correspondence.CurveCoordinateField
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# A global rational generator identifies the entire covered affine curve

**Status:** a global coordinate on an integral affine scheme, whose generic value is a
transcendental generator, is an actual isomorphism with Ga if a surjective actual line
cover exists. This holds over any field. Ordinary Spec full faithfulness recovers both
algebra maps. A prime over bottom makes the cover's algebra map injective. Its composite
with polynomial evaluation is nonconstant and finite. Integral elements of the generated
fraction field lie in the integrally closed polynomial ring, giving the coordinate
algebra isomorphism. Normality, dimension and finiteness of the supplied cover are not
premises of this criterion. Named consumer:
`CurveGlobalCoordinate.exists_whole_curve_coordinate` supplies the actual global coordinate,
generator and surjective orbit internally (#21).
-/

namespace AclGeom.CurveGlobalCoordinate
noncomputable section
open Polynomial
universe u
variable {k A F : Type u} [Field k] [CommRing A] [Field F]
    [Algebra k A] [Algebra k F] [Algebra k[X] F] [IsScalarTower k k[X] F]
    [IsFractionRing k[X] F]

/-- A birational polynomial coordinate is an isomorphism once an injective polynomial
cover exists. Named consumer: the actual global curve coordinate is an isomorphism. -/
theorem bijective_of_polynomial_cover
    (α : k[X] →ₐ[k] A) (σ : A →ₐ[k] k[X]) (hσ : Function.Injective σ)
    (j : A →ₐ[k] F) (hj : Function.Injective j)
    (hja : j.comp α = IsScalarTower.toAlgHom k k[X] F) : Function.Bijective α := by
  have hα : Function.Injective α := by
    intro a b h
    apply IsFractionRing.injective k[X] F
    have hh := congrArg j h
    change (j.comp α) a = (j.comp α) b at hh
    rw [hja] at hh
    exact hh
  let ψ := σ.comp α
  have hψ : Function.Injective ψ := hσ.comp hα
  have hq : (ψ X).natDegree ≠ 0 := by
    intro h
    have hc : ψ X = ψ (C ((ψ X).coeff 0)) :=
      (Polynomial.eq_C_of_natDegree_eq_zero h).trans (ψ.commutes _).symm
    exact X_ne_C _ (hψ hc)
  have hfin : ψ.toRingHom.Finite :=
    AdditiveOrbit.finite_of_nonconstant_polynomial_image ψ X hq
  refine ⟨hα, ?_⟩
  intro a
  have ha : α.toRingHom.IsIntegralElem a :=
    RingHom.IsIntegralElem.of_map hσ (hfin.to_isIntegral (σ a))
  have hjint : IsIntegral k[X] (j a) := by
    have hh := ha.map j.toRingHom
    have he : j.toRingHom.comp α.toRingHom = algebraMap k[X] F :=
      congrArg AlgHom.toRingHom hja
    rw [he] at hh
    exact hh
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hjint
  refine ⟨r, hj ?_⟩
  change (j.comp α) r = j a
  rw [hja]
  exact hr
end
end AclGeom.CurveGlobalCoordinate

namespace AclGeom.CurveGlobalCoordinate
noncomputable section
open Polynomial
universe u

/-- Named consumer: integral closure turns the whole-curve coordinate into an isomorphism. -/
theorem fractionRing_of_generator {k F : Type u} [Field k] [Field F] [Algebra k F]
    (t : F) (ht : Transcendental k t)
    (htop : IntermediateField.adjoin k ({t} : Set F) = ⊤) :
    let : Algebra k[X] F := (aeval t).toRingHom.toAlgebra
    IsFractionRing k[X] F := by
  let : Algebra k[X] F := (aeval t).toRingHom.toAlgebra
  have : FaithfulSMul k[X] F := (faithfulSMul_iff_algebraMap_injective k[X] F).mpr
    (transcendental_iff_injective.mp ht)
  apply IsFractionRing.of_field
  intro z
  apply (IntermediateField.mem_adjoin_simple_iff k z).mp
  rw [htop]
  trivial
end
end AclGeom.CurveGlobalCoordinate

namespace AclGeom.CurveGlobalCoordinate
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
universe u
variable {k : Type u} [Field k]
attribute [local instance] SchemeGenericTranslate.sectionsAlgebra
  ActionFunctionField.functionFieldAlgebra

/-- A global rational generator is an actual line isomorphism when a surjective line cover
exists. Named consumer: the internally chosen coordinate of the regular-affine action. -/
theorem isIso_of_surjective_line_cover
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    (x : V ⟶ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X)
    (t : V.left.functionField) (ht : Transcendental k t)
    (htop : IntermediateField.adjoin k ({t} : Set V.left.functionField) = ⊤)
    (hgen : SchemeGenericTranslate.genericParameter V ≫ x = AffineSchemeAction.linePoint k t)
    (o : (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ⟶ V)
    [Surjective o.left] : IsIso x := by
  classical
  let A : Type u := Γ(V.left, ⊤)
  let R := AdditiveGroupScheme.CoordinateRing k 1
  let F : Type u := V.left.functionField
  let e : V ≅ (Spec (.of A)).asOver (Spec (.of k)) :=
    SchemeGenericTranslate.sectionsSpecIso V
  let e₀ : V.left ≅ Spec (.of A) := (Over.forget (Spec (.of k))).mapIso e
  let x₀ : V.left ⟶ Spec (.of R) := x.left
  let o₀ : Spec (.of R) ⟶ V.left := o.left
  let g₀ : Spec (.of F) ⟶ V.left := (SchemeGenericTranslate.genericParameter V).left
  let ν : R →ₐ[k] F := AffineSchemeAction.lineEval t
  have hgen₀ : g₀ ≫ x₀ = Spec.map (CommRingCat.ofHom ν.toRingHom) :=
    congrArg Over.Hom.left hgen
  have : Nonempty (⊤ : V.left.Opens) := ⟨⟨genericPoint V.left, trivial⟩⟩
  have : IsScalarTower k A F := SchemeGenericTranslate.sections_functionField_isScalarTower V
  let j : A →ₐ[k] F := IsScalarTower.toAlgHom k A F
  have hj : Function.Injective j := V.left.germToFunctionField_injective ⊤
  obtain ⟨α₀, hα₀⟩ := AdditiveOrbit.exists_algHom_of_spec_hom R A (e.inv ≫ x)
  obtain ⟨σ₀, hσ₀⟩ := AdditiveOrbit.exists_algHom_of_spec_hom A R (o ≫ e.hom)
  have hαleft := congrArg Over.Hom.left hα₀
  have hσleft := congrArg Over.Hom.left hσ₀
  change Spec.map (CommRingCat.ofHom α₀.toRingHom) = e₀.inv ≫ x₀ at hαleft
  change Spec.map (CommRingCat.ofHom σ₀.toRingHom) = o₀ ≫ e₀.hom at hσleft
  have hgenj : Spec.map (CommRingCat.ofHom j.toRingHom) =
      g₀ ≫ e₀.hom := by
    change Spec.map (V.left.germToFunctionField ⊤) =
      V.left.fromSpecStalk (genericPoint V.left) ≫ V.left.toSpecΓ
    exact (Scheme.fromSpecStalk_toSpecΓ _ _).symm
  have hja₀ : j.comp α₀ = ν := by
    have hh : Spec.map (CommRingCat.ofHom (j.comp α₀).toRingHom) =
        Spec.map (CommRingCat.ofHom ν.toRingHom) := by
      change Spec.map (CommRingCat.ofHom α₀.toRingHom ≫ CommRingCat.ofHom j.toRingHom) = _
      rw [Spec.map_comp, hgenj, hαleft, Category.assoc, Iso.hom_inv_id_assoc]
      exact hgen₀
    have hh' := congrArg CommRingCat.Hom.hom (Spec.map_injective hh)
    exact AlgHom.ext fun a ↦ congrArg (fun f : R →+* F ↦ f a) hh'
  have : Surjective o₀ := inferInstanceAs (Surjective o.left)
  have hsurj : Function.Surjective (PrimeSpectrum.comap σ₀.toRingHom) := by
    have : Surjective (o₀ ≫ e₀.hom) := inferInstance
    have hh : Surjective (Spec.map (CommRingCat.ofHom σ₀.toRingHom)) := by
      rw [hσleft]
      infer_instance
    exact hh.1
  have hσinj : Function.Injective σ₀ := by
    obtain ⟨P, hP⟩ := hsurj (⟨⊥, inferInstance⟩ : PrimeSpectrum A)
    have hcomap : Ideal.comap σ₀.toRingHom P.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal hP
    apply (RingHom.injective_iff_ker_eq_bot σ₀.toRingHom).mpr
    apply le_antisymm ?_ bot_le
    intro a ha
    rw [RingHom.mem_ker] at ha
    change σ₀ a = 0 at ha
    rw [← hcomap]
    change σ₀ a ∈ P.asIdeal
    rw [ha]
    exact P.asIdeal.zero_mem
  let P := AdditiveTranslation.polynomialCoordinates k
  let α : Polynomial k →ₐ[k] A := α₀.comp P.symm.toAlgHom
  let σ : A →ₐ[k] Polynomial k := P.toAlgHom.comp σ₀
  have hσ : Function.Injective σ := P.injective.comp hσinj
  let : Algebra (Polynomial k) F := (Polynomial.aeval t).toRingHom.toAlgebra
  have : IsScalarTower k (Polynomial k) F := IsScalarTower.of_algebraMap_eq fun c ↦
    ((Polynomial.aeval t).commutes c).symm
  have : IsFractionRing (Polynomial k) F := fractionRing_of_generator t ht htop
  have hja : j.comp α = IsScalarTower.toAlgHom k (Polynomial k) F := by
    apply AlgHom.ext
    intro p
    change (j.comp α₀) (P.symm p) = Polynomial.aeval t p
    rw [hja₀]
    change AffineSchemeAction.lineEval (k := k) t (P.symm p) = Polynomial.aeval t p
    rw [AdditiveTranslation.lineEval_polynomialCoordinates]
    rw [P.apply_symm_apply]
  have hbij : Function.Bijective α := bijective_of_polynomial_cover α σ hσ j hj hja
  have hα₀bij : Function.Bijective α₀ := by
    have heq : α₀ = α.comp P.toAlgHom := by
      apply AlgHom.ext
      intro r
      exact (congrArg α₀ (P.symm_apply_apply r)).symm
    rw [heq]
    exact hbij.comp P.bijective
  have : IsIso (Spec.map (CommRingCat.ofHom α₀.toRingHom)) :=
    (isIso_SpecMap_iff).mpr hα₀bij
  have : IsIso (e₀.inv ≫ x₀) := by rw [← hαleft]; infer_instance
  have : IsIso x₀ := IsIso.of_isIso_comp_left e₀.inv x₀
  have : IsIso x.left := this
  have : IsIso ((Over.forget (Spec (.of k))).map x) := inferInstanceAs (IsIso x.left)
  exact isIso_of_reflects_iso x (Over.forget (Spec (.of k)))
end
end AclGeom.CurveGlobalCoordinate
