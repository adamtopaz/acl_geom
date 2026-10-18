/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AffineAction
import AclGeom.Correspondence.AffineSchemeAction
import AclGeom.Correspondence.PointwiseFaithfulness
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
# The regular principal-open affine coefficient map

**Status:** proved criterion for an actual open parameter family over an ACF base (#21).
The rational coefficients and affine evaluation identity are explicit premises. Localizing
at the product of the nonzero multiplier numerator and denominator constructs an actual
map to the standard affine group, a genuine point on that open and every point formula.
Named consumer: `SchemeAffineMorphism` supplies the parameter chart and all coefficient
premises internally. The function-field universe is independent of the base universe.
-/

namespace AclGeom.RegularGroupMorphism

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A pointwise affine formula for rational coefficients gives a regular affine-group map
 on an internally chosen nonempty principal open. Named consumer: the actual global map. -/
theorem exists_local_model (G : AlgebraicGroup k)
    {F : Type v} [Field F] [Algebra k F] {t : F} (ht : Transcendental k t)
    (Φ : (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) →* AffineTransformation k)
    {A : Type u} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G.toGroupScheme.X)
    [IsOpenImmersion g.left] (d a b : A) (hd : d ≠ 0) (ha : a ≠ 0)
    (hfield : ∀ (φ : A →ₐ[k] k), φ d ≠ 0 →
      algebraMap k F ((Φ ((unitIsoSpecAsOver k).hom ≫
        (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).multiplier : k) * t +
      algebraMap k F (Φ ((unitIsoSpecAsOver k).hom ≫
        (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).shift =
        algebraMap k F (φ a / φ d) * t + algebraMap k F (φ b / φ d)) :
    ∃ (U : Over (Spec (.of k))) (j : U ⟶ G.toGroupScheme.X)
      (_ : IsOpenImmersion j.left) (_p0 : 𝟙_ (Over (Spec (.of k))) ⟶ U)
      (fU : U ⟶ (AffineGroupScheme.algebraicGroup k).toGroupScheme.X),
      ∀ p : 𝟙_ (Over (Spec (.of k))) ⟶ U,
        p ≫ fU = (AffineGroupScheme.pointsMulEquiv k).symm (Φ (p ≫ j)) := by
  classical
  let S := Localization.Away (a * d)
  have : IsDomain S := IsLocalization.Away.isDomain S (mul_ne_zero ha hd)
  have : Algebra.FiniteType k S := inferInstance
  let κ : A →ₐ[k] S := IsScalarTower.toAlgHom k A S
  have hunit : IsUnit (κ a) ∧ IsUnit (κ d) := by
    have hh : IsUnit (κ a * κ d) := by
      rw [← map_mul]
      exact IsLocalization.Away.algebraMap_isUnit (S := S) (a * d)
    exact ⟨isUnit_of_mul_isUnit_left hh, isUnit_of_mul_isUnit_right hh⟩
  let au : Sˣ := hunit.1.unit * hunit.2.unit⁻¹
  let bz : S := κ b * (hunit.2.unit⁻¹ : Sˣ)
  let U := (Spec (.of S)).asOver (Spec (.of k))
  let i : U ⟶ (Spec (.of A)).asOver (Spec (.of k)) :=
    (algSpec (.of k)).map (CommAlgCat.ofHom κ).op
  have : IsOpenImmersion i.left := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A S)))
    infer_instance
  let j : U ⟶ G.toGroupScheme.X := i ≫ g
  have : IsOpenImmersion j.left := by
    change IsOpenImmersion (i.left ≫ g.left)
    infer_instance
  let fU : U ⟶ (AffineGroupScheme.algebraicGroup k).toGroupScheme.X :=
    AffineSchemeAction.groupPoint k au bz
  have hex : Nonempty (S →ₐ[k] k) := by
    by_contra hn
    have hh : IsNilpotent (1 : S) := isNilpotent_of_forall_algHom_eq_zero
      (fun φ ↦ False.elim (hn ⟨φ⟩))
    exact not_isNilpotent_one hh
  let φ0 : S →ₐ[k] k := Classical.choice hex
  let p0 : 𝟙_ (Over (Spec (.of k))) ⟶ U := (unitIsoSpecAsOver k).hom ≫
    (algSpec (.of k)).map (CommAlgCat.ofHom φ0).op
  refine ⟨U, j, inferInstance, p0, fU, ?_⟩
  intro p
  let p' : (algSpec (.of k)).obj (.op (CommAlgCat.of k k)) ⟶
      (algSpec (.of k)).obj (.op (CommAlgCat.of k S)) :=
    (unitIsoSpecAsOver k).inv ≫ p
  have : (algSpec (.of k)).Full := algSpec.instFull
  let φ : S →ₐ[k] k := ((algSpec (.of k)).preimage p').unop.hom
  have hφ : (algSpec (.of k)).map (CommAlgCat.ofHom φ).op = p' :=
    (algSpec (.of k)).map_preimage p'
  have hp : p = (unitIsoSpecAsOver k).hom ≫
      (algSpec (.of k)).map (CommAlgCat.ofHom φ).op := by
    rw [hφ]
    exact (Iso.hom_inv_id_assoc (unitIsoSpecAsOver k) p).symm
  have hpLeft : p.left = Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    rw [hp]
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) = _
    rw [Category.id_comp]
  let ψ : A →ₐ[k] k := φ.comp κ
  have hdψ : ψ d ≠ 0 := (hunit.2.map φ).ne_zero
  have hcomp : (algSpec (.of k)).map (CommAlgCat.ofHom ψ).op =
      (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ i :=
    (algSpec (.of k)).map_comp (CommAlgCat.ofHom φ).op (CommAlgCat.ofHom κ).op
  have hpj : p ≫ j = (unitIsoSpecAsOver k).hom ≫
      (algSpec (.of k)).map (CommAlgCat.ofHom ψ).op ≫ g := by
    rw [hcomp, hp]
    rfl
  let T : AffineTransformation k := ⟨Units.map φ.toMonoidHom au, φ bz⟩
  have hvalues : (T.multiplier : k) = ψ a / ψ d ∧ T.shift = ψ b / ψ d := by
    have hinv : φ (hunit.2.unit⁻¹ : Sˣ) = (φ (κ d))⁻¹ := by
      have he := Units.val_inv_eq_inv_val (Units.map φ.toMonoidHom hunit.2.unit)
      change φ (hunit.2.unit⁻¹ : Sˣ) = (φ (hunit.2.unit : S))⁻¹ at he
      simpa only [hunit.2.unit_spec] using he
    constructor
    · change φ ((hunit.1.unit * hunit.2.unit⁻¹ : Sˣ) : S) = _
      rw [Units.val_mul, map_mul, hunit.1.unit_spec, hinv, div_eq_mul_inv]
      rfl
    · change φ (κ b * (hunit.2.unit⁻¹ : Sˣ)) = _
      rw [map_mul, hinv, div_eq_mul_inv]
      rfl
  have hT : T = Φ (p ≫ j) := by
    apply AffineTransformation.eval_injective ht
    change algebraMap k F (T.multiplier : k) * t + algebraMap k F T.shift =
      algebraMap k F ((Φ (p ≫ j)).multiplier : k) * t + algebraMap k F (Φ (p ≫ j)).shift
    rw [hvalues.1, hvalues.2, hpj]
    exact (hfield ψ hdψ).symm
  have heval : φ.comp (AffineGroupScheme.eval k au bz) =
      AffineGroupScheme.eval k T.multiplier T.shift := by
    apply AffineGroupScheme.hom_ext
    · rw [AlgHom.comp_apply, AffineGroupScheme.eval_dilation,
        AffineGroupScheme.eval_dilation]
      rfl
    · rw [AlgHom.comp_apply, AffineGroupScheme.eval_translation,
        AffineGroupScheme.eval_translation]
  have hpT : p ≫ fU = (AffineGroupScheme.pointsMulEquiv k).symm T := by
    apply Over.OverMorphism.ext
    have hspec1 : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (AffineGroupScheme.eval k au bz).toRingHom) =
        Spec.map (CommRingCat.ofHom (φ.comp (AffineGroupScheme.eval k au bz)).toRingHom) :=
      (Spec.map_comp (CommRingCat.ofHom (AffineGroupScheme.eval k au bz).toRingHom)
        (CommRingCat.ofHom φ.toRingHom)).symm
    have hspec2 := congrArg (fun f : AffineGroupScheme.CoordinateRing k →ₐ[k] k ↦
      Spec.map (CommRingCat.ofHom f.toRingHom)) heval
    have hleft : p.left ≫ Spec.map (CommRingCat.ofHom
        (AffineGroupScheme.eval k au bz).toRingHom) =
        Spec.map (CommRingCat.ofHom
          (AffineGroupScheme.eval k T.multiplier T.shift).toRingHom) :=
      (congrArg (fun q : Spec (.of k) ⟶ Spec (.of S) ↦
        q ≫ Spec.map (CommRingCat.ofHom (AffineGroupScheme.eval k au bz).toRingHom))
          hpLeft).trans (hspec1.trans hspec2)
    exact hleft.trans (AffineGroupScheme.pointsMulEquiv_symm_apply_left k T).symm
  rw [hT] at hpT
  exact hpT

end

end AclGeom.RegularGroupMorphism
