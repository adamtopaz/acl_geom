/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.SchemeCoefficientPoints
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Faithfulness and algebraicity of affine coefficients

**Status:** proved for actual affine scheme actions with the global point-kernel criterion
and a generating field coordinate (#21). The point criterion uses an actual monomorphic
parameter family and explicit affine specialization formulas. Over an ACF base and a
finite-type parameter domain, its fraction field is algebraic over the two-coefficient field,
allowing purely inseparable extensions. Named consumer: `SchemeAffineParameters` supplies
all chart, coordinate, coefficient and specialization premises internally.
-/

namespace AclGeom.AffineCoefficients

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct
open SchemeGenericTranslate

universe u

variable {k : Type u} [Field k]

attribute [local instance] sectionsAlgebra ActionFunctionField.functionFieldAlgebra

/-- Agreement on the two actual affine coefficients determines a localized parameter point.
 Named consumer: algebraicity over the rational affine coefficient field. -/
theorem localized_coefficients_points_injective (G : AlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [ModObj G.toGroupScheme.X V]
    (hker : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
      ModObj.pointAct V q = 𝟙 V → q = 1)
    {t : V.left.functionField}
    (htop : IntermediateField.adjoin k ({t} : Set V.left.functionField) = ⊤)
    {A : Type u} [CommRing A] [Algebra k A]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G.toGroupScheme.X) [Mono g]
    (d a b : A)
    (hformula : ∀ (φ : A →ₐ[k] k), φ d ≠ 0 →
      (ActionFunctionField.functionFieldAction G V ((unitIsoSpecAsOver k).hom ≫
        (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).unop t =
          algebraMap k V.left.functionField (φ a / φ d) * t +
            algebraMap k V.left.functionField (φ b / φ d)) :
    let S := Localization.Away d
    let a0 : S := algebraMap A S a * IsLocalization.Away.invSelf d
    let b0 : S := algebraMap A S b * IsLocalization.Away.invSelf d
    let B := Algebra.adjoin k ({a0, b0} : Set S)
    Function.Injective (fun φ : S →ₐ[k] k ↦ φ.comp B.val) := by
  let S := Localization.Away d
  let a0 : S := algebraMap A S a * IsLocalization.Away.invSelf d
  let b0 : S := algebraMap A S b * IsLocalization.Away.invSelf d
  let B := Algebra.adjoin k ({a0, b0} : Set S)
  let restrict (φ : S →ₐ[k] k) : A →ₐ[k] k :=
    φ.comp (IsScalarTower.toAlgHom k A S)
  have hd (φ : S →ₐ[k] k) : restrict φ d ≠ 0 :=
    ((IsLocalization.Away.algebraMap_isUnit (S := S) d).map φ).ne_zero
  have hinv (φ : S →ₐ[k] k) : φ (IsLocalization.Away.invSelf d : S) =
      (restrict φ d)⁻¹ := by
    apply mul_right_cancel₀ (hd φ)
    rw [inv_mul_cancel₀ (hd φ)]
    calc
      _ = φ ((IsLocalization.Away.invSelf d : S) * algebraMap A S d) :=
        (map_mul φ _ _).symm
      _ = 1 := by rw [mul_comm, IsLocalization.Away.mul_invSelf, map_one]
  have hvalue (φ : S →ₐ[k] k) (n : A) :
      φ (algebraMap A S n * IsLocalization.Away.invSelf d) =
        restrict φ n / restrict φ d := by
    rw [map_mul, hinv, div_eq_mul_inv]
    rfl
  change Function.Injective (fun φ : S →ₐ[k] k ↦ φ.comp B.val)
  intro φ ψ heq
  have ha : φ a0 = ψ a0 := by
    let x : B := ⟨a0, Algebra.subset_adjoin (Set.mem_insert _ _)⟩
    exact AlgHom.congr_fun heq x
  have hb : φ b0 = ψ b0 := by
    let x : B := ⟨b0, Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
    exact AlgHom.congr_fun heq x
  let sp (φ : S →ₐ[k] k) : (Spec (.of k)).asOver (Spec (.of k)) ⟶
      (Spec (.of A)).asOver (Spec (.of k)) :=
    (algSpec (.of k)).map (CommAlgCat.ofHom (restrict φ)).op
  let q (φ : S →ₐ[k] k) := (unitIsoSpecAsOver k).hom ≫ sp φ ≫ g
  have ht : (ActionFunctionField.functionFieldAction G V (q φ)).unop t =
      (ActionFunctionField.functionFieldAction G V (q ψ)).unop t := by
    have hφ : (ActionFunctionField.functionFieldAction G V (q φ)).unop t =
        algebraMap k V.left.functionField (restrict φ a / restrict φ d) * t +
          algebraMap k V.left.functionField (restrict φ b / restrict φ d) :=
      hformula (restrict φ) (hd φ)
    have hψ : (ActionFunctionField.functionFieldAction G V (q ψ)).unop t =
        algebraMap k V.left.functionField (restrict ψ a / restrict ψ d) * t +
          algebraMap k V.left.functionField (restrict ψ b / restrict ψ d) :=
      hformula (restrict ψ) (hd ψ)
    rw [hφ, hψ]
    change algebraMap k V.left.functionField (restrict φ a / restrict φ d) * t +
        algebraMap k V.left.functionField (restrict φ b / restrict φ d) = _
    rw [← hvalue φ a, ← hvalue φ b, ← hvalue ψ a, ← hvalue ψ b]
    rw [ha, hb]
  have hq : q φ = q ψ := by
    apply ActionFunctionField.functionFieldAction_injective G V hker
    apply MulOpposite.unop_injective
    let P := IntermediateField.adjoin k ({t} : Set V.left.functionField)
    let incl : P →ₐ[k] V.left.functionField := IsScalarTower.toAlgHom k P V.left.functionField
    have he : (ActionFunctionField.functionFieldAction G V (q φ)).unop.toAlgHom.comp incl =
        (ActionFunctionField.functionFieldAction G V (q ψ)).unop.toAlgHom.comp incl := by
      apply IntermediateField.adjoin_algHom_ext k
      intro z hz
      have hzt : z = t := Set.mem_singleton_iff.1 hz
      subst z
      exact ht
    apply AlgEquiv.ext
    intro x
    have hx : x ∈ P := by
      change x ∈ IntermediateField.adjoin k ({t} : Set V.left.functionField)
      rw [htop]
      trivial
    exact congrArg (fun f : P →ₐ[k] V.left.functionField ↦ f ⟨x, hx⟩) he
  have hmap : sp φ = sp ψ := by
    apply (cancel_epi (unitIsoSpecAsOver k).hom).mp
    apply (cancel_mono g).mp
    rw [Category.assoc, Category.assoc]
    exact hq
  have hleft := congrArg (fun f : (Spec (.of k)).asOver (Spec (.of k)) ⟶
    (Spec (.of A)).asOver (Spec (.of k)) ↦ f.left) hmap
  change Spec.map (CommRingCat.ofHom (restrict φ).toRingHom) =
    Spec.map (CommRingCat.ofHom (restrict ψ).toRingHom) at hleft
  have hrestrict : restrict φ = restrict ψ := AlgHom.ext fun n ↦
    congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of k ↦ f.hom n)
      (Spec.map_injective hleft)
  have hr : φ.toRingHom.comp (algebraMap A S) = ψ.toRingHom.comp (algebraMap A S) :=
    congrArg AlgHom.toRingHom hrestrict
  have hfull := IsLocalization.ringHom_ext (Submonoid.powers d) hr
  exact AlgHom.ext fun x ↦ RingHom.congr_fun hfull x

end

end AclGeom.AffineCoefficients

namespace AclGeom.AffineCoefficients

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

attribute [local instance] SchemeGenericTranslate.sectionsAlgebra
  ActionFunctionField.functionFieldAlgebra

/-- The two rational affine coefficients retain the parameter fraction field up to an
 algebraic extension, allowing pure inseparability. The actual group consumer supplies
 the denominator and every specialization formula internally. -/
theorem isAlgebraic_of_affine_specializations (G : AlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [ModObj G.toGroupScheme.X V]
    (hker : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
      ModObj.pointAct V q = 𝟙 V → q = 1)
    {t : V.left.functionField}
    (htop : IntermediateField.adjoin k ({t} : Set V.left.functionField) = ⊤)
    {A : Type u} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G.toGroupScheme.X) [Mono g]
    (d a b : A) (hd : d ≠ 0)
    (hformula : ∀ (φ : A →ₐ[k] k), φ d ≠ 0 →
      (ActionFunctionField.functionFieldAction G V ((unitIsoSpecAsOver k).hom ≫
        (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).unop t =
          algebraMap k V.left.functionField (φ a / φ d) * t +
            algebraMap k V.left.functionField (φ b / φ d)) :
    Algebra.IsAlgebraic (IntermediateField.adjoin k
      ({algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) d,
        algebraMap A (FractionRing A) b / algebraMap A (FractionRing A) d} :
          Set (FractionRing A))) (FractionRing A) := by
  let C := FractionRing A
  let S := Localization.Away d
  let evC : A →ₐ[k] C := IsScalarTower.toAlgHom k A C
  have hinj : Function.Injective evC := IsFractionRing.injective A C
  have hdC : evC d ≠ 0 := by
    intro h
    apply hd
    apply hinj
    simpa only [map_zero] using h
  let locMap : S →ₐ[k] C := IsLocalization.Away.liftAlgHom d (f := evC)
    (isUnit_iff_ne_zero.mpr hdC)
  have hlocMap (n : A) : locMap (algebraMap A S n) = evC n :=
    IsLocalization.Away.lift_eq d (g := evC.toRingHom) (isUnit_iff_ne_zero.mpr hdC) n
  let : Algebra S C := locMap.toAlgebra
  have : IsScalarTower A S C := IsScalarTower.of_algebraMap_eq (fun n ↦ (hlocMap n).symm)
  have : IsScalarTower k S C := IsScalarTower.of_algHom locMap
  have : IsFractionRing S C :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers d) S C
  have : IsDomain S := IsLocalization.Away.isDomain S hd
  have : Algebra.FiniteType k S := inferInstance
  let a0 : S := algebraMap A S a * IsLocalization.Away.invSelf d
  let b0 : S := algebraMap A S b * IsLocalization.Away.invSelf d
  let B := Algebra.adjoin k ({a0, b0} : Set S)
  let C0 := IntermediateField.adjoin k ({evC a / evC d, evC b / evC d} : Set C)
  have hinv : locMap (IsLocalization.Away.invSelf d : S) = (evC d)⁻¹ := by
    apply mul_right_cancel₀ hdC
    rw [inv_mul_cancel₀ hdC]
    calc
      _ = locMap ((IsLocalization.Away.invSelf d : S) * algebraMap A S d) := by
        rw [map_mul, hlocMap]
      _ = 1 := by rw [mul_comm, IsLocalization.Away.mul_invSelf, map_one]
  have hvalue (n : A) : locMap (algebraMap A S n * IsLocalization.Away.invSelf d) =
      evC n / evC d := by
    rw [map_mul, hlocMap, hinv, div_eq_mul_inv]
  have hle : B ≤ C0.toSubalgebra.comap locMap := by
    apply Algebra.adjoin_le
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · change locMap a0 ∈ C0
      rw [hvalue]
      exact IntermediateField.subset_adjoin k _ (Set.mem_insert _ _)
    · have hz' : z = b0 := Set.mem_singleton_iff.mp hz
      subst z
      change locMap b0 ∈ C0
      rw [hvalue]
      exact IntermediateField.subset_adjoin k _
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  let f : B →ₐ[k] C0 := (locMap.comp B.val).codRestrict C0.toSubalgebra (fun z ↦ hle z.property)
  let : Algebra B C0 := f.toAlgebra
  have : IsScalarTower B C0 C := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  apply isAlgebraic_fractionRing_of_injective_points (k := k) (B := B) (A := S)
    (C := C0) (E := C)
  exact localized_coefficients_points_injective G V hker htop g d a b hformula

end

end AclGeom.AffineCoefficients
