/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AffineTranslationSubgroup
import AclGeom.Correspondence.MultiplicativeScalarAction

/-!
# The actual multiplier projection of the affine group

**Status:** the projection to Gm is a surjective regular group morphism, with a scaling
section and the literal unit-coordinate formula over every commutative coefficient algebra.
Named consumer: the regular conjugation character of the actual normal subgroup in the
coupled regular-affine model (#21). No inverse to a finite isogeny is introduced.
-/

namespace AclGeom.AdditiveRigidity
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
universe u
variable (k : Type u) [Field k]

/-- Named consumer: the actual multiplier projection's group law. -/
theorem unitPoint_one {C : Type u} [CommRing C] [Algebra k C] :
    unitPoint k (1 : Cˣ) = 1 := by
  change Spec.mapMulEquiv (R := k) (S := AddMonoidAlgebra k ℤ) (T := C)
    ((unitsMulEquivConv k C).symm 1) = 1
  rw [map_one, map_one]

/-- Named consumer: the actual multiplier projection's group law. -/
theorem unitPoint_mul {C : Type u} [CommRing C] [Algebra k C] (a b : Cˣ) :
    unitPoint k (a * b) = unitPoint k a * unitPoint k b := by
  change Spec.mapMulEquiv (R := k) (S := AddMonoidAlgebra k ℤ) (T := C)
    ((unitsMulEquivConv k C).symm (a * b)) =
      Spec.mapMulEquiv ((unitsMulEquivConv k C).symm a) *
        Spec.mapMulEquiv ((unitsMulEquivConv k C).symm b)
  rw [map_mul, map_mul]
end
end AclGeom.AdditiveRigidity

namespace AclGeom.AffineDilation
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
universe u
variable (k : Type u) [Field k]

/-- Named consumer: the regular conjugation character of the actual normal subgroup. -/
def projection : (AffineGroupScheme.algebraicGroup k).toGroupScheme.X ⟶
    (multiplicativeGroup k).toGroupScheme.X :=
  (algSpec (.of k)).map (CommAlgCat.ofHom
    ((unitsMulEquivConv k (AffineGroupScheme.CoordinateRing k)).symm
      (AffineGroupScheme.dilationUnit k)).ofConv).op

/-- The actual multiplier projection has the literal unit coordinate over every algebra.
Named consumer: the regular character and its joint conjugation formula. -/
theorem groupPoint_comp_projection {C : Type u} [CommRing C] [Algebra k C]
    (a : Cˣ) (b : C) :
    AffineSchemeAction.groupPoint k a b ≫ projection k = AdditiveRigidity.unitPoint k a := by
  let φ : AddMonoidAlgebra k ℤ →ₐ[k] AffineGroupScheme.CoordinateRing k :=
    ((unitsMulEquivConv k (AffineGroupScheme.CoordinateRing k)).symm
      (AffineGroupScheme.dilationUnit k)).ofConv
  have hφ : (AffineGroupScheme.eval k a b).comp φ =
      ((unitsMulEquivConv k C).symm a).ofConv := by
    have hh : WithConv.toConv ((AffineGroupScheme.eval k a b).comp φ) =
        (unitsMulEquivConv k C).symm a := by
      apply (unitsMulEquivConv k C).injective
      apply Units.ext
      rw [MulEquiv.apply_symm_apply, unitsMulEquivConv_apply_val]
      change ((AffineGroupScheme.eval k a b).comp φ)
        (AddMonoidAlgebra.single (1 : ℤ) (1 : k)) = (a : C)
      rw [AlgHom.comp_apply, unitsMulEquivConv_symm_apply_single,
        AffineGroupScheme.eval_dilation]
    exact congrArg WithConv.ofConv hh
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (AffineGroupScheme.eval k a b).toRingHom) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) =
    Spec.map (CommRingCat.ofHom ((unitsMulEquivConv k C).symm a).ofConv.toRingHom)
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom hφ

/-- Named consumer: surjectivity of the actual character to Gm. -/
def scalingSection : (multiplicativeGroup k).toGroupScheme.X ⟶
    (AffineGroupScheme.algebraicGroup k).toGroupScheme.X :=
  AffineSchemeAction.groupPoint k
    (unitsMulEquivConv k (AddMonoidAlgebra k ℤ)
      (WithConv.toConv (AlgHom.id k (AddMonoidAlgebra k ℤ)))) 0

/-- Named consumer: the actual multiplier projection is surjective. -/
theorem scalingSection_comp_projection : scalingSection k ≫ projection k = 𝟙 _ := by
  let u := unitsMulEquivConv k (AddMonoidAlgebra k ℤ)
    (WithConv.toConv (AlgHom.id k (AddMonoidAlgebra k ℤ)))
  have he : scalingSection k ≫ projection k = AdditiveRigidity.unitPoint k u :=
    groupPoint_comp_projection k u 0
  refine he.trans ?_
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom
    ((unitsMulEquivConv k (AddMonoidAlgebra k ℤ)).symm u).ofConv.toRingHom) = 𝟙 _
  rw [MulEquiv.symm_apply_apply]
  exact Spec.map_id _

/-- Named consumer: the actual normal-subgroup conjugation character is a group morphism. -/
instance projection_isMonHom : IsMonHom (projection k) := by
  let A := (AffineGroupScheme.algebraicGroup k).toGroupScheme.X
  let M := (multiplicativeGroup k).toGroupScheme.X
  constructor
  · have hh : (1 : (Spec (.of k)).asOver (Spec (.of k)) ⟶ A) ≫ projection k = 1 := by
      rw [← AffineSchemeAction.groupPoint_one k, groupPoint_comp_projection,
        AdditiveRigidity.unitPoint_one]
    apply (cancel_epi (unitIsoSpecAsOver k).inv).mp
    rw [← Category.assoc]
    simpa only [comp_one, one_eq_one] using hh
  · have key {C : Type u} [CommRing C] [Algebra k C]
        (p : (Spec (.of C)).asOver (Spec (.of k)) ⟶ A ⊗ A) :
        p ≫ μ[A] ≫ projection k = p ≫ (projection k ⊗ₘ projection k) ≫ μ[M] := by
      obtain ⟨a, b, hab⟩ := AffineSchemeAction.exists_groupPoint k (p ≫ fst A A)
      obtain ⟨c, d, hcd⟩ := AffineSchemeAction.exists_groupPoint k (p ≫ snd A A)
      have hp : lift (AffineSchemeAction.groupPoint k a b)
          (AffineSchemeAction.groupPoint k c d) = p := by
        apply CartesianMonoidalCategory.hom_ext
        · simpa only [lift_fst] using hab
        · simpa only [lift_snd] using hcd
      calc
        _ = (AffineSchemeAction.groupPoint k a b * AffineSchemeAction.groupPoint k c d) ≫
            projection k := by rw [← hp]; rfl
        _ = AdditiveRigidity.unitPoint k (a * c) := by
          rw [AffineSchemeAction.groupPoint_mul, groupPoint_comp_projection]
        _ = AdditiveRigidity.unitPoint k a * AdditiveRigidity.unitPoint k c :=
          AdditiveRigidity.unitPoint_mul k a c
        _ = _ := by
          rw [← hp, lift_map_assoc, ← Hom.mul_def, groupPoint_comp_projection,
            groupPoint_comp_projection]
    let e := AffineSchemeAction.tensorSpecIso k
      (AffineGroupScheme.CoordinateRing k) (AffineGroupScheme.CoordinateRing k)
    apply (cancel_epi e.inv).mp
    exact key e.inv

/-- Named consumer: the regular character of the actual normal subgroup is surjective. -/
theorem projection_surjective : Surjective (projection k).left := by
  constructor
  intro x
  exact ⟨(scalingSection k).left x,
    congrArg (fun q : (multiplicativeGroup k).toGroupScheme.X ⟶
      (multiplicativeGroup k).toGroupScheme.X ↦ q.left x) (scalingSection_comp_projection k)⟩

/-- Named consumer: compose the SAME actual affine morphism with its dilation character. -/
def character : (AffineGroupScheme.algebraicGroup k).Hom (multiplicativeGroup k) :=
  Grp.homMk (projection k)

/-- Named consumer: the actual character's multiplier is the original affine coefficient. -/
theorem point_comp_projection
    (q : 𝟙_ (Over (Spec (.of k))) ⟶ (AffineGroupScheme.algebraicGroup k).toGroupScheme.X) :
    q ≫ projection k = (multiplicativeGroup.pointsMulEquiv k).symm
      (AffineGroupScheme.pointsMulEquiv k q).multiplier := by
  let a := AffineGroupScheme.pointsMulEquiv k q
  have hq : q = (unitIsoSpecAsOver k).hom ≫
      AffineSchemeAction.groupPoint k a.multiplier a.shift := by
    calc
      _ = (AffineGroupScheme.pointsMulEquiv k).symm a :=
        ((AffineGroupScheme.pointsMulEquiv k).symm_apply_apply q).symm
      _ = _ := by
        apply Over.OverMorphism.ext
        exact (AffineGroupScheme.pointsMulEquiv_symm_apply_left k a).trans
          (Category.id_comp _).symm
  calc
    _ = ((unitIsoSpecAsOver k).hom ≫
        AffineSchemeAction.groupPoint k a.multiplier a.shift) ≫ projection k :=
      congrArg (fun g ↦ g ≫ projection k) hq
    _ = _ := by
      rw [Category.assoc, groupPoint_comp_projection, AdditiveRigidity.unitPoint_eq_points]

end
end AclGeom.AffineDilation
