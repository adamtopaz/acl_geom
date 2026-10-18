/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AffineSchemeAction

/-!
# The actual translation subgroup of the affine group

**Status:** the actual Ga inclusion, its regular shift retraction, monomorphism and group
laws are proved over every field. Point formulas hold over every commutative coefficient
algebra in the base universe. The group identities use such points on actual affine tensor
spectra, so no reducedness or algebraic-closedness premise is needed. Named consumers: the
actual Ga-to-affine factorization and subgroup translation theorem of Lemma 8.4 (#21).
-/

namespace AclGeom.AdditiveTranslation
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u
variable (k : Type u) [Field k]

/-- Named consumer: the actual additive-to-affine translation factorization. -/
def inclusion : (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ⟶
    (AffineGroupScheme.algebraicGroup k).toGroupScheme.X :=
  (algSpec (.of k)).map (CommAlgCat.ofHom
    (AffineGroupScheme.eval k 1 (AffineSchemeAction.lineCoordinate k))).op

/-- Named consumer: extracting the actual translation coordinate of a subgroup. -/
def shift : (AffineGroupScheme.algebraicGroup k).toGroupScheme.X ⟶
    (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X :=
  (algSpec (.of k)).map (CommAlgCat.ofHom (AffineGroupScheme.includeTranslation k)).op

/-- Named consumers: the actual translation group law and subgroup point formula. -/
theorem linePoint_comp_inclusion {C : Type u} [CommRing C] [Algebra k C] (x : C) :
    AffineSchemeAction.linePoint k x ≫ inclusion k = AffineSchemeAction.groupPoint k 1 x := by
  have hh : (AffineSchemeAction.lineEval (k := k) x).comp
      (AffineGroupScheme.eval k 1 (AffineSchemeAction.lineCoordinate k)) =
        AffineGroupScheme.eval k 1 x := by
    apply AffineGroupScheme.hom_ext
    · simp only [AlgHom.comp_apply, AffineGroupScheme.eval_dilation, Units.val_one, map_one]
    · simp only [AlgHom.comp_apply, AffineGroupScheme.eval_translation,
        AffineSchemeAction.lineEval_lineCoordinate]
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom
      (AffineSchemeAction.lineEval (k := k) x).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (AffineGroupScheme.eval k 1
      (AffineSchemeAction.lineCoordinate k)).toRingHom) =
        Spec.map (CommRingCat.ofHom (AffineGroupScheme.eval k 1 x).toRingHom)
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  change ((AffineSchemeAction.lineEval (k := k) x).comp
    (AffineGroupScheme.eval k 1 (AffineSchemeAction.lineCoordinate k))).toRingHom =
      (AffineGroupScheme.eval k 1 x).toRingHom
  exact congrArg AlgHom.toRingHom hh

/-- Named consumer: the inclusion is a monomorphism, so its factorization is a group morphism. -/
theorem inclusion_comp_shift : inclusion k ≫ shift k = 𝟙 _ := by
  have hh : (AffineGroupScheme.eval k 1 (AffineSchemeAction.lineCoordinate k)).comp
      (AffineGroupScheme.includeTranslation k) =
        AlgHom.id k (AdditiveGroupScheme.CoordinateRing k 1) := by
    apply AffineSchemeAction.lineHom_ext
    change (AffineGroupScheme.eval k 1 (AffineSchemeAction.lineCoordinate k))
      (AffineGroupScheme.translation k) = AffineSchemeAction.lineCoordinate k
    exact AffineGroupScheme.eval_translation _ _
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  change ((AffineGroupScheme.eval k 1 (AffineSchemeAction.lineCoordinate k)).comp
    (AffineGroupScheme.includeTranslation k)).toRingHom = RingHom.id _
  exact congrArg AlgHom.toRingHom hh

/-- Named consumer: the actual translation group morphism. -/
theorem linePoint_mul {C : Type u} [CommRing C] [Algebra k C] (x y : C) :
    AffineSchemeAction.linePoint k x * AffineSchemeAction.linePoint k y =
      AffineSchemeAction.linePoint k (x + y) := by
  have hh : WithConv.toConv (AffineSchemeAction.lineEval (k := k) x) *
      WithConv.toConv (AffineSchemeAction.lineEval (k := k) y) =
        WithConv.toConv (AffineSchemeAction.lineEval (k := k) (x + y)) := by
    apply WithConv.ofConv_injective
    apply AffineSchemeAction.lineHom_ext
    rw [AlgHom.convMul_apply]
    change (Algebra.TensorProduct.lift (AffineSchemeAction.lineEval (k := k) x)
      (AffineSchemeAction.lineEval (k := k) y) (fun _ _ ↦ Commute.all _ _))
        (Coalgebra.comul (R := k) (SymmetricAlgebra.ι k (Fin 1 → k)
          (Pi.basisFun k (Fin 1) 0))) =
            (AffineSchemeAction.lineEval (k := k) (x + y)) (AffineSchemeAction.lineCoordinate k)
    rw [SymmetricAlgebra.comul_ι]
    simp only [map_add, Algebra.TensorProduct.lift_tmul, map_one]
    change (AffineSchemeAction.lineEval (k := k) x) (AffineSchemeAction.lineCoordinate k) * 1 +
      1 * (AffineSchemeAction.lineEval (k := k) y) (AffineSchemeAction.lineCoordinate k) = _
    simp only [AffineSchemeAction.lineEval_lineCoordinate, _root_.mul_one, _root_.one_mul]
  have h := congrArg (Spec.mapMulEquiv (R := k)
    (S := AdditiveGroupScheme.CoordinateRing k 1) (T := C)) hh
  rw [map_mul] at h
  exact h

/-- Named consumer: the actual translation morphism preserves the unit. -/
theorem linePoint_zero {C : Type u} [CommRing C] [Algebra k C] :
    AffineSchemeAction.linePoint k (0 : C) = 1 := by
  have hh : WithConv.toConv (AffineSchemeAction.lineEval (k := k) (0 : C)) = 1 := by
    apply WithConv.ofConv_injective
    apply AffineSchemeAction.lineHom_ext
    rw [AffineSchemeAction.lineEval_lineCoordinate]
    change 0 = algebraMap k C
      ((Bialgebra.counitAlgHom k (SymmetricAlgebra k (Fin 1 → k)))
        (SymmetricAlgebra.ι k (Fin 1 → k) (Pi.basisFun k (Fin 1) 0)))
    simp only [SymmetricAlgebra.counitAlgHom_eq, SymmetricAlgebra.algebraMapInv_ι, map_zero]
  exact (congrArg (Spec.mapMulEquiv (R := k)
    (S := AdditiveGroupScheme.CoordinateRing k 1) (T := C)) hh).trans (map_one _)
end
end AclGeom.AdditiveTranslation

namespace AclGeom.AdditiveTranslation
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
universe u
variable (k : Type u) [Field k]

/-- Named consumer: an actual Ga-to-affine group morphism has multiplier one. -/
theorem linePoint_comp_groupPoint {C : Type u} [CommRing C] [Algebra k C]
    (x : C) (a : (AdditiveGroupScheme.CoordinateRing k 1)ˣ)
    (z : AdditiveGroupScheme.CoordinateRing k 1) :
    AffineSchemeAction.linePoint k x ≫ AffineSchemeAction.groupPoint k a z =
      AffineSchemeAction.groupPoint k
        (Units.map (AffineSchemeAction.lineEval (k := k) x).toMonoidHom a)
        (AffineSchemeAction.lineEval (k := k) x z) := by
  have hh : (AffineSchemeAction.lineEval (k := k) x).comp (AffineGroupScheme.eval k a z) =
      AffineGroupScheme.eval k
        (Units.map (AffineSchemeAction.lineEval (k := k) x).toMonoidHom a)
        (AffineSchemeAction.lineEval (k := k) x z) := by
    apply AffineGroupScheme.hom_ext
    · simp only [AlgHom.comp_apply, AffineGroupScheme.eval_dilation, Units.coe_map]
      rfl
    · simp only [AlgHom.comp_apply, AffineGroupScheme.eval_translation]
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval (k := k) x).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (AffineGroupScheme.eval k a z).toRingHom) =
      Spec.map (CommRingCat.ofHom (AffineGroupScheme.eval k
        (Units.map (AffineSchemeAction.lineEval (k := k) x).toMonoidHom a)
        (AffineSchemeAction.lineEval (k := k) x z)).toRingHom)
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  change ((AffineSchemeAction.lineEval (k := k) x).comp
    (AffineGroupScheme.eval k a z)).toRingHom = _
  exact congrArg AlgHom.toRingHom hh
end
end AclGeom.AdditiveTranslation

namespace AclGeom.AdditiveTranslation
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u
variable (k : Type u) [Field k]

/-- Named consumer: the translation factor of an actual Ga group morphism is a group morphism. -/
instance inclusion_mono : Mono (inclusion k) := by
  constructor
  intro Z f g h
  have hh := congrArg (fun z ↦ z ≫ shift k) h
  simpa only [Category.assoc, inclusion_comp_shift, Category.comp_id] using hh

/-- Named consumer: the actual translation factorization of a Ga subgroup. -/
instance inclusion_isMonHom : IsMonHom (inclusion k) := by
  let N := (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
  let A := (AffineGroupScheme.algebraicGroup k).toGroupScheme.X
  constructor
  · have hh : (1 : (Spec (.of k)).asOver (Spec (.of k)) ⟶ N) ≫ inclusion k = 1 := by
      rw [← linePoint_zero k, linePoint_comp_inclusion, AffineSchemeAction.groupPoint_one]
    apply (cancel_epi (unitIsoSpecAsOver k).inv).mp
    simpa only [← Category.assoc, comp_one, one_eq_one] using hh
  · have key {C : Type u} [CommRing C] [Algebra k C]
        (p : (Spec (.of C)).asOver (Spec (.of k)) ⟶ N ⊗ N) :
        p ≫ μ[N] ≫ inclusion k = p ≫ (inclusion k ⊗ₘ inclusion k) ≫ μ[A] := by
      obtain ⟨x, hx⟩ := AffineSchemeAction.exists_linePoint k (p ≫ fst N N)
      obtain ⟨y, hy⟩ := AffineSchemeAction.exists_linePoint k (p ≫ snd N N)
      have hp : lift (AffineSchemeAction.linePoint k x) (AffineSchemeAction.linePoint k y) = p := by
        apply CartesianMonoidalCategory.hom_ext
        · simpa only [lift_fst] using hx
        · simpa only [lift_snd] using hy
      calc
        _ = (AffineSchemeAction.linePoint k x * AffineSchemeAction.linePoint k y) ≫
            inclusion k := by rw [← hp]; rfl
        _ = AffineSchemeAction.groupPoint k 1 (x + y) := by
          rw [linePoint_mul, linePoint_comp_inclusion]
        _ = AffineSchemeAction.groupPoint k 1 x * AffineSchemeAction.groupPoint k 1 y := by
          rw [AffineSchemeAction.groupPoint_mul]
          simp only [_root_.one_mul, Units.val_one, add_comm]
        _ = _ := by
          rw [← hp, lift_map_assoc, ← Hom.mul_def, linePoint_comp_inclusion,
            linePoint_comp_inclusion]
    let e := AffineSchemeAction.tensorSpecIso k
      (AdditiveGroupScheme.CoordinateRing k 1) (AdditiveGroupScheme.CoordinateRing k 1)
    apply (cancel_epi e.inv).mp
    exact key e.inv

/-- The actual group morphism identifying Ga with the translation subgroup. Named consumer:
the finite-isogeny translation factorization of the actual subgroup. -/
def groupInclusion : (AdditiveGroupScheme.algebraicGroup k 1).Hom
    (AffineGroupScheme.algebraicGroup k) := Grp.homMk (inclusion k)
end
end AclGeom.AdditiveTranslation
