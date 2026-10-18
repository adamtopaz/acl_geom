/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AffineSchemeAction

/-!
# Scalar maps on the actual additive group

**Status:** the actual scalar scheme map and its formula on every commutative coefficient
algebra in the base universe are proved over every field. Named consumers: the actual
Ga automorphism classification and normal additive-subgroup conjugation character (#21).
-/

namespace AclGeom.AdditiveRigidity
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u

/-- Named consumers: actual Ga automorphisms and the normal additive-subgroup character. -/
def scale (k : Type u) [Field k] (a : k) :
    (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ⟶
      (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X :=
  (algSpec (.of k)).map (CommAlgCat.ofHom
    (AffineSchemeAction.lineEval (algebraMap k _ a * AffineSchemeAction.lineCoordinate k))).op

/-- Named consumer: scalar conjugation on the actual normal additive subgroup. -/
theorem linePoint_comp_scale (k : Type u) [Field k]
    {C : Type u} [CommRing C] [Algebra k C] (a : k) (x : C) :
    AffineSchemeAction.linePoint k x ≫ scale k a =
      AffineSchemeAction.linePoint k (algebraMap k C a * x) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval x).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval
        (algebraMap k _ a * AffineSchemeAction.lineCoordinate k)).toRingHom) =
    Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval (algebraMap k C a * x)).toRingHom)
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  change ((AffineSchemeAction.lineEval x).comp (AffineSchemeAction.lineEval
    (algebraMap k (AdditiveGroupScheme.CoordinateRing k 1) a *
      AffineSchemeAction.lineCoordinate k))).toRingHom =
    (AffineSchemeAction.lineEval (algebraMap k C a * x)).toRingHom
  apply congrArg AlgHom.toRingHom
  apply AffineSchemeAction.lineHom_ext
  simp only [AlgHom.comp_apply, AffineSchemeAction.lineEval_lineCoordinate, map_mul,
    AlgHom.commutes]
end
end AclGeom.AdditiveRigidity
