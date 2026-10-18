/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.SchemeFunctionFieldBase
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# The actual smooth curve stalk base algebra

**Status:** proved for actual scheme stalks. The actual structure morphism supplies one base-
field algebra compatible with global-section germs and the actual function field. Actual
scheme smoothness and local finite type supply formal smoothness and essential finite type;
closed-point residue fields are algebraic over the same ACF base algebra. Named consumer:
actual smooth-curve stalk normality.

These are ACF dimension-one results. Projective presentation, joint regularity of extended
rational families, rational-action regularization and the full original classifier remain
owed. Original group/chunk/six-point statements, algebraization/descent and every true
bypassed auxiliary remain obligations. All eight original #21 work items and the full durable
goal remain active and incomplete.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.SmoothCurveStalks
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {k : Type u} [Field k]

/-- The actual base-field algebra on an actual scheme stalk. Named consumer: smooth
stalk normality, using the SAME canonical base algebra on the actual function field. -/
@[instance_reducible]
def stalkAlgebra (X : Over (Spec (.of k))) (x : X.left) :
    Algebra k (X.left.presheaf.stalk x) :=
  (((Scheme.ΓSpecIso (.of k)).inv ≫
    (Spec (.of k)).presheaf.germ ⊤ (X.hom x) trivial) ≫ X.hom.stalkMap x).hom.toAlgebra

/-- The actual base field is the stalk of its spectrum at every point.
Named consumers: actual stalk smoothness and essential finite type. -/
theorem baseGerm_isIso (y : Spec (.of k)) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ y trivial) := by
  have hy : y = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  subst y
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv, Iso.inv_hom_id_assoc]
  infer_instance

/-- The actual pullback stalk algebra is the canonical global-section germ algebra.
Named consumer: its scalar tower with the actual generic-stalk field. -/
theorem stalkAlgebra_eq_germ (X : Over (Spec (.of k))) (x : X.left) :
    stalkAlgebra X x =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop ≫
        X.left.presheaf.germ ⊤ x trivial).hom.toAlgebra := by
  apply Algebra.algebra_ext
  intro c
  change (((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ (X.hom x) trivial) ≫ X.hom.stalkMap x) c =
    ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop ≫
      X.left.presheaf.germ ⊤ x trivial) c
  exact congrArg (fun g ↦ g c)
    ((Category.assoc _ _ _).trans
      (congrArg (fun g ↦ (Scheme.ΓSpecIso (.of k)).inv ≫ g)
        (X.hom.germ_stalkMap ⊤ x trivial)))

/-- Actual scheme smoothness gives formal smoothness of the actual base-field stalk algebra.
Named consumer: integral closedness of every actual smooth-curve stalk. -/
theorem stalk_formallySmooth (X : Over (Spec (.of k))) [Smooth X.hom] (x : X.left) :
    letI := stalkAlgebra X x
    Algebra.FormallySmooth k (X.left.presheaf.stalk x) := by
  let u : CommRingCat.of k ⟶ (Spec (.of k)).presheaf.stalk (X.hom x) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤ (X.hom x) trivial
  have : IsIso u := baseGerm_isIso _
  have hu : u.hom.FormallySmooth :=
    RingHom.FormallySmooth.of_bijective (asIso u).commRingCatIsoToRingEquiv.bijective
  have hx : x ∈ X.hom.smoothLocus := by rw [X.hom.smoothLocus_eq_top]; trivial
  have hf := Scheme.Hom.mem_smoothLocus.mp hx
  exact (hu.comp hf).toAlgebra

/-- Actual local finite type gives essential finite type of the same actual stalk algebra.
Named consumer: its finite cotangent module and generic differential rank. -/
theorem stalk_essFiniteType (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    (x : X.left) :
    letI := stalkAlgebra X x
    Algebra.EssFiniteType k (X.left.presheaf.stalk x) := by
  let u : CommRingCat.of k ⟶ (Spec (.of k)).presheaf.stalk (X.hom x) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤ (X.hom x) trivial
  have : IsIso u := baseGerm_isIso _
  have hu : u.hom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _
      (asIso u).commRingCatIsoToRingEquiv.surjective).essFiniteType
  exact hu.comp (LocallyOfFiniteType.stalkMap X.hom x)

attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- The same actual stalk and function-field algebras form the canonical scalar tower.
Named consumer: smooth-curve local normality from the actual curve dimension. -/
theorem stalk_functionField_isScalarTower
    (X : Over (Spec (.of k))) [IsIntegral X.left] (x : X.left) :
    letI := stalkAlgebra X x
    IsScalarTower k (X.left.presheaf.stalk x) X.left.functionField := by
  rw [stalkAlgebra_eq_germ]
  let : Algebra k (X.left.presheaf.stalk x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop ≫
      X.left.presheaf.germ ⊤ x trivial).hom.toAlgebra
  have : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩
  have hbase (c : k) : algebraMap k X.left.functionField c =
      X.left.germToFunctionField ⊤ (((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) c) := by
    rw [ActionFunctionField.functionFieldAlgebra_eq_germ X]
    rfl
  refine IsScalarTower.of_algebraMap_eq fun c ↦ ?_
  rw [hbase]
  exact (Scheme.algebraMap_germ_eq_germToFunctionField X.left
    (show x ∈ (⊤ : X.left.Opens) from trivial)
    (((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) c)).symm

/-- The actual stalk structure morphism has its literal base-field formula.
Named consumer: the actual closed-point residue algebra. -/
theorem SpecMap_stalkAlgebra (X : Over (Spec (.of k))) (x : X.left) :
    letI := stalkAlgebra X x
    Spec.map (CommRingCat.ofHom (algebraMap k (X.left.presheaf.stalk x))) =
      X.left.fromSpecStalk x ≫ X.hom := by
  change Spec.map (((Scheme.ΓSpecIso (.of k)).inv ≫
    (Spec (.of k)).presheaf.germ ⊤ (X.hom x) trivial) ≫ X.hom.stalkMap x) = _
  rw [Spec.map_comp, ← Spec.fromSpecStalk_eq]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk X.hom

/-- Closed-point residue fields are algebraic over the SAME actual stalk base algebra.
Named consumer: the internal residue section in actual smooth-curve local normality. -/
theorem stalk_residue_isAlgebraic [IsAlgClosed k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    (x : X.left) (hx : IsClosed ({x} : Set X.left)) :
    letI := stalkAlgebra X x
    Algebra.IsAlgebraic k (IsLocalRing.ResidueField (X.left.presheaf.stalk x)) := by
  let := stalkAlgebra X x
  let ρ : CommRingCat.of k ⟶ X.left.residueField x :=
    CommRingCat.ofHom (algebraMap k (IsLocalRing.ResidueField (X.left.presheaf.stalk x)))
  have hρ : ρ = CommRingCat.ofHom (algebraMap k (X.left.presheaf.stalk x)) ≫
      X.left.residue x := rfl
  have hspec : Spec.map ρ = X.left.fromSpecResidueField x ≫ X.hom := by
    calc
      Spec.map ρ = Spec.map (X.left.residue x) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k (X.left.presheaf.stalk x))) :=
        (congrArg Spec.map hρ).trans (Spec.map_comp _ _)
      _ = Spec.map (X.left.residue x) ≫ (X.left.fromSpecStalk x ≫ X.hom) :=
        congrArg (fun g ↦ Spec.map (X.left.residue x) ≫ g) (SpecMap_stalkAlgebra X x)
      _ = X.left.fromSpecResidueField x ≫ X.hom := (Category.assoc _ _ _).symm
  have hmap : ρ = (residueFieldIsoBase X.hom x hx).inv :=
    Spec.map_injective (hspec.trans (SpecMap_residueFieldIsoBase_inv X.hom x hx).symm)
  have hs : Function.Surjective ρ := by
    rw [hmap]
    exact (residueFieldIsoBase X.hom x hx).symm.commRingCatIsoToRingEquiv.surjective
  constructor
  intro z
  obtain ⟨c, rfl⟩ := hs z
  exact isAlgebraic_algebraMap c

end
end AclGeom.SmoothCurveStalks
