/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveClosedPointPlace
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Actual proper models and centers of places

**Status:** proved for actual proper integral schemes over any field. The valuative criterion
constructs a unique actual map from the spectrum of each place ring, with the prescribed
generic-point map. Its closed-point image defines the actual center. Named consumer: the
actual closed-point/place equivalence.

The given proper normal curve is an actual input. Completion construction, the scheme API from
smoothness to local normality, joint regularity of extended families, rational-action
regularization and the full original classifier remain owed, alongside group/chunk/six-point
statements, algebraization/descent and every true bypassed auxiliary. All eight original #21
work items and the full durable goal remain active and incomplete.
-/

namespace AclGeom.CurvePointsPlaces
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {k : Type u} [Field k]
attribute [local instance] ActionFunctionField.functionFieldAlgebra

/-- A place has a unique map into an actual proper integral model extending its generic
point. Named consumer: the actual center and the closed-point/place correspondence. -/
theorem existsUnique_placeModelMap
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (P : Place k X.left.functionField) :
    ∃! m : Spec (.of P.val) ⟶ X.left,
      Spec.map (CommRingCat.ofHom P.val.subtype) ≫ m =
        X.left.fromSpecStalk (genericPoint X.left) := by
  let j := Spec.map (CommRingCat.ofHom P.val.subtype)
  let b : k →+* P.val := (algebraMap k X.left.functionField).codRestrict
    P.val (fun c ↦ P.algebraMap_mem c)
  have hD : IsDomain P.val := inferInstance
  have hV : ValuationRing P.val := inferInstance
  have hFrac : IsFractionRing P.val X.left.functionField := inferInstance
  have hb : X.left.fromSpecStalk (genericPoint X.left) ≫ X.hom =
      j ≫ Spec.map (CommRingCat.ofHom b) := by
    refine (Over.w (SchemeGenericTranslate.genericParameter X)).trans ?_
    exact Spec.map_comp (CommRingCat.ofHom b) (CommRingCat.ofHom P.val.subtype)
  let sq : ValuativeCommSq X.hom :=
    { R := P.val
      domain := hD
      valuationRing := hV
      K := X.left.functionField
      isFractionRing := hFrac
      i₁ := X.left.fromSpecStalk (genericPoint X.left)
      i₂ := Spec.map (CommRingCat.ofHom b)
      commSq := ⟨hb⟩ }
  have hproper : IsProper X.hom := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hproper
  obtain ⟨m, hm, _⟩ := (hproper.1.1.1.existence sq).exists_lift
  have hgen : j ≫ m = X.left.fromSpecStalk (genericPoint X.left) := hm
  have : X.left.IsSeparated := by
    constructor
    rw [← Limits.terminal.comp_from X.hom]
    infer_instance
  have : IsDominant j := by
    rw [isDominant_iff]
    change DenseRange (PrimeSpectrum.comap P.val.subtype)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
    intro z hz
    have hz0 : z = 0 := Subtype.ext hz
    simpa only [hz0] using Ideal.zero_mem (nilradical P.val)
  refine ⟨m, hgen, ?_⟩
  intro q hq
  exact ext_of_isDominant j (hq.trans hgen.symm)

/-- The unique actual model map of a place. Named consumer: its actual center point. -/
def placeModelMap
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (P : Place k X.left.functionField) : Spec (.of P.val) ⟶ X.left :=
  (existsUnique_placeModelMap X P).choose

/-- The chosen model map retains the literal canonical generic point.
Named consumer: identifying its actual local-ring image with the place. -/
theorem placeModelMap_generic
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (P : Place k X.left.functionField) :
    Spec.map (CommRingCat.ofHom P.val.subtype) ≫ placeModelMap X P =
      X.left.fromSpecStalk (genericPoint X.left) :=
  (existsUnique_placeModelMap X P).choose_spec.1

/-- The center is the image of the closed point of the actual valuation-ring spectrum.
Named consumer: the closed-point/place equivalence, which proves closedness internally. -/
def placeCenter
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (P : Place k X.left.functionField) : X.left :=
  placeModelMap X P (IsLocalRing.closedPoint P.val)

end
end AclGeom.CurvePointsPlaces
