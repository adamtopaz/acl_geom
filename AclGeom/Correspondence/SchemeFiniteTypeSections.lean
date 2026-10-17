/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.SchemeGenericTranslate
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Finite type of the actual affine section algebra

Named consumers: actual coefficient families, group parameter charts and the separating
parameter of the actual curve field.

**Status:** proved for affine locally finite-type schemes over any field, using the actual
base algebra on global sections.
-/

namespace AclGeom.SchemeGenericTranslate

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

variable {k : Type u} [Field k]

attribute [local instance] sectionsAlgebra

/-- The actual global-section algebra of an affine locally finite-type scheme is finite type.
Named consumers: the group parameter chart and its curve function-field data. -/
theorem finiteType_sections (V : Over (Spec (.of k))) [IsAffine V.left]
    [LocallyOfFiniteType V.hom] : Algebra.FiniteType k Γ(V.left, ⊤) := by
  have h := (V.hom.finiteType_appLE (isAffineOpen_top _) (isAffineOpen_top _) (by simp)).comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  have htop : V.hom.appLE ⊤ ⊤ (by simp) = V.hom.appTop := Scheme.Hom.appLE_eq_app V.hom
  rw [htop] at h
  exact h

end

end AclGeom.SchemeGenericTranslate
