/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCompletion.ValuativeUniqueness
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Proper Normal Model

**Status:** proved, with a named consumer in the actual curve-completion construction.
These lemmas reach CurveCompletion.connectedGroup_completion_and_extensions: an actual
one-dimensional connected algebraic group over an ACF base embeds openly in a constructed
proper normal integral dimension-one curve, and its individual automorphisms extend uniquely.
The original smooth separated curve is retained. Projectivity, jointly regular extended
families and the full rational/non-affine classifier remain separate source obligations.
The source of truth is `sources/blueprint.tex`, Lemma `affine-action` (#21).
-/

namespace AclGeom.CurveCompletion
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {k F : Type u} [Field k] [Field F] [Algebra k F]

/-- The actual normalization model is proper, deriving both valuative halves, finite type and quasi-
separatedness internally from a separating parameter. Named consumer:
exists_proper_normal_completion. -/
theorem modelHom_isProper (t : F) (ht : t ≠ 0) (htr : Transcendental k t)
    [FiniteDimensional (IntermediateField.adjoin k ({t} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F] :
    IsProper (modelHom (k := k) t ht) := by
  have : LocallyOfFiniteType (modelHom (k := k) t ht) :=
    modelHom_locallyOfFiniteType t ht htr
  have : IsLocallyNoetherian (model (k := k) t ht) :=
    LocallyOfFiniteType.isLocallyNoetherian (modelHom (k := k) t ht)
  have : QuasiSeparatedSpace (model (k := k) t ht) := inferInstance
  have : QuasiSeparated (modelHom (k := k) t ht) := inferInstance
  apply IsProper.of_valuativeCriterion
  exact ValuativeCriterion.iff.mpr
    ⟨modelHom_valuative_existence t ht htr, modelHom_valuative_uniqueness t ht⟩

end
end AclGeom.CurveCompletion
