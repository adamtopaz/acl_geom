/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.FiniteNormalTransport
import AclGeom.Correspondence.FieldEquivDiagram

/-!
# Extending strict field-equivalence triangles across a source field

A literal composition triangle of field equivalences can be transported
across any intermediate field in an algebraic closure of its source.  We
choose algebraic-closure lifts of the left and right arrows and define the
direct lift to be their composite.  Restricting those lifts gives another
literal composition triangle, with no normality hypothesis on the enlarged
source field.

This construction is useful when a finite chart has been obtained as a
pullback along an algebraic-closure comparison.  Normality is needed to
restrict an independently chosen deck correction, but it is not needed to
extend an already strict triangle by its two successive arrows.
-/

namespace AclGeom

open IntermediateField
open AlgebraicClosureTransport

noncomputable section

universe u

namespace FieldEquiv.CompositionTriangle

variable {X Y Z : Type u} [Field X] [Field Y] [Field Z]
  (T : FieldEquiv.CompositionTriangle X Y Z)

/-- A chosen algebraic-closure lift of the left arrow. -/
noncomputable def sourceExtensionLeftTransport :
    AlgebraicClosureTransport X Y :=
  AlgebraicClosureTransport.lift T.left

/-- A chosen algebraic-closure lift of the right arrow. -/
noncomputable def sourceExtensionRightTransport :
    AlgebraicClosureTransport Y Z :=
  AlgebraicClosureTransport.lift T.right

/-- The image of an enlarged source field under the lifted left arrow. -/
noncomputable def sourceExtensionMiddleField
    (L : IntermediateField X (AlgebraicClosure X)) :
    IntermediateField Y (AlgebraicClosure Y) :=
  (T.sourceExtensionLeftTransport).mapField L

/-- The image of an enlarged source field under the strict composite of
the lifted left and right arrows. -/
noncomputable def sourceExtensionTargetField
    (L : IntermediateField X (AlgebraicClosure X)) :
    IntermediateField Z (AlgebraicClosure Z) :=
  ((T.sourceExtensionLeftTransport).trans
    T.sourceExtensionRightTransport).mapField L

/-- The left arrow restricted to the enlarged source and its transported
middle field. -/
noncomputable def sourceExtensionLeftEquiv
    (L : IntermediateField X (AlgebraicClosure X)) :
    (↥L) ≃+* (↥(T.sourceExtensionMiddleField L)) :=
  T.sourceExtensionLeftTransport.mapFieldEquiv L

/-- The right arrow restricted to the transported middle field.  The final
carrier identification records that successive transport is the same as
transport by the composite. -/
noncomputable def sourceExtensionRightEquiv
    (L : IntermediateField X (AlgebraicClosure X)) :
    (↥(T.sourceExtensionMiddleField L)) ≃+*
      (↥(T.sourceExtensionTargetField L)) :=
  (T.sourceExtensionRightTransport.mapFieldEquiv
      (T.sourceExtensionMiddleField L)).trans
    (IntermediateField.equivOfEq
      ((T.sourceExtensionLeftTransport.mapField_trans
        T.sourceExtensionRightTransport L).symm)).toRingEquiv

/-- The strict composite lift restricted to the enlarged source. -/
noncomputable def sourceExtensionDirectEquiv
    (L : IntermediateField X (AlgebraicClosure X)) :
    (↥L) ≃+* (↥(T.sourceExtensionTargetField L)) :=
  ((T.sourceExtensionLeftTransport).trans
    T.sourceExtensionRightTransport).mapFieldEquiv L

/-- The original middle field embeds literally in the middle field of the
extended triangle. -/
noncomputable def sourceExtensionMiddleRingHom
    (L : IntermediateField X (AlgebraicClosure X)) :
    Y →+* (↥(T.sourceExtensionMiddleField L)) :=
  algebraMap Y (↥(T.sourceExtensionMiddleField L))

/-- The original target field embeds literally in the target field of the
extended triangle. -/
noncomputable def sourceExtensionTargetRingHom
    (L : IntermediateField X (AlgebraicClosure X)) :
    Z →+* (↥(T.sourceExtensionTargetField L)) :=
  algebraMap Z (↥(T.sourceExtensionTargetField L))

/-- Restriction of the lifted arrows preserves literal composition. -/
theorem sourceExtension_left_trans_right
    (L : IntermediateField X (AlgebraicClosure X)) :
    (T.sourceExtensionLeftEquiv L).trans
        (T.sourceExtensionRightEquiv L) =
      T.sourceExtensionDirectEquiv L := by
  apply RingEquiv.ext
  intro x
  apply Subtype.ext
  rfl

/-- Package the enlarged arrows as a literal composition triangle. -/
noncomputable def sourceExtension
    (L : IntermediateField X (AlgebraicClosure X)) :
    FieldEquiv.CompositionTriangle
      (↥L)
      (↥(T.sourceExtensionMiddleField L))
      (↥(T.sourceExtensionTargetField L)) where
  left := T.sourceExtensionLeftEquiv L
  right := T.sourceExtensionRightEquiv L
  direct := T.sourceExtensionDirectEquiv L
  composition := T.sourceExtension_left_trans_right L

/-- On the original source field, the enlarged left arrow is exactly the
original left equivalence. -/
@[simp] theorem sourceExtensionLeftEquiv_algebraMap
    (L : IntermediateField X (AlgebraicClosure X)) (x : X) :
    T.sourceExtensionLeftEquiv L (algebraMap X (↥L) x) =
      algebraMap Y (↥(T.sourceExtensionMiddleField L)) (T.left x) := by
  exact (DFunLike.congr_fun
    (T.sourceExtensionLeftTransport.mapFieldEquiv_commutes L) x).symm

/-- On the original middle field, the enlarged right arrow is exactly the
original right equivalence. -/
@[simp] theorem sourceExtensionRightEquiv_algebraMap
    (L : IntermediateField X (AlgebraicClosure X)) (y : Y) :
    T.sourceExtensionRightEquiv L
        (algebraMap Y (↥(T.sourceExtensionMiddleField L)) y) =
      algebraMap Z (↥(T.sourceExtensionTargetField L)) (T.right y) := by
  apply Subtype.ext
  change T.sourceExtensionRightTransport.closureEquiv
      (algebraMap Y (AlgebraicClosure Y) y) =
    algebraMap Z (AlgebraicClosure Z) (T.right y)
  exact T.sourceExtensionRightTransport.commutes_apply y

/-- The extended right arrow forms an exact square with the original right
arrow and the two literal old-field embeddings. -/
theorem sourceExtensionRightEquiv_comp_middleRingHom
    (L : IntermediateField X (AlgebraicClosure X)) :
    (T.sourceExtensionRightEquiv L).toRingHom.comp
        (T.sourceExtensionMiddleRingHom L) =
      (T.sourceExtensionTargetRingHom L).comp T.right.toRingHom := by
  ext y
  exact congrArg Subtype.val
    (T.sourceExtensionRightEquiv_algebraMap L y)

/-- On the original source field, the enlarged direct arrow is the
original strict composite. -/
@[simp] theorem sourceExtensionDirectEquiv_algebraMap
    (L : IntermediateField X (AlgebraicClosure X)) (x : X) :
    T.sourceExtensionDirectEquiv L (algebraMap X (↥L) x) =
      algebraMap Z (↥(T.sourceExtensionTargetField L)) (T.direct x) := by
  apply Subtype.ext
  change ((T.sourceExtensionLeftTransport).trans
      T.sourceExtensionRightTransport).closureEquiv
        (algebraMap X (AlgebraicClosure X) x) =
    algebraMap Z (AlgebraicClosure Z) (T.direct x)
  rw [← DFunLike.congr_fun T.composition x]
  exact ((T.sourceExtensionLeftTransport).trans
    T.sourceExtensionRightTransport).commutes_apply x

end FieldEquiv.CompositionTriangle

end

end AclGeom
