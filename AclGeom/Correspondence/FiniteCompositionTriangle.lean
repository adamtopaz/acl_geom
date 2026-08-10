/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.FiniteNormalTransport
import AclGeom.Correspondence.FieldEquivDiagram

/-!
# Strict composition triangles on finite normal covers

Two finite-correspondence pairs with a literally shared middle coordinate
act on algebraic closures of their coordinate fields.  This file packages
the reusable finite-normal-cover construction behind that action.

The source cover contains the normal closures of the left branch, the
pullback of the right branch, and the direct composite branch.  Transport
gives common middle and target covers.  The independently chosen direct
lift differs from strict two-step composition by a vertical deck
automorphism; normality restricts that defect to the common target cover,
where its inverse corrects the direct lift to a literal composition
identity.
-/

namespace AclGeom

open IntermediateField
open AlgebraicClosureTransport

noncomputable section

namespace FiniteCorrespondencePair
namespace FiniteCoverTriangle

variable {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω]
  (P Q : FiniteCorrespondencePair E Ω) (h : P.target = Q.source)

/-- The left branch transport followed by the canonical identification of
its target coordinate field with the right branch source coordinate
field. -/
noncomputable def sourceToMiddleTransport :=
  P.coordinateClosureTransport.trans (P.middleClosureTransport Q h)

/-- A common finite normal source cover containing the left and direct
branch normalizations and the pullback of the right branch normalization. -/
noncomputable def sourceCover :=
  ((P.sourceFiniteNormalCover.sup
      (Q.sourceFiniteNormalCover.map
        (sourceToMiddleTransport P Q h).symm)).sup
    (P.comp Q h).sourceFiniteNormalCover)

/-- The common middle cover obtained by transporting the source cover
through the left branch. -/
noncomputable def middleCover :=
  (sourceCover P Q h).map (sourceToMiddleTransport P Q h)

/-- The common target cover obtained by strict two-step transport. -/
noncomputable def targetCover :=
  (sourceCover P Q h).map (P.chainCoordinateClosureTransport Q h)

/-- Transporting the middle cover through the right branch gives the same
target field as strict two-step transport. -/
theorem rightMap_field :
    ((middleCover P Q h).map Q.coordinateClosureTransport).field =
      (targetCover P Q h).field := by
  ext z
  simp [targetCover, middleCover, sourceToMiddleTransport,
    FiniteCorrespondencePair.chainCoordinateClosureTransport]

/-- The left equivalence on the common finite covers. -/
noncomputable def leftEquiv :
    (↥(sourceCover P Q h).field) ≃+*
      (↥(middleCover P Q h).field) :=
  (sourceCover P Q h).mapEquiv (sourceToMiddleTransport P Q h)

/-- The right equivalence on the common finite covers. -/
noncomputable def rightEquiv :
    (↥(middleCover P Q h).field) ≃+*
      (↥(targetCover P Q h).field) :=
  ((middleCover P Q h).mapEquiv Q.coordinateClosureTransport).trans
    (IntermediateField.equivOfEq (rightMap_field P Q h)).toRingEquiv

/-- Strict two-step transport restricted to the common source and target
covers. -/
noncomputable def compositeEquiv :
    (↥(sourceCover P Q h).field) ≃+*
      (↥(targetCover P Q h).field) :=
  (sourceCover P Q h).mapEquiv
    (P.chainCoordinateClosureTransport Q h)

/-- Restriction commutes literally with the two-step composition. -/
theorem leftEquiv_trans_rightEquiv :
    (leftEquiv P Q h).trans (rightEquiv P Q h) =
      compositeEquiv P Q h := by
  apply RingEquiv.ext
  intro x
  apply Subtype.ext
  rfl

/-- The independently selected direct transport carries the common source
cover onto the same target field as strict composition. -/
theorem directMap_field :
    ((sourceCover P Q h).map
      (P.directCompositeClosureTransport Q h)).field =
        (targetCover P Q h).field := by
  exact (sourceCover P Q h).correctedMap_field
    (P.chainCoordinateClosureTransport Q h)
    (P.directCompositeClosureTransport Q h)
    (P.compositionDefect Q h)
    (P.chainCoordinateClosureTransport_trans_compositionDefect Q h)

/-- The independently selected direct lift restricted to the common
finite covers. -/
noncomputable def directEquiv :
    (↥(sourceCover P Q h).field) ≃+*
      (↥(targetCover P Q h).field) :=
  (sourceCover P Q h).correctedMapEquiv
    (P.chainCoordinateClosureTransport Q h)
    (P.directCompositeClosureTransport Q h)
    (P.compositionDefect Q h)
    (P.chainCoordinateClosureTransport_trans_compositionDefect Q h)

/-- The vertical composition defect restricted to the common target
finite normal cover. -/
noncomputable def defectEquiv :
    (↥(targetCover P Q h).field) ≃ₐ[↥Q.targetField]
      (↥(targetCover P Q h).field) :=
  (targetCover P Q h).restrictAlgEquiv (P.compositionDefect Q h)

/-- Correct the direct lift by the inverse restricted deck defect. -/
noncomputable def strictDirectEquiv :
    (↥(sourceCover P Q h).field) ≃+*
      (↥(targetCover P Q h).field) :=
  (directEquiv P Q h).trans (defectEquiv P Q h).symm.toRingEquiv

/-- Strict composition followed by the deck defect is the direct lift on
the common finite cover. -/
theorem compositeEquiv_trans_defectEquiv :
    (compositeEquiv P Q h).trans (defectEquiv P Q h).toRingEquiv =
      directEquiv P Q h :=
  (sourceCover P Q h).mapEquiv_trans_restrictAlgEquiv
    (P.chainCoordinateClosureTransport Q h)
    (P.directCompositeClosureTransport Q h)
    (P.compositionDefect Q h)
    (P.chainCoordinateClosureTransport_trans_compositionDefect Q h)

/-- The corrected direct arrow is literally the composite of the left and
right finite-cover equivalences. -/
theorem strictComposition :
    (leftEquiv P Q h).trans (rightEquiv P Q h) =
      strictDirectEquiv P Q h := by
  rw [leftEquiv_trans_rightEquiv]
  exact FieldEquiv.eq_trans_symm_of_trans_eq
    (compositeEquiv P Q h) (directEquiv P Q h)
    (defectEquiv P Q h).toRingEquiv
    (compositeEquiv_trans_defectEquiv P Q h)

namespace OnSourceCover

variable
  (N : AlgebraicClosureTransport.FiniteNormalCover (↥P.sourceField))

/-- The middle cover obtained by transporting an arbitrary finite normal
source cover through the left branch.  Unlike `sourceCover`, the input
cover is supplied by the caller; this is useful when several composition
triangles must act on one common compositum. -/
noncomputable def middleCover :=
  N.map (sourceToMiddleTransport P Q h)

/-- The target cover obtained by transporting the supplied source cover
through the strict two-step chain. -/
noncomputable def targetCover :=
  N.map (P.chainCoordinateClosureTransport Q h)

/-- Transporting the middle cover through the right branch gives the same
target field as strict two-step transport. -/
theorem rightMap_field :
    ((middleCover P Q h N).map Q.coordinateClosureTransport).field =
      (targetCover P Q h N).field := by
  ext z
  simp [targetCover, middleCover, sourceToMiddleTransport,
    FiniteCorrespondencePair.chainCoordinateClosureTransport]

/-- The left branch restricted to the supplied common source cover. -/
noncomputable def leftEquiv :
    (↥N.field) ≃+* (↥(middleCover P Q h N).field) :=
  N.mapEquiv (sourceToMiddleTransport P Q h)

/-- The right branch restricted to the transported middle cover. -/
noncomputable def rightEquiv :
    (↥(middleCover P Q h N).field) ≃+*
      (↥(targetCover P Q h N).field) :=
  ((middleCover P Q h N).mapEquiv Q.coordinateClosureTransport).trans
    (IntermediateField.equivOfEq (rightMap_field P Q h N)).toRingEquiv

/-- Strict two-step transport restricted to the supplied source cover. -/
noncomputable def compositeEquiv :
    (↥N.field) ≃+* (↥(targetCover P Q h N).field) :=
  N.mapEquiv (P.chainCoordinateClosureTransport Q h)

/-- Restriction to an arbitrary source cover commutes literally with the
two-step composition. -/
theorem leftEquiv_trans_rightEquiv :
    (leftEquiv P Q h N).trans (rightEquiv P Q h N) =
      compositeEquiv P Q h N := by
  apply RingEquiv.ext
  intro x
  apply Subtype.ext
  rfl

/-- The independently selected direct lift restricted to the supplied
source cover and the strict target cover. -/
noncomputable def directEquiv :
    (↥N.field) ≃+* (↥(targetCover P Q h N).field) :=
  N.correctedMapEquiv
    (P.chainCoordinateClosureTransport Q h)
    (P.directCompositeClosureTransport Q h)
    (P.compositionDefect Q h)
    (P.chainCoordinateClosureTransport_trans_compositionDefect Q h)

/-- The vertical composition defect restricted to the transported target
cover. -/
noncomputable def defectEquiv :
    (↥(targetCover P Q h N).field) ≃ₐ[↥Q.targetField]
      (↥(targetCover P Q h N).field) :=
  (targetCover P Q h N).restrictAlgEquiv (P.compositionDefect Q h)

/-- Correct the direct lift by the inverse restricted deck defect. -/
noncomputable def strictDirectEquiv :
    (↥N.field) ≃+* (↥(targetCover P Q h N).field) :=
  (directEquiv P Q h N).trans (defectEquiv P Q h N).symm.toRingEquiv

/-- Strict composition followed by the deck defect is the direct lift on
the supplied source cover. -/
theorem compositeEquiv_trans_defectEquiv :
    (compositeEquiv P Q h N).trans
        (defectEquiv P Q h N).toRingEquiv =
      directEquiv P Q h N :=
  N.mapEquiv_trans_restrictAlgEquiv
    (P.chainCoordinateClosureTransport Q h)
    (P.directCompositeClosureTransport Q h)
    (P.compositionDefect Q h)
    (P.chainCoordinateClosureTransport_trans_compositionDefect Q h)

/-- The corrected direct arrow is literally the composite of the left and
right arrows on any supplied finite normal source cover. -/
theorem strictComposition :
    (leftEquiv P Q h N).trans (rightEquiv P Q h N) =
      strictDirectEquiv P Q h N := by
  rw [leftEquiv_trans_rightEquiv]
  exact FieldEquiv.eq_trans_symm_of_trans_eq
    (compositeEquiv P Q h N) (directEquiv P Q h N)
    (defectEquiv P Q h N).toRingEquiv
    (compositeEquiv_trans_defectEquiv P Q h N)

/-- Package the three restricted arrows as one literal composition
triangle on the supplied source cover. -/
noncomputable def compositionTriangle :
    FieldEquiv.CompositionTriangle
      (↥N.field)
      (↥(middleCover P Q h N).field)
      (↥(targetCover P Q h N).field) where
  left := leftEquiv P Q h N
  right := rightEquiv P Q h N
  direct := strictDirectEquiv P Q h N
  composition := strictComposition P Q h N

end OnSourceCover

end FiniteCoverTriangle
end FiniteCorrespondencePair

end

end AclGeom
