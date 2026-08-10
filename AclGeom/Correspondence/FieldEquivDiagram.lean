/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Faithful four-arrow diagrams of field equivalences

The presented correspondence-family groupoid records formal composition
relations, but equality in that quotient is not by itself equality of
function-field maps.  This file supplies the semantic target needed for
that comparison.  Its arrows are literal field equivalences, so equality is
faithful by definition.

Equivalences between three varying field charts can be conjugated to three
fixed reference fields.  Conjugation preserves composition, inverse, and
equality.  Four commuting composition triangles on those reference fields
then satisfy the exact right-arrow cancellation formula

`c = a ≫ e⁻¹ ≫ b`.

The construction is deliberately independent of how the field
equivalences arise.  In the group-chunk application they are restrictions
of semilinear algebraic-closure transports to one common finite normal
curve cover.
-/

namespace AclGeom

noncomputable section

universe u

namespace FieldEquiv

variable {X Y Z X' Y' Z' : Type u}
  [Field X] [Field Y] [Field Z]
  [Field X'] [Field Y'] [Field Z']

/-- Conjugate a field equivalence by equivalences of its source and target
charts.  The result is oriented from the new source to the new target. -/
def conjugate (eX : X ≃+* X') (eY : Y ≃+* Y')
    (f : X ≃+* Y) : X' ≃+* Y' :=
  eX.symm.trans (f.trans eY)

/-- Pointwise formula for conjugation. -/
@[simp] theorem conjugate_apply (eX : X ≃+* X') (eY : Y ≃+* Y')
    (f : X ≃+* Y) (x : X') :
    conjugate eX eY f x = eY (f (eX.symm x)) :=
  rfl

/-- Conjugation carries an identity equivalence to an identity
equivalence. -/
@[simp] theorem conjugate_refl (eX : X ≃+* X') :
    conjugate eX eX (RingEquiv.refl X) = RingEquiv.refl X' := by
  ext x
  simp [conjugate]

/-- Conjugation preserves composition of field equivalences exactly. -/
theorem conjugate_trans (eX : X ≃+* X') (eY : Y ≃+* Y')
    (eZ : Z ≃+* Z') (f : X ≃+* Y) (g : Y ≃+* Z) :
    (conjugate eX eY f).trans (conjugate eY eZ g) =
      conjugate eX eZ (f.trans g) := by
  ext x
  simp [conjugate]

/-- Conjugation preserves inverse equivalences exactly. -/
@[simp] theorem conjugate_symm (eX : X ≃+* X') (eY : Y ≃+* Y')
    (f : X ≃+* Y) :
    (conjugate eX eY f).symm = conjugate eY eX f.symm := by
  ext y
  simp [conjugate]

/-- Conjugation by fixed chart equivalences is faithful. -/
theorem conjugate_injective (eX : X ≃+* X') (eY : Y ≃+* Y') :
    Function.Injective (conjugate eX eY : (X ≃+* Y) → (X' ≃+* Y')) := by
  intro f g h
  ext x
  have hx := congrArg (fun F : X' ≃+* Y' ↦ eY.symm (F (eX x))) h
  simpa [conjugate] using hx

/-- Equality can be checked after conjugating both equivalences to fixed
reference charts. -/
theorem conjugate_eq_iff (eX : X ≃+* X') (eY : Y ≃+* Y')
    (f g : X ≃+* Y) :
    conjugate eX eY f = conjugate eX eY g ↔ f = g :=
  ⟨fun h ↦ conjugate_injective eX eY h,
    congrArg (conjugate eX eY)⟩

/-- Cancel a target automorphism from an equality of field equivalences.
This small algebraic lemma keeps deck-correction proofs independent of the
implementation of the finite normal covers on which they are applied. -/
theorem eq_trans_symm_of_trans_eq (f g : X ≃+* Y) (d : Y ≃+* Y)
    (h : f.trans d = g) : f = g.trans d.symm := by
  ext x
  have hx := congrArg (fun e : X ≃+* Y ↦ e x) h
  change d (f x) = g x at hx
  change f x = d.symm (g x)
  rw [← hx]
  simp

/-- A semantic four-arrow diagram on three fixed field charts.  Its four
faces are literal equalities of field equivalences rather than relations
in a formal quotient groupoid. -/
structure FourArrowDiagram (X Y Z : Type u)
    [Field X] [Field Y] [Field Z] where
  /-- The repeated left-family arrow labelled by `s`. -/
  leftS : X ≃+* Y
  /-- The repeated left-family arrow labelled by `sA`. -/
  leftSA : X ≃+* Y
  /-- The first based right-family arrow labelled by `e`. -/
  rightE : Y ≃+* Z
  /-- The inverse-input right-family arrow labelled by `a`. -/
  rightA : Y ≃+* Z
  /-- The second based right-family arrow labelled by `b`. -/
  rightB : Y ≃+* Z
  /-- The output right-family arrow labelled by `c`. -/
  rightC : Y ≃+* Z
  /-- The repeated composite arrow labelled by `u`. -/
  compositeU : X ≃+* Z
  /-- The repeated composite arrow labelled by `uB`. -/
  compositeUB : X ≃+* Z
  /-- The semantic face `s ≫ e = u`. -/
  se_u : leftS.trans rightE = compositeU
  /-- The semantic face `sA ≫ a = u`. -/
  sA_a_u : leftSA.trans rightA = compositeU
  /-- The semantic face `s ≫ b = uB`. -/
  s_b_uB : leftS.trans rightB = compositeUB
  /-- The semantic face `sA ≫ c = uB`. -/
  sA_c_uB : leftSA.trans rightC = compositeUB

namespace FourArrowDiagram

variable (D : FourArrowDiagram X Y Z)

/-- Transport a semantic four-arrow diagram to three reference fields by
conjugating every arrow. -/
def conjugate (eX : X ≃+* X') (eY : Y ≃+* Y')
    (eZ : Z ≃+* Z') : FourArrowDiagram X' Y' Z' where
  leftS := FieldEquiv.conjugate eX eY D.leftS
  leftSA := FieldEquiv.conjugate eX eY D.leftSA
  rightE := FieldEquiv.conjugate eY eZ D.rightE
  rightA := FieldEquiv.conjugate eY eZ D.rightA
  rightB := FieldEquiv.conjugate eY eZ D.rightB
  rightC := FieldEquiv.conjugate eY eZ D.rightC
  compositeU := FieldEquiv.conjugate eX eZ D.compositeU
  compositeUB := FieldEquiv.conjugate eX eZ D.compositeUB
  se_u := by
    rw [FieldEquiv.conjugate_trans, D.se_u]
  sA_a_u := by
    rw [FieldEquiv.conjugate_trans, D.sA_a_u]
  s_b_uB := by
    rw [FieldEquiv.conjugate_trans, D.s_b_uB]
  sA_c_uB := by
    rw [FieldEquiv.conjugate_trans, D.sA_c_uB]

/-- The transported diagram has the pointwise conjugated output arrow. -/
@[simp] theorem conjugate_rightC
    (eX : X ≃+* X') (eY : Y ≃+* Y') (eZ : Z ≃+* Z') :
    (D.conjugate eX eY eZ).rightC =
      FieldEquiv.conjugate eY eZ D.rightC :=
  rfl

/-- **Faithful semantic four-arrow cancellation.**  Four literal
composition identities between field equivalences force the output
right-family map to be the based difference product of the other three. -/
theorem right_cancellation :
    D.rightC = (D.rightA.trans D.rightE.symm).trans D.rightB := by
  ext y
  let x := D.leftSA.symm y
  have hsc := congrArg (fun f : X ≃+* Z ↦ f x) D.sA_c_uB
  have hsb := congrArg (fun f : X ≃+* Z ↦ f x) D.s_b_uB
  have hsa := congrArg (fun f : X ≃+* Z ↦ f x) D.sA_a_u
  have hse := congrArg (fun f : X ≃+* Z ↦ f x) D.se_u
  change D.rightC (D.leftSA x) = D.compositeUB x at hsc
  change D.rightB (D.leftS x) = D.compositeUB x at hsb
  change D.rightA (D.leftSA x) = D.compositeU x at hsa
  change D.rightE (D.leftS x) = D.compositeU x at hse
  change D.rightC y = D.rightB (D.rightE.symm (D.rightA y))
  calc
    D.rightC y = D.rightC (D.leftSA x) := by simp [x]
    _ = D.compositeUB x := hsc
    _ = D.rightB (D.leftS x) := hsb.symm
    _ = D.rightB (D.rightE.symm (D.rightE (D.leftS x))) := by simp
    _ = D.rightB (D.rightE.symm (D.compositeU x)) := by rw [hse]
    _ = D.rightB (D.rightE.symm (D.rightA (D.leftSA x))) := by rw [hsa]
    _ = D.rightB (D.rightE.symm (D.rightA y)) := by simp [x]

/-- Pointwise form of semantic four-arrow cancellation. -/
theorem right_cancellation_apply (y : Y) :
    D.rightC y = D.rightB (D.rightE.symm (D.rightA y)) := by
  exact DFunLike.congr_fun D.right_cancellation y

/-- Cancellation is invariant under simultaneous conjugation to any three
reference field charts. -/
theorem conjugate_right_cancellation
    (eX : X ≃+* X') (eY : Y ≃+* Y') (eZ : Z ≃+* Z') :
    (D.conjugate eX eY eZ).rightC =
      (((D.conjugate eX eY eZ).rightA.trans
        (D.conjugate eX eY eZ).rightE.symm).trans
          (D.conjugate eX eY eZ).rightB) :=
  (D.conjugate eX eY eZ).right_cancellation

end FourArrowDiagram

end FieldEquiv

end

end AclGeom
