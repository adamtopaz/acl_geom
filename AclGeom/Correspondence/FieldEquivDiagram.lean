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

/-- One literal composition triangle of field equivalences. -/
structure CompositionTriangle (X Y Z : Type u)
    [Field X] [Field Y] [Field Z] where
  /-- The left arrow. -/
  left : X ≃+* Y
  /-- The right arrow. -/
  right : Y ≃+* Z
  /-- The direct composite arrow. -/
  direct : X ≃+* Z
  /-- Literal composition of the two successive arrows. -/
  composition : left.trans right = direct

namespace CompositionTriangle

variable (T : CompositionTriangle X Y Z)

/-- Conjugate an entire composition triangle to three reference fields. -/
def conjugate (eX : X ≃+* X') (eY : Y ≃+* Y')
    (eZ : Z ≃+* Z') : CompositionTriangle X' Y' Z' where
  left := FieldEquiv.conjugate eX eY T.left
  right := FieldEquiv.conjugate eY eZ T.right
  direct := FieldEquiv.conjugate eX eZ T.direct
  composition := by
    rw [FieldEquiv.conjugate_trans, T.composition]

/-- A source chart canonically induces a middle chart by transporting
backwards through the left arrow. -/
def inducedMiddleChart (eX : X ≃+* X') : Y ≃+* X' :=
  T.left.symm.trans eX

/-- A source chart canonically induces a target chart by transporting
backwards through the direct arrow. -/
def inducedTargetChart (eX : X ≃+* X') : Z ≃+* X' :=
  T.direct.symm.trans eX

/-- With the induced middle chart, the conjugated left arrow is the
identity on the reference source. -/
@[simp] theorem conjugate_induced_left (eX : X ≃+* X') :
    (T.conjugate eX (T.inducedMiddleChart eX)
      (T.inducedTargetChart eX)).left = RingEquiv.refl X' := by
  ext x
  simp [conjugate, inducedMiddleChart]

/-- With the induced target chart, the conjugated direct arrow is the
identity on the reference source. -/
@[simp] theorem conjugate_induced_direct (eX : X ≃+* X') :
    (T.conjugate eX (T.inducedMiddleChart eX)
      (T.inducedTargetChart eX)).direct = RingEquiv.refl X' := by
  ext x
  simp [conjugate, inducedTargetChart]

end CompositionTriangle

/-- Four composition triangles together with compatible identifications of
all their source, middle, and target fields with three reference fields.
The four compatibility equations say exactly that repeated edge labels
remain the same after conjugation. -/
structure FourTriangleReference
    (X Y Z Xse Yse Zse Xsa Ysa Zsa Xsb Ysb Zsb Xsc Ysc Zsc : Type u)
    [Field X] [Field Y] [Field Z]
    [Field Xse] [Field Yse] [Field Zse]
    [Field Xsa] [Field Ysa] [Field Zsa]
    [Field Xsb] [Field Ysb] [Field Zsb]
    [Field Xsc] [Field Ysc] [Field Zsc] where
  /-- The `s·e=u` triangle. -/
  se : CompositionTriangle Xse Yse Zse
  /-- The `sA·a=u` triangle. -/
  sAa : CompositionTriangle Xsa Ysa Zsa
  /-- The `s·b=uB` triangle. -/
  sb : CompositionTriangle Xsb Ysb Zsb
  /-- The `sA·c=uB` triangle. -/
  sAc : CompositionTriangle Xsc Ysc Zsc
  /-- Reference chart for the first source field. -/
  seX : Xse ≃+* X
  /-- Reference chart for the first middle field. -/
  seY : Yse ≃+* Y
  /-- Reference chart for the first target field. -/
  seZ : Zse ≃+* Z
  /-- Reference chart for the second source field. -/
  sAaX : Xsa ≃+* X
  /-- Reference chart for the second middle field. -/
  sAaY : Ysa ≃+* Y
  /-- Reference chart for the second target field. -/
  sAaZ : Zsa ≃+* Z
  /-- Reference chart for the third source field. -/
  sbX : Xsb ≃+* X
  /-- Reference chart for the third middle field. -/
  sbY : Ysb ≃+* Y
  /-- Reference chart for the third target field. -/
  sbZ : Zsb ≃+* Z
  /-- Reference chart for the fourth source field. -/
  sAcX : Xsc ≃+* X
  /-- Reference chart for the fourth middle field. -/
  sAcY : Ysc ≃+* Y
  /-- Reference chart for the fourth target field. -/
  sAcZ : Zsc ≃+* Z
  /-- The repeated `s` arrow agrees after reference conjugation. -/
  leftS :
    (sb.conjugate sbX sbY sbZ).left =
      (se.conjugate seX seY seZ).left
  /-- The repeated `sA` arrow agrees after reference conjugation. -/
  leftSA :
    (sAc.conjugate sAcX sAcY sAcZ).left =
      (sAa.conjugate sAaX sAaY sAaZ).left
  /-- The repeated `u` composite agrees after reference conjugation. -/
  compositeU :
    (sAa.conjugate sAaX sAaY sAaZ).direct =
      (se.conjugate seX seY seZ).direct
  /-- The repeated `uB` composite agrees after reference conjugation. -/
  compositeUB :
    (sAc.conjugate sAcX sAcY sAcZ).direct =
      (sb.conjugate sbX sbY sbZ).direct

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

namespace FourTriangleReference

variable {Xse Yse Zse Xsa Ysa Zsa Xsb Ysb Zsb Xsc Ysc Zsc : Type u}
  [Field Xse] [Field Yse] [Field Zse]
  [Field Xsa] [Field Ysa] [Field Zsa]
  [Field Xsb] [Field Ysb] [Field Zsb]
  [Field Xsc] [Field Ysc] [Field Zsc]

/-- Four composition triangles with chosen charts to one reference source
acquire canonical middle and target charts.  All repeated left and direct
arrows then agree because their conjugates are identities. -/
def ofSourceCharts
    (se : CompositionTriangle Xse Yse Zse)
    (sAa : CompositionTriangle Xsa Ysa Zsa)
    (sb : CompositionTriangle Xsb Ysb Zsb)
    (sAc : CompositionTriangle Xsc Ysc Zsc)
    (seX : Xse ≃+* X) (sAaX : Xsa ≃+* X)
    (sbX : Xsb ≃+* X) (sAcX : Xsc ≃+* X) :
    FourTriangleReference X X X
      Xse Yse Zse Xsa Ysa Zsa Xsb Ysb Zsb Xsc Ysc Zsc where
  se := se
  sAa := sAa
  sb := sb
  sAc := sAc
  seX := seX
  seY := se.inducedMiddleChart seX
  seZ := se.inducedTargetChart seX
  sAaX := sAaX
  sAaY := sAa.inducedMiddleChart sAaX
  sAaZ := sAa.inducedTargetChart sAaX
  sbX := sbX
  sbY := sb.inducedMiddleChart sbX
  sbZ := sb.inducedTargetChart sbX
  sAcX := sAcX
  sAcY := sAc.inducedMiddleChart sAcX
  sAcZ := sAc.inducedTargetChart sAcX
  leftS := by simp
  leftSA := by simp
  compositeU := by simp
  compositeUB := by simp

variable {Xse Yse Zse Xsa Ysa Zsa Xsb Ysb Zsb Xsc Ysc Zsc : Type u}
  [Field Xse] [Field Yse] [Field Zse]
  [Field Xsa] [Field Ysa] [Field Zsa]
  [Field Xsb] [Field Ysb] [Field Zsb]
  [Field Xsc] [Field Ysc] [Field Zsc]
  (R : FourTriangleReference
    X Y Z Xse Yse Zse Xsa Ysa Zsa Xsb Ysb Zsb Xsc Ysc Zsc)

/-- Compatible reference charts turn four independently typed composition
triangles into one semantic four-arrow diagram. -/
def toFourArrowDiagram : FourArrowDiagram X Y Z where
  leftS := (R.se.conjugate R.seX R.seY R.seZ).left
  leftSA := (R.sAa.conjugate R.sAaX R.sAaY R.sAaZ).left
  rightE := (R.se.conjugate R.seX R.seY R.seZ).right
  rightA := (R.sAa.conjugate R.sAaX R.sAaY R.sAaZ).right
  rightB := (R.sb.conjugate R.sbX R.sbY R.sbZ).right
  rightC := (R.sAc.conjugate R.sAcX R.sAcY R.sAcZ).right
  compositeU := (R.se.conjugate R.seX R.seY R.seZ).direct
  compositeUB := (R.sb.conjugate R.sbX R.sbY R.sbZ).direct
  se_u := (R.se.conjugate R.seX R.seY R.seZ).composition
  sA_a_u := by
    rw [(R.sAa.conjugate R.sAaX R.sAaY R.sAaZ).composition,
      R.compositeU]
  s_b_uB := by
    rw [← R.leftS,
      (R.sb.conjugate R.sbX R.sbY R.sbZ).composition]
  sA_c_uB := by
    rw [← R.leftSA,
      (R.sAc.conjugate R.sAcX R.sAcY R.sAcZ).composition,
      R.compositeUB]

end FourTriangleReference

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
