/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.Family
import AclGeom.Correspondence.GroupConfiguration
import Mathlib.CategoryTheory.Groupoid.FreeGroupoid

/-!
# The presented groupoid of a correspondence multiplication family

A generically finite multiplication locus does not itself define a
single-valued operation on its parameter curve.  It does, however, give
exact composition relations among the three normalized correspondence
families in a partial quadrangle.  This module keeps those two facts
separate.

`PresentedFamilyGroupoid M` is the genuine three-object groupoid generated
by arrows

* `T(t) : X₀ ⟶ X₁`,
* `S(s) : X₁ ⟶ X₂`, and
* `U(u) : X₀ ⟶ X₂`,

subject to the relation `T(t) ≫ S(s) = U(u)` for every selected component
`M.IsRealization s t u`.  It is constructed as a quotient of the free
groupoid, so composition, inverse, and associativity are genuine category
operations rather than additional axioms.

The four exact family components in `FourArrowDifferenceDiagram` then give
the blueprint cancellation identity on the `T`-arrow chart.  This is the
parameter-labelled categorical layer above the finite normal-cover branch
groupoids; it does not identify a family parameter with a deck
transformation of one fixed finite cover.
-/

namespace AclGeom

noncomputable section

open CategoryTheory

universe u v

variable {k : Type u} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω]

/-- The three objects on which the `T`, `S`, and `U` correspondence
families act. -/
inductive CorrespondenceFamilyObject (Ω : Type v)
  | x0
  | x1
  | x2
  deriving DecidableEq

/-- The parameter-labelled generating arrows of the three correspondence
families. -/
inductive CorrespondenceFamilyGenerator (Ω : Type v) :
    CorrespondenceFamilyObject Ω → CorrespondenceFamilyObject Ω → Type v
  | t (a : Ω) : CorrespondenceFamilyGenerator Ω .x0 .x1
  | s (a : Ω) : CorrespondenceFamilyGenerator Ω .x1 .x2
  | u (a : Ω) : CorrespondenceFamilyGenerator Ω .x0 .x2

instance : Quiver (CorrespondenceFamilyObject Ω) where
  Hom := CorrespondenceFamilyGenerator Ω

/-- The free groupoid on the three parameter-labelled arrow families. -/
abbrev FreeCorrespondenceFamilyGroupoid (Ω : Type v) :=
  Quiver.FreeGroupoid (CorrespondenceFamilyObject Ω)

namespace FreeCorrespondenceFamilyGroupoid

/-- The object `X₀` in the free family groupoid. -/
def x0 : FreeCorrespondenceFamilyGroupoid Ω :=
  (Quiver.FreeGroupoid.of (CorrespondenceFamilyObject Ω)).obj .x0

/-- The object `X₁` in the free family groupoid. -/
def x1 : FreeCorrespondenceFamilyGroupoid Ω :=
  (Quiver.FreeGroupoid.of (CorrespondenceFamilyObject Ω)).obj .x1

/-- The object `X₂` in the free family groupoid. -/
def x2 : FreeCorrespondenceFamilyGroupoid Ω :=
  (Quiver.FreeGroupoid.of (CorrespondenceFamilyObject Ω)).obj .x2

/-- A generating member of the `T`-family. -/
def t (a : Ω) : x0 (Ω := Ω) ⟶ x1 (Ω := Ω) :=
  (Quiver.FreeGroupoid.of (CorrespondenceFamilyObject Ω)).map
    (CorrespondenceFamilyGenerator.t a)

/-- A generating member of the `S`-family. -/
def s (a : Ω) : x1 (Ω := Ω) ⟶ x2 (Ω := Ω) :=
  (Quiver.FreeGroupoid.of (CorrespondenceFamilyObject Ω)).map
    (CorrespondenceFamilyGenerator.s a)

/-- A generating member of the `U`-family. -/
def u (a : Ω) : x0 (Ω := Ω) ⟶ x2 (Ω := Ω) :=
  (Quiver.FreeGroupoid.of (CorrespondenceFamilyObject Ω)).map
    (CorrespondenceFamilyGenerator.u a)

end FreeCorrespondenceFamilyGroupoid

variable (M : FiniteCorrespondenceMultiplication (k := k) (Ω := Ω))

/-- The generating composition relations supplied by the selected prime
components of the multiplication locus. -/
inductive CorrespondenceFamilyRelation :
    HomRel (FreeCorrespondenceFamilyGroupoid Ω)
  | multiplication (s t u : Ω) (h : M.IsRealization s t u) :
      CorrespondenceFamilyRelation
        (FreeCorrespondenceFamilyGroupoid.t t ≫
          FreeCorrespondenceFamilyGroupoid.s s)
        (FreeCorrespondenceFamilyGroupoid.u u)

/-- The genuine three-object groupoid presented by the normalized generic
`T`, `S`, and `U` family components.  Quotienting a free groupoid by an
arbitrary homogeneous relation again carries a groupoid instance. -/
abbrev PresentedFamilyGroupoid :=
  CategoryTheory.Quotient (CorrespondenceFamilyRelation M)

namespace PresentedFamilyGroupoid

/-- The object `X₀` of the presented family groupoid. -/
def x0 : PresentedFamilyGroupoid M :=
  (CategoryTheory.Quotient.functor (CorrespondenceFamilyRelation M)).obj
    FreeCorrespondenceFamilyGroupoid.x0

/-- The object `X₁` of the presented family groupoid. -/
def x1 : PresentedFamilyGroupoid M :=
  (CategoryTheory.Quotient.functor (CorrespondenceFamilyRelation M)).obj
    FreeCorrespondenceFamilyGroupoid.x1

/-- The object `X₂` of the presented family groupoid. -/
def x2 : PresentedFamilyGroupoid M :=
  (CategoryTheory.Quotient.functor (CorrespondenceFamilyRelation M)).obj
    FreeCorrespondenceFamilyGroupoid.x2

/-- The arrow represented by the `T`-family member with parameter `a`. -/
def t (a : Ω) : x0 M ⟶ x1 M :=
  (CategoryTheory.Quotient.functor (CorrespondenceFamilyRelation M)).map
    (FreeCorrespondenceFamilyGroupoid.t a)

/-- The arrow represented by the `S`-family member with parameter `a`. -/
def s (a : Ω) : x1 M ⟶ x2 M :=
  (CategoryTheory.Quotient.functor (CorrespondenceFamilyRelation M)).map
    (FreeCorrespondenceFamilyGroupoid.s a)

/-- The arrow represented by the `U`-family member with parameter `a`. -/
def u (a : Ω) : x0 M ⟶ x2 M :=
  (CategoryTheory.Quotient.functor (CorrespondenceFamilyRelation M)).map
    (FreeCorrespondenceFamilyGroupoid.u a)

/-- Every selected component of the ternary multiplication locus is the
corresponding literal composition in the presented groupoid. -/
theorem t_comp_s_eq_u {s t u : Ω} (h : M.IsRealization s t u) :
    PresentedFamilyGroupoid.t M t ≫ PresentedFamilyGroupoid.s M s =
      PresentedFamilyGroupoid.u M u := by
  exact CategoryTheory.Quotient.sound
    (CorrespondenceFamilyRelation M)
    (CorrespondenceFamilyRelation.multiplication s t u h)

/-- The four selected prime components in a difference diagram cancel in
the genuine family groupoid.  With the categorical composition convention,
the displayed output is `b ≫ e⁻¹ ≫ a`; this is the difference product
whose two input slots are `(b,a)`. -/
theorem fourArrow_cancellation {s a b e : Ω}
    (D : M.FourArrowDifferenceDiagram s a b e) :
    PresentedFamilyGroupoid.t M D.c =
      groupoidDifferenceProduct
        (PresentedFamilyGroupoid.t M e)
        (PresentedFamilyGroupoid.t M b)
        (PresentedFamilyGroupoid.t M a) := by
  let te := PresentedFamilyGroupoid.t M e
  let ta := PresentedFamilyGroupoid.t M a
  let tb := PresentedFamilyGroupoid.t M b
  let tc := PresentedFamilyGroupoid.t M D.c
  let ss := PresentedFamilyGroupoid.s M s
  let ssA := PresentedFamilyGroupoid.s M D.sA
  let uu := PresentedFamilyGroupoid.u M D.u
  let uuB := PresentedFamilyGroupoid.u M D.uB
  have hse : te ≫ ss = uu := t_comp_s_eq_u M D.se_u
  have hsa : ta ≫ ssA = uu := t_comp_s_eq_u M D.sA_a_u
  have hsb : tb ≫ ss = uuB := t_comp_s_eq_u M D.s_b_uB
  have hsc : tc ≫ ssA = uuB := t_comp_s_eq_u M D.sA_c_uB
  apply (cancel_mono ssA).1
  simp only [groupoidDifferenceProduct, Category.assoc]
  rw [hsc, hsa, ← hse]
  change uuB = tb ≫ inv te ≫ te ≫ ss
  simpa using hsb.symm

/-- Swapping the two independent chart inputs in the four-arrow
construction yields the ordinary difference-product order
`a ≫ e⁻¹ ≫ b`. -/
theorem fourArrow_cancellation_swapped {s a b e : Ω}
    (D : M.FourArrowDifferenceDiagram s b a e) :
    PresentedFamilyGroupoid.t M D.c =
      groupoidDifferenceProduct
        (PresentedFamilyGroupoid.t M e)
        (PresentedFamilyGroupoid.t M a)
        (PresentedFamilyGroupoid.t M b) :=
  fourArrow_cancellation M D

end PresentedFamilyGroupoid

end

end AclGeom
