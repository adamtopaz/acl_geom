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

The generic construction `PresentedFamilyGroupoidOf R` is also exposed for
an arbitrary ternary relation `R`.  This lets the rank-two `A/B/C` family
composition from a `Psi` witness use the same categorical layer without
pretending its parameters are single field elements.
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

section ArbitraryRelation

variable {P : Type v} (R : P → P → P → Prop)

/-- The generating composition relations attached to an arbitrary ternary
parameter locus, oriented as `T(t) ≫ S(s) = U(u)`. -/
inductive CorrespondenceFamilyRelationOf :
    HomRel (FreeCorrespondenceFamilyGroupoid P)
  | multiplication (t s u : P) (h : R t s u) :
      CorrespondenceFamilyRelationOf
        (FreeCorrespondenceFamilyGroupoid.t t ≫
          FreeCorrespondenceFamilyGroupoid.s s)
        (FreeCorrespondenceFamilyGroupoid.u u)

/-- The genuine three-object groupoid presented by any ternary relation on
the parameter type. -/
abbrev PresentedFamilyGroupoidOf :=
  CategoryTheory.Quotient (CorrespondenceFamilyRelationOf R)

namespace PresentedFamilyGroupoidOf

/-- The object `X₀` in the groupoid presented by `R`. -/
def x0 : PresentedFamilyGroupoidOf R :=
  (CategoryTheory.Quotient.functor (CorrespondenceFamilyRelationOf R)).obj
    FreeCorrespondenceFamilyGroupoid.x0

/-- The object `X₁` in the groupoid presented by `R`. -/
def x1 : PresentedFamilyGroupoidOf R :=
  (CategoryTheory.Quotient.functor (CorrespondenceFamilyRelationOf R)).obj
    FreeCorrespondenceFamilyGroupoid.x1

/-- The object `X₂` in the groupoid presented by `R`. -/
def x2 : PresentedFamilyGroupoidOf R :=
  (CategoryTheory.Quotient.functor (CorrespondenceFamilyRelationOf R)).obj
    FreeCorrespondenceFamilyGroupoid.x2

/-- A `T`-family arrow in the groupoid presented by `R`. -/
def t (a : P) : x0 R ⟶ x1 R :=
  (CategoryTheory.Quotient.functor (CorrespondenceFamilyRelationOf R)).map
    (FreeCorrespondenceFamilyGroupoid.t a)

/-- An `S`-family arrow in the groupoid presented by `R`. -/
def s (a : P) : x1 R ⟶ x2 R :=
  (CategoryTheory.Quotient.functor (CorrespondenceFamilyRelationOf R)).map
    (FreeCorrespondenceFamilyGroupoid.s a)

/-- A `U`-family arrow in the groupoid presented by `R`. -/
def u (a : P) : x0 R ⟶ x2 R :=
  (CategoryTheory.Quotient.functor (CorrespondenceFamilyRelationOf R)).map
    (FreeCorrespondenceFamilyGroupoid.u a)

/-- Every point of `R` gives its defining literal composition in the
presented groupoid. -/
theorem t_comp_s_eq_u {t s u : P} (h : R t s u) :
    PresentedFamilyGroupoidOf.t R t ≫ PresentedFamilyGroupoidOf.s R s =
      PresentedFamilyGroupoidOf.u R u := by
  exact CategoryTheory.Quotient.sound
    (CorrespondenceFamilyRelationOf R)
    (CorrespondenceFamilyRelationOf.multiplication t s u h)

/-- Relabel the three generating families along a parameter map, with
values already taken in a target presented family groupoid. -/
def relabelPrefunctor {Q : Type v} (S : Q → Q → Q → Prop)
    (f : P → Q) :
    CorrespondenceFamilyObject P ⥤q PresentedFamilyGroupoidOf S where
  obj
    | .x0 => x0 S
    | .x1 => x1 S
    | .x2 => x2 S
  map g := by
    cases g with
    | t a => exact t S (f a)
    | s a => exact s S (f a)
    | u a => exact u S (f a)

/-- The functor on free family groupoids induced by relabelling every
parameter with `f`. -/
def freeRelabelFunctor {Q : Type v} (S : Q → Q → Q → Prop)
    (f : P → Q) :
    FreeCorrespondenceFamilyGroupoid P ⥤ PresentedFamilyGroupoidOf S :=
  Quiver.FreeGroupoid.lift (relabelPrefunctor S f)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem freeRelabelFunctor_t {Q : Type v}
    (S : Q → Q → Q → Prop) (f : P → Q) (a : P) :
    (freeRelabelFunctor S f).map (FreeCorrespondenceFamilyGroupoid.t a) =
      t S (f a) := by
  have h := Prefunctor.congr_hom
    (Quiver.FreeGroupoid.lift_spec (relabelPrefunctor S f))
    (CorrespondenceFamilyGenerator.t a)
  simpa [freeRelabelFunctor, FreeCorrespondenceFamilyGroupoid.t,
    relabelPrefunctor] using h

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem freeRelabelFunctor_s {Q : Type v}
    (S : Q → Q → Q → Prop) (f : P → Q) (a : P) :
    (freeRelabelFunctor S f).map (FreeCorrespondenceFamilyGroupoid.s a) =
      s S (f a) := by
  have h := Prefunctor.congr_hom
    (Quiver.FreeGroupoid.lift_spec (relabelPrefunctor S f))
    (CorrespondenceFamilyGenerator.s a)
  simpa [freeRelabelFunctor, FreeCorrespondenceFamilyGroupoid.s,
    relabelPrefunctor] using h

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem freeRelabelFunctor_u {Q : Type v}
    (S : Q → Q → Q → Prop) (f : P → Q) (a : P) :
    (freeRelabelFunctor S f).map (FreeCorrespondenceFamilyGroupoid.u a) =
      u S (f a) := by
  have h := Prefunctor.congr_hom
    (Quiver.FreeGroupoid.lift_spec (relabelPrefunctor S f))
    (CorrespondenceFamilyGenerator.u a)
  simpa [freeRelabelFunctor, FreeCorrespondenceFamilyGroupoid.u,
    relabelPrefunctor] using h

/-- A map of parameter sets carrying every source multiplication relation
to a target relation induces a functor of the presented groupoids. -/
def map {Q : Type v} {S : Q → Q → Q → Prop} (f : P → Q)
    (hf : ∀ {t s u}, R t s u → S (f t) (f s) (f u)) :
    PresentedFamilyGroupoidOf R ⥤ PresentedFamilyGroupoidOf S :=
  CategoryTheory.Quotient.lift (CorrespondenceFamilyRelationOf R)
    (freeRelabelFunctor S f) (by
      rintro _ _ _ _ hrel
      cases hrel with
      | multiplication t s u h =>
          simp only [Functor.map_comp, freeRelabelFunctor_t,
            freeRelabelFunctor_s, freeRelabelFunctor_u]
          exact t_comp_s_eq_u S (hf h))

@[simp] theorem map_t {Q : Type v} {S : Q → Q → Q → Prop}
    (f : P → Q) (hf : ∀ {t s u}, R t s u → S (f t) (f s) (f u))
    (a : P) :
    (map R f hf).map (t R a) = t S (f a) := by
  exact CategoryTheory.Quotient.lift_map_functor_map
    (CorrespondenceFamilyRelationOf R) (freeRelabelFunctor S f) _
    (FreeCorrespondenceFamilyGroupoid.t a)

@[simp] theorem map_s {Q : Type v} {S : Q → Q → Q → Prop}
    (f : P → Q) (hf : ∀ {t s u}, R t s u → S (f t) (f s) (f u))
    (a : P) :
    (map R f hf).map (s R a) = s S (f a) := by
  exact CategoryTheory.Quotient.lift_map_functor_map
    (CorrespondenceFamilyRelationOf R) (freeRelabelFunctor S f) _
    (FreeCorrespondenceFamilyGroupoid.s a)

@[simp] theorem map_u {Q : Type v} {S : Q → Q → Q → Prop}
    (f : P → Q) (hf : ∀ {t s u}, R t s u → S (f t) (f s) (f u))
    (a : P) :
    (map R f hf).map (u R a) = u S (f a) := by
  exact CategoryTheory.Quotient.lift_map_functor_map
    (CorrespondenceFamilyRelationOf R) (freeRelabelFunctor S f) _
    (FreeCorrespondenceFamilyGroupoid.u a)

/-- Relabel a family presentation contravariantly: the first and second
families are exchanged and every target arrow is inverted.  This is the
covariant groupoid form of an anti-homomorphism between the right-arrow
charts. -/
def reverseRelabelPrefunctor {Q : Type v} (S : Q → Q → Q → Prop)
    (f : P → Q) :
    CorrespondenceFamilyObject P ⥤q PresentedFamilyGroupoidOf S where
  obj
    | .x0 => x2 S
    | .x1 => x1 S
    | .x2 => x0 S
  map g := by
    cases g with
    | t a => exact inv (s S (f a))
    | s a => exact inv (t S (f a))
    | u a => exact inv (u S (f a))

/-- The free-groupoid functor underlying contravariant relabelling. -/
def freeReverseRelabelFunctor {Q : Type v}
    (S : Q → Q → Q → Prop) (f : P → Q) :
    FreeCorrespondenceFamilyGroupoid P ⥤ PresentedFamilyGroupoidOf S :=
  Quiver.FreeGroupoid.lift (reverseRelabelPrefunctor S f)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem freeReverseRelabelFunctor_t {Q : Type v}
    (S : Q → Q → Q → Prop) (f : P → Q) (a : P) :
    (freeReverseRelabelFunctor S f).map
        (FreeCorrespondenceFamilyGroupoid.t a) =
      inv (s S (f a)) := by
  have h := Prefunctor.congr_hom
    (Quiver.FreeGroupoid.lift_spec (reverseRelabelPrefunctor S f))
    (CorrespondenceFamilyGenerator.t a)
  simpa [freeReverseRelabelFunctor, FreeCorrespondenceFamilyGroupoid.t,
    reverseRelabelPrefunctor] using h

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem freeReverseRelabelFunctor_s {Q : Type v}
    (S : Q → Q → Q → Prop) (f : P → Q) (a : P) :
    (freeReverseRelabelFunctor S f).map
        (FreeCorrespondenceFamilyGroupoid.s a) =
      inv (t S (f a)) := by
  have h := Prefunctor.congr_hom
    (Quiver.FreeGroupoid.lift_spec (reverseRelabelPrefunctor S f))
    (CorrespondenceFamilyGenerator.s a)
  simpa [freeReverseRelabelFunctor, FreeCorrespondenceFamilyGroupoid.s,
    reverseRelabelPrefunctor] using h

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem freeReverseRelabelFunctor_u {Q : Type v}
    (S : Q → Q → Q → Prop) (f : P → Q) (a : P) :
    (freeReverseRelabelFunctor S f).map
        (FreeCorrespondenceFamilyGroupoid.u a) =
      inv (u S (f a)) := by
  have h := Prefunctor.congr_hom
    (Quiver.FreeGroupoid.lift_spec (reverseRelabelPrefunctor S f))
    (CorrespondenceFamilyGenerator.u a)
  simpa [freeReverseRelabelFunctor, FreeCorrespondenceFamilyGroupoid.u,
    reverseRelabelPrefunctor] using h

set_option backward.isDefEq.respectTransparency false in
/-- If relabelling exchanges the two inputs of every ternary relation,
it induces a functor that reverses the three target arrows. -/
def reverseMap {Q : Type v} {S : Q → Q → Q → Prop} (f : P → Q)
    (hf : ∀ {t s u}, R t s u → S (f s) (f t) (f u)) :
    PresentedFamilyGroupoidOf R ⥤ PresentedFamilyGroupoidOf S :=
  CategoryTheory.Quotient.lift (CorrespondenceFamilyRelationOf R)
    (freeReverseRelabelFunctor S f) (by
      rintro _ _ _ _ hrel
      cases hrel with
      | multiplication t s u h =>
          simp only [Functor.map_comp, freeReverseRelabelFunctor_t,
            freeReverseRelabelFunctor_s, freeReverseRelabelFunctor_u]
          have ht := congrArg (fun g ↦ CategoryTheory.inv g)
            (t_comp_s_eq_u S (hf h))
          simpa only [IsIso.inv_comp] using ht)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem reverseMap_t {Q : Type v} {S : Q → Q → Q → Prop}
    (f : P → Q)
    (hf : ∀ {t s u}, R t s u → S (f s) (f t) (f u)) (a : P) :
    (reverseMap R f hf).map (t R a) = inv (s S (f a)) := by
  change (freeReverseRelabelFunctor S f).map
    (FreeCorrespondenceFamilyGroupoid.t a) = _
  exact freeReverseRelabelFunctor_t S f a

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem reverseMap_s {Q : Type v} {S : Q → Q → Q → Prop}
    (f : P → Q)
    (hf : ∀ {t s u}, R t s u → S (f s) (f t) (f u)) (a : P) :
    (reverseMap R f hf).map (s R a) = inv (t S (f a)) := by
  change (freeReverseRelabelFunctor S f).map
    (FreeCorrespondenceFamilyGroupoid.s a) = _
  exact freeReverseRelabelFunctor_s S f a

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem reverseMap_u {Q : Type v} {S : Q → Q → Q → Prop}
    (f : P → Q)
    (hf : ∀ {t s u}, R t s u → S (f s) (f t) (f u)) (a : P) :
    (reverseMap R f hf).map (u R a) = inv (u S (f a)) := by
  change (freeReverseRelabelFunctor S f).map
    (FreeCorrespondenceFamilyGroupoid.u a) = _
  exact freeReverseRelabelFunctor_u S f a

/-- Four points of an arbitrary ternary relation cancel on the
right-family arrow chart.  If

`s · e = u`, `sA · a = u`, `s · b = uB`, and
`sA · c = uB`,

then the presented `S`-family arrow satisfies `c = a e⁻¹ b`. -/
theorem fourArrow_right_cancellation
    {s e a b u sA uB c : P}
    (hse : R s e u) (hsa : R sA a u)
    (hsb : R s b uB) (hsc : R sA c uB) :
    PresentedFamilyGroupoidOf.s R c =
      groupoidDifferenceProduct
        (PresentedFamilyGroupoidOf.s R e)
        (PresentedFamilyGroupoidOf.s R a)
        (PresentedFamilyGroupoidOf.s R b) := by
  let ts := PresentedFamilyGroupoidOf.t R s
  let tsA := PresentedFamilyGroupoidOf.t R sA
  let se := PresentedFamilyGroupoidOf.s R e
  let sa := PresentedFamilyGroupoidOf.s R a
  let sb := PresentedFamilyGroupoidOf.s R b
  let sc := PresentedFamilyGroupoidOf.s R c
  let uu := PresentedFamilyGroupoidOf.u R u
  let uuB := PresentedFamilyGroupoidOf.u R uB
  have hse' : ts ≫ se = uu := t_comp_s_eq_u R hse
  have hsa' : tsA ≫ sa = uu := t_comp_s_eq_u R hsa
  have hsb' : ts ≫ sb = uuB := t_comp_s_eq_u R hsb
  have hsc' : tsA ≫ sc = uuB := t_comp_s_eq_u R hsc
  change sc = sa ≫ inv se ≫ sb
  apply (cancel_epi tsA).1
  rw [hsc', ← Category.assoc, hsa', ← hse']
  simpa [Category.assoc] using hsb'.symm

end PresentedFamilyGroupoidOf

end ArbitraryRelation

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
