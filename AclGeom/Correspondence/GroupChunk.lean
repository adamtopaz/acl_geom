/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.Composition
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# The rational group chunk theorem

The algebraic core of Weil's group-chunk construction.  Once a chosen branch
on the common normal cover makes the generic multiplication and inverse
single-valued, the three identities in blueprint Theorem
`rational-group-chunk` force an honest group:

* `RationalGroupChunk` records associativity and the two generic inverse
  identities in their everywhere-defined algebraic form;
* `RationalGroupChunk.toGroup` constructs the canonical group structure,
  proving rather than assuming the identity laws;
* `TranslationGroupChunk` records the faithful chart of left translations
  in the automorphism group of the normalized function field;
* `TranslationGroupChunk.translationHom` is that chart as an injective group
  homomorphism.

The geometric gluing/descent layer and its applications to the six-point and
affine configurations are built on this core in subsequent slices.

**Status:** in progress (M4a, checklist C3, issue #12 pipeline step 2).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

/-- The everywhere-defined algebraic core of a rational group chunk after
passing to the selected branch on its common normal cover.  The two inverse
laws are the pointwise forms of blueprint hypothesis (iii). -/
structure RationalGroupChunk (V : Type*) where
  /-- Generic multiplication, made single-valued on the selected branch. -/
  mul : V → V → V
  /-- Generic inverse on the selected branch. -/
  inv : V → V
  /-- Generic associativity, promoted to an identity of rational maps. -/
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  /-- Left cancellation by the selected inverse. -/
  inv_mul_mul : ∀ a b, mul (inv a) (mul a b) = b
  /-- Right cancellation by the selected inverse. -/
  mul_mul_inv : ∀ a b, mul (mul b a) (inv a) = b

namespace RationalGroupChunk

variable {V : Type*} (C : RationalGroupChunk V)

/-- The left unit produced from a parameter `a`. -/
def leftUnit (a : V) : V := C.mul (C.inv a) a

/-- The right unit produced from a parameter `a`. -/
def rightUnit (a : V) : V := C.mul a (C.inv a)

/-- Every `leftUnit a` acts as a left identity. -/
theorem leftUnit_mul (a b : V) : C.mul (C.leftUnit a) b = b := by
  rw [leftUnit, C.mul_assoc]
  exact C.inv_mul_mul a b

/-- Every `rightUnit a` acts as a right identity. -/
theorem mul_rightUnit (a b : V) : C.mul b (C.rightUnit a) = b := by
  rw [rightUnit, ← C.mul_assoc]
  exact C.mul_mul_inv a b

/-- A left unit and a right unit necessarily coincide. -/
theorem leftUnit_eq_rightUnit (a b : V) : C.leftUnit a = C.rightUnit b := by
  calc
    C.leftUnit a = C.mul (C.leftUnit a) (C.rightUnit b) :=
      (C.mul_rightUnit b (C.leftUnit a)).symm
    _ = C.rightUnit b := C.leftUnit_mul a (C.rightUnit b)

/-- All parameter-dependent left units coincide. -/
theorem leftUnit_eq_leftUnit (a b : V) : C.leftUnit a = C.leftUnit b :=
  (C.leftUnit_eq_rightUnit a b).trans (C.leftUnit_eq_rightUnit b b).symm

/-- All parameter-dependent right units coincide. -/
theorem rightUnit_eq_rightUnit (a b : V) : C.rightUnit a = C.rightUnit b :=
  (C.leftUnit_eq_rightUnit a a).symm.trans (C.leftUnit_eq_rightUnit a b)

/-- The canonical group carried by a nonempty rational group chunk.

The identity is `i(a₀) * a₀` for an arbitrary parameter `a₀`;
`leftUnit_eq_leftUnit` proves independence of this choice.  The resulting
group multiplication and inverse are definitionally the chunk operations. -/
@[reducible] def toGroup [Nonempty V] : Group V := by
  let a₀ : V := Classical.choice inferInstance
  letI : Mul V := ⟨C.mul⟩
  letI : Inv V := ⟨C.inv⟩
  letI : One V := ⟨C.leftUnit a₀⟩
  exact Group.ofLeftAxioms
    (fun a b c ↦ C.mul_assoc a b c)
    (fun a ↦ C.leftUnit_mul a₀ a)
    (fun a ↦ C.leftUnit_eq_leftUnit a a₀)

end RationalGroupChunk

section TranslationChart

variable (k F V : Type*) [Field k] [Field F] [Algebra k F]

/-- A rational group chunk together with its faithful chart of left
translations on the normalized function field.  These are the germs `L_a`
in blueprint (8.2). -/
structure TranslationGroupChunk extends RationalGroupChunk V where
  /-- The birational left translation attached to a chart parameter. -/
  translation : V → (F ≃ₐ[k] F)
  /-- Composition of translations is chart multiplication. -/
  translation_mul : ∀ a b,
    translation (mul a b) = translation a * translation b
  /-- The selected inverse gives the inverse birational transformation. -/
  translation_inv : ∀ a, translation (inv a) = (translation a)⁻¹
  /-- The translation chart is generically faithful. -/
  translation_injective : Function.Injective translation

namespace TranslationGroupChunk

variable {k F V : Type*} [Field k] [Field F] [Algebra k F]
    (C : TranslationGroupChunk k F V) [Nonempty V]

/-- The multiplication and identity underlying the canonical chunk group,
exposed as the instance parameter needed by bundled homomorphisms. -/
@[reducible] def chunkMulOne : MulOne V where
  one := C.toRationalGroupChunk.leftUnit (Classical.choice inferInstance)
  mul := C.mul

/-- The faithful translation chart as a group homomorphism into the
`k`-automorphism group of the normalized function field. -/
def translationHom : @MonoidHom V (F ≃ₐ[k] F) C.chunkMulOne inferInstance := by
  letI : MulOne V := C.chunkMulOne
  let a₀ : V := Classical.choice inferInstance
  refine
    { toFun := C.translation
      map_one' := ?_
      map_mul' := C.translation_mul }
  change C.translation (C.toRationalGroupChunk.leftUnit a₀) = 1
  calc
    C.translation (C.toRationalGroupChunk.leftUnit a₀) =
        C.translation (C.inv a₀) * C.translation a₀ := C.translation_mul _ _
    _ = (C.translation a₀)⁻¹ * C.translation a₀ := by rw [C.translation_inv]
    _ = 1 := inv_mul_cancel _

/-- The translation homomorphism is injective. -/
theorem translationHom_injective : Function.Injective (translationHom C) :=
  fun _ _ h ↦ C.translation_injective h

omit [Nonempty V] in
/-- Equality of left translations detects equality of chart parameters. -/
theorem translation_eq_iff {a b : V} : C.translation a = C.translation b ↔ a = b :=
  C.translation_injective.eq_iff

end TranslationGroupChunk

end TranslationChart

end

end AclGeom
