/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import AclGeom.Functorial.Literal
import Mathlib.CategoryTheory.Quotient
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The Frobenius-orbit groupoid and full faithfulness

Blueprint §20.5. Two arrows `Φ, Φ' : A ⟶ B` of `Ext^i` are related when `Φ' = F_B^n ∘ Φ` for an
integer `n` (`PerfExt.frobRel`, (20.17)). By Frobenius naturality this is a congruence, and the
quotient `CategoryTheory.Quotient PerfExt.frobRel` is the groupoid `Ext^i/Frob` of
(20.18)–(20.21). The literal geometry functor is constant on classes (20.12) and descends to
`geomQuot` (20.22).

* `geomQuot_map_bijective`: for objects of transcendence degree at least five the descended
  functor is bijective on Hom-sets (blueprint (20.23), Thm `functorial-reconstruction`). The
  restriction to the full subgroupoid `PerfExt.rankFive` is full and faithful.
* `geomLit_map_bijective_of_p_eq_one`: in characteristic zero the literal functor is already
  bijective on Hom-sets; its restriction to `PerfExt.rankFiveCharZero` is full and faithful.
* `geomLit_map_not_injective`: in positive characteristic and positive transcendence degree the
  literal functor is not faithful, because `F_A^1 ≠ 𝟙` has trivial image (the blueprint
  warning before §20.1).

**Status:** proved.
-/

namespace AclGeom

open CategoryTheory

noncomputable section

universe u v

namespace PerfExt

/-- Two arrows differ by an integral Frobenius power of the target (blueprint (20.17)). -/
def frobRel : HomRel PerfExt.{u, v} := fun _ B Φ Φ' ↦ ∃ n : ℤ, Φ' = Φ ≫ B.frobHom n

/-- The Frobenius relation is a congruence: an equivalence on every Hom-set, stable under
composition on both sides (blueprint (20.17) and (20.20)). -/
instance congruence_frobRel : Congruence frobRel.{u, v} where
  equivalence :=
    { refl := fun Φ ↦ ⟨0, by rw [frobHom_zero, Category.comp_id]⟩
      symm := fun ⟨n, h⟩ ↦ ⟨-n, by
        rw [h, Category.assoc, frobHom_add, add_neg_cancel, frobHom_zero, Category.comp_id]⟩
      trans := fun ⟨m, h⟩ ⟨n, h'⟩ ↦ ⟨m + n, by rw [h', h, Category.assoc, frobHom_add]⟩ }
  comp_left _ _ _ := fun ⟨n, h⟩ ↦ ⟨n, by rw [h, Category.assoc]⟩
  comp_right g := fun ⟨n, h⟩ ↦ ⟨n, by
    rw [h, Category.assoc, frobHom_naturality, Category.assoc]⟩

end PerfExt

open PerfExt

/-- **The descended geometry functor** (blueprint (20.22)) on the Frobenius-orbit groupoid
`Ext^i/Frob = CategoryTheory.Quotient frobRel` of (20.18)–(20.21). -/
def geomQuot : CategoryTheory.Quotient frobRel.{u, v} ⥤ Core PartOrd.{v} :=
  CategoryTheory.Quotient.lift frobRel geomLit fun _ B _ _ ⟨n, h⟩ ↦ by
    rw [h, Functor.map_comp, B.geomLit_map_frobHom, Category.comp_id]

theorem geomQuot_map_functor_map {A B : PerfExt.{u, v}} (Φ : A ⟶ B) :
    geomQuot.map ((CategoryTheory.Quotient.functor frobRel).map Φ) = geomLit.map Φ :=
  CategoryTheory.Quotient.lift_map_functor_map _ _ _ _

/-- **Functorial reconstruction** (blueprint (20.23), Thm `functorial-reconstruction`): for
objects of transcendence degree at least five, the descended geometry functor is bijective on
Hom-sets. -/
theorem geomQuot_map_bijective {A B : CategoryTheory.Quotient frobRel.{u, v}}
    (htr : (5 : Cardinal) ≤ Algebra.trdeg A.as.base A.as.ext) :
    Function.Bijective (geomQuot.map : (A ⟶ B) → (geomQuot.obj A ⟶ geomQuot.obj B)) := by
  constructor
  · intro q₁ q₂ h
    obtain ⟨Φ₁, rfl⟩ := (CategoryTheory.Quotient.functor frobRel).map_surjective q₁
    obtain ⟨Φ₂, rfl⟩ := (CategoryTheory.Quotient.functor frobRel).map_surjective q₂
    rw [geomQuot_map_functor_map, geomQuot_map_functor_map] at h
    exact CategoryTheory.Quotient.sound _ ((geomLit_map_eq_iff htr Φ₁ Φ₂).1 h)
  · intro f
    obtain ⟨Φ, hΦ⟩ := geomLit_map_surjective (B := B.as) htr f
    exact ⟨(CategoryTheory.Quotient.functor frobRel).map Φ,
      (geomQuot_map_functor_map Φ).trans hΦ⟩

namespace PerfExt

/-- The full subgroupoid of `Ext^i/Frob` on extensions of transcendence degree at least five. -/
def rankFive : ObjectProperty (CategoryTheory.Quotient frobRel.{u, v}) :=
  fun A ↦ (5 : Cardinal) ≤ Algebra.trdeg A.as.base A.as.ext

/-- The full subgroupoid of `Ext^i` on characteristic-zero extensions of transcendence degree
at least five. -/
def rankFiveCharZero : ObjectProperty PerfExt.{u, v} :=
  fun A ↦ (5 : Cardinal) ≤ Algebra.trdeg A.base A.ext ∧ A.perf.p = 1

end PerfExt

/-- The descended functor is full on extensions of transcendence degree at least five. -/
instance : (rankFive.ι ⋙ geomQuot).Full where
  map_surjective {X _} f := by
    obtain ⟨g, hg⟩ := (geomQuot_map_bijective X.property).2 f
    exact ⟨ObjectProperty.homMk g, hg⟩

/-- The descended functor is faithful on extensions of transcendence degree at least five. -/
instance : (rankFive.ι ⋙ geomQuot).Faithful where
  map_injective {X _} _ _ h := ObjectProperty.hom_ext _ ((geomQuot_map_bijective X.property).1 h)

/-- **Characteristic zero**: the literal functor is bijective on Hom-sets from an extension of
transcendence degree at least five to a characteristic-zero extension. -/
theorem geomLit_map_bijective_of_p_eq_one {A B : PerfExt.{u, v}}
    (htr : (5 : Cardinal) ≤ Algebra.trdeg A.base A.ext) (hp : B.perf.p = 1) :
    Function.Bijective (geomLit.map : (A ⟶ B) → (geomLit.obj A ⟶ geomLit.obj B)) := by
  refine ⟨fun Φ₁ Φ₂ h ↦ ?_, geomLit_map_surjective htr⟩
  obtain ⟨n, hn⟩ := (geomLit_map_eq_iff htr Φ₁ Φ₂).1 h
  rw [hn, B.frobHom_eq_id hp, Category.comp_id]

/-- The literal functor is full on characteristic-zero extensions of transcendence degree at
least five. -/
instance : (rankFiveCharZero.ι ⋙ geomLit).Full where
  map_surjective {X Y} f := by
    obtain ⟨g, hg⟩ := (geomLit_map_bijective_of_p_eq_one X.property.1 Y.property.2).2 f
    exact ⟨ObjectProperty.homMk g, hg⟩

/-- The literal functor is faithful on characteristic-zero extensions of transcendence degree at
least five. -/
instance : (rankFiveCharZero.ι ⋙ geomLit).Faithful where
  map_injective {X Y} _ _ h := ObjectProperty.hom_ext _
    ((geomLit_map_bijective_of_p_eq_one X.property.1 Y.property.2).1 h)

namespace PerfExt

/-- In positive characteristic and positive transcendence degree, Frobenius is a nontrivial
automorphism of the object. -/
theorem frobHom_one_ne_id (A : PerfExt.{u, v}) (hp : A.perf.p ≠ 1)
    (htr : 0 < Algebra.trdeg A.base A.ext) : A.frobHom 1 ≠ 𝟙 A := by
  intro h
  have hpos : 0 < Algebra.trdeg (A.perf.basePerf A.base) A.perf.carrier :=
    Cardinal.lift_lt.1 ((Cardinal.lift_lt.2 htr).trans_le
      (lift_trdeg_le_of_orderIso (A.perf.latticeIso A.base)))
  obtain ⟨z, hz⟩ := exists_notMem_racl_of_mk_lt_trdeg (k := A.perf.basePerf A.base)
    (∅ : Set A.perf.carrier) (by simpa using hpos)
  have h10 : (1 : ℤ) = 0 :=
    frobeniusZPow_injective (k := A.perf.basePerf A.base) A.perf.p hp hz
      (congrArg Hom.toRingEquiv h)
  exact one_ne_zero h10

end PerfExt

/-- **Positive characteristic**: the literal functor is not faithful on the automorphisms of an
extension of positive transcendence degree (blueprint warning before §20.1). -/
theorem geomLit_map_not_injective (A : PerfExt.{u, v}) (hp : A.perf.p ≠ 1)
    (htr : 0 < Algebra.trdeg A.base A.ext) :
    ¬ Function.Injective (geomLit.map : (A ⟶ A) → (geomLit.obj A ⟶ geomLit.obj A)) :=
  fun h ↦ A.frobHom_one_ne_id hp htr (h ((A.geomLit_map_frobHom 1).trans (geomLit.map_id A).symm))

end

end AclGeom
