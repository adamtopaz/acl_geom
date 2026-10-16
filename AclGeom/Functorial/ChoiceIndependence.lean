/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import AclGeom.Functorial.Literal
import Mathlib.CategoryTheory.InducedCategory

/-!
# Independence of the chosen perfections

Blueprint §20.1. Two chosen perfections of the same extension `K/k` are related by a unique
isomorphism `u_K` restricting to the identity of `K` (`PerfExt.comparison`,
`PerfExt.eq_comparison`). It carries the perfected base onto the perfected base and induces the
identity of `𝒢(K/k)` (`PerfExt.geomLit_map_comparison`).

A choice of perfections `c` for all relatively algebraically closed extensions (`RACExt`) gives
the choice-dependent groupoid `ChoiceGroupoid c`. For two choices, transport
`Φ ↦ u_A⁻¹ ≫ Φ ≫ u_B` is an equivalence between them (`choiceTransport`, `choiceEquivalence`),
and the geometry functors agree under it (`choiceTransport_comp_geomLit`).

Arrows preserve transcendence degree (`PerfExt.trdeg_eq_of_hom`), so the condition
`trdeg(K/k) ≥ 5` is invariant under arrows.

**Status:** proved.
-/

namespace AclGeom

open CategoryTheory

noncomputable section

universe u v

/-- A relatively algebraically closed extension `K/k`, without a chosen perfection. -/
structure RACExt : Type (max u v + 1) where
  /-- The base field `k`. -/
  base : Type u
  /-- The extension field `K`. -/
  ext : Type v
  /-- The field structure of the base. -/
  [fieldBase : Field base]
  /-- The field structure of the extension. -/
  [fieldExt : Field ext]
  /-- The extension structure. -/
  [algebra : Algebra base ext]
  /-- The base is relatively algebraically closed in the extension. -/
  isRAC : IsRAC (⊥ : IntermediateField base ext)

attribute [instance] RACExt.fieldBase RACExt.fieldExt RACExt.algebra

namespace PerfExt

variable (A : PerfExt.{u, v})

/-- The same extension with another chosen perfection. -/
abbrev withPerf (π : Perfection A.ext) : PerfExt.{u, v} where
  base := A.base
  ext := A.ext
  isRAC := A.isRAC
  perf := π

/-- **The comparison isomorphism** `u_K` of blueprint §20.1: the isomorphism between two chosen
perfections of the same extension restricting to the identity of `K`. -/
def comparison (π : Perfection A.ext) : A ⟶ A.withPerf π :=
  ⟨A.perf.liftEquiv π (RingEquiv.refl _),
    A.perf.compatible_liftEquiv π (CrossBase.compatible_refl (k := A.base))⟩

theorem comparison_incl (π : Perfection A.ext) (x : A.ext) :
    (A.comparison π).toRingEquiv (A.perf.incl x) = π.incl x :=
  A.perf.liftEquiv_incl π _ x

/-- **Uniqueness of the comparison**: an arrow restricting to the identity of `K` is the
comparison isomorphism. -/
theorem eq_comparison {π : Perfection A.ext} (Φ : A ⟶ A.withPerf π)
    (hΦ : ∀ x, Φ.toRingEquiv (A.perf.incl x) = π.incl x) : Φ = A.comparison π :=
  hom_ext (A.perf.liftEquiv_ext π (σ := RingEquiv.refl _) hΦ)

/-- The comparison of a perfection with itself is the identity. -/
theorem comparison_self : A.comparison A.perf = 𝟙 A :=
  hom_ext A.perf.liftEquiv_refl

/-- Comparisons compose (the composition law for the transport of blueprint §20.1). -/
theorem comparison_comp_comparison (π π' : Perfection A.ext) :
    A.comparison π ≫ (A.withPerf π).comparison π' = A.comparison π' :=
  A.eq_comparison (π := π') (A.comparison π ≫ (A.withPerf π).comparison π') fun x ↦ by
    rw [comp_toRingEquiv, RingEquiv.trans_apply, comparison_incl]
    exact (A.withPerf π).comparison_incl π' x

/-- Comparing to another perfection and back is the identity. -/
@[reassoc (attr := simp)]
theorem comparison_comp_comparison_self (π : Perfection A.ext) :
    A.comparison π ≫ (A.withPerf π).comparison A.perf = 𝟙 A := by
  rw [comparison_comp_comparison, comparison_self]

/-- **The comparison induces the identity of `𝒢(K/k)`** (blueprint §20.1). -/
theorem geomLit_map_comparison (π : Perfection A.ext) :
    geomLit.map (A.comparison π) = 𝟙 (geomLit.obj A) := by
  have h := A.perf.induces_liftEquiv π (CrossBase.compatible_refl (k := A.base))
  rw [CrossBase.closedIFMap_refl] at h
  have he := ((Perfection.induces_iff_eq_inducedIso (A.comparison π).compatible).1 h).symm
  exact Core.hom_ext <| PartOrd.ext fun M ↦ congrArg (· M) he

/-- **Arrows preserve transcendence degree** (blueprint §20.1): the image of an arrow is an
order isomorphism of the closed lattices. -/
theorem trdeg_eq_of_hom {A B : PerfExt.{u, v}} (Φ : A ⟶ B) :
    Algebra.trdeg A.base A.ext = Algebra.trdeg B.base B.ext :=
  trdeg_eq_of_orderIso (orderIsoOfPartOrdIso (geomLit.map Φ).iso)

end PerfExt

/-- The object of `Ext^i` given by a choice of perfections. -/
abbrev ofChoice (c : ∀ E : RACExt.{u, v}, Perfection E.ext) (E : RACExt.{u, v}) :
    PerfExt.{u, v} where
  base := E.base
  ext := E.ext
  isRAC := E.isRAC
  perf := c E

/-- **The choice-dependent groupoid** of blueprint §20.1: relatively algebraically closed
extensions, with arrows the compatible isomorphisms of their chosen perfections `c`. -/
abbrev ChoiceGroupoid (c : ∀ E : RACExt.{u, v}, Perfection E.ext) : Type (max u v + 1) :=
  InducedCategory PerfExt.{u, v} (ofChoice c)

variable (c₁ c₂ : ∀ E : RACExt.{u, v}, Perfection E.ext)

/-- Comparing a choice of perfections with another choice and back is the identity. -/
@[reassoc (attr := simp)]
theorem ofChoice_comparison_comp (c c' : ∀ E : RACExt.{u, v}, Perfection E.ext)
    (E : RACExt.{u, v}) :
    (ofChoice c E).comparison (c' E) ≫ (ofChoice c' E).comparison (c E) = 𝟙 (ofChoice c E) :=
  (ofChoice c E).comparison_comp_comparison_self (c' E)

/-- **Transport between two choices of perfections** (blueprint §20.1): the identity on objects,
and `Φ ↦ u_A⁻¹ ≫ Φ ≫ u_B` on arrows, with `u_A⁻¹` the comparison back to the first choice. -/
def choiceTransport : ChoiceGroupoid c₁ ⥤ ChoiceGroupoid c₂ where
  obj E := E
  map {E E'} Φ := InducedCategory.homMk ((ofChoice c₂ E).comparison (c₁ E) ≫ Φ.hom ≫
    (ofChoice c₁ E').comparison (c₂ E'))
  map_id E := InducedCategory.hom_ext (by simp)
  map_comp f g := InducedCategory.hom_ext (by simp)

instance : (choiceTransport c₁ c₂).Full where
  map_surjective {E E'} Ψ := ⟨InducedCategory.homMk ((ofChoice c₁ E).comparison (c₂ E) ≫ Ψ.hom ≫
    (ofChoice c₂ E').comparison (c₁ E')), InducedCategory.hom_ext (by simp [choiceTransport])⟩

instance : (choiceTransport c₁ c₂).Faithful where
  map_injective {E E'} Φ Φ' h := InducedCategory.hom_ext (by
    have h' := congrArg (fun g : (choiceTransport c₁ c₂).obj E ⟶ (choiceTransport c₁ c₂).obj E' ↦
      (ofChoice c₁ E).comparison (c₂ E) ≫ g.hom ≫ (ofChoice c₂ E').comparison (c₁ E')) h
    simpa [choiceTransport] using h')

instance : (choiceTransport c₁ c₂).EssSurj where
  mem_essImage E := ⟨E, ⟨Iso.refl _⟩⟩

instance : (choiceTransport c₁ c₂).IsEquivalence where

/-- **The two choice-dependent groupoids are equivalent** (blueprint §20.1). -/
def choiceEquivalence : ChoiceGroupoid c₁ ≌ ChoiceGroupoid c₂ :=
  (choiceTransport c₁ c₂).asEquivalence

/-- **The geometry functors for the two choices agree** under the transport (blueprint §20.1). -/
theorem choiceTransport_comp_geomLit :
    choiceTransport c₁ c₂ ⋙ inducedFunctor (ofChoice c₂) ⋙ geomLit =
      inducedFunctor (ofChoice c₁) ⋙ geomLit :=
  CategoryTheory.Functor.ext (fun _ ↦ rfl) fun {E E'} Φ ↦ by
    simp [choiceTransport, PerfExt.geomLit_map_comparison]
    rfl

end

end AclGeom
