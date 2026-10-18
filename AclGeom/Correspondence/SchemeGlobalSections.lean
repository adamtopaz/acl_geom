/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.SchemeGenericTranslate
import AclGeom.Correspondence.HopfSpecPoints

/-!
# Algebra maps on global sections and morphisms to affine spectra

**Status:** actual morphisms over the base field give algebra maps on global sections and
are recovered by their spectrum maps. Conversely, a base-algebra map into global sections
gives an actual morphism over the base. No affineness of the source is needed. Named
consumer: `AdditiveRigidity.exists_multiplicative_lift`, which constructs a regular character.
-/

namespace AclGeom.AdditiveRigidity
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {k : Type u} [Field k]
attribute [local instance] SchemeGenericTranslate.sectionsAlgebra

/-- Named consumer: the unit-valued conjugation coefficient gives an actual regular character. -/
theorem exists_spec_pullback (X : Over (Spec (.of k)))
    (R : Type u) [CommRing R] [Algebra k R]
    (f : X ⟶ (Spec (.of R)).asOver (Spec (.of k))) :
    ∃ φ : R →ₐ[k] Γ(X.left, ⊤),
      φ.toRingHom = ((Scheme.ΓSpecIso (.of R)).inv ≫ f.left.appTop).hom ∧
      X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) = f.left := by
  let f₀ : X.left ⟶ Spec (.of R) := f.left
  let b : Γ(Spec (.of R), ⊤) ⟶ Γ(X.left, ⊤) := f₀.appTop
  let β : R →+* Γ(X.left, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ b).hom
  have hOver : f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = X.hom := Over.w f
  have happ : (Spec.map (CommRingCat.ofHom (algebraMap k R))).appTop ≫ b = X.hom.appTop := by
    dsimp only [b]
    rw [← Scheme.Hom.comp_appTop, hOver]
  have hbase : CommRingCat.ofHom (algebraMap k R) ≫
      (Scheme.ΓSpecIso (.of R)).inv ≫ b =
      (Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, happ]
  let φ : R →ₐ[k] Γ(X.left, ⊤) :=
    { β with
      commutes' := fun a ↦ congrArg (fun h : CommRingCat.of k ⟶ Γ(X.left, ⊤) ↦ h a) hbase }
  refine ⟨φ, rfl, ?_⟩
  change X.left.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ b) = f₀
  calc
    _ = (X.left.toSpecΓ ≫ Spec.map b) ≫ Spec.map (Scheme.ΓSpecIso (.of R)).inv := by
      rw [Spec.map_comp, Category.assoc]
    _ = (f₀ ≫ (Spec (.of R)).toSpecΓ) ≫ Spec.map (Scheme.ΓSpecIso (.of R)).inv :=
      congrArg (fun h ↦ h ≫ Spec.map (Scheme.ΓSpecIso (.of R)).inv)
        (Scheme.toSpecΓ_naturality f₀).symm
    _ = f₀ := by
      change (f₀ ≫ (Spec (.of R)).isoSpec.hom) ≫
        Spec.map (Scheme.ΓSpecIso (.of R)).inv = f₀
      rw [Scheme.isoSpec_Spec_hom, Category.assoc, ← Spec.map_comp,
        Iso.inv_hom_id, Spec.map_id, Category.comp_id]
end
end AclGeom.AdditiveRigidity

namespace AclGeom.AdditiveRigidity
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
universe u
variable {k : Type u} [Field k]
attribute [local instance] SchemeGenericTranslate.sectionsAlgebra

/-- Named consumer: a unit-valued global coefficient gives an actual regular character. -/
def fromGlobal (X : Over (Spec (.of k))) (R : Type u) [CommRing R] [Algebra k R]
    (φ : R →ₐ[k] Γ(X.left, ⊤)) : X ⟶ (Spec (.of R)).asOver (Spec (.of k)) := by
  refine Over.homMk (X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)) ?_
  obtain ⟨β, _, hb⟩ := exists_spec_pullback X k (toUnit X ≫ (unitIsoSpecAsOver k).hom)
  have hβ : β.toRingHom = algebraMap k Γ(X.left, ⊤) := by
    apply RingHom.ext
    intro c
    change β c = algebraMap k Γ(X.left, ⊤) c
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using β.commutes c
  rw [hβ] at hb
  change X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(X.left, ⊤))) =
    X.hom ≫ 𝟙 _ at hb
  rw [Category.comp_id] at hb
  have hcomm : CommRingCat.ofHom (algebraMap k R) ≫ CommRingCat.ofHom φ.toRingHom =
      CommRingCat.ofHom (algebraMap k Γ(X.left, ⊤)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact φ.commutes c
  change (X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k R)) = X.hom
  rw [Category.assoc, ← Spec.map_comp, hcomm, hb]
end
end AclGeom.AdditiveRigidity
