/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AdditiveOrbitCover
import AclGeom.Correspondence.ActionOrbit
import AclGeom.Correspondence.AffineTranslationSubgroup
import AclGeom.Correspondence.SchemePointExt

/-!
# The actual finite surjective Ga orbit cover in a regular affine curve action

**Status:** the orbit-cover step of Lemma 8.4 is proved for a subgroup already presented
as Ga in a genuine regular action on an integral affine locally finite-type curve of
dimension one over an ACF base. The ambient algebraic group is arbitrary. Its actual
regular action, global point-kernel criterion and monic Ga inclusion internally supply a
moved base-field point. The actual orbit map is finite and surjective, has the chosen
origin, and satisfies the joint translation-action scheme diagram and literal addition
over every commutative coefficient algebra in the base universe. Every characteristic is
included. No orbit, point, nonconstancy, dominance or finite-cover certificate is a premise.

Normality, connectedness and an ambient group-dimension bound are not needed for this
auxiliary. Arbitrary one-dimensional normal-subgroup/isogeny classification, rational and
non-affine actions, regularization, completion/points, the full original classifier and
all true bypassed auxiliaries remain owed. All eight original #21 work items and the full
durable goal stay open. This theorem supplies an actual orbit cover, not an identification
of an arbitrary one-dimensional subgroup with Ga or a rational-action regularization.
-/

namespace AclGeom.AdditiveOrbit
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The actual Ga subgroup has an internally chosen finite surjective orbit cover of the
original affine curve, with its actual joint translation diagram. No orbit, base point,
dominance, nonconstancy or finite-cover certificate is supplied by the caller. -/
theorem exists_finite_orbit_cover
    (G : AlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] [ModObj G.toGroupScheme.X V]
    (hker : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
      ModObj.pointAct V q = 𝟙 V → q = 1)
    (hdimV : topologicalKrullDim V.left = 1)
    (i : (AdditiveGroupScheme.algebraicGroup k 1).Hom G) [Mono i.hom.hom] :
    ∃ p : 𝟙_ (Over (Spec (.of k))) ⟶ V,
      IsFinite (orbitMap i.hom.hom p).left ∧ Surjective (orbitMap i.hom.hom p).left ∧
      ((unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k (0 : k)) ≫
        orbitMap i.hom.hom p = p ∧
      μ[(AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X] ≫ orbitMap i.hom.hom p =
        lift (fst (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
          (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ≫ i.hom.hom)
          (snd (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
            (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ≫ orbitMap i.hom.hom p) ≫
              γ[G.toGroupScheme.X, V] ∧
      ∀ (C : Type u) [CommRing C] [Algebra k C] (b c : C),
        lift (AffineSchemeAction.linePoint k b ≫ i.hom.hom)
          (AffineSchemeAction.linePoint k c ≫ orbitMap i.hom.hom p) ≫ γ[G.toGroupScheme.X, V] =
            AffineSchemeAction.linePoint k (b + c) ≫ orbitMap i.hom.hom p := by
  classical
  let N := (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
  let Q (b : k) : 𝟙_ (Over (Spec (.of k))) ⟶ N :=
    (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k b
  have hQ₀ : Q 0 = 1 := by
    change (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k (0 : k) = 1
    rw [AdditiveTranslation.linePoint_zero, comp_one]
  have hQ₁ : Q 1 ≠ 1 := by
    intro h
    apply (one_ne_zero : (1 : k) ≠ 0)
    apply AffineSchemeAction.linePoint_injective k
    apply (cancel_epi (unitIsoSpecAsOver k).hom).mp
    exact h.trans hQ₀.symm
  let g := Q 1 ≫ i.hom.hom
  have hg : g ≠ 1 := by
    intro h
    apply hQ₁
    apply (cancel_mono i.hom.hom).mp
    rw [one_comp]
    exact h
  have hact : ModObj.pointAct V g ≠ 𝟙 V := fun h ↦ hg (hker g h)
  obtain ⟨p, hp⟩ : ∃ p : 𝟙_ (Over (Spec (.of k))) ⟶ V,
      p ≫ ModObj.pointAct V g ≠ p := by
    by_contra! h
    apply hact
    apply AdditiveRigidity.over_hom_ext_of_points
    intro p
    simpa only [Category.comp_id] using h p
  let o := orbitMap i.hom.hom p
  have h₀ : Q 0 ≫ o = p := by
    rw [point_comp_orbitMap, hQ₀, one_comp, ModObj.pointAct_one, Category.comp_id]
  have hsep : AffineSchemeAction.linePoint k (0 : k) ≫ o ≠
      AffineSchemeAction.linePoint k (1 : k) ≫ o := by
    intro h
    have hh : Q 0 ≫ o = Q 1 ≫ o := by
      simpa only [Q, Category.assoc] using
        congrArg (fun z ↦ (unitIsoSpecAsOver k).hom ≫ z) h
    rw [h₀, point_comp_orbitMap] at hh
    exact hp hh.symm
  obtain ⟨hfin, hsurj⟩ := finite_surjective_of_separates_zero_one V hdimV o hsep
  have hjoint := mul_comp_orbitMap i.hom.hom p
  refine ⟨p, hfin, hsurj, h₀, hjoint, ?_⟩
  intro C _ _ b c
  calc
    _ = lift (AffineSchemeAction.linePoint k b) (AffineSchemeAction.linePoint k c) ≫
        μ[N] ≫ o := by
      rw [hjoint]
      simp only [comp_lift_assoc, lift_fst_assoc, lift_snd_assoc]
    _ = _ := by
      rw [← Category.assoc, ← Hom.mul_def, AdditiveTranslation.linePoint_mul]
end
end AclGeom.AdditiveOrbit
