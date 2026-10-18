/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.MultiplicativeAutomorphisms
import AclGeom.Correspondence.NormalConjugation
import AclGeom.Correspondence.GroupSchemePoints
import AclGeom.Correspondence.IntegralProduct
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# A normal multiplicative subgroup of a connected algebraic group is central

**Status:** proved over an algebraically closed field, in every characteristic (#21).
The actual normal multiplicative-subgroup morphism supplies a regular conjugation lift
internally. Every point slice is an actual group-scheme automorphism, hence identity or
inversion. A multiplicative point distinct from its inverse separates the alternatives,
including in characteristic two. Irreducibility and closed orbit fibers force the identity
alternative. Product integrality and point extensionality then prove the actual joint
scheme conjugation identity. No exponent, constancy or conjugation-action certificate is
a caller premise.

This is the torus alternative in the original proof of blueprint Lemma 8.4. It does not
identify an arbitrary one-dimensional normal subgroup with the multiplicative group, prove
the required isogeny classification, or regularize rational actions. The full classifier,
remaining group/chunk/six-point results, algebraization/descent and every true bypassed
auxiliary remain owed. All eight original #21 items and the full durable goal stay open.
-/

namespace AclGeom.MultiplicativeRigidity
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.GrpObj CategoryTheory.MonObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The torus alternative in the proof of blueprint Lemma 8.4: an actual normal
 multiplicative subgroup of a connected algebraic group is central. The conjugation lift,
 exponent alternatives, a separating point and joint scheme identity are all proved
 internally, in every characteristic. This does not classify arbitrary one-dimensional
 normal subgroups or regularize rational curve actions. -/
theorem normal_multiplicativeGroup_conj
    (G : ConnectedAlgebraicGroup k)
    (i : (multiplicativeGroup k).Hom G.toAlgebraicGroup)
    [IsMonHom.Normal i.hom.hom] :
    G.toGroupScheme.X ◁ i.hom.hom ≫ conj G.toGroupScheme.X =
      snd G.toGroupScheme.X (multiplicativeGroup k).toGroupScheme.X ≫ i.hom.hom := by
  classical
  let GX := G.toGroupScheme.X
  let N := (multiplicativeGroup k).toGroupScheme.X
  let i₀ : N ⟶ GX := i.hom.hom
  obtain ⟨ψ, hψ⟩ := IsMonHom.Normal.exists_comp_eq_conj i₀
  let c (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : N ⟶ N :=
    lift (toUnit N ≫ q) (𝟙 N) ≫ ψ
  have hauto (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : c q = 𝟙 N ∨ c q = ι[N] := by
    obtain ⟨e, he⟩ := NormalConjugation.exists_groupIso_conjugation_lift i₀ ψ hψ q
    simpa only [he] using groupIso_eq_id_or_inv k e
  have hc₁ : c 1 = 𝟙 N := by
    apply (cancel_mono i₀).mp
    simp [c, hψ, lift_whiskerLeft_assoc]
  have hcomp (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX)
      (p : 𝟙_ (Over (Spec (.of k))) ⟶ N) : p ≫ c q = lift q p ≫ ψ := by
    simp only [c, comp_lift_assoc, Category.comp_id]
    simp only [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  obtain ⟨u, hu⟩ : ∃ u : kˣ, u ≠ u⁻¹ := by
    obtain ⟨a, ha⟩ := Finset.exists_notMem ({0, 1, -1} : Finset k)
    have ha₀ : a ≠ 0 := fun h ↦ ha (by simp [h])
    have ha₁ : a ≠ 1 := fun h ↦ ha (by simp [h])
    have ha_neg_one : a ≠ -1 := fun h ↦ ha (by simp [h])
    let u := Units.mk0 a ha₀
    refine ⟨u, ?_⟩
    intro h
    have hm := congrArg (fun v : kˣ ↦ v * u) h
    rw [_root_.inv_mul_cancel] at hm
    have hm' := congrArg Units.val hm
    change a * a = 1 at hm'
    rcases mul_self_eq_one_iff.mp hm' with h | h
    · exact ha₁ h
    · exact ha_neg_one h
  let p : 𝟙_ (Over (Spec (.of k))) ⟶ N := (multiplicativeGroup.pointsMulEquiv k).symm u
  have hp : p ≠ p⁻¹ := by
    intro h
    apply hu
    simpa only [p, map_inv, MulEquiv.apply_symm_apply] using
      congrArg (multiplicativeGroup.pointsMulEquiv k) h
  have hpval : p.left (IsLocalRing.closedPoint k) ≠ (p⁻¹).left (IsLocalRing.closedPoint k) := by
    intro h
    exact hp (GroupScheme.pointsEquivClosedPoints.injective (Subtype.ext h))
  let O : GX ⟶ N := lift (𝟙 GX) (toUnit GX ≫ p) ≫ ψ
  have hOcomp (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : q ≫ O = p ≫ c q := by
    rw [hcomp]
    simp only [O, comp_lift_assoc, Category.comp_id]
    simp only [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  have hO₁ : (1 : 𝟙_ (Over (Spec (.of k))) ⟶ GX) ≫ O = p := by
    rw [hOcomp, hc₁, Category.comp_id]
  have hvals (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : q ≫ O = p ∨ q ≫ O = p⁻¹ := by
    rw [hOcomp]
    rcases hauto q with h | h
    · exact Or.inl (by rw [h, Category.comp_id])
    · exact Or.inr (by rw [h]; rfl)
  have hpclosed : IsClosed ({p.left (IsLocalRing.closedPoint k)} : Set N.left) :=
    (GroupScheme.pointsEquivClosedPoints p).property
  have hpinvclosed : IsClosed ({(p⁻¹).left (IsLocalRing.closedPoint k)} : Set N.left) :=
    (GroupScheme.pointsEquivClosedPoints p⁻¹).property
  let Z₀ := O.left ⁻¹' {p.left (IsLocalRing.closedPoint k)}
  let Z₁ := O.left ⁻¹' {(p⁻¹).left (IsLocalRing.closedPoint k)}
  have hZ₀ : IsClosed Z₀ := hpclosed.preimage O.left.continuous
  have hZ₁ : IsClosed Z₁ := hpinvclosed.preimage O.left.continuous
  have hclosed : IsClosed (Z₀ ∪ Z₁) := hZ₀.union hZ₁
  have hsub : closedPoints GX.left ⊆ Z₀ ∪ Z₁ := by
    intro y hy
    obtain ⟨q, hq⟩ := GroupScheme.pointsEquivClosedPoints.surjective
      (⟨y, hy⟩ : closedPoints GX.left)
    have hqy : q.left (IsLocalRing.closedPoint k) = y := congrArg Subtype.val hq
    rcases hvals q with h | h
    · left
      change O.left y = p.left (IsLocalRing.closedPoint k)
      rw [← hqy]
      exact congrArg (fun f ↦ f.left (IsLocalRing.closedPoint k)) h
    · right
      change O.left y = (p⁻¹).left (IsLocalRing.closedPoint k)
      rw [← hqy]
      exact congrArg (fun f ↦ f.left (IsLocalRing.closedPoint k)) h
  have : JacobsonSpace GX.left := LocallyOfFiniteType.jacobsonSpace GX.hom
  have hden : closure (closedPoints GX.left) = Set.univ := by
    simpa only [Set.univ_inter, closure_univ] using
      JacobsonSpace.closure_inter_closedPoints_eq_closure
        (isClosed_univ : IsClosed (Set.univ : Set GX.left)).isLocallyClosed
  have hcover : Set.univ ⊆ Z₀ ∪ Z₁ := by
    rw [← hden]
    exact closure_minimal hsub hclosed
  have hconst (y : GX.left) : O.left y = p.left (IsLocalRing.closedPoint k) := by
    rcases isPreirreducible_iff_isClosed_union_isClosed.mp
      (IrreducibleSpace.isIrreducible_univ GX.left).isPreirreducible Z₀ Z₁ hZ₀ hZ₁ hcover with h | h
    · exact h (Set.mem_univ y)
    · have he : O.left ((1 : 𝟙_ (Over (Spec (.of k))) ⟶ GX).left
          (IsLocalRing.closedPoint k)) = (p⁻¹).left (IsLocalRing.closedPoint k) :=
        h (Set.mem_univ _)
      have hu := congrArg (fun f ↦ f.left (IsLocalRing.closedPoint k)) hO₁
      exact False.elim (hpval (hu.symm.trans he))
  have hfix (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : p ≫ c q = p := by
    rw [← hOcomp]
    apply GroupScheme.pointsEquivClosedPoints.injective
    apply Subtype.ext
    exact hconst (q.left (IsLocalRing.closedPoint k))
  have hcall (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : c q = 𝟙 N := by
    rcases hauto q with h | h
    · exact h
    · have hf := hfix q
      rw [h] at hf
      change p⁻¹ = p at hf
      exact False.elim (hp hf.symm)
  have : IsIntegral N.left :=
    inferInstanceAs (IsIntegral (Spec (.of (AddMonoidAlgebra k ℤ))))
  have : IsIntegral (GX ⊗ N).left := isIntegral_pullback_of_isAlgClosed GX.hom N.hom
  have : LocallyOfFiniteType (GX ⊗ N).hom := by
    change LocallyOfFiniteType (Limits.pullback.fst GX.hom N.hom ≫ GX.hom)
    infer_instance
  have hψeq : ψ = snd GX N := by
    apply Over.OverMorphism.ext
    have : LocallyOfFiniteType (ψ.left ≫ N.hom) := by rw [Over.w ψ]; infer_instance
    refine AlgebraicGeometry.ext_of_apply_eq N.hom Set.univ isClosed_univ.isLocallyClosed
      dense_univ ?_ ((Over.w ψ).trans (Over.w (snd GX N)).symm)
    intro y _ hy
    let q : 𝟙_ (Over (Spec (.of k))) ⟶ GX ⊗ N :=
      Over.homMk (pointOfClosedPoint (GX ⊗ N).hom y hy)
        (pointOfClosedPoint_comp (GX ⊗ N).hom y hy)
    have hq : lift (q ≫ fst GX N) (q ≫ snd GX N) = q := by simp
    have hpoint : q ≫ ψ = q ≫ snd GX N := by
      rw [← hq, ← hcomp, hcall, Category.comp_id, lift_snd]
    have he := congrArg (fun f ↦ f.left (IsLocalRing.closedPoint k)) hpoint
    have hqy : q.left (IsLocalRing.closedPoint k) = y :=
      pointOfClosedPoint_apply (GX ⊗ N).hom y hy _
    change ψ.left (q.left (IsLocalRing.closedPoint k)) =
      (snd GX N).left (q.left (IsLocalRing.closedPoint k)) at he
    rwa [hqy] at he
  change GX ◁ i₀ ≫ conj GX = snd GX N ≫ i₀
  rw [← hψ, hψeq]
end
end AclGeom.MultiplicativeRigidity
