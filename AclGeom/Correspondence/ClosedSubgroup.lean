/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveCosetGeneric
import AclGeom.Correspondence.IntegralProduct
import AclGeom.Correspondence.GroupSubobject
import Mathlib.Topology.KrullDimension

/-!
# The reduced algebraic subgroup defined by a closed set of points

The named consumer is blueprint `lem:curve-coset`. A closed irreducible subset of an algebraic
group over an algebraically closed field whose rational points form a subgroup has a genuine
connected algebraic subgroup structure. Multiplication and inversion restrict as actual scheme
morphisms. Reducedness and Jacobson density prove the restrictions, and the monic inclusion
proves the group-object laws. The generic-product hypotheses are handled by the source consumer.

**Status:** the actual connected closed subgroup is constructed; the general source consumer is
`curveCoset_of_genericProduct`.
-/

namespace AclGeom

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open GroupScheme

universe u

/-- A closed irreducible subset of an algebraic group whose `k`-points form a subgroup has an
actual connected closed algebraic subgroup structure, with the same topological dimension.
Named consumer: the general curve-coset lemma. -/
theorem exists_connectedClosedSubgroup_of_points {k : Type u} [Field k] [IsAlgClosed k]
    (G : AlgebraicGroup k) (Z : Closeds G.carrier) (hZi : IsIrreducible (Z : Set G.carrier))
    (h1 : (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X).left
      (IsLocalRing.closedPoint k) ∈ Z)
    (hdiv : ∀ a b : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
      a.left (IsLocalRing.closedPoint k) ∈ Z → b.left (IsLocalRing.closedPoint k) ∈ Z →
        (a * b⁻¹).left (IsLocalRing.closedPoint k) ∈ Z) :
    ∃ (H : ConnectedAlgebraicGroup k) (inclusion : H.toAlgebraicGroup.Hom G),
      IsClosedImmersion inclusion.schemeHom ∧ Set.range inclusion.schemeHom = Z ∧
      topologicalKrullDim H.toAlgebraicGroup.carrier = topologicalKrullDim Z := by
  classical
  let G₀ := G.toGroupScheme.X
  let H₀ := reducedOver G₀ Z
  let i : H₀ ⟶ G₀ := reducedOverι G₀ Z
  have : IsIntegral H₀.left := isIntegral_subscheme_vanishingIdeal Z hZi
  have : IsClosedImmersion i.left := by
    change IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
    infer_instance
  have : Mono i.left := inferInstance
  have : Mono i := Over.mono_of_mono_left i
  have : LocallyOfFiniteType H₀.hom := by
    change LocallyOfFiniteType (i.left ≫ G₀.hom)
    infer_instance
  have : QuasiCompact H₀.hom := by
    change QuasiCompact (i.left ≫ G₀.hom)
    infer_instance
  have hirange : Set.range i.left = (Z : Set G.carrier) := by
    change Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = Z
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hi (x : H₀.left) : i.left x ∈ Z := by
    change i.left x ∈ (Z : Set G.carrier)
    rw [← hirange]
    exact Set.mem_range_self x
  let S : Subgroup (𝟙_ (Over (Spec (.of k))) ⟶ G₀) :=
    Subgroup.ofDiv {p | p.left (IsLocalRing.closedPoint k) ∈ Z} ⟨1, h1⟩
      (fun a ha b hb ↦ hdiv a b ha hb)
  -- Closed points detect whether the range of a morphism is in `Z`.
  have range_of_points : ∀ {T : Over (Spec (.of k))} [LocallyOfFiniteType T.hom]
      (v : T ⟶ G₀),
      (∀ p : 𝟙_ (Over (Spec (.of k))) ⟶ T,
        (p ≫ v).left (IsLocalRing.closedPoint k) ∈ Z) → Set.range v.left ⊆ Z := by
    intro T _ v hv
    have : JacobsonSpace T.left := LocallyOfFiniteType.jacobsonSpace T.hom
    have hclosed := Z.isClosed.preimage v.left.continuous
    have hsub : closure (closedPoints T.left) ⊆ v.left ⁻¹' (Z : Set G.carrier) := by
      refine closure_minimal ?_ hclosed
      intro x hxc
      obtain ⟨p, hp⟩ := (pointsEquivClosedPoints (G := T)).surjective
        (⟨x, hxc⟩ : closedPoints T.left)
      have he : p.left (IsLocalRing.closedPoint k) = x := congrArg Subtype.val hp
      have hz := hv p
      change v.left (p.left (IsLocalRing.closedPoint k)) ∈ Z at hz
      rwa [he] at hz
    have hden : closure (closedPoints T.left) = Set.univ := by
      simpa only [Set.univ_inter, closure_univ] using
        JacobsonSpace.closure_inter_closedPoints_eq_closure
          (isClosed_univ : IsClosed (Set.univ : Set T.left)).isLocallyClosed
    rintro _ ⟨x, rfl⟩
    exact hsub (hden.symm ▸ Set.mem_univ x)
  have lift_of_points : ∀ {T : Over (Spec (.of k))} [IsReduced T.left]
      [LocallyOfFiniteType T.hom] (v : T ⟶ G₀),
      (∀ p : 𝟙_ (Over (Spec (.of k))) ⟶ T,
        (p ≫ v).left (IsLocalRing.closedPoint k) ∈ Z) → ∃ w : T ⟶ H₀, w ≫ i = v := by
    intro T _ _ v hv
    let w₀ := liftToReducedSubscheme Z v.left (range_of_points v hv)
    let w : T ⟶ H₀ := Over.homMk w₀ (by
      change w₀ ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ G₀.hom = T.hom
      rw [← Category.assoc, liftToReducedSubscheme_subschemeι]
      exact Over.w v)
    exact ⟨w, Over.OverMorphism.ext (liftToReducedSubscheme_subschemeι Z v.left
      (range_of_points v hv))⟩
  -- Restricted unit.
  let e : 𝟙_ (Over (Spec (.of k))) ⟶ H₀ := liftPoint Z 1 h1
  have he : e ≫ i = η[G₀] := by
    change liftPoint Z 1 h1 ≫ reducedOverι G₀ Z = η[G₀]
    rw [liftPoint_comp_reducedOverι, Hom.one_def, toUnit_unit, Category.id_comp]
  -- Restricted multiplication on the actual integral scheme product.
  have : IsIntegral (H₀ ⊗ H₀).left :=
    isIntegral_pullback_of_isAlgClosed H₀.hom H₀.hom
  have : LocallyOfFiniteType (H₀ ⊗ H₀).hom := by
    change LocallyOfFiniteType (pullback.fst H₀.hom H₀.hom ≫ H₀.hom)
    infer_instance
  obtain ⟨m, hm⟩ := lift_of_points ((i ⊗ₘ i) ≫ μ[G₀]) (by
    intro p
    have ha : p ≫ fst H₀ H₀ ≫ i ∈ S := by
      change i.left ((p ≫ fst H₀ H₀).left (IsLocalRing.closedPoint k)) ∈ Z
      exact hi _
    have hb : p ≫ snd H₀ H₀ ≫ i ∈ S := by
      change i.left ((p ≫ snd H₀ H₀).left (IsLocalRing.closedPoint k)) ∈ Z
      exact hi _
    have hp : p ≫ (i ⊗ₘ i) ≫ μ[G₀] =
        (p ≫ fst H₀ H₀ ≫ i) * (p ≫ snd H₀ H₀ ≫ i) := by
      rw [← lift_fst_comp_snd_comp i i, ← Hom.mul_def, MonObj.comp_mul]
    rw [hp]
    exact S.mul_mem ha hb)
  -- Restricted inverse.
  obtain ⟨j, hj⟩ := lift_of_points (i ≫ ι[G₀]) (by
    intro p
    have hp : p ≫ i ∈ S := by
      change i.left (p.left (IsLocalRing.closedPoint k)) ∈ Z
      exact hi _
    rw [← Category.assoc, ← Hom.inv_def]
    exact S.inv_mem hp)
  -- All group laws follow through the actual monic inclusion.
  let : GrpObj H₀ := groupObjectOfMono i e m j he hm hj
  let Hs : GroupScheme k := Grp.mk H₀
  let Ha : AlgebraicGroup k := AlgebraicGroup.ofGroupScheme Hs
  let Hc : ConnectedAlgebraicGroup k :=
    { Ha with geometricallyIntegral := geometricallyIntegral_of_isAlgClosed H₀.hom }
  let inclusion : Hc.toAlgebraicGroup.Hom G := Grp.homMk'' i he hm
  let eh : H₀.left ≃ₜ Z :=
    i.left.isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hirange)
  refine ⟨Hc, inclusion, ?_, ?_, ?_⟩
  · change IsClosedImmersion i.left
    infer_instance
  · exact hirange
  · exact IsHomeomorph.topologicalKrullDim_eq _ eh.isHomeomorph

end

end AclGeom
