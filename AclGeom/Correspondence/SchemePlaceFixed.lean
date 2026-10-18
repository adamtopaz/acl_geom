/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Curves.PlaceProfiles
import AclGeom.Correspondence.ActionSemicontinuity
import AclGeom.Curves.PlaceTransport
import AclGeom.Correspondence.GroupPointTopology
import AclGeom.Correspondence.FiniteActionIrreducible
import AclGeom.Correspondence.SchemePlaceBoundary

/-!
# The connected-group fixed-boundary argument

The regular action supplies closed order conditions on the actual function field. Finite
section profiles make the orbit fibers locally closed; irreducibility and translations
then show every boundary place is fixed. A fixed boundary place is chosen internally.

Named source consumer: blueprint `lem:affine-action`, for a regular action on an affine
integral locally finite-type curve of dimension one over an algebraically closed field.
Rational regularization, projective presentation and joint regularity remain separate.

**Status:** proved for actual connected regular actions on affine curves over algebraically
closed fields, in every characteristic.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.SchemePlaceAction

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj ActionFunctionField

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

attribute [local instance] functionFieldAlgebra

/-- Private gluing step; the public actual-scheme consumer must derive order closedness. -/
private theorem fixed_of_isClosed_orders (G : ConnectedAlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] [ModObj G.toGroupScheme.X V]
    (hdim : topologicalKrullDim V.left = 1)
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X)
    {P : Place k V.left.functionField} (hP : P ∈ Place.boundary (globalSections V)) :
    letI := scheme_functionField_isFunctionFieldOneVar k V hdim
    letI := GroupPointTopology.topology G.toAlgebraicGroup
    (∀ (r : Γ(V.left, ⊤)), r ≠ 0 → ∀ m : ℤ,
      IsClosed {h : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X |
        m ≤ P.ord ((functionFieldAction G.toAlgebraicGroup V h).unop
          (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) r))}) →
    placeAction G.toAlgebraicGroup V g P = P := by
  classical
  have : IsFunctionFieldOneVar k V.left.functionField :=
    scheme_functionField_isFunctionFieldOneVar k V hdim
  let : TopologicalSpace (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :=
    GroupPointTopology.topology G.toAlgebraicGroup
  intro hclosed
  have : Nonempty (⊤ : V.left.Opens) := ⟨⟨genericPoint V.left, trivial⟩⟩
  have : IsFractionRing Γ(V.left, ⊤) V.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen V.left ⊤ (isAffineOpen_top V.left)
  have := GroupPointTopology.irreducibleSpace G
  let ρ := placeAction G.toAlgebraicGroup V
  let B := Place.boundary (globalSections V)
  have hB : B.Finite := boundary_finite V hdim
  have horbit : ∀ h : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X, ρ h P ∈ B :=
    fun h ↦ (placeAction_mem_boundary_iff G.toAlgebraicGroup V h P).2 hP
  obtain ⟨s, hs0, hsep⟩ := Place.exists_finset_ord_separating Γ(V.left, ⊤) hB
  have ho : ∀ (h : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) (a : Γ(V.left, ⊤)),
      (ρ h P).ord (algebraMap Γ(V.left, ⊤) V.left.functionField a) =
        P.ord ((functionFieldAction G.toAlgebraicGroup V h).unop
          (algebraMap Γ(V.left, ⊤) V.left.functionField a)) := by
    intro h a
    change (placeAction G.toAlgebraicGroup V h P).ord _ = _
    rw [placeAction_apply, Place.ord_comap]
  have hc : ∀ a ∈ s, ∀ m : ℤ,
      IsClosed {h : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X |
        m ≤ P.ord ((functionFieldAction G.toAlgebraicGroup V h).unop
          (algebraMap Γ(V.left, ⊤) V.left.functionField a))} := by
    intro a ha m
    have ha0 : a ≠ 0 := by
      intro he
      apply hs0 a ha
      rw [he, map_zero]
    exact hclosed a ha0 m
  have hfiber : ∀ Q ∈ B, IsLocallyClosed
      {h : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X | ρ h P = Q} := by
    intro Q hQ
    have he : {h : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X | ρ h P = Q} =
        (⋂ a ∈ s, {h | Q.ord (algebraMap Γ(V.left, ⊤) V.left.functionField a) ≤
          P.ord ((functionFieldAction G.toAlgebraicGroup V h).unop
            (algebraMap Γ(V.left, ⊤) V.left.functionField a))}) ∩
        (⋃ a ∈ s, {h | Q.ord (algebraMap Γ(V.left, ⊤) V.left.functionField a) + 1 ≤
          P.ord ((functionFieldAction G.toAlgebraicGroup V h).unop
            (algebraMap Γ(V.left, ⊤) V.left.functionField a))})ᶜ := by
      ext h
      constructor
      · intro hPQ
        constructor
        · refine Set.mem_iInter.2 fun a ↦ Set.mem_iInter.2 fun _ha ↦ ?_
          have e := ho h a
          rw [hPQ] at e
          exact e.le
        · intro hu
          obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hu
          obtain ⟨_ha, hgt⟩ := Set.mem_iUnion.1 ha
          rw [Set.mem_ofPred_eq] at hgt
          rw [← ho h a, hPQ] at hgt
          omega
      · rintro ⟨hlo, hhi⟩
        apply hsep (ρ h P) (horbit h) Q hQ
        intro a ha
        rw [ho h a]
        have h1 := Set.mem_iInter.1 (Set.mem_iInter.1 hlo a) ha
        rw [Set.mem_ofPred_eq] at h1
        have h2 : ¬ Q.ord (algebraMap Γ(V.left, ⊤) V.left.functionField a) + 1 ≤
            P.ord ((functionFieldAction G.toAlgebraicGroup V h).unop
              (algebraMap Γ(V.left, ⊤) V.left.functionField a)) :=
          fun hh ↦ hhi (Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨ha, hh⟩⟩)
        omega
    rw [he]
    exact (isClosed_iInter fun a ↦ isClosed_iInter fun ha ↦ hc a ha _).isLocallyClosed.inter
      (isClosed_biUnion_finset fun a ha ↦ hc a ha _).isOpen_compl.isLocallyClosed
  exact FiniteAction.fixed_of_finite_locallyClosed_fibers ρ
    (GroupPointTopology.leftMulHomeo G.toAlgebraicGroup)
    (GroupPointTopology.leftMulHomeo_apply G.toAlgebraicGroup) P hB horbit hfiber g


/-- A connected algebraic group acting regularly on an actual affine curve fixes every
boundary place. Named source consumer: the fixed-boundary step of `lem:affine-action`.
All curve prerequisites and order closedness are derived internally. -/
theorem placeAction_eq_of_mem_boundary (G : ConnectedAlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] [ModObj G.toGroupScheme.X V]
    (hdim : topologicalKrullDim V.left = 1)
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X)
    {P : Place k V.left.functionField} (hP : P ∈ Place.boundary (globalSections V)) :
    placeAction G.toAlgebraicGroup V g P = P := by
  have : IsFunctionFieldOneVar k V.left.functionField :=
    scheme_functionField_isFunctionFieldOneVar k V hdim
  let : TopologicalSpace (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :=
    GroupPointTopology.topology G.toAlgebraicGroup
  apply fixed_of_isClosed_orders G V hdim g hP
  intro r hr m
  have hh (h : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :
      (GroupScheme.pointsEquivClosedPoints (G := G.toGroupScheme.X)).symm
        (GroupPointTopology.pointsHomeo G.toAlgebraicGroup h) = h :=
    Equiv.symm_apply_apply _ h
  have hc := (ActionSemicontinuity.isClosed_setOf_le_ord
    G.toAlgebraicGroup V hdim P hr m).preimage
      (GroupPointTopology.pointsHomeo G.toAlgebraicGroup).continuous
  change IsClosed {h : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X |
    m ≤ P.ord ((functionFieldAction G.toAlgebraicGroup V
      ((GroupScheme.pointsEquivClosedPoints (G := G.toGroupScheme.X)).symm
        (GroupPointTopology.pointsHomeo G.toAlgebraicGroup h))).unop
          (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) r))} at hc
  have he : {h : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X |
      m ≤ P.ord ((functionFieldAction G.toAlgebraicGroup V
        ((GroupScheme.pointsEquivClosedPoints (G := G.toGroupScheme.X)).symm
          (GroupPointTopology.pointsHomeo G.toAlgebraicGroup h))).unop
            (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) r))} =
      {h | m ≤ P.ord ((functionFieldAction G.toAlgebraicGroup V h).unop
        (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) r))} := by
    ext h
    change (m ≤ P.ord ((functionFieldAction G.toAlgebraicGroup V
      ((GroupScheme.pointsEquivClosedPoints (G := G.toGroupScheme.X)).symm
        (GroupPointTopology.pointsHomeo G.toAlgebraicGroup h))).unop
          (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) r))) ↔ _
    rw [hh]
    rfl
  rw [he] at hc
  exact hc

/-- An actual affine curve with a regular connected-group action has a boundary place
fixed by every k-point. Named consumer: the missing fixed place in `lem:affine-action`. -/
theorem exists_fixed_boundary_place (G : ConnectedAlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] [ModObj G.toGroupScheme.X V]
    (hdim : topologicalKrullDim V.left = 1) :
    ∃ P : Place k V.left.functionField, P ∈ Place.boundary (globalSections V) ∧
      ∀ g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X,
        placeAction G.toAlgebraicGroup V g P = P := by
  obtain ⟨P, hP⟩ := boundary_nonempty V hdim
  exact ⟨P, hP, fun g ↦ placeAction_eq_of_mem_boundary G V hdim g hP⟩

end

end AclGeom.SchemePlaceAction
