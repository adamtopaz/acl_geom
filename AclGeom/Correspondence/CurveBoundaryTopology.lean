/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurvePointTopology
import Mathlib.Topology.JacobsonSpace

/-!
# The literal finite boundary of an actual curve

**Status:** proved for actual Noetherian integral dimension-one schemes. The complement of
every actual nonempty open is finite and consists of closed points. A continuous map from an
irreducible space into finitely many closed points is constant. Named consumer: the actual
joint fixed-boundary theorem.

The regular action on the ambient curve is an actual input. Completion construction, joint
regularity of extended rational families, rational-action regularization and the full original
classifier remain owed. Original group/chunk/six-point statements, algebraization/descent and
every true bypassed auxiliary remain obligations. All eight original #21 work items and the
full durable goal remain active and incomplete.

For actual smooth integral dimension-one curves over an ACF base, SmoothCurveStalks now
derives integral closedness of every actual stalk and DVRs at closed points internally; its
actual connected-group and individual proper-smooth extension consumers have no normality
premise.
-/

namespace AclGeom.CurveBoundary
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
attribute [local instance] specializationOrder

/-- The literal boundary of a nonempty open in a Noetherian integral curve is finite and
consists of actual closed points. Named consumer: the actual joint fixed-boundary theorem. -/
theorem finite_closed_complement
    (X : Scheme.{u}) [IsIntegral X] [TopologicalSpace.NoetherianSpace X]
    (hdim : topologicalKrullDim X = 1) (U : X.Opens) [Nonempty U] :
    ((U : Set X)ᶜ).Finite ∧ ∀ x ∈ ((U : Set X)ᶜ), IsClosed ({x} : Set X) := by
  have hgen : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))
  have hclosed (x : X) (hx : x ∈ ((U : Set X)ᶜ)) : IsClosed ({x} : Set X) :=
    (CurvePointsPlaces.isClosed_singleton_iff_ne_genericPoint X hdim x).mpr
      (fun e ↦ hx (e.symm ▸ hgen))
  have hB : IsClosed ((U : Set X)ᶜ) := U.isOpen.isClosed_compl
  have : QuasiSober ↥((U : Set X)ᶜ) := hB.isClosedEmbedding_subtypeVal.quasiSober
  have hproper : closure ((U : Set X)ᶜ) ≠ Set.univ := by
    rw [hB.closure_eq]
    intro h
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    have hx : x.val ∈ ((U : Set X)ᶜ) := h ▸ Set.mem_univ x.val
    exact hx x.property
  have hf := TopologicalSpace.NoetherianSpace.finite_coheight_one_of_closure_ne_univ hproper
  have he : Order.krullDim X = topologicalKrullDim X :=
    (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).symm
  refine ⟨hf.subset ?_, hclosed⟩
  intro x hx
  refine ⟨hx, le_antisymm ?_ ?_⟩
  · have h := (Order.coheight_le_krullDim x).trans (he.trans hdim).le
    exact_mod_cast h
  · apply Order.one_le_iff_ne_zero.mpr
    intro hz
    have : x = genericPoint X := isMax_iff_eq_top.mp (Order.coheight_eq_zero.mp hz)
    exact hx (this.symm ▸ hgen)

/-- A continuous map from an irreducible space into finitely many closed points is constant.
Named consumer: the actual boundary orbit morphism. -/
theorem constant_of_finite_closed_range
    {A B : Type*} [TopologicalSpace A] [PreirreducibleSpace A] [TopologicalSpace B]
    (f : A → B) (hf : Continuous f) (S : Set B) (hS : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set B)) (hmem : ∀ a, f a ∈ S) :
    ∀ a b, f a = f b := by
  have hr : Set.range f ⊆ S := by
    rintro _ ⟨a, rfl⟩
    exact hmem a
  have hd : IsDiscrete (Set.range f) :=
    (hS.isDiscrete_of_subset_closedPoints (fun x hx ↦ hclosed x hx)).mono hr
  have hi : IsPreirreducible (Set.range f) := by
    simpa only [Set.image_univ] using
      PreirreducibleSpace.isPreirreducible_univ.image f hf.continuousOn
  intro a b
  exact hd.subsingleton_of_isPreirreducible hi ⟨a, rfl⟩ ⟨b, rfl⟩

end
end AclGeom.CurveBoundary
