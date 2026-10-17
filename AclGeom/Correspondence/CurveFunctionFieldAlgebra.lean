/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Curves.Places
import AclGeom.Correspondence.LocusDimension
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Topology.KrullDimension

/-!
# One-variable fields and affine opens of curves

Named consumer: the actual scheme-curve/function-field bridge for blueprint Lemma
`affine-action` (#21 row 2). No perfectness or separability is needed for the existing
`IsFunctionFieldOneVar` class. A dimension-one affine open is obtained from a length-one
chain by Mathlib's order isomorphism for an open embedding, without a new cover-dimension API.

**Status:** proved; both lemmas are consumed by the actual scheme-curve field theorem.
-/

namespace AclGeom

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

/-- A finitely generated field of transcendence degree one is a one-variable function field.
Named consumer: the actual function field of an integral curve scheme. -/
theorem isFunctionFieldOneVar_of_trdeg_eq_one (k F : Type*) [Field k] [Field F]
    [Algebra k F] [Algebra.EssFiniteType k F] (htr : Algebra.trdeg k F = 1) :
    IsFunctionFieldOneVar k F := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis k F
  have hcard : s.card = 1 := by
    have h := hs.cardinalMk_eq_trdeg
    rw [Cardinal.mk_coe_finset, htr] at h
    exact_mod_cast h
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.1 hcard
  have halg := hs.isAlgebraic_field
  have hr : Set.range ((↑) : ({t} : Finset F) → F) = {t} := by
    ext x
    simp
  rw [hr] at halg
  have : Algebra.EssFiniteType (IntermediateField.adjoin k ({t} : Set F)) F :=
    Algebra.EssFiniteType.of_comp k _ _
  exact ⟨⟨t, hs.1.transcendental ⟨t, Finset.mem_singleton_self t⟩,
    Algebra.finite_of_essFiniteType_of_isAlgebraic⟩⟩

/-- A dimension-one scheme contains a nonempty affine open of dimension one.
Named consumer: the finite-type-domain dimension calculation for its actual function field. -/
theorem exists_isAffineOpen_dimension_one (X : Scheme)
    (hX : topologicalKrullDim X = 1) :
    ∃ U : X.Opens, IsAffineOpen U ∧ Nonempty U ∧ topologicalKrullDim U = 1 := by
  obtain ⟨C, D, hCD⟩ := Order.one_le_krullDim_iff.1 hX.ge
  obtain ⟨x, hx⟩ := C.isIrreducible.nonempty
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding
    (Subtype.val : U → X) U.isOpenEmbedding
  let c : {Z : IrreducibleCloseds X | ((Subtype.val : U → X) ⁻¹' Z).Nonempty} :=
    ⟨C, ⟨⟨x, hxU⟩, hx⟩⟩
  let d : {Z : IrreducibleCloseds X | ((Subtype.val : U → X) ⁻¹' Z).Nonempty} :=
    ⟨D, ⟨⟨x, hxU⟩, hCD.le hx⟩⟩
  have hcd : c < d := hCD
  have hlo : (1 : WithBot ℕ∞) ≤ topologicalKrullDim U :=
    Order.one_le_krullDim_iff.2 ⟨e.symm c, e.symm d, e.symm.strictMono hcd⟩
  refine ⟨U, hU, ⟨⟨x, hxU⟩⟩, le_antisymm ?_ hlo⟩
  exact (topologicalKrullDim_subspace_le X (U : Set X)).trans hX.le

end

end AclGeom
