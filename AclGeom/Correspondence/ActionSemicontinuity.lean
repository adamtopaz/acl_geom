/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.PlaceTransport
import AclGeom.Correspondence.GroupSchemePoints
import AclGeom.Correspondence.SchemeActionSections
import AclGeom.Correspondence.SchemeCurveFunctionField
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Orders at a place along a regular action

Let an algebraic group `G` act regularly on an affine integral curve `V` over an algebraically
closed field `k`, and fix a place `P` of the function field of `V`. For a nonzero global section
`r` of `V` and an integer `m`, the set of `k`-points `g` with `m ≤ ord_P (g • r)` is closed
(`isClosed_setOf_le_ord`); here `k`-points are identified with the closed points of `G`.

Proof. Near a point `g₀`, take an affine open `U ∋ g₀` of `G`. By
`SchemeActionSections.exists_pointAut_appTop_eq_sum`, every `g ∈ U` moves the generic germ of `r`
to `∑ cᵢ(g) • sᵢ` with fixed `cᵢ` and fixed germs `sᵢ`. The elements of order at least `m`,
together with `0`, form a `k`-subspace `W` (`Place.ordFiltration`). If `g₀` lies outside the set,
then `g₀ • r` is nonzero and outside `W`, so some linear form `φ` vanishing on `W` is nonzero at
`g₀ • r`. Then `∑ φ(sᵢ) cᵢ` is a section over `U` which is nonzero at `g₀`; its basic open set is
a neighbourhood of `g₀` outside the set. No finite-dimensionality of `W` is needed.

Named consumer: the exact order level sets of the fixed-boundary argument for `lem:affine-action`.

**Status:** proved; consumed by the actual connected regular-action fixed-boundary theorem.
-/

namespace AclGeom.ActionSemicontinuity

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj ActionFunctionField
  SchemeActionSections

universe u

variable {k : Type u} [Field k]

attribute [local instance] functionFieldAlgebra isIso_hom_left

/-- **Orders at a place are upper semicontinuous along a regular action.** For a nonzero global
section `r` of an affine integral curve `V` and an integer `m`, the closed points `x` of `G` whose
`k`-point moves the generic germ of `r` to an element of order at least `m` at `P` form a closed
set. The one-variable hypothesis needed by `Place.ord` is derived from the curve. -/
theorem isClosed_setOf_le_ord [IsAlgClosed k] (G : AlgebraicGroup k) (V : Over (Spec (.of k)))
    [IsIntegral V.left] [IsAffine V.left] [LocallyOfFiniteType V.hom]
    (hdim : topologicalKrullDim V.left = 1) [ModObj G.toGroupScheme.X V]
    (P : Place k V.left.functionField) {r : Γ(V.left, ⊤)} (hr : r ≠ 0) (m : ℤ) :
    haveI := scheme_functionField_isFunctionFieldOneVar k V hdim
    IsClosed {x : closedPoints G.carrier | m ≤ P.ord
      ((functionFieldAction G V
        ((GroupScheme.pointsEquivClosedPoints (G := G.toGroupScheme.X)).symm x)).unop
        (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) r))} := by
  have := scheme_functionField_isFunctionFieldOneVar k V hdim
  change IsClosed _
  -- The action on generic germs is pullback of global sections.
  have hgerm : ∀ (φ : V ≅ V) (t : Γ(V.left, ⊤)),
      algEquivOfIso φ (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) t) =
        V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩)
          (φ.hom.left.appTop t) := fun φ t ↦
    congrArg (fun f ↦ f.hom t) (Scheme.Hom.germToFunctionField_top_comp φ.hom.left)
  have hconst : ∀ c : k, V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩)
      (((Scheme.ΓSpecIso (.of k)).inv ≫ V.hom.appTop).hom c) =
        algebraMap k V.left.functionField c := fun c ↦ by
    rw [functionFieldAlgebra_eq_germ V]
    rfl
  have hpoint : ∀ x : closedPoints G.carrier,
      ((GroupScheme.pointsEquivClosedPoints (G := G.toGroupScheme.X)).symm x).left
        (IsLocalRing.closedPoint k) = x := fun x ↦ by
    rw [← GroupScheme.pointsEquivClosedPoints_apply, Equiv.apply_symm_apply]
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (x : G.carrier))
    (U := ⊤) trivial
  obtain ⟨n, c, s, hcs⟩ := exists_pointAut_appTop_eq_sum G V hU r
  -- Near `x`, the action moves the germ of `r` to a combination of fixed germs.
  have hw : ∀ (g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X)
      (hg : g.left (IsLocalRing.closedPoint k) ∈ U),
      (functionFieldAction G V g).unop
          (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) r) =
        ∑ i, pointEval g U hg (c i) •
          V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) (s i) := by
    intro g hg
    refine (hgerm (ModObj.pointAut V g) r).trans ?_
    rw [hcs g hg, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, hconst, Algebra.smul_def]
  let W := P.ordFiltration m
  -- The point `x` is outside the set, so `x • r` is nonzero and outside `W`.
  have hxU' : ((GroupScheme.pointsEquivClosedPoints (G := G.toGroupScheme.X)).symm x).left
      (IsLocalRing.closedPoint k) ∈ U := by
    rw [hpoint x]
    exact hxU
  have : Nonempty (⊤ : V.left.Opens) := ⟨⟨genericPoint _, trivial⟩⟩
  have hne : (functionFieldAction G V
      ((GroupScheme.pointsEquivClosedPoints (G := G.toGroupScheme.X)).symm x)).unop
        (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) r) ≠ 0 :=
    (map_ne_zero_iff _ (functionFieldAction G V _).unop.injective).2
      ((map_ne_zero_iff _ (Scheme.germToFunctionField_injective V.left ⊤)).2 hr)
  have hnotW : (functionFieldAction G V
      ((GroupScheme.pointsEquivClosedPoints (G := G.toGroupScheme.X)).symm x)).unop
        (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) r) ∉ W :=
    fun hmem ↦ hx ((P.mem_ordFiltration hne).1 hmem)
  obtain ⟨φ, hφ, hφx⟩ : ∃ φ : Module.Dual k V.left.functionField, φ ∈ W.dualAnnihilator ∧
      φ ((functionFieldAction G V
        ((GroupScheme.pointsEquivClosedPoints (G := G.toGroupScheme.X)).symm x)).unop
          (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) r)) ≠ 0 := by
    by_contra h
    exact hnotW ((Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).1
      fun φ hφ ↦ not_not.1 fun hne ↦ h ⟨φ, hφ, hne⟩)
  -- The section `∑ φ(sᵢ) cᵢ` over `U` computes `φ (g • r)` at every point `g` of `U`.
  obtain ⟨cφ, hcφdef⟩ : ∃ cφ : Γ(G.carrier, U), cφ = ∑ i,
      ((Scheme.ΓSpecIso (.of k)).inv ≫ G.toGroupScheme.X.hom.appLE ⊤ U le_top).hom
        (φ (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) (s i))) * c i :=
    ⟨_, rfl⟩
  have hcφ : ∀ (g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X)
      (hg : g.left (IsLocalRing.closedPoint k) ∈ U),
      pointEval g U hg cφ = φ ((functionFieldAction G V g).unop
        (V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) r)) := by
    intro g hg
    rw [hcφdef, hw g hg, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, pointEval_appLE, map_smul, smul_eq_mul, mul_comm]
  refine ⟨{y | (y : G.carrier) ∈ G.carrier.basicOpen cφ}, ?_,
    (G.carrier.basicOpen cφ).isOpen.preimage continuous_subtype_val, ?_⟩
  · intro y hy hle
    have hyU : ((GroupScheme.pointsEquivClosedPoints (G := G.toGroupScheme.X)).symm y).left
        (IsLocalRing.closedPoint k) ∈ U := by
      rw [hpoint y]
      exact G.carrier.basicOpen_le cφ hy
    have h0 : pointEval _ U hyU cφ ≠ 0 := by
      rw [ne_eq, pointEval_eq_zero_iff, hpoint y, not_not]
      exact hy
    rw [hcφ _ hyU] at h0
    exact h0 ((Submodule.mem_dualAnnihilator φ).1 hφ _ (Or.inr hle))
  · by_contra hxc
    apply hφx
    rw [← hcφ _ hxU', pointEval_eq_zero_iff, hpoint x]
    exact hxc
end

end AclGeom.ActionSemicontinuity
