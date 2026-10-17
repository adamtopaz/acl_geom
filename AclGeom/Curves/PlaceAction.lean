/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.Divisors

/-!
# Places transported along automorphisms

A `k`-automorphism `σ` of `F` moves each place of `F/k`: the new valuation ring is the preimage
`σ⁻¹(O)` (`Place.comap`). Pullback of valuation rings reverses composition, so this is an action
of the opposite group of `k`-automorphisms on the places.

For a finitely generated `k`-subalgebra `A` of a one-variable function field over an algebraically
closed field, only finitely many places fail to contain `A` (`Place.boundary_finite`). An
automorphism preserving `A` permutes these places (`Place.comap_mem_boundary_iff`).

Named consumers: the action of a scheme action on the places of a curve's function field and the
boundary of an affine curve (`Correspondence.SchemePlaceAction`), toward blueprint
`lem:affine-action`. This is the field-place analogue of extending automorphisms to a completion;
it does not prove the source's scheme extension statement.

**Status:** proved; the actual scheme and affine-curve consumers are checked independently.
-/

namespace AclGeom

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Place

/-- The place moved by a `k`-automorphism: its valuation ring is the preimage. -/
def comap (σ : F ≃ₐ[k] F) (P : Place k F) : Place k F where
  val := P.val.comap (σ : F →+* F)
  algebraMap_mem' c := by
    change σ (algebraMap k F c) ∈ P.val
    rw [σ.commutes]
    exact P.algebraMap_mem c
  ne_top' h := P.ne_top <| top_unique fun x _ ↦ by
    have hx : σ.symm x ∈ P.val.comap (σ : F →+* F) := by
      rw [h]
      exact ValuationSubring.mem_top _
    change σ (σ.symm x) ∈ P.val at hx
    rwa [AlgEquiv.apply_symm_apply] at hx

theorem mem_comap {σ : F ≃ₐ[k] F} {P : Place k F} {x : F} :
    x ∈ (P.comap σ).val ↔ σ x ∈ P.val :=
  Iff.rfl

/-- Places are determined by their valuation rings. -/
theorem ext_val {P Q : Place k F} (h : P.val = Q.val) : P = Q := by
  obtain ⟨v, _, _⟩ := P
  obtain ⟨w, _, _⟩ := Q
  dsimp only at h
  subst h
  rfl

/-- The opposite group of `k`-automorphisms acts on places by pulling back valuation rings. -/
instance : MulAction (F ≃ₐ[k] F)ᵐᵒᵖ (Place k F) where
  smul σ P := P.comap σ.unop
  one_smul _ := ext_val (SetLike.ext fun _ ↦ Iff.rfl)
  mul_smul _ _ _ := ext_val (SetLike.ext fun _ ↦ Iff.rfl)

/-- The literal formula for transport by an element of the opposite automorphism group. -/
theorem op_smul_eq_comap (σ : F ≃ₐ[k] F) (P : Place k F) : MulOpposite.op σ • P = P.comap σ :=
  rfl

/-- The boundary of a `k`-subalgebra `A`: the places whose valuation ring does not contain `A`. -/
def boundary (A : Subalgebra k F) : Set (Place k F) :=
  {P | ¬ (A : Set F) ⊆ P.val}

/-- A place containing a set of generators contains the subalgebra they generate. -/
theorem adjoin_subset_val {s : Set F} {P : Place k F} (hs : s ⊆ P.val) :
    (Algebra.adjoin k s : Set F) ⊆ P.val := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact hs hx
  | algebraMap r => exact P.algebraMap_mem r
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

/-- **The boundary of a finitely generated subalgebra is finite.** Each place of the boundary is
a pole of one of finitely many nonzero generators. -/
theorem boundary_finite [IsAlgClosed k] [IsFunctionFieldOneVar k F] {A : Subalgebra k F}
    (hA : A.FG) : (boundary A).Finite := by
  classical
  obtain ⟨s, rfl⟩ := hA
  have hfin : (⋃ a ∈ ((s.filter (· ≠ 0) : Finset F) : Set F),
      {P : Place k F | 1 < P.val.valuation a}).Finite :=
    (s.filter (· ≠ 0)).finite_toSet.biUnion fun a ha ↦
      finite_setOf_one_lt_valuation (k := k) (Finset.mem_filter.1 ha).2
  refine hfin.subset fun P hP ↦ ?_
  by_contra hno
  apply hP
  apply adjoin_subset_val
  intro a ha
  by_cases ha0 : a = 0
  · rw [ha0]
    exact P.val.zero_mem
  · by_contra hna
    apply hno
    refine Set.mem_biUnion (x := a) (Finset.mem_filter.2 ⟨ha, ha0⟩) ?_
    exact not_le.1 fun h ↦ hna ((P.val.valuation_le_one_iff a).1 h)

/-- An automorphism preserving `A` permutes the boundary of `A`. -/
theorem comap_mem_boundary_iff {A : Subalgebra k F} {σ : F ≃ₐ[k] F}
    (hσ : A.map (σ : F →ₐ[k] F) = A) {P : Place k F} :
    P.comap σ ∈ boundary A ↔ P ∈ boundary A := by
  change ¬ (A : Set F) ⊆ (P.comap σ).val ↔ ¬ (A : Set F) ⊆ P.val
  refine not_congr ⟨fun h y hy ↦ ?_, fun h x hx ↦ ?_⟩
  · rw [← hσ] at hy
    obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.1 hy
    exact h hx
  · have hσx : (σ : F →ₐ[k] F) x ∈ A.map (σ : F →ₐ[k] F) := Subalgebra.mem_map.2 ⟨x, hx, rfl⟩
    rw [hσ] at hσx
    exact h hσx

end Place

end AclGeom
