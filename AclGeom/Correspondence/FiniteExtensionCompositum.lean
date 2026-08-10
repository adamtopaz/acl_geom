/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.FiniteCover

/-!
# Adjoining a finite subextension to a larger function field

Let `F ≤ E` be intermediate fields in one ambient field and let `N/F` be
finite.  Although `E/F` need not be finite, adjoining `N` to `E` is again a
finite extension of `E`.  This file gives a concrete version of that fact:
choose the standard finite basis of `N/F`, adjoin its values to `E`, and use
the same basis to prove both containment of all of `N` and finiteness over
`E`.

The construction is useful when several normal covers over smaller
parameter blocks must be placed inside one common cover over a larger
independent-input field.
-/

namespace AclGeom

open IntermediateField

noncomputable section

universe u

namespace FiniteExtensionCompositum

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (F E : IntermediateField k K)
  (N : IntermediateField (↥F) K)
  [FiniteDimensional (↥F) (↥N)]

/-- The values in the ambient field of the standard finite basis of `N/F`. -/
def basisValues : Fin (Module.finrank (↥F) (↥N)) → K :=
  fun i ↦ (Module.finBasis (↥F) (↥N) i : K)

/-- If `F ≤ E`, every selected basis value of `N/F` is integral over `E`. -/
theorem basisValues_isIntegral_of_le (hFE : F ≤ E)
    (i : Fin (Module.finrank (↥F) (↥N))) :
    IsIntegral (↥E) (basisValues F N i) := by
  letI : Algebra (↥F) (↥E) := (IntermediateField.inclusion hFE).toAlgebra
  letI : IsScalarTower (↥F) (↥E) K :=
    IsScalarTower.of_algebraMap_eq' rfl
  let b := Module.finBasis (↥F) (↥N)
  have hiN : IsIntegral (↥F) (b i) :=
    (Algebra.IsAlgebraic.of_finite (↥F) (↥N)).isAlgebraic (b i) |>.isIntegral
  have hiK : IsIntegral (↥F) (b i : K) := hiN.map N.val
  exact hiK.tower_top

/-- A field containing `F` and all selected basis values contains the whole
finite field `N`, after restriction to the ground field. -/
theorem restrictScalars_le_of_basisValues_subset
    {G : IntermediateField k K} (hFG : F ≤ G)
    (hbasis : Set.range (basisValues F N) ⊆ G) :
    N.restrictScalars k ≤ G := by
  intro z hz
  let b := Module.finBasis (↥F) (↥N)
  let zN : N := ⟨z, hz⟩
  have hF (r : F) : (r : K) ∈ G := hFG r.2
  have hb (i : Fin (Module.finrank (↥F) (↥N))) : (b i : K) ∈ G := by
    apply hbasis
    exact Set.mem_range_self i
  have hsum : ∑ i, ((b.repr zN i : F) : K) * (b i : K) ∈ G := by
    exact Subring.sum_mem G.toSubring fun i _ ↦ G.mul_mem (hF _) (hb i)
  have hzsum := congrArg (fun y : N ↦ (y : K)) (b.sum_repr zN)
  have hzsum' : ∑ i, ((b.repr zN i : F) : K) * (b i : K) = z := by
    simpa [Algebra.smul_def] using hzsum
  exact hzsum' ▸ hsum

/-- The concrete compositum obtained by adjoining a finite basis of `N/F`
to the larger field `E`. -/
def field : IntermediateField k K :=
  E ⊔ adjoin k (Set.range (basisValues F N))

/-- The larger base field embeds in the finite-basis compositum. -/
theorem le_field : E ≤ field F E N := le_sup_left

/-- The finite field `N` embeds in the finite-basis compositum. -/
theorem normal_le_field (hFE : F ≤ E) :
    N.restrictScalars k ≤ field F E N := by
  apply restrictScalars_le_of_basisValues_subset F N (hFE.trans le_sup_left)
  intro _ hx
  exact (le_sup_right : adjoin k (Set.range (basisValues F N)) ≤
      field F E N) (subset_adjoin k _ hx)

/-- The finite-basis compositum as an extension of `E`. -/
def over : IntermediateField (↥E) K :=
  extendScalars (le_field F E N)

/-- Adjoining a finite subextension to a larger field remains finite over
that larger field. -/
theorem over_finiteDimensional (hFE : F ≤ E) :
    FiniteDimensional (↥E) (↥(over F E N)) := by
  have key : over F E N = adjoin (↥E) (Set.range (basisValues F N)) := by
    refine restrictScalars_injective k ?_
    unfold over field
    rw [extendScalars_restrictScalars, restrictScalars_adjoin,
      adjoin_union, adjoin_self]
  rw [key]
  exact finiteDimensional_adjoin fun x hx ↦ by
    obtain ⟨i, rfl⟩ := hx
    exact basisValues_isIntegral_of_le F E N hFE i

/-- Finiteness of two nested concrete intermediate-field extensions composes
to finiteness of their direct extension inside the same ambient field. -/
theorem extendScalars_trans_finiteDimensional
    {E₀ E₁ E₂ : IntermediateField k K}
    (h01 : E₀ ≤ E₁) (h12 : E₁ ≤ E₂)
    (hfin01 : FiniteDimensional (↥E₀) (↥(extendScalars h01)))
    (hfin12 : FiniteDimensional (↥E₁) (↥(extendScalars h12))) :
    FiniteDimensional (↥E₀) (↥(extendScalars (h01.trans h12))) := by
  letI : Algebra (↥E₀) (↥E₁) :=
    (IntermediateField.inclusion h01).toAlgebra
  letI : Algebra (↥E₁) (↥E₂) :=
    (IntermediateField.inclusion h12).toAlgebra
  letI : Algebra (↥E₀) (↥E₂) :=
    (IntermediateField.inclusion (h01.trans h12)).toAlgebra
  letI : IsScalarTower (↥E₀) (↥E₁) (↥E₂) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional (↥E₀) (↥E₁) := by
    change FiniteDimensional (↥E₀) (↥(extendScalars h01))
    exact hfin01
  letI : FiniteDimensional (↥E₁) (↥E₂) := by
    change FiniteDimensional (↥E₁) (↥(extendScalars h12))
    exact hfin12
  change FiniteDimensional (↥E₀) (↥E₂)
  exact FiniteDimensional.trans (↥E₀) (↥E₁) (↥E₂)

end FiniteExtensionCompositum

end

end AclGeom
