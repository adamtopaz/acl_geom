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

/-! ## A finite coefficient field and two selected branches -/

namespace FiniteCoefficientBranchCompositum

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
  (F : IntermediateField k Ω)
  (P Q : FiniteCorrespondencePair (↥F) Ω)
  (hsource : P.source = Q.source)
  (C : IntermediateField (↥F) Ω)
  [FiniteDimensional (↥F) (↥C)]

/-- The selected source-coordinate field, restricted back to the ground
field so that coefficient and branch extensions can be composed in one
ambient lattice. -/
def sourceField : IntermediateField k Ω :=
  P.sourceField.restrictScalars k

/-- The coefficient field lies in the selected source-coordinate field. -/
theorem coefficientField_le_sourceField :
    F ≤ sourceField F P := by
  intro z hz
  change z ∈ P.sourceField
  exact P.sourceField.algebraMap_mem ⟨z, hz⟩

/-- Adjoin the finite coefficient extension to the source-coordinate
field. -/
def coefficientSourceField : IntermediateField k Ω :=
  FiniteExtensionCompositum.field F (sourceField F P) C

/-- The source-coordinate field embeds in the coefficient-source
compositum. -/
theorem sourceField_le_coefficientSourceField :
    sourceField F P ≤ coefficientSourceField F P C :=
  FiniteExtensionCompositum.le_field F (sourceField F P) C

/-- The finite coefficient extension embeds in the coefficient-source
compositum. -/
theorem coefficientExtension_le_coefficientSourceField :
    C.restrictScalars k ≤ coefficientSourceField F P C :=
  FiniteExtensionCompositum.normal_le_field F (sourceField F P) C
    (coefficientField_le_sourceField F P)

/-- The coefficient-source compositum remains finite over the source
coordinate field. -/
theorem coefficientSourceField_finiteDimensional :
    FiniteDimensional (↥(sourceField F P))
      (↥(extendScalars
        (sourceField_le_coefficientSourceField F P C))) :=
  FiniteExtensionCompositum.over_finiteDimensional
    F (sourceField F P) C (coefficientField_le_sourceField F P)

/-- The first selected branch, viewed over the restricted source field. -/
def firstBranchOverSource :
    IntermediateField (↥(sourceField F P)) Ω := by
  change IntermediateField (↥P.sourceField) Ω
  exact P.branchOverSource

/-- The first selected branch remains finite over the restricted source
field. -/
theorem firstBranchOverSource_finiteDimensional :
    FiniteDimensional (↥(sourceField F P))
      (↥(firstBranchOverSource F P)) := by
  change FiniteDimensional (↥P.sourceField) (↥P.branchOverSource)
  exact P.branchOverSource_finiteDimensional

/-- Adjoin the first selected branch to the coefficient-source
compositum. -/
def withFirstBranch : IntermediateField k Ω := by
  letI := firstBranchOverSource_finiteDimensional F P
  exact FiniteExtensionCompositum.field
    (sourceField F P) (coefficientSourceField F P C)
      (firstBranchOverSource F P)

/-- The coefficient-source compositum lies in the first-branch
compositum. -/
theorem coefficientSourceField_le_withFirstBranch :
    coefficientSourceField F P C ≤ withFirstBranch F P C := by
  letI := firstBranchOverSource_finiteDimensional F P
  exact FiniteExtensionCompositum.le_field
    (sourceField F P) (coefficientSourceField F P C)
      (firstBranchOverSource F P)

/-- The first selected branch lies in the first-branch compositum. -/
theorem firstBranch_le_withFirstBranch :
    (firstBranchOverSource F P).restrictScalars k ≤
      withFirstBranch F P C := by
  letI := firstBranchOverSource_finiteDimensional F P
  exact FiniteExtensionCompositum.normal_le_field
    (sourceField F P) (coefficientSourceField F P C)
      (firstBranchOverSource F P)
      (sourceField_le_coefficientSourceField F P C)

/-- Adjoining the first selected branch is finite over the
coefficient-source compositum. -/
theorem withFirstBranch_finiteDimensional :
    FiniteDimensional (↥(coefficientSourceField F P C))
      (↥(extendScalars
        (coefficientSourceField_le_withFirstBranch F P C))) := by
  letI := firstBranchOverSource_finiteDimensional F P
  exact FiniteExtensionCompositum.over_finiteDimensional
    (sourceField F P) (coefficientSourceField F P C)
      (firstBranchOverSource F P)
      (sourceField_le_coefficientSourceField F P C)

/-- The common source field embeds in the second selected branch field. -/
theorem sourceField_le_secondBranchField
    (hsource : P.source = Q.source) :
    P.sourceField ≤ Q.branchField := by
  unfold FiniteCorrespondencePair.sourceField
    FiniteCorrespondencePair.branchField
  apply adjoin.mono
  simp [hsource]

/-- The second selected branch, rebased over the first literal source
field using the equality of the two source coordinates. -/
def secondBranchOverSource :
    IntermediateField (↥(sourceField F P)) Ω := by
  change IntermediateField (↥P.sourceField) Ω
  exact extendScalars (sourceField_le_secondBranchField F P Q hsource)

/-- Over the common source field, the second branch is generated by its
selected target coordinate. -/
theorem secondBranchOverSource_eq_adjoin_target :
    secondBranchOverSource F P Q hsource =
      adjoin (↥(sourceField F P)) {Q.target} := by
  change extendScalars (sourceField_le_secondBranchField F P Q hsource) =
    adjoin (↥P.sourceField) {Q.target}
  unfold FiniteCorrespondencePair.branchField
  rw [extendScalars_adjoin]
  apply le_antisymm
  · apply adjoin_le_iff.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [← hsource]
      exact (adjoin P.sourceField {Q.target}).algebraMap_mem
        ⟨P.source, subset_adjoin (↥F) _ (by simp)⟩
    · exact subset_adjoin P.sourceField _ (by simp)
  · apply adjoin_le_iff.2
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact subset_adjoin P.sourceField _ (by simp)

/-- The second selected branch is finite over the common source field. -/
theorem secondBranchOverSource_finiteDimensional :
    FiniteDimensional (↥(sourceField F P))
      (↥(secondBranchOverSource F P Q hsource)) := by
  rw [secondBranchOverSource_eq_adjoin_target F P Q hsource]
  exact finiteDimensional_adjoin fun z hz ↦ by
    rw [Set.mem_singleton_iff] at hz
    subst z
    have hAlg := (mem_racl_iff (↥F)).1 Q.target_mem_source
    have hAlg' : IsAlgebraic (↥P.sourceField) Q.target := by
      have hsourceField : P.sourceField = Q.sourceField := by
        unfold FiniteCorrespondencePair.sourceField
        rw [hsource]
      rw [hsourceField]
      exact hAlg
    exact hAlg'.isIntegral

/-- Adjoin the second selected branch as the last finite step. -/
def field : IntermediateField k Ω := by
  letI := secondBranchOverSource_finiteDimensional F P Q hsource
  exact FiniteExtensionCompositum.field
    (sourceField F P) (withFirstBranch F P C)
      (secondBranchOverSource F P Q hsource)

/-- The first-branch compositum embeds in the full joint field. -/
theorem withFirstBranch_le_field :
    withFirstBranch F P C ≤ field F P Q hsource C := by
  letI := secondBranchOverSource_finiteDimensional F P Q hsource
  exact FiniteExtensionCompositum.le_field
    (sourceField F P) (withFirstBranch F P C)
      (secondBranchOverSource F P Q hsource)

/-- The second selected branch embeds in the full joint field. -/
theorem secondBranch_le_field :
    (secondBranchOverSource F P Q hsource).restrictScalars k ≤
      field F P Q hsource C := by
  letI := secondBranchOverSource_finiteDimensional F P Q hsource
  exact FiniteExtensionCompositum.normal_le_field
    (sourceField F P) (withFirstBranch F P C)
      (secondBranchOverSource F P Q hsource)
      ((sourceField_le_coefficientSourceField F P C).trans
        (coefficientSourceField_le_withFirstBranch F P C))

/-- Adjoining the second selected branch remains finite. -/
theorem field_over_withFirstBranch_finiteDimensional :
    FiniteDimensional (↥(withFirstBranch F P C))
      (↥(extendScalars (withFirstBranch_le_field F P Q hsource C))) := by
  letI := secondBranchOverSource_finiteDimensional F P Q hsource
  exact FiniteExtensionCompositum.over_finiteDimensional
    (sourceField F P) (withFirstBranch F P C)
      (secondBranchOverSource F P Q hsource)
      ((sourceField_le_coefficientSourceField F P C).trans
        (coefficientSourceField_le_withFirstBranch F P C))

/-- The source-coordinate field embeds in the full coefficient-and-branch
compositum. -/
theorem sourceField_le_field :
    sourceField F P ≤ field F P Q hsource C :=
  (sourceField_le_coefficientSourceField F P C).trans
    ((coefficientSourceField_le_withFirstBranch F P C).trans
      (withFirstBranch_le_field F P Q hsource C))

/-- The full coefficient-and-branch compositum is finite over the selected
source-coordinate field. -/
theorem field_finiteDimensional :
    FiniteDimensional (↥(sourceField F P))
      (↥(extendScalars (sourceField_le_field F P Q hsource C))) := by
  have hfinFirst : FiniteDimensional (↥(sourceField F P))
      (↥(extendScalars
        ((sourceField_le_coefficientSourceField F P C).trans
          (coefficientSourceField_le_withFirstBranch F P C)))) :=
    FiniteExtensionCompositum.extendScalars_trans_finiteDimensional
      (sourceField_le_coefficientSourceField F P C)
      (coefficientSourceField_le_withFirstBranch F P C)
      (coefficientSourceField_finiteDimensional F P C)
      (withFirstBranch_finiteDimensional F P C)
  exact FiniteExtensionCompositum.extendScalars_trans_finiteDimensional
    ((sourceField_le_coefficientSourceField F P C).trans
      (coefficientSourceField_le_withFirstBranch F P C))
    (withFirstBranch_le_field F P Q hsource C)
    hfinFirst
    (field_over_withFirstBranch_finiteDimensional F P Q hsource C)

/-- A finite normal source field containing the coefficient extension and
both selected correspondence branches. -/
def normalField : IntermediateField (↥(sourceField F P)) Ω :=
  FiniteCover.normalClosureOver (sourceField_le_field F P Q hsource C)

/-- The joint finite field embeds in its source-normal closure. -/
theorem field_le_normalField :
    extendScalars (sourceField_le_field F P Q hsource C) ≤
      normalField F P Q hsource C :=
  FiniteCover.extendScalars_le_normalClosureOver
    (sourceField_le_field F P Q hsource C)

/-- On restriction to the ground field, the entire joint field lies in
the normal source field. -/
theorem field_le_normalField_restrictScalars :
    field F P Q hsource C ≤
      (normalField F P Q hsource C).restrictScalars k := by
  change extendScalars (sourceField_le_field F P Q hsource C) ≤
    normalField F P Q hsource C
  exact field_le_normalField F P Q hsource C

/-- The finite coefficient extension lies in the joint normal source
field. -/
theorem coefficientExtension_le_normalField :
    C.restrictScalars k ≤
      (normalField F P Q hsource C).restrictScalars k :=
  (coefficientExtension_le_coefficientSourceField F P C).trans
    ((coefficientSourceField_le_withFirstBranch F P C).trans
      ((withFirstBranch_le_field F P Q hsource C).trans
        (field_le_normalField_restrictScalars F P Q hsource C)))

/-- The first selected branch lies in the joint normal source field. -/
theorem firstBranch_le_normalField :
    (firstBranchOverSource F P).restrictScalars k ≤
      (normalField F P Q hsource C).restrictScalars k :=
  (firstBranch_le_withFirstBranch F P C).trans
    ((withFirstBranch_le_field F P Q hsource C).trans
      (field_le_normalField_restrictScalars F P Q hsource C))

/-- The second selected branch lies in the joint normal source field. -/
theorem secondBranch_le_normalField :
    (secondBranchOverSource F P Q hsource).restrictScalars k ≤
      (normalField F P Q hsource C).restrictScalars k :=
  (secondBranch_le_field F P Q hsource C).trans
    (field_le_normalField_restrictScalars F P Q hsource C)

/-- The coefficient-and-branch normal field is finite over the source. -/
theorem normalField_finiteDimensional :
    FiniteDimensional (↥(sourceField F P))
      (↥(normalField F P Q hsource C)) :=
  FiniteCover.normalClosureOver_finiteDimensional
    (sourceField_le_field F P Q hsource C)
    (field_finiteDimensional F P Q hsource C)

/-- In the algebraically closed ambient field, the joint normal field is
normal over the source-coordinate field. -/
theorem normalField_normal [IsAlgClosed Ω] :
    Normal (↥(sourceField F P))
      (↥(normalField F P Q hsource C)) := by
  letI := field_finiteDimensional F P Q hsource C
  exact FiniteCover.normalClosureOver_normal
    (sourceField_le_field F P Q hsource C)
    (Algebra.IsAlgebraic.of_finite _ _)

end FiniteCoefficientBranchCompositum

end

end AclGeom
