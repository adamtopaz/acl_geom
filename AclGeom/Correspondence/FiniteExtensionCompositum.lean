/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.FamilyCover
import AclGeom.Correspondence.FiniteNormalTransport

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

namespace IntermediateField

/-- Intermediate fields with the same carrier in a common ambient field
have canonically equivalent underlying fields, even when their displayed
scalar fields are different. -/
def ringEquivOfCarrierEq
    {F F' Ω : Type*} [Field F] [Field F'] [Field Ω]
    [Algebra F Ω] [Algebra F' Ω]
    (S : IntermediateField F Ω) (T : IntermediateField F' Ω)
    (h : (S : Set Ω) = (T : Set Ω)) : (↥S) ≃+* (↥T) where
  toFun x := ⟨x, by
    change (x : Ω) ∈ (T : Set Ω)
    rw [← h]
    exact x.2⟩
  invFun y := ⟨y, by
    change (y : Ω) ∈ (S : Set Ω)
    rw [h]
    exact y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_add' x y := by ext; rfl
  map_mul' x y := by ext; rfl

@[simp] theorem ringEquivOfCarrierEq_val
    {F F' Ω : Type*} [Field F] [Field F'] [Field Ω]
    [Algebra F Ω] [Algebra F' Ω]
    (S : IntermediateField F Ω) (T : IntermediateField F' Ω)
    (h : (S : Set Ω) = (T : Set Ω)) (x : S) :
    ((ringEquivOfCarrierEq S T h x : T) : Ω) = x :=
  rfl

/-- Adjoining equal ambient elements to intermediate fields with the same
ambient carrier gives one field carrier, even when the displayed scalar
fields differ. -/
theorem adjoin_singleton_carrier_eq_of_carrier_eq
    {F F' Ω : Type*} [Field F] [Field F'] [Field Ω]
    [Algebra F Ω] [Algebra F' Ω]
    (S : IntermediateField F Ω) (T : IntermediateField F' Ω)
    (hbase : (S : Set Ω) = (T : Set Ω))
    {x y : Ω} (hxy : x = y) :
    ((adjoin (↥S) {x}) : Set Ω) =
      ((adjoin (↥T) {y}) : Set Ω) := by
  have hrange : Set.range (algebraMap (↥S) Ω) =
      Set.range (algebraMap (↥T) Ω) := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨⟨a, ?_⟩, rfl⟩
      change (a : Ω) ∈ (T : Set Ω)
      rw [← hbase]
      exact a.2
    · rintro ⟨a, rfl⟩
      refine ⟨⟨a, ?_⟩, rfl⟩
      change (a : Ω) ∈ (S : Set Ω)
      rw [hbase]
      exact a.2
  have hfield : (adjoin (↥S) {x}).toSubfield =
      (adjoin (↥T) {y}).toSubfield := by
    rw [adjoin_toSubfield, adjoin_toSubfield, hrange, hxy]
  exact congrArg (fun U : Subfield Ω ↦ U.carrier) hfield

/-- Include a ground-field intermediate field in an intermediate field
displayed over a larger scalar field, given containment after restricting
scalars. -/
def algHomIntoOfLeRestrictScalars
    {k F Ω : Type*} [Field k] [Field F] [Field Ω]
    [Algebra k F] [Algebra k Ω] [Algebra F Ω] [IsScalarTower k F Ω]
    (E : IntermediateField k Ω) (N : IntermediateField F Ω)
    (h : E ≤ N.restrictScalars k) : (↥E) →ₐ[k] (↥N) where
  toFun x := ⟨x, h x.2⟩
  map_one' := by ext; rfl
  map_mul' x y := by ext; rfl
  map_zero' := by ext; rfl
  map_add' x y := by ext; rfl
  commutes' x := by ext; rfl

/-- The image of an embedded field after applying a semilinear ambient
automorphism.  This records the moved coefficient presentation rather than
silently requiring the automorphism to preserve it. -/
def imageUnderAutomorphism
    {k E L : Type*} [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra k L]
    (i : E →ₐ[k] L) (sigma : L ≃ₐ[k] L) : IntermediateField k L :=
  i.fieldRange.map sigma.toAlgHom

/-- An embedded field is semilinearly equivalent to its image under an
ambient automorphism. -/
noncomputable def equivImageUnderAutomorphism
    {k E L : Type*} [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra k L]
    (i : E →ₐ[k] L) (sigma : L ≃ₐ[k] L) :
    E ≃ₐ[k] imageUnderAutomorphism i sigma :=
  (AlgEquiv.ofInjective i i.injective).trans (i.fieldRange.equivMap sigma.toAlgHom)

/-- Pointwise, the semilinear image equivalence is ambient application of
the chosen automorphism after the original embedding. -/
@[simp] theorem equivImageUnderAutomorphism_apply
    {k E L : Type*} [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra k L]
    (i : E →ₐ[k] L) (sigma : L ≃ₐ[k] L) (x : E) :
    ((equivImageUnderAutomorphism i sigma x :
      imageUnderAutomorphism i sigma) : L) = sigma (i x) :=
  rfl

/-- An element of the embedded presentation that comes from the scalar
field is fixed by the source chart induced from a scalar-linear ambient
automorphism. -/
theorem equivImageUnderAutomorphism_eq_of_eq_algebraMap
    {k F E L : Type*} [Field k] [Field F] [Field E] [Field L]
    [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F L]
    [IsScalarTower k F L]
    (i : E →ₐ[k] L) (sigma : L ≃ₐ[F] L) (x : E) (y : F)
    (hxy : i x = algebraMap F L y) :
    ((equivImageUnderAutomorphism i (sigma.restrictScalars k) x :
      imageUnderAutomorphism i (sigma.restrictScalars k)) : L) = i x := by
  rw [equivImageUnderAutomorphism_apply, hxy]
  change sigma (algebraMap F L y) = algebraMap F L y
  exact sigma.commutes y

/-- View the semilinear image field back in the original ambient field
rather than only inside the chosen normal intermediate field. -/
def ambientImageUnderAutomorphism
    {k F Ω : Type*} [Field k] [Field F] [Field Ω]
    [Algebra k F] [Algebra k Ω] [Algebra F Ω] [IsScalarTower k F Ω]
    (E : IntermediateField k Ω) (N : IntermediateField F Ω)
    (h : E ≤ N.restrictScalars k) (sigma : (↥N) ≃ₐ[k] (↥N)) :
    IntermediateField k Ω :=
  (imageUnderAutomorphism (algHomIntoOfLeRestrictScalars E N h) sigma).map
    (N.restrictScalars k).val

/-- The original field is semilinearly equivalent to its image in the
original ambient field. -/
noncomputable def equivAmbientImageUnderAutomorphism
    {k F Ω : Type*} [Field k] [Field F] [Field Ω]
    [Algebra k F] [Algebra k Ω] [Algebra F Ω] [IsScalarTower k F Ω]
    (E : IntermediateField k Ω) (N : IntermediateField F Ω)
    (h : E ≤ N.restrictScalars k) (sigma : (↥N) ≃ₐ[k] (↥N)) :
    (↥E) ≃ₐ[k] (↥(ambientImageUnderAutomorphism E N h sigma)) :=
  (equivImageUnderAutomorphism
      (algHomIntoOfLeRestrictScalars E N h) sigma).trans
    ((imageUnderAutomorphism
      (algHomIntoOfLeRestrictScalars E N h) sigma).equivMap
        (N.restrictScalars k).val)

/-- The ambient semilinear image remains inside the same total
intermediate field. -/
theorem ambientImageUnderAutomorphism_le
    {k F Ω : Type*} [Field k] [Field F] [Field Ω]
    [Algebra k F] [Algebra k Ω] [Algebra F Ω] [IsScalarTower k F Ω]
    (E : IntermediateField k Ω) (N : IntermediateField F Ω)
    (h : E ≤ N.restrictScalars k) (sigma : (↥N) ≃ₐ[k] (↥N)) :
    ambientImageUnderAutomorphism E N h sigma ≤ N.restrictScalars k := by
  intro z hz
  rw [ambientImageUnderAutomorphism, mem_map] at hz
  obtain ⟨x, _, rfl⟩ := hz
  change ((x : ↥N) : Ω) ∈ N
  exact (x : ↥N).2

/-- A semilinear automorphism of a total field gives an equivalence between
the original nested extension and the same total field displayed over the
moved ambient image of its base. -/
noncomputable def extensionEquivUnderAutomorphism
    {k F Ω : Type*} [Field k] [Field F] [Field Ω]
    [Algebra k F] [Algebra k Ω] [Algebra F Ω] [IsScalarTower k F Ω]
    (E : IntermediateField k Ω) (N : IntermediateField F Ω)
    (h : E ≤ N.restrictScalars k) (sigma : (↥N) ≃ₐ[k] (↥N)) :
    AclGeom.FiniteCover.ExtensionEquiv h
      (ambientImageUnderAutomorphism_le E N h sigma) where
  baseEquiv := equivAmbientImageUnderAutomorphism E N h sigma
  totalEquiv := sigma
  commutes := by
    apply AlgHom.ext
    intro x
    rfl

/-- Finiteness of the original nested extension transports to the same
total field displayed over its moved semilinear base. -/
theorem ambientImageUnderAutomorphism_finiteDimensional
    {k F Ω : Type*} [Field k] [Field F] [Field Ω]
    [Algebra k F] [Algebra k Ω] [Algebra F Ω] [IsScalarTower k F Ω]
    (E : IntermediateField k Ω) (N : IntermediateField F Ω)
    (h : E ≤ N.restrictScalars k) (sigma : (↥N) ≃ₐ[k] (↥N))
    (hfin : FiniteDimensional (↥E) (↥(extendScalars h))) :
    FiniteDimensional
      (↥(ambientImageUnderAutomorphism E N h sigma))
      (↥(extendScalars (ambientImageUnderAutomorphism_le E N h sigma))) := by
  let h' := ambientImageUnderAutomorphism_le E N h sigma
  let e := extensionEquivUnderAutomorphism E N h sigma
  letI : Algebra (↥E) (↥(N.restrictScalars k)) :=
    (inclusion h).toAlgebra
  letI : Algebra (↥(ambientImageUnderAutomorphism E N h sigma))
      (↥(N.restrictScalars k)) := (inclusion h').toAlgebra
  letI : FiniteDimensional (↥E) (↥(N.restrictScalars k)) := by
    change FiniteDimensional (↥E) (↥(extendScalars h))
    exact hfin
  apply Module.Finite.of_equiv_equiv e.baseEquiv.toRingEquiv
    e.totalEquiv.toRingEquiv
  apply RingHom.ext
  intro x
  exact (e.commutes_apply x).symm

end IntermediateField

namespace AclGeom

open IntermediateField

noncomputable section

namespace FiniteCover

variable {k F Ω : Type*} [Field k] [Field F] [Field Ω]
  [Algebra k F] [Algebra k Ω] [Algebra F Ω] [IsScalarTower k F Ω]

/-- The concrete normal closures of a finite extension and its semilinear
image are equivalent over the same base equivalence that moves the source
field.  The total-field automorphism is retained in the intervening
extension equivalence. -/
noncomputable def normalCoverEquivUnderAutomorphism [IsAlgClosed Ω]
    (E : IntermediateField k Ω) (N : IntermediateField F Ω)
    (h : E ≤ N.restrictScalars k) (sigma : (↥N) ≃ₐ[k] (↥N))
    (hfin : FiniteDimensional (↥E) (↥(extendScalars h))) :
    (↥(normalClosureOver h)) ≃+*
      (↥(normalClosureOver
        (IntermediateField.ambientImageUnderAutomorphism_le E N h sigma))) := by
  let h' := IntermediateField.ambientImageUnderAutomorphism_le E N h sigma
  let hfin' := IntermediateField.ambientImageUnderAutomorphism_finiteDimensional
    E N h sigma hfin
  letI : FiniteDimensional (↥E) (↥(extendScalars h)) := hfin
  letI : FiniteDimensional
      (↥(IntermediateField.ambientImageUnderAutomorphism E N h sigma))
      (↥(extendScalars h')) := hfin'
  let c := normalClosureOverEquivCanonical h
    (Algebra.IsAlgebraic.of_finite _ _)
  let c' := normalClosureOverEquivCanonical h'
    (Algebra.IsAlgebraic.of_finite _ _)
  let e := IntermediateField.extensionEquivUnderAutomorphism E N h sigma
  exact c.toRingEquiv.trans
    ((e.normalLift).normalEquiv.trans c'.symm.toRingEquiv)

/-- The concrete normal-cover equivalence extends the semilinear image
equivalence on the displayed base field. -/
@[simp] theorem normalCoverEquivUnderAutomorphism_algebraMap
    [IsAlgClosed Ω]
    (E : IntermediateField k Ω) (N : IntermediateField F Ω)
    (h : E ≤ N.restrictScalars k) (sigma : (↥N) ≃ₐ[k] (↥N))
    (hfin : FiniteDimensional (↥E) (↥(extendScalars h))) (x : E) :
    normalCoverEquivUnderAutomorphism E N h sigma hfin
        (algebraMap (↥E) (↥(normalClosureOver h)) x) =
      algebraMap
        (↥(IntermediateField.ambientImageUnderAutomorphism E N h sigma))
        (↥(normalClosureOver
          (IntermediateField.ambientImageUnderAutomorphism_le E N h sigma)))
        (IntermediateField.equivAmbientImageUnderAutomorphism E N h sigma x) := by
  simp [normalCoverEquivUnderAutomorphism,
    IntermediateField.extensionEquivUnderAutomorphism]

/-- Correct the semilinear normal-cover comparison by a target deck
transformation so that it preserves the literal selected copy of the whole
total field.  This is the branch-faithful form of the coefficient change. -/
noncomputable def basedBranchEquivUnderAutomorphism [IsAlgClosed Ω]
    (E : IntermediateField k Ω) (N : IntermediateField F Ω)
    (h : E ≤ N.restrictScalars k) (sigma : (↥N) ≃ₐ[k] (↥N))
    (hfin : FiniteDimensional (↥E) (↥(extendScalars h))) :
    FiniteCoverBasedBranchEquiv h
      (IntermediateField.ambientImageUnderAutomorphism_le E N h sigma) := by
  let h' := IntermediateField.ambientImageUnderAutomorphism_le E N h sigma
  let hfin' := IntermediateField.ambientImageUnderAutomorphism_finiteDimensional
    E N h sigma hfin
  apply finiteCoverBasedBranchEquivOfExtensionEquiv h h' hfin'
    (IntermediateField.extensionEquivUnderAutomorphism E N h sigma)
    (normalCoverEquivUnderAutomorphism E N h sigma hfin)
  apply RingHom.ext
  intro x
  exact normalCoverEquivUnderAutomorphism_algebraMap E N h sigma hfin x

/-- The based semilinear comparison sends the literal selected total-field
branch to the literal selected branch over the moved source image. -/
@[simp] theorem basedBranchEquivUnderAutomorphism_selected
    [IsAlgClosed Ω]
    (E : IntermediateField k Ω) (N : IntermediateField F Ω)
    (h : E ≤ N.restrictScalars k) (sigma : (↥N) ≃ₐ[k] (↥N))
    (hfin : FiniteDimensional (↥E) (↥(extendScalars h))) :
    (basedBranchEquivUnderAutomorphism E N h sigma hfin).branchEquiv
        (finiteCoverSelectedBranch h) =
      finiteCoverSelectedBranch
        (IntermediateField.ambientImageUnderAutomorphism_le E N h sigma) :=
  (basedBranchEquivUnderAutomorphism E N h sigma hfin).map_selected

end FiniteCover

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

/-- The finite-basis compositum lies in every ambient field containing both
the larger base and the adjoined finite extension. -/
theorem field_le_of_le {G : IntermediateField k K}
    (hEG : E ≤ G) (hNG : N.restrictScalars k ≤ G) :
    field F E N ≤ G := by
  apply sup_le hEG
  apply adjoin_le_iff.2
  intro z hz
  obtain ⟨i, rfl⟩ := hz
  apply hNG
  exact (Module.finBasis (↥F) (↥N) i).2

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

omit [FiniteDimensional (↥F) (↥C)] C in
include hsource in
/-- When the displayed sources are literally equal, the source equivalence
induced by equal branch ideals has the same ambient value as the identity. -/
theorem extensionEquiv_base_coe_eq_of_source_eq
    (hideal : P.ideal = Q.ideal) (z : sourceField F P) :
    ((((P.extensionEquivOfIdealEq Q hideal).baseEquiv
        (⟨z, z.2⟩ : P.sourceField) : Q.sourceField) : Ω)) = z := by
  let e := P.extensionEquivOfIdealEq Q hideal
  let f : P.sourceField →ₐ[↥F] Ω :=
    Q.sourceField.val.comp e.baseEquiv.toAlgHom
  have hfg : f = P.sourceField.val := by
    apply adjoin_algHom_ext (↥F)
    rintro _ hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    change (((e.baseEquiv ⟨P.source, _⟩ : Q.sourceField) : Ω)) =
      P.source
    simpa [e, hsource] using congrArg Subtype.val
      (P.extensionEquivOfIdealEq_base_source Q hideal)
  exact DFunLike.congr_fun hfg (⟨z, z.2⟩ : P.sourceField)

omit [FiniteDimensional (↥F) (↥C)] C in
/-- Equal selected branch ideals with a literally common source give a
source-linear equivalence between the two literal branch fields. -/
noncomputable def branchEquivOfIdealEq
    (hideal : P.ideal = Q.ideal) :
    (↥(firstBranchOverSource F P)) ≃ₐ[↥(sourceField F P)]
      (↥(secondBranchOverSource F P Q hsource)) :=
  { (P.extensionEquivOfIdealEq Q hideal).totalEquiv.toRingEquiv with
    commutes' := fun z ↦ by
      apply Subtype.ext
      change ((((P.extensionEquivOfIdealEq Q hideal).totalEquiv
          (IntermediateField.inclusion P.sourceField_le_branchField
            (⟨z, z.2⟩ : P.sourceField)) : Q.branchField) : Ω)) = z
      rw [FiniteCover.ExtensionEquiv.commutes_apply]
      exact extensionEquiv_base_coe_eq_of_source_eq
        F P Q hsource hideal z }

omit [FiniteDimensional (↥F) (↥C)] C in
/-- The common-source branch equivalence sends the first displayed target
to the second displayed target. -/
@[simp] theorem branchEquivOfIdealEq_target
    (hideal : P.ideal = Q.ideal) :
    branchEquivOfIdealEq F P Q hsource hideal
        ⟨P.target, by
          change P.target ∈ P.branchField
          exact subset_adjoin (↥F) _ (by simp)⟩ =
      ⟨Q.target, by
        change Q.target ∈ Q.branchField
        exact subset_adjoin (↥F) _ (by simp)⟩ := by
  exact P.extensionEquivOfIdealEq_total_target Q hideal

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

/-- Any smaller coefficient field contained in the chosen finite
coefficient extension, together with the literal source coordinate, lies in
the joint normal field. -/
theorem coefficientSourceAdjoin_le_normalField
    (E : IntermediateField k Ω) (hEC : E ≤ C.restrictScalars k) :
    (adjoin E {P.source}).restrictScalars k ≤
      (normalField F P Q hsource C).restrictScalars k := by
  rw [restrictScalars_adjoin_eq_sup]
  apply sup_le
  · exact hEC.trans
      (coefficientExtension_le_normalField F P Q hsource C)
  · apply adjoin_le_iff.2
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    apply firstBranch_le_normalField F P Q hsource C
    change P.source ∈ P.branchField
    exact subset_adjoin (↥F) _ (by simp)

/-- The first selected branch lies in the joint normal field as an
extension of the common source field. -/
theorem firstBranch_le_normalField_overSource :
    firstBranchOverSource F P ≤ normalField F P Q hsource C := by
  change (firstBranchOverSource F P).restrictScalars k ≤
    (normalField F P Q hsource C).restrictScalars k
  exact firstBranch_le_normalField F P Q hsource C

/-- The second selected branch lies in the joint normal source field. -/
theorem secondBranch_le_normalField :
    (secondBranchOverSource F P Q hsource).restrictScalars k ≤
      (normalField F P Q hsource C).restrictScalars k :=
  (secondBranch_le_field F P Q hsource C).trans
    (field_le_normalField_restrictScalars F P Q hsource C)

/-- The second selected branch lies in the joint normal field as an
extension of the common source field. -/
theorem secondBranch_le_normalField_overSource :
    secondBranchOverSource F P Q hsource ≤
      normalField F P Q hsource C := by
  change (secondBranchOverSource F P Q hsource).restrictScalars k ≤
    (normalField F P Q hsource C).restrictScalars k
  exact secondBranch_le_normalField F P Q hsource C

/-- The coefficient-and-branch normal field is finite over the source. -/
theorem normalField_finiteDimensional :
    FiniteDimensional (↥(sourceField F P))
      (↥(normalField F P Q hsource C)) :=
  FiniteCover.normalClosureOver_finiteDimensional
    (sourceField_le_field F P Q hsource C)
    (field_finiteDimensional F P Q hsource C)

/-- If the chosen coefficient extension is also finite over a smaller
coefficient field, then the joint normal field is finite over that smaller
field with the same literal source adjoined. -/
theorem normalField_finiteDimensional_over_coefficientSource
    (E : IntermediateField k Ω) (hEC : E ≤ C.restrictScalars k)
    (hfinEC : FiniteDimensional (↥E) (↥(extendScalars hEC))) :
    FiniteDimensional
      (↥((adjoin E {P.source}).restrictScalars k))
      (↥(extendScalars
        (coefficientSourceAdjoin_le_normalField
          F P Q hsource C E hEC))) := by
  let B : IntermediateField k Ω :=
    (adjoin E {P.source}).restrictScalars k
  let CE : IntermediateField (↥E) Ω := extendScalars hEC
  let D : IntermediateField k Ω :=
    FiniteExtensionCompositum.field E B CE
  have hEB : E ≤ B := by
    change E ≤ (adjoin E {P.source}).restrictScalars k
    rw [restrictScalars_adjoin_eq_sup]
    exact le_sup_left
  letI : FiniteDimensional (↥E) (↥CE) := hfinEC
  have hBD : B ≤ D :=
    FiniteExtensionCompositum.le_field E B CE
  have hCD : C.restrictScalars k ≤ D := by
    change CE.restrictScalars k ≤ D
    exact FiniteExtensionCompositum.normal_le_field E B CE hEB
  have hBN : B ≤
      (normalField F P Q hsource C).restrictScalars k :=
    coefficientSourceAdjoin_le_normalField F P Q hsource C E hEC
  have hDN : D ≤
      (normalField F P Q hsource C).restrictScalars k := by
    exact FiniteExtensionCompositum.field_le_of_le E B CE hBN
      (coefficientExtension_le_normalField F P Q hsource C)
  have hSD : sourceField F P ≤ D := by
    change (adjoin F {P.source}).restrictScalars k ≤ D
    rw [restrictScalars_adjoin_eq_sup]
    apply sup_le
    · exact (show F ≤ C.restrictScalars k from fun z hz ↦
        C.algebraMap_mem ⟨z, hz⟩) |>.trans hCD
    · apply adjoin_le_iff.2
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      apply hBD
      change P.source ∈ (adjoin E {P.source}).restrictScalars k
      rw [restrictScalars_adjoin_eq_sup]
      exact (le_sup_right : adjoin k {P.source} ≤
        E ⊔ adjoin k {P.source}) (subset_adjoin k _ (by simp))
  have hfinBD : FiniteDimensional (↥B) (↥(extendScalars hBD)) :=
    FiniteExtensionCompositum.over_finiteDimensional E B CE hEB
  have hfinSN : FiniteDimensional (↥(sourceField F P))
      (↥(normalField F P Q hsource C)) :=
    normalField_finiteDimensional F P Q hsource C
  have hfinDN : FiniteDimensional (↥D) (↥(extendScalars hDN)) := by
    letI : Algebra (↥(sourceField F P)) (↥D) :=
      (IntermediateField.inclusion hSD).toAlgebra
    letI : Algebra (↥D) (↥(normalField F P Q hsource C)) :=
      (IntermediateField.inclusion hDN).toAlgebra
    letI : Algebra (↥(sourceField F P))
        (↥(normalField F P Q hsource C)) :=
      (IntermediateField.inclusion (hSD.trans hDN)).toAlgebra
    letI : IsScalarTower (↥(sourceField F P)) (↥D)
        (↥(normalField F P Q hsource C)) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (↥(sourceField F P))
        (↥(normalField F P Q hsource C)) := hfinSN
    change FiniteDimensional (↥D)
      (↥(normalField F P Q hsource C))
    exact FiniteDimensional.right (↥(sourceField F P)) (↥D)
      (↥(normalField F P Q hsource C))
  change FiniteDimensional (↥B) (↥(extendScalars hBN))
  exact FiniteExtensionCompositum.extendScalars_trans_finiteDimensional
    hBD hDN hfinBD hfinDN

/-- In the algebraically closed ambient field, the joint normal field is
normal over the source-coordinate field. -/
theorem normalField_normal [IsAlgClosed Ω] :
    Normal (↥(sourceField F P))
      (↥(normalField F P Q hsource C)) := by
  letI := field_finiteDimensional F P Q hsource C
  exact FiniteCover.normalClosureOver_normal
    (sourceField_le_field F P Q hsource C)
    (Algebra.IsAlgebraic.of_finite _ _)

/-- Renormalize the joint field over a smaller coefficient field with the
same literal source coordinate.  This extra normal closure is necessary
because the old and new source bases need not contain one another. -/
def rebasedNormalField
    (E : IntermediateField k Ω) (hEC : E ≤ C.restrictScalars k) :
    IntermediateField
      (↥((adjoin E {P.source}).restrictScalars k)) Ω :=
  FiniteCover.normalClosureOver
    (coefficientSourceAdjoin_le_normalField F P Q hsource C E hEC)

/-- The renormalized joint field is finite over the smaller
coefficient/source field. -/
theorem rebasedNormalField_finiteDimensional
    (E : IntermediateField k Ω) (hEC : E ≤ C.restrictScalars k)
    (hfinEC : FiniteDimensional (↥E) (↥(extendScalars hEC))) :
    FiniteDimensional
      (↥((adjoin E {P.source}).restrictScalars k))
      (↥(rebasedNormalField F P Q hsource C E hEC)) :=
  FiniteCover.normalClosureOver_finiteDimensional
    (coefficientSourceAdjoin_le_normalField F P Q hsource C E hEC)
    (normalField_finiteDimensional_over_coefficientSource
      F P Q hsource C E hEC hfinEC)

/-- In the algebraically closed ambient field, the renormalized joint field
is normal over the smaller coefficient/source field. -/
theorem rebasedNormalField_normal [IsAlgClosed Ω]
    (E : IntermediateField k Ω) (hEC : E ≤ C.restrictScalars k)
    (hfinEC : FiniteDimensional (↥E) (↥(extendScalars hEC))) :
    Normal
      (↥((adjoin E {P.source}).restrictScalars k))
      (↥(rebasedNormalField F P Q hsource C E hEC)) := by
  letI := normalField_finiteDimensional_over_coefficientSource
    F P Q hsource C E hEC hfinEC
  exact FiniteCover.normalClosureOver_normal
    (coefficientSourceAdjoin_le_normalField F P Q hsource C E hEC)
    (Algebra.IsAlgebraic.of_finite _ _)

/-- The original pairwise normal field lies in its renormalization over the
smaller coefficient/source field. -/
theorem normalField_le_rebasedNormalField
    (E : IntermediateField k Ω) (hEC : E ≤ C.restrictScalars k) :
    (normalField F P Q hsource C).restrictScalars k ≤
      (rebasedNormalField F P Q hsource C E hEC).restrictScalars k := by
  change extendScalars
      (coefficientSourceAdjoin_le_normalField F P Q hsource C E hEC) ≤
    rebasedNormalField F P Q hsource C E hEC
  exact FiniteCover.extendScalars_le_normalClosureOver
    (coefficientSourceAdjoin_le_normalField F P Q hsource C E hEC)

/-- The canonical algebraic-closure model of the pairwise field after
rebasing to the smaller coefficient/source field. -/
noncomputable def rebasedCanonicalCover
    (E : IntermediateField k Ω) (hEC : E ≤ C.restrictScalars k)
    (hfinEC : FiniteDimensional (↥E) (↥(extendScalars hEC))) :
    AlgebraicClosureTransport.FiniteNormalCover
      (↥((adjoin E {P.source}).restrictScalars k)) where
  field := FiniteCover.canonicalNormalClosure
    (coefficientSourceAdjoin_le_normalField F P Q hsource C E hEC)
  finiteDimensional :=
    FiniteCover.canonicalNormalClosure_finiteDimensional
      (coefficientSourceAdjoin_le_normalField F P Q hsource C E hEC)
      (normalField_finiteDimensional_over_coefficientSource
        F P Q hsource C E hEC hfinEC)
  normal := by
    letI : FiniteDimensional
        (↥((adjoin E {P.source}).restrictScalars k))
        (↥(extendScalars
          (coefficientSourceAdjoin_le_normalField
            F P Q hsource C E hEC))) :=
      normalField_finiteDimensional_over_coefficientSource
        F P Q hsource C E hEC hfinEC
    exact FiniteCover.canonicalNormalClosure_normal
      (coefficientSourceAdjoin_le_normalField F P Q hsource C E hEC)
      (Algebra.IsAlgebraic.of_finite _ _)

/-- The concrete ambient renormalization and its canonical cover are
equivalent over the smaller coefficient/source field. -/
noncomputable def rebasedNormalFieldEquivCanonical [IsAlgClosed Ω]
    (E : IntermediateField k Ω) (hEC : E ≤ C.restrictScalars k)
    (hfinEC : FiniteDimensional (↥E) (↥(extendScalars hEC))) :
    (↥(rebasedNormalField F P Q hsource C E hEC)) ≃ₐ[
        ↥((adjoin E {P.source}).restrictScalars k)]
      (↥(rebasedCanonicalCover F P Q hsource C E hEC hfinEC).field) := by
  letI : FiniteDimensional
      (↥((adjoin E {P.source}).restrictScalars k))
      (↥(extendScalars
        (coefficientSourceAdjoin_le_normalField
          F P Q hsource C E hEC))) :=
    normalField_finiteDimensional_over_coefficientSource
      F P Q hsource C E hEC hfinEC
  exact FiniteCover.normalClosureOverEquivCanonical
    (coefficientSourceAdjoin_le_normalField F P Q hsource C E hEC)
    (Algebra.IsAlgebraic.of_finite _ _)

/-- The first literal target branch, now regarded over the smaller common
coefficient/source field. -/
def firstBranchOverRebasedSource
    (E : IntermediateField k Ω) :
    IntermediateField
      (↥((adjoin E {P.source}).restrictScalars k)) Ω :=
  adjoin (↥((adjoin E {P.source}).restrictScalars k)) {P.target}

/-- The second literal target branch, regarded over the same smaller common
coefficient/source field. -/
def secondBranchOverRebasedSource
    (E : IntermediateField k Ω) :
    IntermediateField
      (↥((adjoin E {P.source}).restrictScalars k)) Ω :=
  adjoin (↥((adjoin E {P.source}).restrictScalars k)) {Q.target}

/-- The first literal branch lies in the ambient renormalization over the
smaller common source. -/
theorem firstBranchOverRebasedSource_le_rebasedNormalField
    (E : IntermediateField k Ω) (hEC : E ≤ C.restrictScalars k) :
    firstBranchOverRebasedSource F P E ≤
      rebasedNormalField F P Q hsource C E hEC := by
  apply adjoin_le_iff.2
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  apply normalField_le_rebasedNormalField F P Q hsource C E hEC
  apply firstBranch_le_normalField F P Q hsource C
  change P.target ∈ P.branchField
  exact subset_adjoin (↥F) _ (by simp)

/-- The second literal branch lies in the same ambient renormalization. -/
theorem secondBranchOverRebasedSource_le_rebasedNormalField
    (E : IntermediateField k Ω) (hEC : E ≤ C.restrictScalars k) :
    secondBranchOverRebasedSource F P Q E ≤
      rebasedNormalField F P Q hsource C E hEC := by
  apply adjoin_le_iff.2
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  apply normalField_le_rebasedNormalField F P Q hsource C E hEC
  apply secondBranch_le_normalField F P Q hsource C
  change Q.target ∈ Q.branchField
  exact subset_adjoin (↥F) _ (by simp)

/-- The first literal common-base branch embedded in the canonical rebased
normal cover. -/
noncomputable def firstBranchEmbeddingInRebasedCanonical [IsAlgClosed Ω]
    (E : IntermediateField k Ω) (hEC : E ≤ C.restrictScalars k)
    (hfinEC : FiniteDimensional (↥E) (↥(extendScalars hEC))) :
    NormalBranchEmbedding
      (↥((adjoin E {P.source}).restrictScalars k))
      (↥(firstBranchOverRebasedSource F P E))
      (↥(rebasedCanonicalCover F P Q hsource C E hEC hfinEC).field) :=
  ⟨(rebasedNormalFieldEquivCanonical
      F P Q hsource C E hEC hfinEC).toAlgHom.comp
    (IntermediateField.inclusion
      (firstBranchOverRebasedSource_le_rebasedNormalField
        F P Q hsource C E hEC))⟩

/-- The second literal common-base branch embedded in the same canonical
rebased normal cover. -/
noncomputable def secondBranchEmbeddingInRebasedCanonical [IsAlgClosed Ω]
    (E : IntermediateField k Ω) (hEC : E ≤ C.restrictScalars k)
    (hfinEC : FiniteDimensional (↥E) (↥(extendScalars hEC))) :
    NormalBranchEmbedding
      (↥((adjoin E {P.source}).restrictScalars k))
      (↥(secondBranchOverRebasedSource F P Q E))
      (↥(rebasedCanonicalCover F P Q hsource C E hEC hfinEC).field) :=
  ⟨(rebasedNormalFieldEquivCanonical
      F P Q hsource C E hEC hfinEC).toAlgHom.comp
    (IntermediateField.inclusion
      (secondBranchOverRebasedSource_le_rebasedNormalField
        F P Q hsource C E hEC))⟩

/-- Place the first literal branch from a rebased pairwise comparison in
any larger canonical normal cover containing that comparison cover. -/
noncomputable def firstBranchEmbeddingInRebasedCanonicalIn [IsAlgClosed Ω]
    (E : IntermediateField k Ω) (hEC : E ≤ C.restrictScalars k)
    (hfinEC : FiniteDimensional (↥E) (↥(extendScalars hEC)))
    (N : AlgebraicClosureTransport.FiniteNormalCover
      (↥((adjoin E {P.source}).restrictScalars k)))
    (hle : (rebasedCanonicalCover
      F P Q hsource C E hEC hfinEC).field ≤ N.field) :
    NormalBranchEmbedding
      (↥((adjoin E {P.source}).restrictScalars k))
      (↥(firstBranchOverRebasedSource F P E)) (↥N.field) :=
  ⟨(IntermediateField.inclusion hle).comp
    (firstBranchEmbeddingInRebasedCanonical
      F P Q hsource C E hEC hfinEC).toAlgHom⟩

/-- Place the second literal branch from a rebased pairwise comparison in
the same larger canonical normal cover. -/
noncomputable def secondBranchEmbeddingInRebasedCanonicalIn [IsAlgClosed Ω]
    (E : IntermediateField k Ω) (hEC : E ≤ C.restrictScalars k)
    (hfinEC : FiniteDimensional (↥E) (↥(extendScalars hEC)))
    (N : AlgebraicClosureTransport.FiniteNormalCover
      (↥((adjoin E {P.source}).restrictScalars k)))
    (hle : (rebasedCanonicalCover
      F P Q hsource C E hEC hfinEC).field ≤ N.field) :
    NormalBranchEmbedding
      (↥((adjoin E {P.source}).restrictScalars k))
      (↥(secondBranchOverRebasedSource F P Q E)) (↥N.field) :=
  ⟨(IntermediateField.inclusion hle).comp
    (secondBranchEmbeddingInRebasedCanonical
      F P Q hsource C E hEC hfinEC).toAlgHom⟩

/-- The second literal branch, transported back along the ideal-induced
branch equivalence, as an embedding of the first branch into the joint
normal field. -/
noncomputable def secondBranchEmbeddingOfIdealEq
    (hideal : P.ideal = Q.ideal) :
    NormalBranchEmbedding (↥(sourceField F P))
      (↥(firstBranchOverSource F P))
      (↥(normalField F P Q hsource C)) :=
  ⟨(IntermediateField.inclusion
      (secondBranch_le_normalField_overSource F P Q hsource C)).comp
    (branchEquivOfIdealEq F P Q hsource hideal).toAlgHom⟩

/-- Normality extends the ideal-induced branch comparison to a deck
transformation of the finite joint normal field. -/
noncomputable def branchAutomorphismOfIdealEq [IsAlgClosed Ω]
    (hideal : P.ideal = Q.ideal) :
    (↥(normalField F P Q hsource C)) ≃ₐ[↥(sourceField F P)]
      (↥(normalField F P Q hsource C)) := by
  letI : Algebra (↥(firstBranchOverSource F P))
      (↥(normalField F P Q hsource C)) :=
    (IntermediateField.inclusion
      (firstBranch_le_normalField_overSource F P Q hsource C)).toAlgebra
  letI : IsScalarTower (↥(sourceField F P))
      (↥(firstBranchOverSource F P))
      (↥(normalField F P Q hsource C)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Normal (↥(sourceField F P))
      (↥(normalField F P Q hsource C)) :=
    normalField_normal F P Q hsource C
  exact (secondBranchEmbeddingOfIdealEq
    F P Q hsource C hideal).extendToAut

/-- The extended deck transformation restricts to the prescribed
ideal-induced equivalence from the first literal branch to the second. -/
theorem branchAutomorphismOfIdealEq_inclusion_apply [IsAlgClosed Ω]
    (hideal : P.ideal = Q.ideal) (x : firstBranchOverSource F P) :
    branchAutomorphismOfIdealEq F P Q hsource C hideal
        (IntermediateField.inclusion
          (firstBranch_le_normalField_overSource F P Q hsource C) x) =
      IntermediateField.inclusion
        (secondBranch_le_normalField_overSource F P Q hsource C)
        (branchEquivOfIdealEq F P Q hsource hideal x) := by
  letI : Algebra (↥(firstBranchOverSource F P))
      (↥(normalField F P Q hsource C)) :=
    (IntermediateField.inclusion
      (firstBranch_le_normalField_overSource F P Q hsource C)).toAlgebra
  letI : IsScalarTower (↥(sourceField F P))
      (↥(firstBranchOverSource F P))
      (↥(normalField F P Q hsource C)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Normal (↥(sourceField F P))
      (↥(normalField F P Q hsource C)) :=
    normalField_normal F P Q hsource C
  change ((secondBranchEmbeddingOfIdealEq F P Q hsource C hideal).toAlgHom
      |>.liftNormal (↥(normalField F P Q hsource C)))
        (algebraMap (↥(firstBranchOverSource F P))
          (↥(normalField F P Q hsource C)) x) = _
  exact (secondBranchEmbeddingOfIdealEq F P Q hsource C hideal).toAlgHom
    |>.liftNormal_commutes (↥(normalField F P Q hsource C)) x

/-- In particular, the joint normal-field automorphism sends the first
displayed target to the second displayed target. -/
@[simp] theorem branchAutomorphismOfIdealEq_target [IsAlgClosed Ω]
    (hideal : P.ideal = Q.ideal) :
    branchAutomorphismOfIdealEq F P Q hsource C hideal
        (IntermediateField.inclusion
          (firstBranch_le_normalField_overSource F P Q hsource C)
          ⟨P.target, by
            change P.target ∈ P.branchField
            exact subset_adjoin (↥F) _ (by simp)⟩) =
      IntermediateField.inclusion
        (secondBranch_le_normalField_overSource F P Q hsource C)
        ⟨Q.target, by
          change Q.target ∈ Q.branchField
          exact subset_adjoin (↥F) _ (by simp)⟩ := by
  rw [branchAutomorphismOfIdealEq_inclusion_apply]
  exact congrArg
    (IntermediateField.inclusion
      (secondBranch_le_normalField_overSource F P Q hsource C))
    (branchEquivOfIdealEq_target F P Q hsource hideal)

end FiniteCoefficientBranchCompositum

end

end AclGeom
