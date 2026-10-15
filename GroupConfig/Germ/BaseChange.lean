/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.BaseNesting
import GroupConfig.Germ.Inverse
import GroupConfig.Germ.GenericSet
import GroupConfig.Germ.HW
import GroupConfig.Germ.Definable

/-!
# Base change of germs

Blueprint `sources/group_configuration/08-proof.tex`, `lem:hw-basechange`, first paragraph of
the proof: germs over a base field and germs over a small algebraically closed extension of it
are the same objects.

Both base fields are intermediate fields `K₀ ≤ K₁` of `K` over the ambient base `k`, so that
nested base changes never appear.  For tuples `a`, `a'` independent from `K₁` over `K₀`, a
representative `(M, f)` of a germ over `K₀` is a representative `(acl_{K₁}(M), f)` of a germ
over `K₁` (`Representative.baseChange`), and equivalent representatives stay equivalent, so
germs transport along the base change (`Germ.baseChange`).  The graph ideal is unchanged
(`Germ.graphIdeal_baseChange`), hence so are the code (`Germ.codeSet_baseChange`) and, up to
the new base, the canonical base (`Germ.racl_cb_baseChange`); values at generic points are
unchanged (`Germ.evalGen_baseChange`); conjugation by automorphisms over `K₁`, composition,
identities and inverses are compatible with the base change (`Germ.map_baseChange`,
`Germ.comp_baseChange`, `Germ.id_baseChange`, `Germ.IsInverse.baseChange`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** transport of germs, codes, values, conjugation, composition and inverses along a
base change complete; the transport of orbits, difference sets and the hypotheses of
`thm:hw-bij` is in `GroupConfig.Germ.BaseChangeHW`.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### Transport of quasi-rational expressions along ring homomorphisms -/

section Transport

variable {L L' : Type*} [Field L] [Field L'] [Algebra L K] [Algebra L' K] {ι κ : Type*}

theorem aeval_map_of_comp_eq (φ : L →+* L') (hφ : (algebraMap L' K).comp φ = algebraMap L K)
    (u : ι → K) (P : MvPolynomial ι L) : aeval u (MvPolynomial.map φ P) = aeval u P := by
  rw [aeval_def, aeval_def, eval₂_map, hφ]

theorem QuasiRational.isDefinedAt_map_iff_of_comp_eq (φ : L →+* L')
    (hφ : (algebraMap L' K).comp φ = algebraMap L K) (f : QuasiRational L ι κ) (u : ι → K) :
    (f.map φ).IsDefinedAt u ↔ f.IsDefinedAt u := by
  unfold QuasiRational.IsDefinedAt
  simp only [QuasiRational.map]
  exact forall_congr' fun j ↦ by rw [aeval_map_of_comp_eq φ hφ]

theorem QuasiRational.eval_map_of_comp_eq [PerfectField K] (φ : L →+* L')
    (hφ : (algebraMap L' K).comp φ = algebraMap L K) (f : QuasiRational L ι κ) (u : ι → K) :
    (f.map φ).eval u = f.eval u := by
  funext j
  simp only [QuasiRational.eval, QuasiRational.map, aeval_map_of_comp_eq φ hφ]

/-- An automorphism of `K` over a subfield is an automorphism over every smaller subfield. -/
def algEquivRestrict (h : range (algebraMap L K) ⊆ range (algebraMap L' K)) (σ : K ≃ₐ[L'] K) :
    K ≃ₐ[L] K where
  toRingEquiv := σ.toRingEquiv
  commutes' x := by
    obtain ⟨x', hx'⟩ := h ⟨x, rfl⟩
    change σ (algebraMap L K x) = algebraMap L K x
    rw [← hx']
    exact σ.commutes x'

@[simp]
theorem coe_algEquivRestrict (h : range (algebraMap L K) ⊆ range (algebraMap L' K))
    (σ : K ≃ₐ[L'] K) : ⇑(algEquivRestrict h σ) = ⇑σ := rfl

end Transport

/-! ### Inclusions of intermediate fields over different bases -/

section Incl

variable {k₀ k₁ : Type*} [Field k₀] [Field k₁] [Algebra k₀ K] [Algebra k₁ K]

/-- The inclusion of an intermediate field `M` over `k₀` into an intermediate field `N` over
`k₁` containing it. -/
def inclBase (M : IntermediateField k₀ K) (N : IntermediateField k₁ K) (h : (M : Set K) ⊆ N) :
    ↥M →+* ↥N where
  toFun x := ⟨x, h x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem algebraMap_comp_inclBase (M : IntermediateField k₀ K) (N : IntermediateField k₁ K)
    (h : (M : Set K) ⊆ N) : (algebraMap (↥N) K).comp (inclBase M N h) = algebraMap (↥M) K := by
  ext x
  rfl

end Incl

/-! ### The two bases -/

variable (K₀ K₁ : IntermediateField k K) [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)]

section Bases

variable (h₀₁ : K₀ ≤ K₁)
include h₀₁

/-- Restriction of automorphisms over `K₁` to automorphisms over `K₀`. -/
def restrictBase (σ : K ≃ₐ[↥K₁] K) : K ≃ₐ[↥K₀] K :=
  algEquivRestrict (by rw [range_algebraMap_coe, range_algebraMap_coe]; exact h₀₁) σ

omit [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)] in
@[simp]
theorem coe_restrictBase (σ : K ≃ₐ[↥K₁] K) : ⇑(restrictBase K₀ K₁ h₀₁ σ) = ⇑σ := rfl

omit [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)] in
/-- Smallness transfers to a field over `K₁` with the same carrier. -/
theorem isSmall_base_of_coe_eq {F : IntermediateField (↥K₀) K} (hF : IsSmall (↥K₀) (F : Set K))
    {F'' : IntermediateField (↥K₁) K} (h : (F'' : Set K) = (F : Set K)) :
    IsSmall (↥K₁) (F'' : Set K) := by
  unfold IsSmall at hF ⊢
  rw [erk_base_empty K₁, h]
  rw [erk_base_empty K₀] at hF
  exact fun htop ↦ hF (eq_top_iff.2 (htop ▸ erk_base_mono k h₀₁ _))

omit [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)] in
/-- Small sets over `K₀` are small over `K₁`. -/
theorem isSmall_base_mono {C : Set K} (hC : IsSmall (↥K₀) C) : IsSmall (↥K₁) C := by
  unfold IsSmall at hC ⊢
  rw [erk_base_empty K₁]
  rw [erk_base_empty K₀] at hC
  exact fun htop ↦ hC (eq_top_iff.2 (htop ▸ erk_base_mono k h₀₁ _))

omit [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)] in
/-- Independence over `K₁` is independence over `K₀` relative to `K₁`. -/
theorem indepOver_base_le_iff (A B : Set K) :
    IndepOver (↥K₁) ∅ A B ↔ IndepOver (↥K₀) (K₁ : Set K) A B := by
  rw [indepOver_base_iff K₁, ← indepOver_coe_union_iff K₀,
    union_eq_right.2 (SetLike.coe_subset_coe.2 h₀₁)]

variable [IsAlgClosed K]

omit [IsAlgClosed (↥K₀)] in
/-- The closure of `K₁` over `K₀` is `K₁`. -/
theorem coe_racl_base_self : ((racl (↥K₀) (K₁ : Set K) : IntermediateField (↥K₀) K) : Set K) =
    (K₁ : Set K) := by
  have h : racl k ((K₀ : Set K) ∪ K₁) = K₁ :=
    le_antisymm (racl_le_of_isAlgClosed (union_subset h₀₁ le_rfl))
      (fun w hw ↦ subset_racl k _ (Or.inr hw))
  rw [racl_base_coe K₀, h]

omit [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)] in
/-- Closing a field over `K₀` containing `K₁` over `K₁` does not change it. -/
theorem coe_racl_base_of_le (F : IntermediateField (↥K₀) K) [IsAlgClosed (↥F)]
    (hK₁F : (K₁ : Set K) ⊆ F) :
    ((racl (↥K₁) (F : Set K) : IntermediateField (↥K₁) K) : Set K) = (F : Set K) := by
  have h : racl (↥K₀) ((K₁ : Set K) ∪ F) = F :=
    le_antisymm (racl_le_of_isAlgClosed (union_subset hK₁F le_rfl))
      (fun w hw ↦ subset_racl (↥K₀) _ (Or.inr hw))
  rw [racl_base_coe K₁, ← union_eq_right.2 (SetLike.coe_subset_coe.2 h₀₁), union_assoc,
    ← racl_base_coe K₀, h]

omit [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)] [IsAlgClosed K] in
/-- The carrier of `acl_{K₁}(S)` is the carrier of `acl_{K₀}(K₁ ∪ S)`. -/
theorem coe_racl_base_eq (S : Set K) :
    ((racl (↥K₁) S : IntermediateField (↥K₁) K) : Set K) =
      ((racl (↥K₀) ((K₁ : Set K) ∪ S) : IntermediateField (↥K₀) K) : Set K) := by
  rw [racl_base_coe K₁, racl_base_coe K₀, ← union_assoc,
    union_eq_right.2 (SetLike.coe_subset_coe.2 h₀₁)]

end Bases

variable [IsAlgClosed K] [UniversalDomain (↥K₀) K] [UniversalDomain (↥K₁) K] {ι κ : Type*}
  [Finite ι] [Finite κ] {a : ι → K} {a' : κ → K}

/-! ### Generic points over the two bases -/

section Bridge

variable (h₀₁ : K₀ ≤ K₁) (hK₁ : IsSmall (↥K₀) (K₁ : Set K))
  (ha : IndepOver (↥K₀) ∅ (range a) (K₁ : Set K))
include h₀₁ hK₁ ha

omit [Finite κ] [UniversalDomain (↥K₁) K] in
/-- `lem:dim`(2): the locus of a tuple independent from `K₁` is the same over `K₁` and `K₀`. -/
theorem locusIdeal_coe_eq : locusIdeal (↥K₁) a = locusIdeal (↥K₀) a := by
  have hind : IndepOver (↥K₀) ∅ (range a)
      ((racl (↥K₀) (K₁ : Set K) : IntermediateField (↥K₀) K) : Set K) := by
    have h := indepOver_racl_right_iff.2 ha
    rwa [empty_union] at h
  have haa : IsGenericOver (racl (↥K₀) (K₁ : Set K)) a a :=
    isGenericOver_self_of_indepOver hK₁.racl hind
  rw [← haa.locusIdeal_eq]
  exact locusIdeal_congr _ (by rw [range_algebraMap_coe, range_algebraMap_coe,
    coe_racl_base_self K₀ K₁ h₀₁]) a

omit [Finite κ] [UniversalDomain (↥K₁) K] in
/-- Generic points over a field `N` over `K₁` are generic over the field `M` over `K₀` with
the same carrier. -/
theorem isGenericOver_base_iff {N : IntermediateField (↥K₁) K} {M : IntermediateField (↥K₀) K}
    (hNM : (N : Set K) = (M : Set K)) {y : ι → K} :
    IsGenericOver N a y ↔ IsGenericOver M a y := by
  rw [isGenericOver_iff_locusIdeal_eq, isGenericOver_iff_locusIdeal_eq,
    locusIdeal_coe_eq K₀ K₁ h₀₁ hK₁ ha, locusIdeal_congr (↥N) (L' := ↥M)
      (by rw [range_algebraMap_coe, range_algebraMap_coe, hNM]) y]

omit [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)] [IsAlgClosed K] [UniversalDomain (↥K₀) K]
  [UniversalDomain (↥K₁) K] [Finite ι] [Finite κ] h₀₁ hK₁ ha in
theorem isGen_iff_locusIdeal_eq (L : Type*) [Field L] [Algebra L K] {y : ι → K} :
    IsGen L a y ↔ locusIdeal L y = locusIdeal L a := by
  constructor
  · intro h
    unfold locusIdeal
    rw [h]
  · intro h
    unfold IsGen
    rw [← locusIdeal_comap L y, ← locusIdeal_comap L a, h]

omit [Finite κ] [UniversalDomain (↥K₁) K] in
/-- Generic points over `K₁` are the generic points over `K₀` independent from `K₁`. -/
theorem isGen_base_iff {y : ι → K} :
    IsGen (↥K₁) a y ↔ IsGen (↥K₀) a y ∧ IndepOver (↥K₀) ∅ (range y) (K₁ : Set K) := by
  have hind : IndepOver (↥K₀) ∅ (range a)
      ((racl (↥K₀) (K₁ : Set K) : IntermediateField (↥K₀) K) : Set K) := by
    have h := indepOver_racl_right_iff.2 ha
    rwa [empty_union] at h
  have haa : IsGenericOver (racl (↥K₀) (K₁ : Set K)) a a :=
    isGenericOver_self_of_indepOver hK₁.racl hind
  have hcongr : ∀ u : ι → K, locusIdeal (↥K₁) u = locusIdeal (↥(racl (↥K₀) (K₁ : Set K))) u :=
    fun u ↦ locusIdeal_congr _ (by rw [range_algebraMap_coe, range_algebraMap_coe,
      coe_racl_base_self K₀ K₁ h₀₁]) u
  have e1 : IsGen (↥K₁) a y ↔ IsGenericOver (racl (↥K₀) (K₁ : Set K)) a y := by
    rw [isGen_iff_locusIdeal_eq, isGenericOver_iff_locusIdeal_eq, ← haa.locusIdeal_eq, hcongr y,
      hcongr a]
  rw [e1]
  constructor
  · intro h
    refine ⟨h.isGen, ?_⟩
    have := h.indepOver
    rwa [coe_racl_base_self K₀ K₁ h₀₁] at this
  · rintro ⟨h1, h2⟩
    exact h1.isGenericOver_racl hK₁ h2

end Bridge

/-! ### Base change of representatives -/

namespace Representative

variable (h₀₁ : K₀ ≤ K₁) (hK₁ : IsSmall (↥K₀) (K₁ : Set K))
  (ha : IndepOver (↥K₀) ∅ (range a) (K₁ : Set K))
  (ha' : IndepOver (↥K₀) ∅ (range a') (K₁ : Set K))

omit [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)] [UniversalDomain (↥K₀) K] [UniversalDomain (↥K₁) K]
  [Finite ι] [Finite κ] in
/-- The field of the base change of `r` has the carrier of `acl_{K₀}(K₁ ∪ M)`. -/
theorem coe_racl_base_M (h₀₁ : K₀ ≤ K₁) (r : Representative (↥K₀) K a a') :
    ((racl (↥K₁) (r.M : Set K) : IntermediateField (↥K₁) K) : Set K) =
      ((racl (↥K₀) ((K₁ : Set K) ∪ r.M) : IntermediateField (↥K₀) K) : Set K) :=
  coe_racl_base_eq K₀ K₁ h₀₁ _

omit [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)] [UniversalDomain (↥K₀) K] [UniversalDomain (↥K₁) K]
  [Finite ι] [Finite κ] in
theorem M_le_racl_union (r : Representative (↥K₀) K a a') :
    r.M ≤ racl (↥K₀) ((K₁ : Set K) ∪ r.M) :=
  fun _ hw ↦ subset_racl (↥K₀) _ (Or.inr hw)

omit [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)] [UniversalDomain (↥K₀) K] [UniversalDomain (↥K₁) K]
  [Finite ι] [Finite κ] in
theorem M_subset_racl_base (h₀₁ : K₀ ≤ K₁) (r : Representative (↥K₀) K a a') :
    (r.M : Set K) ⊆ racl (↥K₁) (r.M : Set K) := by
  rw [coe_racl_base_M K₀ K₁ h₀₁]
  exact M_le_racl_union K₀ K₁ r

include h₀₁ hK₁ ha

omit [UniversalDomain (↥K₁) K] [Finite κ] in
/-- A point generic over the new field is generic over the old one. -/
theorem isGenericOver_M_of_racl_base (r : Representative (↥K₀) K a a') {y : ι → K}
    (hy : IsGenericOver (racl (↥K₁) (r.M : Set K)) a y) : IsGenericOver r.M a y :=
  ((isGenericOver_base_iff K₀ K₁ h₀₁ hK₁ ha (coe_racl_base_M K₀ K₁ h₀₁ r)).1 hy).of_le
    (M_le_racl_union K₀ K₁ r)

omit [UniversalDomain (↥K₁) K] [Finite κ] in
/-- Generic points over the new field are independent from it over the old field. -/
theorem indepOver_racl_union_of_racl_base (r : Representative (↥K₀) K a a') {y : ι → K}
    (hy : IsGenericOver (racl (↥K₁) (r.M : Set K)) a y) :
    IndepOver (↥K₀) (r.M : Set K) (range y)
      ((racl (↥K₀) ((K₁ : Set K) ∪ r.M) : IntermediateField (↥K₀) K) : Set K) := by
  have _ := r.isAlgClosed
  exact ((isGenericOver_M_of_racl_base K₀ K₁ h₀₁ hK₁ ha r hy).isGenericOver_iff_indepOver
    r.isSmall (hK₁.union r.isSmall).racl (M_le_racl_union K₀ K₁ r)).1
    ((isGenericOver_base_iff K₀ K₁ h₀₁ hK₁ ha (coe_racl_base_M K₀ K₁ h₀₁ r)).1 hy)

include ha'

omit [UniversalDomain (↥K₁) K] in
/-- The value of `r` at a point generic over the new field is generic over the new field. -/
theorem isGenericOver_eval_racl_base (r : Representative (↥K₀) K a a') {y : ι → K}
    (hy : IsGenericOver (racl (↥K₁) (r.M : Set K)) a y) :
    IsGenericOver (racl (↥K₁) (r.M : Set K)) a' (r.f.eval y) := by
  have _ := r.isAlgClosed
  have hyM : IsGenericOver r.M a y := isGenericOver_M_of_racl_base K₀ K₁ h₀₁ hK₁ ha r hy
  have hz := r.isGenericOver y hyM
  refine (isGenericOver_base_iff K₀ K₁ h₀₁ hK₁ ha' (coe_racl_base_M K₀ K₁ h₀₁ r)).2 ?_
  refine (hz.isGenericOver_iff_indepOver r.isSmall (hK₁.union r.isSmall).racl
    (M_le_racl_union K₀ K₁ r)).2 ?_
  refine (indepOver_racl_left_iff.2
    (indepOver_racl_union_of_racl_base K₀ K₁ h₀₁ hK₁ ha r hy)).mono_left ?_
  rintro _ ⟨j, rfl⟩
  exact r.eval_mem_racl hyM j

omit [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)] [UniversalDomain (↥K₀) K]
  [UniversalDomain (↥K₁) K] [Finite ι] [Finite κ] h₀₁ hK₁ ha ha' in
theorem isDefinedAt_map_inclBase (r : Representative (↥K₀) K a a') {N : IntermediateField (↥K₁) K}
    (h : (r.M : Set K) ⊆ N) (u : ι → K) :
    (r.f.map (inclBase r.M N h)).IsDefinedAt u ↔ r.f.IsDefinedAt u :=
  QuasiRational.isDefinedAt_map_iff_of_comp_eq (inclBase r.M N h)
    (algebraMap_comp_inclBase r.M N h) r.f u

omit [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)] [UniversalDomain (↥K₀) K]
  [UniversalDomain (↥K₁) K] [Finite ι] [Finite κ] h₀₁ hK₁ ha ha' in
theorem eval_map_inclBase (r : Representative (↥K₀) K a a') {N : IntermediateField (↥K₁) K}
    (h : (r.M : Set K) ⊆ N) (u : ι → K) :
    (r.f.map (inclBase r.M N h)).eval u = r.f.eval u :=
  QuasiRational.eval_map_of_comp_eq (inclBase r.M N h) (algebraMap_comp_inclBase r.M N h) r.f u

/-- `lem:hw-basechange`: a representative over `K₀` as a representative over `K₁`. -/
def baseChange (r : Representative (↥K₀) K a a') : Representative (↥K₁) K a a' where
  M := racl (↥K₁) (r.M : Set K)
  isAlgClosed := isAlgClosed_racl _
  isSmall := isSmall_base_of_coe_eq K₀ K₁ h₀₁ (hK₁.union r.isSmall).racl
    (coe_racl_base_M K₀ K₁ h₀₁ r)
  f := r.f.map (inclBase r.M _ (M_subset_racl_base K₀ K₁ h₀₁ r))
  isDefinedAt y hy :=
    (isDefinedAt_map_inclBase K₀ K₁ r (M_subset_racl_base K₀ K₁ h₀₁ r) y).2
      (r.isDefinedAt y (isGenericOver_M_of_racl_base K₀ K₁ h₀₁ hK₁ ha r hy))
  isGenericOver y hy := by
    rw [eval_map_inclBase K₀ K₁ r (M_subset_racl_base K₀ K₁ h₀₁ r) y]
    exact isGenericOver_eval_racl_base K₀ K₁ h₀₁ hK₁ ha ha' r hy

omit [UniversalDomain (↥K₁) K] in
theorem baseChange_M (r : Representative (↥K₀) K a a') :
    (r.baseChange K₀ K₁ h₀₁ hK₁ ha ha').M = racl (↥K₁) (r.M : Set K) := rfl

omit [UniversalDomain (↥K₁) K] in
theorem baseChange_eval (r : Representative (↥K₀) K a a') (u : ι → K) :
    (r.baseChange K₀ K₁ h₀₁ hK₁ ha ha').f.eval u = r.f.eval u :=
  eval_map_inclBase K₀ K₁ r (M_subset_racl_base K₀ K₁ h₀₁ r) u

omit [UniversalDomain (↥K₁) K] in
/-- Equivalent representatives have equivalent base changes. -/
theorem Equivalent.baseChange {r r' : Representative (↥K₀) K a a'} (h : r.Equivalent r') :
    (r.baseChange K₀ K₁ h₀₁ hK₁ ha ha').Equivalent (r'.baseChange K₀ K₁ h₀₁ hK₁ ha ha') := by
  intro y hy
  rw [baseChange_eval, baseChange_eval]
  refine h y ?_
  have hy' := (isGenericOver_base_iff K₀ K₁ h₀₁ hK₁ ha (coe_racl_base_eq K₀ K₁ h₀₁ _)).1 hy
  refine hy'.of_le (racl_mono (k := ↥K₀) ?_)
  refine union_subset (fun w hw ↦ Or.inr (Or.inl ?_)) (fun w hw ↦ Or.inr (Or.inr ?_))
  · exact M_subset_racl_base K₀ K₁ h₀₁ r hw
  · exact M_subset_racl_base K₀ K₁ h₀₁ r' hw

/-- The graph ideal is unchanged by base change. -/
theorem graphIdeal_baseChange (r : Representative (↥K₀) K a a') :
    (r.baseChange K₀ K₁ h₀₁ hK₁ ha ha').graphIdeal = r.graphIdeal := by
  obtain ⟨rb, hrb⟩ : ∃ rb, rb = r.baseChange K₀ K₁ h₀₁ hK₁ ha ha' := ⟨_, rfl⟩
  obtain ⟨re, hre⟩ : ∃ re, re = r.extend (isAlgClosed_racl _) (hK₁.union r.isSmall).racl
      (M_le_racl_union K₀ K₁ r) := ⟨_, rfl⟩
  have hrbM : (rb.M : Set K) = ((racl (↥K₀) ((K₁ : Set K) ∪ r.M) :
      IntermediateField (↥K₀) K) : Set K) := by
    rw [hrb]
    exact coe_racl_base_M K₀ K₁ h₀₁ r
  have hreM : re.M = racl (↥K₀) ((K₁ : Set K) ∪ r.M) := by
    rw [hre]
    rfl
  obtain ⟨y, hy⟩ := exists_isGenericOver (k := ↥K₁) rb.isSmall a
  have hy₁ : IsGenericOver re.M a y := by
    rw [hreM]
    exact (isGenericOver_base_iff K₀ K₁ h₀₁ hK₁ ha hrbM).1 hy
  have e1 : rb.graphIdeal = locusIdeal (↥rb.M) (rb.graphPoint y) :=
    Representative.graphIdeal_eq rb hy
  have e2 : re.graphIdeal = r.graphIdeal := by
    rw [hre]
    exact graphIdeal_eq_of_equivalent (r.extend_equivalent _ _ _)
  have e3 : re.graphIdeal = locusIdeal (↥re.M) (re.graphPoint y) :=
    Representative.graphIdeal_eq re hy₁
  have hpt : rb.graphPoint y = re.graphPoint y := by
    unfold graphPoint
    rw [hrb, hre, baseChange_eval, extend_eval]
  rw [← hrb, ← e2, e1, e3, hpt]
  exact locusIdeal_congr _ (by rw [range_algebraMap_coe, range_algebraMap_coe, hrbM, hreM]) _

end Representative

/-! ### Base change of germs -/

namespace Germ

variable (h₀₁ : K₀ ≤ K₁) (hK₁ : IsSmall (↥K₀) (K₁ : Set K))
  (ha : IndepOver (↥K₀) ∅ (range a) (K₁ : Set K))
  (ha' : IndepOver (↥K₀) ∅ (range a') (K₁ : Set K))
include h₀₁ hK₁ ha ha'

/-- `lem:hw-basechange`: a germ over `K₀` as a germ over `K₁`. -/
def baseChange (g : Germ (↥K₀) a a') : Germ (↥K₁) a a' :=
  Quotient.map (Representative.baseChange K₀ K₁ h₀₁ hK₁ ha ha')
    (fun _ _ h ↦ Representative.Equivalent.baseChange K₀ K₁ h₀₁ hK₁ ha ha' h) g

theorem baseChange_mk (r : Representative (↥K₀) K a a') :
    Germ.baseChange K₀ K₁ h₀₁ hK₁ ha ha' (⟦r⟧ : Germ (↥K₀) a a') =
      ⟦r.baseChange K₀ K₁ h₀₁ hK₁ ha ha'⟧ := rfl

/-- The graph ideal is unchanged by base change. -/
theorem graphIdeal_baseChange (g : Germ (↥K₀) a a') :
    (g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').graphIdeal = g.graphIdeal := by
  induction g using Quotient.inductionOn with
  | h r => exact Representative.graphIdeal_baseChange K₀ K₁ h₀₁ hK₁ ha ha' r

/-- The code is unchanged by base change. -/
theorem codeSet_baseChange (g : Germ (↥K₀) a a') :
    (g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').codeSet = g.codeSet :=
  congrArg (fun I ↦ Classical.choose (exists_finset_closure_eq_idealFod I))
    (graphIdeal_baseChange K₀ K₁ h₀₁ hK₁ ha ha' g)

theorem cb_baseChange (g : Germ (↥K₀) a a') :
    (g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb = adjoin (↥K₁) (idealFod g.graphIdeal : Set K) := by
  unfold cb
  rw [graphIdeal_baseChange]

/-- The canonical base after base change is `K₁` together with the old canonical base. -/
theorem coe_cb_baseChange (g : Germ (↥K₀) a a') :
    ((g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb : Set K) =
      ((adjoin (↥K₀) ((K₁ : Set K) ∪ g.cb) : IntermediateField (↥K₀) K) : Set K) := by
  rw [cb_baseChange, coe_adjoin_base, coe_adjoin_base]
  congr 1
  have hcb : (g.cb : Set K) = ((adjoin k ((K₀ : Set K) ∪ (idealFod g.graphIdeal : Set K)) :
      IntermediateField k K) : Set K) := coe_adjoin_base K₀ _
  rw [hcb]
  refine le_antisymm (adjoin_le_iff.2 (union_subset ?_ ?_)) (adjoin_le_iff.2 (union_subset ?_ ?_))
  · exact fun w hw ↦ subset_adjoin k _ (Or.inr (Or.inl hw))
  · exact fun w hw ↦ subset_adjoin k _ (Or.inr (Or.inr (subset_adjoin k _ (Or.inr hw))))
  · exact fun w hw ↦ subset_adjoin k _ (Or.inl (h₀₁ hw))
  · refine union_subset (fun w hw ↦ subset_adjoin k _ (Or.inl hw)) (adjoin_le_iff.2 ?_)
    exact union_subset (fun w hw ↦ subset_adjoin k _ (Or.inl (h₀₁ hw)))
      (fun w hw ↦ subset_adjoin k _ (Or.inr hw))

/-- Closures over `K₁` do not see the difference between the old and new canonical bases. -/
theorem racl_cb_baseChange (g : Germ (↥K₀) a a') :
    racl (↥K₁) ((g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb : Set K) = racl (↥K₁) (g.cb : Set K) := by
  refine SetLike.coe_injective ?_
  rw [coe_racl_base_eq K₀ K₁ h₀₁, coe_racl_base_eq K₀ K₁ h₀₁, coe_cb_baseChange,
    racl_union_adjoin, ← union_assoc, union_self]

theorem indepOver_cb_baseChange_iff (g : Germ (↥K₀) a a') (W : Set K) :
    IndepOver (↥K₁) ∅ W ((g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb : Set K) ↔
      IndepOver (↥K₀) (K₁ : Set K) W (g.cb : Set K) := by
  have h1 : IndepOver (↥K₁) ∅ W ((g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb : Set K) ↔
      IndepOver (↥K₁) ∅ W (g.cb : Set K) := by
    rw [← indepOver_racl_right_iff (C := ∅) (B := ((g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb : Set K)),
      ← indepOver_racl_right_iff (C := ∅) (B := (g.cb : Set K)), empty_union, empty_union,
      racl_cb_baseChange]
  rw [h1, indepOver_base_le_iff K₀ K₁ h₀₁]

/-! ### Values -/

/-- Values at generic points are unchanged by base change (over fields with the same
carrier). -/
theorem eval_baseChange (g : Germ (↥K₀) a a') {F : IntermediateField (↥K₀) K} [IsAlgClosed (↥F)]
    (hF : IsSmall (↥K₀) (F : Set K)) (hK₁F : (K₁ : Set K) ⊆ F) (hcb : g.cb ≤ F)
    {F'' : IntermediateField (↥K₁) K} [IsAlgClosed (↥F'')] (hF'' : (F'' : Set K) = (F : Set K))
    {y : ι → K} (hy : IsGenericOver F a y) :
    (g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').eval F'' y = g.eval F y := by
  obtain ⟨r, rfl, hrM⟩ := g.exists_rep_M_eq hF hcb
  have hM'' : (r.baseChange K₀ K₁ h₀₁ hK₁ ha ha').M = F'' := by
    refine SetLike.coe_injective ?_
    rw [Representative.baseChange_M, hrM, coe_racl_base_of_le K₀ K₁ h₀₁ F hK₁F, hF'']
  have hyr : IsGenericOver r.M a y := by
    rw [hrM]
    exact hy
  have hy'' : IsGenericOver (r.baseChange K₀ K₁ h₀₁ hK₁ ha ha').M a y := by
    rw [hM'']
    exact (isGenericOver_base_iff K₀ K₁ h₀₁ hK₁ ha hF'').2 hy
  have hcb'' : Germ.cb (⟦r.baseChange K₀ K₁ h₀₁ hK₁ ha ha'⟧ : Germ (↥K₁) a a') ≤ F'' := by
    have e : Germ.cb (⟦r.baseChange K₀ K₁ h₀₁ hK₁ ha ha'⟧ : Germ (↥K₁) a a') =
        adjoin (↥K₁) (idealFod (Germ.graphIdeal (⟦r⟧ : Germ (↥K₀) a a')) : Set K) :=
      cb_baseChange K₀ K₁ h₀₁ hK₁ ha ha' ⟦r⟧
    rw [e, adjoin_le_iff]
    intro w hw
    rw [SetLike.mem_coe, ← SetLike.mem_coe, hF'']
    exact hcb (subset_adjoin (↥K₀) _ hw)
  rw [baseChange_mk, eval_eq_rep (r.baseChange K₀ K₁ h₀₁ hK₁ ha ha')
    (isSmall_base_of_coe_eq K₀ K₁ h₀₁ hF hF'') hcb'' hM''.ge hy'', eval_eq_rep r hF hcb hrM.ge hyr]
  exact Representative.baseChange_eval K₀ K₁ h₀₁ hK₁ ha ha' r y

/-- Generic values are unchanged by base change. -/
theorem evalGen_baseChange (g : Germ (↥K₀) a a') {y : ι → K} (hy : IsGen (↥K₁) a y)
    (hind : IndepOver (↥K₁) ∅ (range y) ((g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb : Set K)) :
    (g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').evalGen y = g.evalGen y := by
  have _ : IsAlgClosed ↥(racl (↥K₀) ((K₁ : Set K) ∪ g.cb)) := isAlgClosed_racl _
  have _ : IsAlgClosed ↥(racl (↥K₁) ((g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb : Set K)) :=
    isAlgClosed_racl _
  have hF : IsSmall (↥K₀) ((racl (↥K₀) ((K₁ : Set K) ∪ g.cb) :
      IntermediateField (↥K₀) K) : Set K) := (hK₁.union g.isSmall_cb).racl
  have hcb : g.cb ≤ racl (↥K₀) ((K₁ : Set K) ∪ g.cb) :=
    fun w hw ↦ subset_racl (↥K₀) _ (Or.inr hw)
  have hK₁F : (K₁ : Set K) ⊆ racl (↥K₀) ((K₁ : Set K) ∪ g.cb) :=
    fun w hw ↦ subset_racl (↥K₀) _ (Or.inl hw)
  have hF'' : ((racl (↥K₁) ((g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb : Set K) :
      IntermediateField (↥K₁) K) : Set K) =
      ((racl (↥K₀) ((K₁ : Set K) ∪ g.cb) : IntermediateField (↥K₀) K) : Set K) := by
    rw [racl_cb_baseChange, coe_racl_base_eq K₀ K₁ h₀₁]
  have hy'' : IsGenericOver (racl (↥K₁) ((g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb : Set K)) a y :=
    hy.isGenericOver_racl (g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').isSmall_cb hind
  have hyF : IsGenericOver (racl (↥K₀) ((K₁ : Set K) ∪ g.cb)) a y :=
    (isGenericOver_base_iff K₀ K₁ h₀₁ hK₁ ha hF'').1 hy''
  rw [evalGen_eq _ (g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').isSmall_cb.racl
      (fun w hw ↦ subset_racl (↥K₁) _ hw) hy'',
    evalGen_eq g hF hcb hyF]
  exact eval_baseChange K₀ K₁ h₀₁ hK₁ ha ha' g hF hK₁F hcb hF'' hyF

/-! ### Conjugation -/

/-- Conjugation by an automorphism over `K₁` commutes with base change. -/
theorem map_baseChange (g : Germ (↥K₀) a a') (σ : K ≃ₐ[↥K₁] K) :
    (g.map (restrictBase K₀ K₁ h₀₁ σ)).baseChange K₀ K₁ h₀₁ hK₁ ha ha' =
      (g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').map σ := by
  apply graphIdeal_injective
  rw [graphIdeal_baseChange, graphIdeal_map, graphIdeal_map, graphIdeal_baseChange]
  rfl

end Germ

/-! ### Extensionality at a generic point -/

namespace Germ

omit [IsAlgClosed (↥K₁)] [UniversalDomain (↥K₁) K] in
/-- `lem:eval`(5): a germ is determined by its generic value at one generic point independent
from both canonical bases. -/
theorem eq_of_evalGen_eq {g g' : Germ (↥K₀) a a'} {y : ι → K} (hy : IsGen (↥K₀) a y)
    (h : IndepOver (↥K₀) ∅ (range y) ((g.cb : Set K) ∪ g'.cb)) (heq : g.evalGen y = g'.evalGen y) :
    g = g' := by
  have _ : IsAlgClosed ↥(racl (↥K₀) ((g.cb : Set K) ∪ g'.cb)) := isAlgClosed_racl _
  have hF : IsSmall (↥K₀) ((racl (↥K₀) ((g.cb : Set K) ∪ g'.cb) :
      IntermediateField (↥K₀) K) : Set K) := (g.isSmall_cb.union g'.isSmall_cb).racl
  have hcb : g.cb ≤ racl (↥K₀) ((g.cb : Set K) ∪ g'.cb) :=
    fun w hw ↦ subset_racl (↥K₀) _ (Or.inl hw)
  have hcb' : g'.cb ≤ racl (↥K₀) ((g.cb : Set K) ∪ g'.cb) :=
    fun w hw ↦ subset_racl (↥K₀) _ (Or.inr hw)
  have hyF : IsGenericOver (racl (↥K₀) ((g.cb : Set K) ∪ g'.cb)) a y :=
    hy.isGenericOver_racl (g.isSmall_cb.union g'.isSmall_cb) h
  refine eq_of_eval_eq hF hcb hcb' hyF ?_
  rw [← evalGen_eq g hF hcb hyF, ← evalGen_eq g' hF hcb' hyF, heq]

omit [IsAlgClosed (↥K₁)] [UniversalDomain (↥K₁) K] in
/-- The generic value at a point independent from the canonical base and a set `W` is
independent from the canonical base and `W`. -/
theorem indepOver_evalGen_union (g : Germ (↥K₀) a a') {y : ι → K} (hy : IsGen (↥K₀) a y)
    {W : Set K} (h : IndepOver (↥K₀) ∅ (range y) ((g.cb : Set K) ∪ W)) :
    IndepOver (↥K₀) ∅ (range (g.evalGen y)) ((g.cb : Set K) ∪ W) := by
  have h1 := indepOver_union_right_iff.1 h
  rw [empty_union] at h1
  refine indepOver_union_right_iff.2 ⟨g.indepOver_evalGen hy h1.1, ?_⟩
  rw [empty_union]
  refine (indepOver_racl_left_iff.2 h1.2).mono_left ?_
  rintro _ ⟨j, rfl⟩
  exact g.evalGen_mem_racl hy h1.1 j

end Germ

omit [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)] [IsAlgClosed K] [UniversalDomain (↥K₀) K]
  [UniversalDomain (↥K₁) K] [Finite ι] [Finite κ] in
theorem indepOver_empty_right {C A : Set K} : IndepOver k C A ∅ := fun _ _ _ ↦ by
  rw [union_empty]

/-! ### Composition, identities and inverses -/

namespace Germ

variable (h₀₁ : K₀ ≤ K₁) (hK₁ : IsSmall (↥K₀) (K₁ : Set K))
  (ha : IndepOver (↥K₀) ∅ (range a) (K₁ : Set K))
  (ha' : IndepOver (↥K₀) ∅ (range a') (K₁ : Set K))
include h₀₁ hK₁ ha ha'

/-- Composition commutes with base change. -/
theorem comp_baseChange {μ : Type*} [Finite μ] {a'' : μ → K}
    (ha'' : IndepOver (↥K₀) ∅ (range a'') (K₁ : Set K)) (g' : Germ (↥K₀) a' a'')
    (g : Germ (↥K₀) a a') :
    (Germ.comp g' g).baseChange K₀ K₁ h₀₁ hK₁ ha ha'' =
      Germ.comp (g'.baseChange K₀ K₁ h₀₁ hK₁ ha' ha'') (g.baseChange K₀ K₁ h₀₁ hK₁ ha ha') := by
  /- A point generic over `K₁` and independent over `K₁` from both canonical bases. -/
  have hW : IsSmall (↥K₁) ((g.cb : Set K) ∪ g'.cb) :=
    isSmall_base_mono K₀ K₁ h₀₁ (g.isSmall_cb.union g'.isSmall_cb)
  obtain ⟨y, hy⟩ := exists_isGenericOver (k := ↥K₁) hW.racl a
  have hygen : IsGen (↥K₁) a y := hy.isGen
  have hyk := (isGen_base_iff K₀ K₁ h₀₁ hK₁ ha).1 hygen
  have hyW : IndepOver (↥K₁) ∅ (range y) ((g.cb : Set K) ∪ g'.cb) := by
    refine indepOver_racl_right_iff.1 ?_
    rw [empty_union]
    exact hy.indepOver
  have h : IndepOver (↥K₀) (K₁ : Set K) (range y) ((g.cb : Set K) ∪ g'.cb) := by
    exact (indepOver_base_le_iff K₀ K₁ h₀₁ _ _).1 hyW
  have hracl : IndepOver (↥K₀) (K₁ : Set K) (range y)
      (racl (↥K₀) ((K₁ : Set K) ∪ ((g.cb : Set K) ∪ g'.cb)) : Set K) :=
    indepOver_racl_right_iff.2 h
  have hyg : IndepOver (↥K₁) ∅ (range y) ((g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb : Set K) :=
    (indepOver_cb_baseChange_iff K₀ K₁ h₀₁ hK₁ ha ha' g _).2 (h.mono_right subset_union_left)
  have hyg' : IndepOver (↥K₁) ∅ (range y) ((g'.baseChange K₀ K₁ h₀₁ hK₁ ha' ha'').cb : Set K) :=
    (indepOver_cb_baseChange_iff K₀ K₁ h₀₁ hK₁ ha' ha'' g' _).2 (h.mono_right subset_union_right)
  have hcbsub : ((g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb : Set K) ∪
      (g'.baseChange K₀ K₁ h₀₁ hK₁ ha' ha'').cb ⊆
      racl (↥K₀) ((K₁ : Set K) ∪ ((g.cb : Set K) ∪ g'.cb)) := by
    rw [coe_cb_baseChange, coe_cb_baseChange]
    refine union_subset ((adjoin_le_racl (↥K₀) _).trans (racl_mono (k := ↥K₀) ?_))
      ((adjoin_le_racl (↥K₀) _).trans (racl_mono (k := ↥K₀) ?_))
    · exact union_subset (fun w hw ↦ Or.inl hw) (fun w hw ↦ Or.inr (Or.inl hw))
    · exact union_subset (fun w hw ↦ Or.inl hw) (fun w hw ↦ Or.inr (Or.inr hw))
  have hyW'' : IndepOver (↥K₁) ∅ (range y)
      (((g'.baseChange K₀ K₁ h₀₁ hK₁ ha' ha'').cb : Set K) ∪
        (g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb) := by
    rw [indepOver_base_le_iff K₀ K₁ h₀₁, union_comm]
    exact hracl.mono_right hcbsub
  /- Independence from the canonical bases of the two composites. -/
  have hlhs : IndepOver (↥K₁) ∅ (range y)
      (((Germ.comp g' g).baseChange K₀ K₁ h₀₁ hK₁ ha ha'').cb : Set K) := by
    rw [indepOver_cb_baseChange_iff]
    refine hracl.mono_right ((cb_comp_le_racl g' g).trans (racl_mono (k := ↥K₀) ?_))
    exact fun w hw ↦ Or.inr hw
  /- The generic values agree. -/
  have hyk' : IndepOver (↥K₀) ∅ (range y) ((g'.cb : Set K) ∪ g.cb) := by
    have h2 : IndepOver (↥K₀) ∅ (range y) ((K₁ : Set K) ∪ ((g.cb : Set K) ∪ g'.cb)) :=
      indepOver_union_right_iff.2 ⟨hyk.2, by rw [empty_union]; exact h⟩
    exact h2.mono_right
      (union_subset (fun w hw ↦ Or.inr (Or.inr hw)) (fun w hw ↦ Or.inr (Or.inl hw)))
  have hyW₂ : IndepOver (↥K₁) ∅ (range y) (((g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb : Set K) ∪
      (g'.baseChange K₀ K₁ h₀₁ hK₁ ha' ha'').cb) := by
    rw [union_comm]
    exact hyW''
  have hz : IsGen (↥K₁) a' (g.evalGen y) := by
    have hz := isGen_evalGen (g.baseChange K₀ K₁ h₀₁ hK₁ ha ha') hygen hyg
    rwa [evalGen_baseChange K₀ K₁ h₀₁ hK₁ ha ha' g hygen hyg] at hz
  have hzind : IndepOver (↥K₁) ∅ (range (g.evalGen y))
      ((g'.baseChange K₀ K₁ h₀₁ hK₁ ha' ha'').cb : Set K) := by
    have hz := (indepOver_evalGen_union K₁ (g.baseChange K₀ K₁ h₀₁ hK₁ ha ha') hygen
      hyW₂).mono_right (subset_union_right (s := ((g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').cb : Set K)))
    rwa [evalGen_baseChange K₀ K₁ h₀₁ hK₁ ha ha' g hygen hyg] at hz
  refine eq_of_evalGen_eq K₁ hygen (hy.indepOver.mono_right (union_subset ?_ ?_)) ?_
  · rw [coe_cb_baseChange, coe_racl_base_eq K₀ K₁ h₀₁]
    refine (adjoin_le_racl (↥K₀) _).trans (racl_le_of_subset_racl (union_subset ?_ ?_))
    · exact fun w hw ↦ subset_racl (↥K₀) _ (Or.inl hw)
    · exact (cb_comp_le_racl g' g).trans (racl_mono (k := ↥K₀) fun w hw ↦ Or.inr hw)
  · refine (cb_comp_le_racl _ _).trans (racl_le_of_subset_racl ?_)
    rw [coe_racl_base_eq K₀ K₁ h₀₁]
    exact hcbsub
  · calc ((Germ.comp g' g).baseChange K₀ K₁ h₀₁ hK₁ ha ha'').evalGen y
        = (Germ.comp g' g).evalGen y := evalGen_baseChange K₀ K₁ h₀₁ hK₁ ha ha'' _ hygen hlhs
      _ = g'.evalGen (g.evalGen y) := evalGen_comp g' g hyk.1 hyk'
      _ = (g'.baseChange K₀ K₁ h₀₁ hK₁ ha' ha'').evalGen (g.evalGen y) :=
          (evalGen_baseChange K₀ K₁ h₀₁ hK₁ ha' ha'' g' hz hzind).symm
      _ = (g'.baseChange K₀ K₁ h₀₁ hK₁ ha' ha'').evalGen
            ((g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').evalGen y) := by
          rw [evalGen_baseChange K₀ K₁ h₀₁ hK₁ ha ha' g hygen hyg]
      _ = (Germ.comp (g'.baseChange K₀ K₁ h₀₁ hK₁ ha' ha'')
            (g.baseChange K₀ K₁ h₀₁ hK₁ ha ha')).evalGen y :=
          (evalGen_comp _ _ hygen hyW'').symm

omit ha' in
/-- Identity germs are compatible with base change. -/
theorem id_baseChange :
    (Germ.id (k := ↥K₀) a).baseChange K₀ K₁ h₀₁ hK₁ ha ha = Germ.id (k := ↥K₁) a := by
  have _ : IsAlgClosed ↥(racl (↥K₀) (K₁ : Set K)) := isAlgClosed_racl _
  have _ : IsAlgClosed ↥(racl (↥K₁) (∅ : Set K)) := isAlgClosed_racl _
  obtain ⟨y, hy⟩ :=
    exists_isGenericOver (k := ↥K₁) (IsSmall.of_finite (k := ↥K₁) finite_empty).racl a
  have hygen : IsGen (↥K₁) a y := hy.isGen
  have hyk := (isGen_base_iff K₀ K₁ h₀₁ hK₁ ha).1 hygen
  have hy0 : IndepOver (↥K₁) ∅ (range y) (racl (↥K₁) (∅ : Set K) : Set K) := hy.indepOver
  have hK₁racl : (racl (↥K₀) (K₁ : Set K) : Set K) ⊆ racl (↥K₁) (∅ : Set K) := by
    rw [coe_racl_base_self K₀ K₁ h₀₁, racl_base_coe K₁, union_empty]
    exact subset_racl k _
  have hidcb : IndepOver (↥K₁) ∅ (range y)
      (((Germ.id a).baseChange K₀ K₁ h₀₁ hK₁ ha ha).cb : Set K) := by
    rw [indepOver_cb_baseChange_iff]
    have h0 : IndepOver (↥K₀) (K₁ : Set K) (range y)
        (racl (↥K₀) ((K₁ : Set K) ∪ ∅) : Set K) :=
      indepOver_racl_right_iff.2 indepOver_empty_right
    rw [union_empty] at h0
    exact h0.mono_right (cb_id_le a _)
  refine eq_of_evalGen_eq K₁ hygen (hy0.mono_right (union_subset ?_ ?_)) ?_
  · rw [coe_cb_baseChange]
    exact fun w hw ↦ hK₁racl (racl_le_of_subset_racl
      (union_subset (subset_racl (↥K₀) _) (cb_id_le a _)) (adjoin_le_racl (↥K₀) _ hw))
  · exact cb_id_le a _
  · rw [evalGen_baseChange K₀ K₁ h₀₁ hK₁ ha ha _ hygen hidcb, evalGen_id hyk.1, evalGen_id hygen]

/-- Inverses are compatible with base change. -/
theorem IsInverse.baseChange {h : Germ (↥K₀) a' a} {g : Germ (↥K₀) a a'} (hi : IsInverse h g) :
    IsInverse (h.baseChange K₀ K₁ h₀₁ hK₁ ha' ha) (g.baseChange K₀ K₁ h₀₁ hK₁ ha ha') :=
  ⟨by rw [← comp_baseChange K₀ K₁ h₀₁ hK₁ ha ha' ha h g, hi.1, id_baseChange],
    by rw [← comp_baseChange K₀ K₁ h₀₁ hK₁ ha' ha ha' g h, hi.2, id_baseChange]⟩

/-- Invertibility is compatible with base change. -/
theorem IsInvertible.baseChange {g : Germ (↥K₀) a a'} (hg : IsInvertible g) :
    IsInvertible (g.baseChange K₀ K₁ h₀₁ hK₁ ha ha') := by
  obtain ⟨h, hi⟩ := hg
  exact ⟨_, hi.baseChange K₀ K₁ h₀₁ hK₁ ha ha'⟩

end Germ

end

end GroupConfig
