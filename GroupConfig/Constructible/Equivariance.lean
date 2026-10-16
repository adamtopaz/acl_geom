/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Constructible.GroupPresentation

/-!
# Equivariance of the actual group presentation

The family `F` of the constructible presentation has coefficients in the base field `k`, so an
automorphism `σ` over `k` carries admissible parameters to admissible parameters, with
parameter germs mapped by `σ` (`QuasiRational.parameterGerm_comp_algEquiv`). The same holds for
invertible pairs and their pair germs, the literal pair domain, and the presentation map into the
actual Hrushovski–Weil group (`QuasiRational.val_pairDomainMap_comp_algEquiv`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** proved (#21). Named consumer:
`GroupConfig.Germ.IsHWBij.exists_constructible_slLift`, whose canonical-base comparison uses
this equivariance of the actual presentation map. The full action classification remains open.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
  [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
  {μ ι κ : Type w} [Finite μ] [Finite ι] [Finite κ]
  {a : ι → K} {a' : κ → K}

attribute [local instance] isAlgClosed_racl

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite μ] [Finite ι] [Finite κ] in
private theorem racl_range_comp (σ : K ≃ₐ[k] K) (u : μ → K) :
    racl k (range (⇑σ ∘ u)) = (racl k (range u)).map σ.toAlgHom := by
  rw [racl_map, range_comp]

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite μ] [Finite ι] [Finite κ] in
/-- A point generic over the image of the parameter closure comes from a generic point. -/
private theorem isGenericOver_symm_comp (σ : K ≃ₐ[k] K) {u : μ → K} {b : ι → K} {y : ι → K}
    (hy : IsGenericOver (racl k (range (⇑σ ∘ u))) b y) :
    IsGenericOver (racl k (range u)) b (⇑σ.symm ∘ y) := by
  have hyy : y = ⇑σ ∘ (⇑σ.symm ∘ y) := by
    funext i
    simp
  rw [← isGenericOver_map_iff σ, ← hyy, ← racl_range_comp]
  exact hy

namespace QuasiRational

variable (F : QuasiRational k (μ ⊕ ι) κ)

omit [IsAlgClosed k] [UniversalDomain k K] [Finite μ] [Finite ι] [Finite κ] in
/-- Admissibility is invariant under automorphisms over `k`. -/
theorem isAdmissible_comp_algEquiv (σ : K ≃ₐ[k] K) {u : μ → K} (hu : F.IsAdmissible a a' u) :
    F.IsAdmissible a a' (⇑σ ∘ u) := by
  intro y hy
  have hy₀ := isGenericOver_symm_comp σ hy
  have hsum : Sum.elim (⇑σ ∘ u) y = ⇑σ ∘ Sum.elim u (⇑σ.symm ∘ y) := by
    funext i
    cases i <;> simp
  obtain ⟨hdef, hgen⟩ := hu _ hy₀
  rw [hsum, F.isDefinedAt_comp_iff, F.eval_comp, racl_range_comp]
  exact ⟨hdef, (isGenericOver_map_iff σ _ a' _).2 hgen⟩

/-- **Parameter germs are equivariant.** -/
theorem parameterGerm_comp_algEquiv (σ : K ≃ₐ[k] K) {u : μ → K} (hu : F.IsAdmissible a a' u) :
    F.parameterGerm (F.isAdmissible_comp_algEquiv σ hu) = (F.parameterGerm hu).map σ := by
  have hN : IsSmall k ((racl k (range (⇑σ ∘ u)) : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite (finite_range _)).racl
  have hM : IsSmall k ((racl k (range u) : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite (finite_range _)).racl
  obtain ⟨y, hy⟩ := exists_isGenericOver hN a
  have hcb : ((F.parameterGerm hu).map σ).cb ≤ racl k (range (⇑σ ∘ u)) := by
    rw [Germ.cb_map, racl_range_comp]
    exact IntermediateField.map_mono _ (F.cb_parameterGerm_le hu)
  refine Germ.eq_of_eval_eq hN (F.cb_parameterGerm_le _) hcb hy ?_
  have hy₀ := isGenericOver_symm_comp σ hy
  have hyy : ⇑σ ∘ (⇑σ.symm ∘ y) = y := by
    funext i
    simp
  have h := (F.parameterGerm hu).eval_map σ hM (F.cb_parameterGerm_le hu) hy₀
  rw [hyy, ← racl_range_comp, F.eval_parameterGerm hu hy₀, ← F.eval_comp] at h
  rw [F.eval_parameterGerm _ hy, h]
  congr 1
  funext i
  cases i <;> simp

variable [Fintype μ]

/-- Invertible pairs are invariant under automorphisms over `k`. -/
theorem isInvertiblePair_comp_algEquiv (σ : K ≃ₐ[k] K) {d : (μ ⊕ μ) → K}
    (hd : F.IsInvertiblePair a a' d) : F.IsInvertiblePair a a' (⇑σ ∘ d) := by
  obtain ⟨⟨hu₁, hi₁⟩, ⟨hu₂, hi₂⟩⟩ := hd
  refine ⟨⟨F.isAdmissible_comp_algEquiv σ hu₁, ?_⟩, ⟨F.isAdmissible_comp_algEquiv σ hu₂, ?_⟩⟩
  · rw [F.parameterGerm_comp_algEquiv σ hu₁]
    exact hi₁.map σ
  · rw [F.parameterGerm_comp_algEquiv σ hu₂]
    exact hi₂.map σ

/-- **Pair germs are equivariant.** -/
theorem pairGerm_comp_algEquiv (σ : K ≃ₐ[k] K) {d : (μ ⊕ μ) → K}
    (hd : F.IsInvertiblePair a a' d) (hd' : F.IsInvertiblePair a a' (⇑σ ∘ d)) :
    F.pairGerm hd' = (F.pairGerm hd).map σ := by
  have h₁ : F.parameterGerm hd'.1.choose = (F.parameterGerm hd.1.choose).map σ :=
    F.parameterGerm_comp_algEquiv σ hd.1.choose
  have h₂ : F.parameterGerm hd'.2.choose = (F.parameterGerm hd.2.choose).map σ :=
    F.parameterGerm_comp_algEquiv σ hd.2.choose
  have hinv : Classical.choose hd'.1.choose_spec =
      (Classical.choose hd.1.choose_spec).map σ := by
    refine (Classical.choose_spec hd'.1.choose_spec).unique ?_
    rw [h₁]
    exact (Classical.choose_spec hd.1.choose_spec).map σ
  change Germ.comp (Classical.choose hd'.1.choose_spec) (F.parameterGerm hd'.2.choose) =
    (Germ.comp (Classical.choose hd.1.choose_spec) (F.parameterGerm hd.2.choose)).map σ
  rw [hinv, h₂, Germ.comp_map]

variable (M : IntermediateField k K) (hM : IsSmall k (M : Set K))
  {f₀ : Germ k a a'} (hb : Germ.IsHWBij f₀) {δ₀ : Germ k a a}
  (hδ₀ : δ₀ ∈ Germ.diffSet f₀) {c : μ → K}
  (hc : adjoin k (range c) = f₀.cb)
  (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
    F.parameterGerm hu = f₀.map σ)
  (hdim : erk k ∅ (range a) = erk k ∅ (range a'))

include hM hb hδ₀ hc hF hdim in
/-- The literal pair domain is invariant under automorphisms over `k`. -/
theorem comp_algEquiv_mem_pairDomain (σ : K ≃ₐ[k] K) {d : (μ ⊕ μ) → K}
    (hd : d ∈ F.pairDomain M c a a') : ⇑σ ∘ d ∈ F.pairDomain M c a a' := by
  have hd' := F.isInvertiblePair_comp_algEquiv σ hd.choose
  refine (F.mem_pairDomain_iff M hM hb hδ₀ hc hF hdim hd').2 ?_
  rw [F.pairGerm_comp_algEquiv σ hd.choose hd']
  exact Germ.IsHW.map_mem_prodSet ((F.mem_pairDomain_iff M hM hb hδ₀ hc hF hdim hd.choose).1 hd) σ

/-- **The presentation map is equivariant**: the image of `σ ∘ d` is the `σ`-image of the image
of `d`. -/
theorem val_pairDomainMap_comp_algEquiv (σ : K ≃ₐ[k] K) (d : F.pairDomain M c a a') :
    (hb.isHW hδ₀).val (F.pairDomainMap M hM hb hδ₀ hc hF hdim
        ⟨⇑σ ∘ d.1, F.comp_algEquiv_mem_pairDomain M hM hb hδ₀ hc hF hdim σ d.2⟩) =
      ((hb.isHW hδ₀).val (F.pairDomainMap M hM hb hδ₀ hc hF hdim d)).map σ := by
  rw [F.val_pairDomainMap, F.val_pairDomainMap]
  exact F.pairGerm_comp_algEquiv σ d.2.choose _

end QuasiRational

end

end GroupConfig
