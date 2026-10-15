/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Constructible.GroupPresentation
import GroupConfig.Constructible.SpaceWords

/-!
# The actual constructible homogeneous-space presentation

Blueprint `sources/group_configuration/09-constructibility.tex`.

The four- and six-letter stabilizer words identify the actual equality and action
relations of the total orbit map on the homogeneous space. One internally chosen pair of
sampling stages gives the group, all generic-point stabilizers and the full constructible
G-set presentation over the literal fields of the source.

**Status:** `thm:constructible` is proved for an actual orbit family of Hrushovski–Weil
bijections. `CanonicalPresentation` chooses that family on the actual canonical code.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
  [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
  {μ ι κ : Type w} [Fintype μ] [Fintype ι] [Finite κ]
  {a : ι → K} {a' : κ → K}

namespace QuasiRational

variable (F : QuasiRational k (μ ⊕ ι) κ)
  (M : IntermediateField k K) (hM : IsSmall k (M : Set K))
  {f₀ : Germ k a a'} (hb : Germ.IsHWBij f₀) {δ₀ : Germ k a a}
  (hδ₀ : δ₀ ∈ Germ.diffSet f₀) {c : μ → K}
  (hc : adjoin k (range c) = f₀.cb)
  (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
    F.parameterGerm hu = f₀.map σ)
  (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
  {L₀ : IntermediateField k K} (hL₀ : IsSmall k (L₀ : Set K))
  (hFt : HasGenericSamples L₀ a' (Fintype.card μ))
  {α : Type*} [Fintype α] (t : α → μ → K) (ht : ∀ i, IsGenericOver L₀ c (t i))
  (hind : erk k (L₀ : Set K) (⋃ i, range (t i)) = ∑ i, erk k (L₀ : Set K) (range (t i)))
  {y₀ : ι → K} (hy₀ : IsGen k a y₀)

include hL₀ hFt ht hind

/-- `thm:constructible`(2): the equality relation of the actual total orbit
map is constructible, by the four-letter stabilizer word. No independence
of the generic base point from the candidate parameters is assumed. -/
theorem isConstructibleOver_pairSpaceKernel
    (hsrc : HasGenericSamples L₀ a (Fintype.card ((((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ μ) ⊕ μ)))
    (hr : 2 * Fintype.card (((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ ι) + 1 ≤ Fintype.card α)
    (hD : IsConstructibleOver (↥(adjoin k (((L₀ : Set K) ∪ ⋃ i, range (t i)) ∪ range y₀)))
      (F.pairDomain M c a a')) :
    IsConstructibleOver (↥(adjoin k (((L₀ : Set K) ∪ ⋃ i, range (t i)) ∪ range y₀)))
      {d : ((μ ⊕ μ) ⊕ (μ ⊕ μ)) → K |
        ∃ (hL : d ∘ Sum.inl ∈ F.pairDomain M c a a')
          (hR : d ∘ Sum.inr ∈ F.pairDomain M c a a'),
          F.pairDomainSpaceMap M hM hb hδ₀ hc hF hdim hy₀ ⟨d ∘ Sum.inl, hL⟩ =
            F.pairDomainSpaceMap M hM hb hδ₀ hc hF hdim hy₀ ⟨d ∘ Sum.inr, hR⟩} := by
  let hw := hb.isHW hδ₀
  let ρ := F.pairDomainMap M hM hb hδ₀ hc hF hdim
  let D := {d : ((μ ⊕ μ) ⊕ (μ ⊕ μ)) → K |
    d ∘ Sum.inl ∈ F.pairDomain M c a a' ∧ d ∘ Sum.inr ∈ F.pairDomain M c a a'}
  let Γ : D → ↥hw.prodSubgroup := fun d ↦
    (ρ ⟨d.val ∘ Sum.inl, d.property.1⟩)⁻¹ * ρ ⟨d.val ∘ Sum.inr, d.property.2⟩
  have hDD : IsConstructibleOver
      (↥(adjoin k (((L₀ : Set K) ∪ ⋃ i, range (t i)) ∪ range y₀))) D :=
    (hD.preimage_comp Sum.inl).inter (hD.preimage_comp Sum.inr)
  have hrep : ∀ d : D, (F.spaceKernelWord hdim).IsGerm d (hw.val (Γ d)) := by
    intro d
    change (F.spaceKernelWord hdim).IsGerm d.val
      (hw.val ((ρ ⟨d.val ∘ Sum.inl, d.property.1⟩)⁻¹ *
        ρ ⟨d.val ∘ Sum.inr, d.property.2⟩))
    rw [hw.val_mul, F.val_pairDomainMap_inv M hM hb hδ₀ hc hF hdim,
      F.val_pairDomainMap M hM hb hδ₀ hc hF hdim]
    exact F.isGerm_spaceKernelWord hdim d.property.1.choose d.property.2.choose
  have hInv : ∀ d : D, (F.spaceKernelWord hdim).IsInvertiblyAdmissible d := fun d ↦
    (F.isInvertiblyAdmissible_spaceKernelWord_iff hdim d).2
      ⟨d.property.1.choose, d.property.2.choose⟩
  have hS := F.isConstructibleOver_wordStabilizer c (F.spaceKernelWord hdim) hdim hb hδ₀ hc hF
    hL₀ (F.hasSamples_spaceKernelWord hdim hFt) hFt hsrc t ht hind hr hy₀ hDD Γ hrep hInv
  convert hS using 1
  ext d
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hL, hR, heq⟩
    refine ⟨⟨hL, hR⟩, ?_⟩
    change ((ρ ⟨d ∘ Sum.inl, hL⟩)⁻¹ * ρ ⟨d ∘ Sum.inr, hR⟩) • hw.iota hy₀ = hw.iota hy₀
    rw [mul_smul, inv_smul_eq_iff]
    exact heq.symm
  · rintro ⟨hd, hfix⟩
    refine ⟨hd.1, hd.2, ?_⟩
    change ((ρ ⟨d ∘ Sum.inl, hd.1⟩)⁻¹ * ρ ⟨d ∘ Sum.inr, hd.2⟩) • hw.iota hy₀ =
      hw.iota hy₀ at hfix
    rw [mul_smul, inv_smul_eq_iff] at hfix
    exact hfix.symm

/-- `thm:constructible`(2): the actual action relation on three domain
points is constructible, by the six-letter stabilizer word. -/
theorem isConstructibleOver_pairSpaceAction
    (hsrc : HasGenericSamples L₀ a
      (Fintype.card (((((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ)) ⊕ μ) ⊕ μ)))
    (hr : 2 * Fintype.card ((((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ)) ⊕ ι) + 1 ≤ Fintype.card α)
    (hD : IsConstructibleOver (↥(adjoin k (((L₀ : Set K) ∪ ⋃ i, range (t i)) ∪ range y₀)))
      (F.pairDomain M c a a')) :
    IsConstructibleOver (↥(adjoin k (((L₀ : Set K) ∪ ⋃ i, range (t i)) ∪ range y₀)))
      {d : (((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ)) → K |
        ∃ (hG : (d ∘ Sum.inl) ∘ Sum.inl ∈ F.pairDomain M c a a')
          (hX : (d ∘ Sum.inl) ∘ Sum.inr ∈ F.pairDomain M c a a')
          (hT : d ∘ Sum.inr ∈ F.pairDomain M c a a'),
          F.pairDomainMap M hM hb hδ₀ hc hF hdim ⟨(d ∘ Sum.inl) ∘ Sum.inl, hG⟩ •
            F.pairDomainSpaceMap M hM hb hδ₀ hc hF hdim hy₀ ⟨(d ∘ Sum.inl) ∘ Sum.inr, hX⟩ =
              F.pairDomainSpaceMap M hM hb hδ₀ hc hF hdim hy₀ ⟨d ∘ Sum.inr, hT⟩} := by
  let hw := hb.isHW hδ₀
  let ρ := F.pairDomainMap M hM hb hδ₀ hc hF hdim
  let D := {d : (((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ)) → K |
    (d ∘ Sum.inl) ∘ Sum.inl ∈ F.pairDomain M c a a' ∧
      (d ∘ Sum.inl) ∘ Sum.inr ∈ F.pairDomain M c a a' ∧
        d ∘ Sum.inr ∈ F.pairDomain M c a a'}
  let Γ : D → ↥hw.prodSubgroup := fun d ↦
    (ρ ⟨d.val ∘ Sum.inr, d.property.2.2⟩)⁻¹ *
      (ρ ⟨(d.val ∘ Sum.inl) ∘ Sum.inl, d.property.1⟩ *
        ρ ⟨(d.val ∘ Sum.inl) ∘ Sum.inr, d.property.2.1⟩)
  have hDD : IsConstructibleOver
      (↥(adjoin k (((L₀ : Set K) ∪ ⋃ i, range (t i)) ∪ range y₀))) D :=
    (hD.preimage_comp (Sum.inl ∘ Sum.inl)).inter
      ((hD.preimage_comp (Sum.inl ∘ Sum.inr)).inter (hD.preimage_comp Sum.inr))
  have hrep : ∀ d : D, (F.spaceActionWord hdim).IsGerm d (hw.val (Γ d)) := by
    intro d
    change (F.spaceActionWord hdim).IsGerm d.val
      (hw.val ((ρ ⟨d.val ∘ Sum.inr, d.property.2.2⟩)⁻¹ *
        (ρ ⟨(d.val ∘ Sum.inl) ∘ Sum.inl, d.property.1⟩ *
          ρ ⟨(d.val ∘ Sum.inl) ∘ Sum.inr, d.property.2.1⟩)))
    rw [hw.val_mul, hw.val_mul, F.val_pairDomainMap_inv M hM hb hδ₀ hc hF hdim,
      F.val_pairDomainMap M hM hb hδ₀ hc hF hdim,
      F.val_pairDomainMap M hM hb hδ₀ hc hF hdim]
    exact F.isGerm_spaceActionWord hdim d.property.1.choose d.property.2.1.choose
      d.property.2.2.choose
  have hInv : ∀ d : D, (F.spaceActionWord hdim).IsInvertiblyAdmissible d := fun d ↦
    (F.isInvertiblyAdmissible_spaceActionWord_iff hdim d).2
      ⟨d.property.1.choose, d.property.2.1.choose, d.property.2.2.choose⟩
  have hS := F.isConstructibleOver_wordStabilizer c (F.spaceActionWord hdim) hdim hb hδ₀ hc hF
    hL₀ (F.hasSamples_spaceActionWord hdim hFt) hFt hsrc t ht hind hr hy₀ hDD Γ hrep hInv
  convert hS using 1
  ext d
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hG, hX, hT, heq⟩
    refine ⟨⟨hG, hX, hT⟩, ?_⟩
    change ((ρ ⟨d ∘ Sum.inr, hT⟩)⁻¹ *
      (ρ ⟨(d ∘ Sum.inl) ∘ Sum.inl, hG⟩ * ρ ⟨(d ∘ Sum.inl) ∘ Sum.inr, hX⟩)) •
      hw.iota hy₀ = hw.iota hy₀
    rw [mul_smul, inv_smul_eq_iff, mul_smul]
    exact heq
  · rintro ⟨hd, hfix⟩
    refine ⟨hd.1, hd.2.1, hd.2.2, ?_⟩
    change ((ρ ⟨d ∘ Sum.inr, hd.2.2⟩)⁻¹ *
      (ρ ⟨(d ∘ Sum.inl) ∘ Sum.inl, hd.1⟩ * ρ ⟨(d ∘ Sum.inl) ∘ Sum.inr, hd.2.1⟩)) •
      hw.iota hy₀ = hw.iota hy₀ at hfix
    rw [mul_smul, inv_smul_eq_iff, mul_smul] at hfix
    exact hfix

/-- `thm:constructible`(2), relative to the actual common sampling fields:
the total orbit map presents the homogeneous space as a constructible G-set.
Named consumer: the internally sampled group-and-space theorem below. -/
theorem constructibleGSetPresentation_pairDomain
    (hsrc : HasGenericSamples L₀ a
      (Fintype.card (((((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ)) ⊕ μ) ⊕ μ)))
    (hr : 2 * Fintype.card ((((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ)) ⊕ ι) + 1 ≤ Fintype.card α)
    (hG : ConstructibleGroupPresentation
      (adjoin k (((L₀ : Set K) ∪ ⋃ i, range (t i)) ∪ range y₀))
      (F.pairDomain M c a a') (F.pairDomainMap M hM hb hδ₀ hc hF hdim)) :
    ConstructibleGSetPresentation (adjoin k (((L₀ : Set K) ∪ ⋃ i, range (t i)) ∪ range y₀))
      (F.pairDomain M c a a') (F.pairDomainMap M hM hb hδ₀ hc hF hdim)
      (F.pairDomain M c a a') (F.pairDomainSpaceMap M hM hb hδ₀ hc hF hdim hy₀) := by
  have hs6 : HasGenericSamples L₀ a
      (Fintype.card ((((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ μ) ⊕ μ)) :=
    hsrc.of_le (by simp only [Fintype.card_sum]; omega)
  have hr4 : 2 * Fintype.card (((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ ι) + 1 ≤ Fintype.card α := by
    simp only [Fintype.card_sum] at hr ⊢
    omega
  exact ⟨hG, hG.domain, F.pairDomainSpaceMap_surjective M hM hb hδ₀ hc hF hdim hy₀,
    F.isConstructibleOver_pairSpaceKernel M hM hb hδ₀ hc hF hdim hL₀ hFt t ht hind hy₀ hs6 hr4
      hG.domain,
    F.isConstructibleOver_pairSpaceAction M hM hb hδ₀ hc hF hdim hL₀ hFt t ht hind hy₀ hsrc hr
      hG.domain⟩

omit hL₀ hFt ht hind

/-- `thm:constructible`: one internally chosen pair of sampling stages
presents the actual group, every generic-point stabilizer, and the actual
homogeneous space, retaining the source provenance, rank and freshness.
No sample or constructible-presentation certificate is an input. -/
theorem exists_fresh_constructibleGroupSpacePresentation
    (F : QuasiRational k (μ ⊕ ι) κ) {f₀ : Germ k a a'} (hb : Germ.IsHWBij f₀) {δ₀ : Germ k a a}
    (hδ₀ : δ₀ ∈ Germ.diffSet f₀) {c : μ → K} (hc : adjoin k (range c) = f₀.cb)
    (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
      F.parameterGerm hu = f₀.map σ)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) (M₀ : IntermediateField k K)
    (hM₀ : IsSmall k (M₀ : Set K)) :
    ∃ (S₀ : Set K) (t₁ : Fin (2 * (6 * Fintype.card μ + Fintype.card ι) + 1) → μ → K),
      S₀.Finite ∧ IndepOver k ∅ S₀ (M₀ : Set K) ∧
      (∃ T : List (Σ τ : Type w, (τ → K) × (τ → K)),
        (∀ p ∈ T, ((⟨p.1, p.2.1⟩ : Σ τ : Type w, τ → K) = ⟨ι, a⟩ ∨
            (⟨p.1, p.2.1⟩ : Σ τ : Type w, τ → K) = ⟨κ, a'⟩) ∧
          IsGenericOver (⊥ : IntermediateField k K) p.2.1 p.2.2) ∧
        S₀ = (⋃ p ∈ T, range p.2.2) ∧
        erk k ∅ S₀ = (T.map fun p ↦ erk k ∅ (range p.2.2)).sum) ∧
      HasGenericSamples (adjoin k S₀) a (8 * Fintype.card μ) ∧
      HasGenericSamples (adjoin k S₀) a' (Fintype.card μ) ∧
      (∀ i, IsGenericOver (⊥ : IntermediateField k K) c (t₁ i)) ∧
      (∀ i, IsGenericOver (adjoin k S₀) c (t₁ i)) ∧
      erk k (adjoin k S₀ : Set K) (⋃ i, range (t₁ i)) =
        ∑ i, erk k (adjoin k S₀ : Set K) (range (t₁ i)) ∧
      IndepOver k ∅ (S₀ ∪ ⋃ i, range (t₁ i)) (M₀ : Set K) ∧
      erk k ∅ (S₀ ∪ ⋃ i, range (t₁ i)) = erk k ∅ S₀ + ∑ i, erk k ∅ (range (t₁ i)) ∧
      ∃ hL : IsSmall k ((adjoin k (S₀ ∪ ⋃ i, range (t₁ i)) : IntermediateField k K) : Set K),
        ConstructibleGroupPresentation (adjoin k (S₀ ∪ ⋃ i, range (t₁ i)))
          (F.pairDomain (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) c a a')
          (F.pairDomainMap (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) hL hb hδ₀ hc hF hdim) ∧
        ∀ (y₀ : ι → K) (hy₀ : IsGen k a y₀),
          IsConstructibleOver (↥(adjoin k ((S₀ ∪ ⋃ i, range (t₁ i)) ∪ range y₀)))
            {d | ∃ hd : d ∈ F.pairDomain (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) c a a',
              F.pairDomainMap (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) hL hb hδ₀ hc hF hdim
                ⟨d, hd⟩ • (hb.isHW hδ₀).iota hy₀ = (hb.isHW hδ₀).iota hy₀} ∧
          ConstructibleGSetPresentation (adjoin k ((S₀ ∪ ⋃ i, range (t₁ i)) ∪ range y₀))
            (F.pairDomain (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) c a a')
            (F.pairDomainMap (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) hL hb hδ₀ hc hF hdim)
            (F.pairDomain (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) c a a')
            (F.pairDomainSpaceMap (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) hL hb hδ₀ hc hF hdim
              hy₀) := by
  obtain ⟨S₀, t₁, hS₀, hfresh₀, hT, hsa, hsa', ht₁, ht₁L, hadd, hfresh, hrk, hL, hP, hH⟩ :=
    F.exists_fresh_constructibleGroupPresentation hb hδ₀ hc hF hdim M₀ hM₀
  have hL₀ : IsSmall k ((adjoin k S₀ : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite hS₀).racl.mono (adjoin_le_racl k S₀)
  have hsrc : HasGenericSamples (adjoin k S₀) a
      (Fintype.card (((((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ)) ⊕ μ) ⊕ μ)) :=
    hsa.of_le (by simp only [Fintype.card_sum]; omega)
  have hr : 2 * Fintype.card ((((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ)) ⊕ ι) + 1 ≤
      Fintype.card (Fin (2 * (6 * Fintype.card μ + Fintype.card ι) + 1)) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  refine ⟨S₀, t₁, hS₀, hfresh₀, hT, hsa, hsa', ht₁, ht₁L, hadd, hfresh, hrk, hL, hP,
    fun y₀ hy₀ ↦ ⟨hH y₀ hy₀, ?_⟩⟩
  have hfield : adjoin k (((adjoin k S₀ : Set K) ∪ ⋃ i, range (t₁ i)) ∪ range y₀) =
      adjoin k ((S₀ ∪ ⋃ i, range (t₁ i)) ∪ range y₀) := by
    simp only [adjoin_union, adjoin_self]
  have hGE : ConstructibleGroupPresentation
      (adjoin k (((adjoin k S₀ : Set K) ∪ ⋃ i, range (t₁ i)) ∪ range y₀))
      (F.pairDomain (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) c a a')
      (F.pairDomainMap (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) hL hb hδ₀ hc hF hdim) := by
    rw [hfield]
    exact ConstructibleGroupPresentation.of_le (adjoin.mono k _ _ subset_union_left) hP
  have h := F.constructibleGSetPresentation_pairDomain (adjoin k (S₀ ∪ ⋃ i, range (t₁ i)))
    hL hb hδ₀ hc hF hdim hL₀ hsa' t₁ ht₁L hadd hy₀ hsrc hr hGE
  rw [hfield] at h
  exact h

end QuasiRational

end

end GroupConfig
