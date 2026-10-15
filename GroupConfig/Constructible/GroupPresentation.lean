/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Constructible.GroupDomain
import GroupConfig.Constructible.PairRelations
import GroupConfig.Constructible.Presentation

/-!
# The actual constructible group presentation

Blueprint `sources/group_configuration/09-constructibility.tex`.

The literal pair domain maps surjectively into the actual Hrushovski–Weil group.
The group operations are identified through its faithful germ embedding and proved
constructible. The actual two-stage samples are chosen internally, with their provenance,
rank and freshness, and give the stabilizer preimage for every generic base point.

**Status:** `thm:constructible`(1) and the stabilizer preimage are proved for the actual family.
The full homogeneous-space presentation is in `SpacePresentation`.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
  [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
  {μ ι κ : Type w} [Fintype μ] [Finite ι] [Finite κ]
  {a : ι → K} {a' : κ → K}

namespace Germ.IsHW

/-- Taking the inverse in the actual group gives the inverse germ.
Named consumers: the group inverse relation and both homogeneous-space words. -/
theorem isInverse_val_inv {g₀ : Germ k a a} (hw : Germ.IsHW g₀)
    (γ : ↥hw.prodSubgroup) : Germ.IsInverse (hw.val γ⁻¹) (hw.val γ) := by
  constructor
  · change hw.val (γ⁻¹ * γ) = Germ.id a
    rw [inv_mul_cancel, hw.val_one]
    rfl
  · change hw.val (γ * γ⁻¹) = Germ.id a
    rw [mul_inv_cancel, hw.val_one]
    rfl

end Germ.IsHW

namespace QuasiRational

variable (F : QuasiRational k (μ ⊕ ι) κ)
  (M : IntermediateField k K) (hM : IsSmall k (M : Set K))
  {f₀ : Germ k a a'} (hb : Germ.IsHWBij f₀) {δ₀ : Germ k a a}
  (hδ₀ : δ₀ ∈ Germ.diffSet f₀) {c : μ → K}
  (hc : adjoin k (range c) = f₀.cb)
  (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
    F.parameterGerm hu = f₀.map σ)
  (hdim : erk k ∅ (range a) = erk k ∅ (range a'))

/-- The actual map from the literal pair domain to the Hrushovski–Weil group.
Named consumer: the constructible-group presentation in `thm:constructible`. -/
def pairDomainMap : F.pairDomain M c a a' → ↥(hb.isHW hδ₀).prodSubgroup :=
  fun d ↦ (hb.isHW hδ₀).ofMem (F.pairDomainGerm_mem M hM hb hδ₀ hc hF hdim d)

/-- The actual presentation map has exactly the specified pair germ.
Named consumers: the group operations and homogeneous-space word relations. -/
theorem val_pairDomainMap (d : F.pairDomain M c a a') :
    (hb.isHW hδ₀).val (F.pairDomainMap M hM hb hδ₀ hc hF hdim d) =
      F.pairDomainGerm M c a a' d := (hb.isHW hδ₀).val_ofMem _

/-- Inverting the actual group image gives the swapped pair germ.
Named consumers: the homogeneous-space kernel and action words. -/
theorem val_pairDomainMap_inv (d : F.pairDomain M c a a') :
    (hb.isHW hδ₀).val (F.pairDomainMap M hM hb hδ₀ hc hF hdim d)⁻¹ =
      F.pairGerm (d := d.val ∘ Sum.swap) ⟨d.property.choose.2, d.property.choose.1⟩ := by
  have hi := (hb.isHW hδ₀).isInverse_val_inv (F.pairDomainMap M hM hb hδ₀ hc hF hdim d)
  rw [F.val_pairDomainMap M hM hb hδ₀ hc hF hdim d] at hi
  exact hi.unique (F.isInverse_pairGerm_swap d.property.choose)

/-- The presentation map covers the actual group, using pairs constructed
from its orbit factors. -/
theorem pairDomainMap_surjective :
    Function.Surjective (F.pairDomainMap M hM hb hδ₀ hc hF hdim) := by
  intro γ
  obtain ⟨d, hd⟩ := F.exists_pairDomainGerm_eq M hM hb hδ₀ hc hF hdim
    ((hb.isHW hδ₀).val_mem γ)
  refine ⟨d, (hb.isHW hδ₀).val_injective ?_⟩
  change (hb.isHW hδ₀).val ((hb.isHW hδ₀).ofMem _) = (hb.isHW hδ₀).val γ
  rw [Germ.IsHW.val_ofMem, hd]

/-- The total orbit map on the actual homogeneous space, based at any
generic point. Named consumer: the constructible homogeneous-space presentation. -/
def pairDomainSpaceMap {y₀ : ι → K} (hy₀ : IsGen k a y₀)
    (d : F.pairDomain M c a a') : (hb.isHW hδ₀).Space :=
  F.pairDomainMap M hM hb hδ₀ hc hF hdim d • (hb.isHW hδ₀).iota hy₀

/-- Transitivity and the actual group presentation make the space map
surjective. No evaluation of a germ at a nongeneric point is used. -/
theorem pairDomainSpaceMap_surjective {y₀ : ι → K} (hy₀ : IsGen k a y₀) :
    Function.Surjective (F.pairDomainSpaceMap M hM hb hδ₀ hc hF hdim hy₀) := by
  intro s
  obtain ⟨γ, hγ⟩ := (hb.isHW hδ₀).exists_smul_eq ((hb.isHW hδ₀).iota hy₀) s
  obtain ⟨d, hd⟩ := F.pairDomainMap_surjective M hM hb hδ₀ hc hF hdim γ
  exact ⟨d, by change F.pairDomainMap M hM hb hδ₀ hc hF hdim d • _ = s; rw [hd, hγ]⟩

include hdim

/-- The literal kernel relation on actual domain points is constructible.
Named consumer: the quotient relation of the group presentation. -/
theorem isConstructibleOver_pairDomainKernel {L : IntermediateField k K}
    (hD : IsConstructibleOver (↥L) (F.pairDomain M c a a'))
    (hFt : HasGenericSamples L a' (Fintype.card μ))
    (hsrc : HasGenericSamples L a (Fintype.card ((μ ⊕ μ) ⊕ (μ ⊕ μ)))) :
    IsConstructibleOver (↥L) {d : ((μ ⊕ μ) ⊕ (μ ⊕ μ)) → K |
      ∃ (hL : d ∘ Sum.inl ∈ F.pairDomain M c a a')
        (hR : d ∘ Sum.inr ∈ F.pairDomain M c a a'),
        F.pairDomainGerm M c a a' ⟨d ∘ Sum.inl, hL⟩ =
          F.pairDomainGerm M c a a' ⟨d ∘ Sum.inr, hR⟩} := by
  convert (hD.preimage_comp Sum.inl).inter ((hD.preimage_comp Sum.inr).inter
    (F.isConstructibleOver_pairKernel hdim hFt hsrc)) using 1
  ext d
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hL, hR, heq⟩
    exact ⟨hL, hR, hL.choose, hR.choose, heq⟩
  · rintro ⟨hL, hR, _, _, heq⟩
    exact ⟨hL, hR, heq⟩

/-- The literal multiplication relation on three actual domain points is
constructible. Named consumer: the operation of the group presentation. -/
theorem isConstructibleOver_pairDomainProduct {L : IntermediateField k K}
    (hD : IsConstructibleOver (↥L) (F.pairDomain M c a a'))
    (hFt : HasGenericSamples L a' (Fintype.card μ))
    (hsrc : HasGenericSamples L a (Fintype.card (((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ)))) :
    IsConstructibleOver (↥L) {d : (((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ)) → K |
      ∃ (hL : (d ∘ Sum.inl) ∘ Sum.inl ∈ F.pairDomain M c a a')
        (hR : (d ∘ Sum.inl) ∘ Sum.inr ∈ F.pairDomain M c a a')
        (hT : d ∘ Sum.inr ∈ F.pairDomain M c a a'),
        Germ.comp (F.pairDomainGerm M c a a' ⟨(d ∘ Sum.inl) ∘ Sum.inl, hL⟩)
          (F.pairDomainGerm M c a a' ⟨(d ∘ Sum.inl) ∘ Sum.inr, hR⟩) =
            F.pairDomainGerm M c a a' ⟨d ∘ Sum.inr, hT⟩} := by
  convert (hD.preimage_comp (Sum.inl ∘ Sum.inl)).inter
    ((hD.preimage_comp (Sum.inl ∘ Sum.inr)).inter
      ((hD.preimage_comp Sum.inr).inter
        (F.isConstructibleOver_pairProduct hdim hFt hsrc))) using 1
  ext d
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hL, hR, hT, heq⟩
    exact ⟨hL, hR, hT, hL.choose, hR.choose, hT.choose, heq⟩
  · rintro ⟨hL, hR, hT, _, _, _, heq⟩
    exact ⟨hL, hR, hT, heq⟩

/-- The literal inverse relation on actual domain points is constructible.
Named consumer: the inverse operation of the group presentation. -/
theorem isConstructibleOver_pairDomainInverse {L : IntermediateField k K}
    (hD : IsConstructibleOver (↥L) (F.pairDomain M c a a'))
    (hFt : HasGenericSamples L a' (Fintype.card μ))
    (hsrc : HasGenericSamples L a (Fintype.card ((μ ⊕ μ) ⊕ (μ ⊕ μ)))) :
    IsConstructibleOver (↥L) {d : ((μ ⊕ μ) ⊕ (μ ⊕ μ)) → K |
      ∃ (hL : d ∘ Sum.inl ∈ F.pairDomain M c a a')
        (hR : d ∘ Sum.inr ∈ F.pairDomain M c a a'),
        Germ.IsInverse (F.pairDomainGerm M c a a' ⟨d ∘ Sum.inr, hR⟩)
          (F.pairDomainGerm M c a a' ⟨d ∘ Sum.inl, hL⟩)} := by
  convert (hD.preimage_comp Sum.inl).inter ((hD.preimage_comp Sum.inr).inter
    (F.isConstructibleOver_pairInverse hdim hFt hsrc)) using 1
  ext d
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hL, hR, hinv⟩
    exact ⟨hL, hR, hL.choose, hR.choose, hinv⟩
  · rintro ⟨hL, hR, _, _, hinv⟩
    exact ⟨hL, hR, hinv⟩

/-- `thm:constructible`(1), relative to one common field of actual samples:
the literal pair domain and its actual surjection present the group, with
all three relations proved internally from the word formulas. -/
theorem constructibleGroupPresentation_pairDomain {L : IntermediateField k K}
    (hD : IsConstructibleOver (↥L) (F.pairDomain M c a a'))
    (hFt : HasGenericSamples L a' (Fintype.card μ))
    (hsrc : HasGenericSamples L a (Fintype.card (((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ)))) :
    ConstructibleGroupPresentation L (F.pairDomain M c a a')
      (F.pairDomainMap M hM hb hδ₀ hc hF hdim) := by
  let hw := hb.isHW hδ₀
  let ρ := F.pairDomainMap M hM hb hδ₀ hc hF hdim
  have hval (d : F.pairDomain M c a a') : hw.val (ρ d) = F.pairDomainGerm M c a a' d :=
    hw.val_ofMem _
  have hs4 : HasGenericSamples L a (Fintype.card ((μ ⊕ μ) ⊕ (μ ⊕ μ))) :=
    hsrc.of_le (by simp only [Fintype.card_sum]; omega)
  refine ⟨hD, F.pairDomainMap_surjective M hM hb hδ₀ hc hF hdim, ?_, ?_, ?_⟩
  · convert F.isConstructibleOver_pairDomainKernel M hdim hD hFt hs4 using 1
    ext d
    simp only [Set.mem_ofPred_eq]
    refine exists_congr fun hL ↦ exists_congr fun hR ↦ ?_
    change (ρ _ = ρ _) ↔ _
    rw [← hw.val_injective.eq_iff, hval, hval]
  · convert F.isConstructibleOver_pairDomainProduct M hdim hD hFt hsrc using 1
    ext d
    simp only [Set.mem_ofPred_eq]
    refine exists_congr fun hL ↦ exists_congr fun hR ↦ exists_congr fun hT ↦ ?_
    change (ρ _ * ρ _ = ρ _) ↔ _
    rw [← hw.val_injective.eq_iff, hw.val_mul, hval, hval, hval, Germ.mul_def]
  · convert F.isConstructibleOver_pairDomainInverse M hdim hD hFt hs4 using 1
    ext d
    simp only [Set.mem_ofPred_eq]
    refine exists_congr fun hL ↦ exists_congr fun hR ↦ ?_
    have hi := hw.isInverse_val_inv
    constructor
    · intro h
      have h' := hi (ρ ⟨d ∘ Sum.inl, hL⟩)
      rw [h, hval, hval] at h'
      exact h'
    · intro h
      apply hw.val_injective
      have h' := hi (ρ ⟨d ∘ Sum.inl, hL⟩)
      rw [hval] at h'
      apply h'.unique
      change Germ.IsInverse (hw.val (ρ ⟨d ∘ Sum.inr, hR⟩)) _
      rw [hval]
      exact h

omit hdim

/-- `thm:constructible`(1) and its actual stabilizer preimage, with both
sampling stages chosen internally. All sample provenance, relative genericity,
joint rank additivity and freshness are retained. No domain constructibility
or presentation certificate is an input. -/
theorem exists_fresh_constructibleGroupPresentation [Fintype ι]
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
                ⟨d, hd⟩ • (hb.isHW hδ₀).iota hy₀ = (hb.isHW hδ₀).iota hy₀} := by
  obtain ⟨S₀, t₁, hS₀, hfresh₀, hT, hsa, hsa', ht₁, ht₁L, hadd, hfresh, hrk, hD, hH⟩ :=
    F.exists_fresh_isConstructibleOver_pairDomain_stabilizer hb hδ₀ hc hF hdim M₀ hM₀
  let L := adjoin k (S₀ ∪ ⋃ i, range (t₁ i))
  have hL : IsSmall k (L : Set K) :=
    (IsSmall.of_finite (hS₀.union (finite_iUnion fun i ↦ finite_range (t₁ i)))).racl.mono
      (adjoin_le_racl k _)
  have hle : adjoin k S₀ ≤ L := adjoin.mono k _ _ subset_union_left
  have hFt : HasGenericSamples L a' (Fintype.card μ) := HasGenericSamples.mono hle hsa'
  have hsrc : HasGenericSamples L a
      (Fintype.card (((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ))) :=
    (HasGenericSamples.mono hle hsa).of_le (by simp only [Fintype.card_sum]; omega)
  have hP := F.constructibleGroupPresentation_pairDomain L hL hb hδ₀ hc hF hdim hD hFt hsrc
  refine ⟨S₀, t₁, hS₀, hfresh₀, hT, hsa, hsa', ht₁, ht₁L, hadd, hfresh, hrk, hL, hP,
    fun y₀ hy₀ ↦ ?_⟩
  convert hH y₀ hy₀ using 1
  ext d
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hd, hfix⟩
    exact ⟨hd, F.pairDomainGerm_mem L hL hb hδ₀ hc hF hdim ⟨d, hd⟩, hfix⟩
  · rintro ⟨hd, hmem, hfix⟩
    exact ⟨hd, hfix⟩

end QuasiRational

end

end GroupConfig
