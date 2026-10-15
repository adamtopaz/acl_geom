/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Constructible.GroupParameters
import GroupConfig.Constructible.GroupDomainFormula
import GroupConfig.Constructible.StabilizerParameters
import GroupConfig.Constructible.FamilySamples

/-!
# The pair domain as a word relation

Blueprint `sources/group_configuration/09-constructibility.tex`, `thm:constructible`(1): the
domain `D_G` of pairs `(u₁, u₂) ∈ Adm^× × Adm^×` satisfying `(∗)` is the set of invertibly
admissible pairs on which the generic stabilisation test of the two-letter word
`g_{u₁}⁻¹ g_{u₂}` holds.

* The inner relation of that test at `((u₁, u₂), v)` is the condition of `(∗)` at `v`, together
  with invertible admissibility of the letter at `v`
  (`GroupConfig.QuasiRational.mem_groupInner_pairWord_iff`).
* For an actual family representing the orbit of an invertible germ, that extra condition holds
  at every generic `v`, so the domain is the intersection of the invertibly admissible pairs with
  the word's stabilisation relation (`GroupConfig.QuasiRational.pairDomain_eq_inter_groupRel`).
  No parameter is assumed to lie in the parameter locus and no germ is assumed to lie in `G`.
* Hence, for a Hrushovski–Weil datum of bijections, the domain over `L₁ = L₀(t)` is
  constructible over `L₁`, for a small field `L₀` containing samples of the source and target
  loci and generic points `t` of the parameter locus over `L₀`
  (`GroupConfig.QuasiRational.isConstructibleOver_pairDomain`).
* For any constructible set of parameters with an actual map to the group represented by a word,
  the parameters fixing `ι(y₀)`, for any generic point `y₀`, form a constructible set
  (`GroupConfig.QuasiRational.isConstructibleOver_wordStabilizer`). In particular the stabiliser
  of `ι(y₀)` in the domain is constructible over `L₁(y₀)`
  (`GroupConfig.QuasiRational.isConstructibleOver_pairStabilizer`).
* Choosing the samples once by `GroupConfig.exists_groupSamples`, the domain is constructible over
  an actual field `k(t₀, t₁)` of jointly independent generic points, fresh from any prescribed small
  field, and each stabiliser over `k(t₀, t₁, y₀)`
  (`GroupConfig.QuasiRational.exists_fresh_isConstructibleOver_pairDomain_stabilizer`,
  `GroupConfig.QuasiRational.exists_fresh_isConstructibleOver_pairDomain`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the identification of `D_G` with a word relation, and the constructibility of `D_G`
and of the stabilisers of generic points over one fresh field of actual samples, are complete.
The presentation of `G` and of `G/H` is not part of this module.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
  [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
  {μ ι κ : Type w} [Fintype μ] [Finite ι] [Finite κ] {a : ι → K} {a' : κ → K}

namespace QuasiRational

/-- The inner relation of the generic stabilisation test of the pair word, at an invertibly
admissible pair: the germ at `v` is invertible, and some point `u'` of the parameter locus with
an invertible admissible germ has `g_v g_{u₁}⁻¹ g_{u₂} = g_{u'}`. -/
theorem mem_groupInner_pairWord_iff (F : QuasiRational k (μ ⊕ ι) κ)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) {d : (μ ⊕ μ) → K}
    (hd : F.IsInvertiblePair a a' d) (c v : μ → K) :
    Sum.elim d v ∈ groupInner F c (F.pairWord hdim) hdim ↔
      ∃ hv : F.IsAdmissible a a' v, Germ.IsInvertible (F.parameterGerm hv) ∧
        ∃ (u' : μ → K) (hu' : F.IsAdmissible a a' u'), InLocus (k := k) c u' ∧
          Germ.IsInvertible (F.parameterGerm hu') ∧
          Germ.comp (F.parameterGerm hv) (F.pairGerm hd) = F.parameterGerm hu' := by
  have hgerm := F.isGerm_pairGerm hdim hd
  constructor
  · rintro ⟨u', hV, ⟨hu, hinv⟩, ⟨-, hv, hvinv⟩, hu', g₀, hv', hg₀, hcomp⟩
    obtain rfl : g₀ = F.pairGerm hd :=
      ((Word.isGerm_mapParams_iff _ _ _ _).1 hg₀).unique hgerm
    exact ⟨hv, hvinv, u', hu', hV, hinv, hcomp.symm⟩
  · rintro ⟨hv, hvinv, u', hu', hV, hinv, hcomp⟩
    exact ⟨u', hV, ⟨hu', hinv⟩,
      ⟨(Word.isInvertiblyAdmissible_mapParams_iff _ _ _).2
        ((F.isInvertiblyAdmissible_pairWord_iff hdim _).2 hd), hv, hvinv⟩,
      hu', F.pairGerm hd, hv, (Word.isGerm_mapParams_iff _ _ _ _).2 hgerm, hcomp.symm⟩

/-- `thm:constructible`(1): for an actual family representing the orbit of an invertible germ,
the domain `D_G` is the set of invertibly admissible pairs satisfying the generic stabilisation
test of the pair word. -/
theorem pairDomain_eq_inter_groupRel (F : QuasiRational k (μ ⊕ ι) κ)
    (M : IntermediateField k K) {f₀ : Germ k a a'} (hf₀ : Germ.IsInvertible f₀) {c : μ → K}
    (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
      F.parameterGerm hu = f₀.map σ)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) :
    F.pairDomain M c a a' =
      {d | F.IsInvertiblePair a a' d} ∩ groupRel M F c (F.pairWord hdim) hdim := by
  ext d
  constructor
  · rintro ⟨hd, hstar⟩
    refine ⟨hd, fun v hv ↦ (F.mem_groupInner_pairWord_iff hdim hd c v).2 ?_⟩
    obtain ⟨hv', u', hu', hV, hinv, hcomp⟩ := hstar v hv
    -- The germ at a generic parameter is in the orbit of `f₀`, hence invertible.
    obtain ⟨hv'', hmem⟩ := exists_parameterGerm_mem_orbit_of_isGen hF hv.isGen
    exact ⟨hv', Germ.isInvertible_of_mem_orbit hf₀ hmem, u', hu', hV, hinv, hcomp⟩
  · rintro ⟨hd, hrel⟩
    refine ⟨hd, fun v hv ↦ ?_⟩
    obtain ⟨hv', -, u', hu', hV, hinv, hcomp⟩ :=
      (F.mem_groupInner_pairWord_iff hdim hd c v).1 (hrel v hv)
    exact ⟨hv', u', hu', hV, hinv, hcomp⟩

/-- `thm:constructible`(1): for a Hrushovski–Weil datum of bijections, the domain `D_G` over
`L₁ = L₀(t)` is constructible over `L₁`. Here `L₀` is a small field containing samples of the
source and target loci, and `t` are generic points of the parameter locus over `L₀` with additive
rank, enough for the pair coordinates. -/
theorem isConstructibleOver_pairDomain (F : QuasiRational k (μ ⊕ ι) κ) {f₀ : Germ k a a'}
    (hb : Germ.IsHWBij f₀) {δ₀ : Germ k a a} (hδ₀ : δ₀ ∈ Germ.diffSet f₀) {c : μ → K}
    (hc : adjoin k (range c) = f₀.cb)
    (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
      F.parameterGerm hu = f₀.map σ)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) {L₀ : IntermediateField k K}
    (hL₀ : IsSmall k (L₀ : Set K)) (hFt : HasGenericSamples L₀ a' (Fintype.card μ))
    (hsrc : HasGenericSamples L₀ a (Fintype.card (((μ ⊕ μ) ⊕ μ) ⊕ μ)))
    {α : Type*} [Fintype α] (t : α → μ → K) (ht : ∀ i, IsGenericOver L₀ c (t i))
    (hind : erk k (L₀ : Set K) (⋃ i, range (t i)) = ∑ i, erk k (L₀ : Set K) (range (t i)))
    (hr : 2 * Fintype.card (μ ⊕ μ) + 1 ≤ Fintype.card α) :
    IsConstructibleOver (↥(adjoin k ((L₀ : Set K) ∪ ⋃ i, range (t i))))
      (F.pairDomain (adjoin k ((L₀ : Set K) ∪ ⋃ i, range (t i))) c a a') := by
  set L₁ := adjoin k ((L₀ : Set K) ∪ ⋃ i, range (t i))
  have hL₁ : IsSmall k (L₁ : Set K) :=
    ((hL₀.union (IsSmall.of_finite (finite_iUnion fun i ↦ finite_range (t i)))).racl).mono
      (adjoin_le_racl k _)
  have hle : L₀ ≤ L₁ := fun x hx ↦ subset_adjoin k _ (Or.inl hx)
  rw [F.pairDomain_eq L₁ L₀ hL₁ hL₀ hb hδ₀ hc hF hdim,
    F.pairDomain_eq_inter_groupRel L₀ hb.isInvertible hF hdim]
  refine IsConstructibleOver.inter ?_ (isConstructibleOver_groupRel F c (F.pairWord hdim) hdim
    hL₀ ⟨⟨trivial, hFt⟩, hFt⟩ hFt hsrc t ht hind hr)
  -- Invertibly admissible pairs: both coordinates are invertibly admissible.
  obtain ⟨n, s, hs, hsind, hn, hsL⟩ := hFt
  have hI := IsConstructibleOver.of_le_intermediateField
    ((adjoin_le_iff.2 (iUnion_subset hsL)).trans hle)
    (F.isConstructibleOver_invertibleAdmissible a a' hdim s hs hsind (by rwa [Fintype.card_fin]))
  exact (hI.preimage_comp Sum.inl).inter (hI.preimage_comp Sum.inr)

/-- `thm:constructible`(2) for an arbitrary word: for a constructible set `D` of parameters and an
actual map `Γ` from `D` to the group whose values are represented by a word `w` with all letters
invertibly admissible, the parameters whose group element fixes `ι(y₀)` form a constructible set.
The point `y₀` is any generic point; it is not assumed independent from the parameters. Named
consumers: the stabiliser of the domain and the kernel and action relations of the homogeneous
space. -/
theorem isConstructibleOver_wordStabilizer {P : Type*} [Fintype P] [Fintype ι]
    (F : QuasiRational k (μ ⊕ ι) κ) (c : μ → K) (w : Word k P a a)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) {f₀ : Germ k a a'} (hb : Germ.IsHWBij f₀)
    {δ₀ : Germ k a a} (hδ₀ : δ₀ ∈ Germ.diffSet f₀) (hc : adjoin k (range c) = f₀.cb)
    (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
      F.parameterGerm hu = f₀.map σ)
    {L₀ : IntermediateField k K} (hL₀ : IsSmall k (L₀ : Set K)) (hws : w.HasSamples L₀)
    (hFt : HasGenericSamples L₀ a' (Fintype.card μ))
    (hsrc : HasGenericSamples L₀ a (Fintype.card ((P ⊕ μ) ⊕ μ)))
    {α : Type*} [Fintype α] (t : α → μ → K) (ht : ∀ i, IsGenericOver L₀ c (t i))
    (hind : erk k (L₀ : Set K) (⋃ i, range (t i)) = ∑ i, erk k (L₀ : Set K) (range (t i)))
    (hr : 2 * Fintype.card (P ⊕ ι) + 1 ≤ Fintype.card α) {y₀ : ι → K} (hy₀ : IsGen k a y₀)
    {D : Set (P → K)}
    (hD : IsConstructibleOver (↥(adjoin k (((L₀ : Set K) ∪ ⋃ i, range (t i)) ∪ range y₀))) D)
    (Γ : D → ↥(hb.isHW hδ₀).prodSubgroup)
    (hrep : ∀ d : D, w.IsGerm d ((hb.isHW hδ₀).val (Γ d)))
    (hInv : ∀ d : D, w.IsInvertiblyAdmissible d) :
    IsConstructibleOver (↥(adjoin k (((L₀ : Set K) ∪ ⋃ i, range (t i)) ∪ range y₀)))
      {d | ∃ hd : d ∈ D, Γ ⟨d, hd⟩ • (hb.isHW hδ₀).iota hy₀ = (hb.isHW hδ₀).iota hy₀} := by
  convert hD.inter
    (isConstructibleOver_stabilizerFibre F c w hdim hL₀ hws hFt hsrc t ht hind hr y₀) using 1
  ext d
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hd, hfix⟩
    exact ⟨hd, (mem_stabilizerRel_iff hL₀ hb hδ₀ (hb.isHW hδ₀) (Γ ⟨d, hd⟩) hc hF hdim
      (hrep ⟨d, hd⟩) (hInv ⟨d, hd⟩) hy₀).2 hfix⟩
  · rintro ⟨hd, hst⟩
    exact ⟨hd, (mem_stabilizerRel_iff hL₀ hb hδ₀ (hb.isHW hδ₀) (Γ ⟨d, hd⟩) hc hF hdim
      (hrep ⟨d, hd⟩) (hInv ⟨d, hd⟩) hy₀).1 hst⟩

/-- `thm:constructible`(2): the stabiliser of `ι(y₀)`, as the set of points of the domain `D_G`
over `L₁ = L₀(t)` whose germ fixes `ι(y₀)`, is constructible over `L₁(y₀)`. The point `y₀` is
any generic point; it is not assumed independent from the parameters. -/
theorem isConstructibleOver_pairStabilizer [Fintype ι] (F : QuasiRational k (μ ⊕ ι) κ)
    {f₀ : Germ k a a'} (hb : Germ.IsHWBij f₀) {δ₀ : Germ k a a} (hδ₀ : δ₀ ∈ Germ.diffSet f₀)
    {c : μ → K} (hc : adjoin k (range c) = f₀.cb)
    (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
      F.parameterGerm hu = f₀.map σ)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) {L₀ : IntermediateField k K}
    (hL₀ : IsSmall k (L₀ : Set K)) (hFt : HasGenericSamples L₀ a' (Fintype.card μ))
    (hsrc : HasGenericSamples L₀ a (Fintype.card (((μ ⊕ μ) ⊕ μ) ⊕ μ)))
    {α : Type*} [Fintype α] (t : α → μ → K) (ht : ∀ i, IsGenericOver L₀ c (t i))
    (hind : erk k (L₀ : Set K) (⋃ i, range (t i)) = ∑ i, erk k (L₀ : Set K) (range (t i)))
    (hr : 2 * Fintype.card ((μ ⊕ μ) ⊕ ι) + 1 ≤ Fintype.card α) {y₀ : ι → K}
    (hy₀ : IsGen k a y₀) :
    IsConstructibleOver (↥(adjoin k (((L₀ : Set K) ∪ ⋃ i, range (t i)) ∪ range y₀)))
      {d | ∃ (hd : d ∈ F.pairDomain (adjoin k ((L₀ : Set K) ∪ ⋃ i, range (t i))) c a a')
          (hmem : F.pairDomainGerm (adjoin k ((L₀ : Set K) ∪ ⋃ i, range (t i))) c a a' ⟨d, hd⟩ ∈
            Germ.IsHW.prodSet δ₀),
        (hb.isHW hδ₀).ofMem hmem • (hb.isHW hδ₀).iota hy₀ = (hb.isHW hδ₀).iota hy₀} := by
  set L₁ := adjoin k ((L₀ : Set K) ∪ ⋃ i, range (t i))
  have hL₁ : IsSmall k (L₁ : Set K) :=
    ((hL₀.union (IsSmall.of_finite (finite_iUnion fun i ↦ finite_range (t i)))).racl).mono
      (adjoin_le_racl k _)
  have hrD : 2 * Fintype.card (μ ⊕ μ) + 1 ≤ Fintype.card α := by
    simp only [Fintype.card_sum] at hr ⊢
    omega
  have hD : IsConstructibleOver (↥(adjoin k (((L₀ : Set K) ∪ ⋃ i, range (t i)) ∪ range y₀)))
      (F.pairDomain L₁ c a a') :=
    IsConstructibleOver.of_le_intermediateField (adjoin.mono k _ _ subset_union_left)
      (F.isConstructibleOver_pairDomain hb hδ₀ hc hF hdim hL₀ hFt hsrc t ht hind hrD)
  -- The actual group element of a domain point, represented by the pair word.
  let Γ : F.pairDomain L₁ c a a' → ↥(hb.isHW hδ₀).prodSubgroup :=
    fun d ↦ (hb.isHW hδ₀).ofMem (F.pairDomainGerm_mem L₁ hL₁ hb hδ₀ hc hF hdim d)
  have h := F.isConstructibleOver_wordStabilizer c (F.pairWord hdim) hdim hb hδ₀ hc hF hL₀
    ⟨⟨trivial, hFt⟩, hFt⟩ hFt hsrc t ht hind hr hy₀ hD Γ
    (fun d ↦ by
      change (F.pairWord hdim).IsGerm d ((hb.isHW hδ₀).val
        ((hb.isHW hδ₀).ofMem (F.pairDomainGerm_mem L₁ hL₁ hb hδ₀ hc hF hdim d)))
      rw [(hb.isHW hδ₀).val_ofMem]
      exact F.isGerm_pairGerm hdim d.2.choose)
    (fun d ↦ (F.isInvertiblyAdmissible_pairWord_iff hdim _).2 d.2.choose)
  convert h using 1
  ext d
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hd, hmem, hfix⟩
    exact ⟨hd, hfix⟩
  · rintro ⟨hd, hfix⟩
    exact ⟨hd, F.pairDomainGerm_mem L₁ hL₁ hb hδ₀ hc hF hdim ⟨d, hd⟩, hfix⟩

/-- `thm:constructible`, with the samples chosen once: for a Hrushovski–Weil datum of bijections
and any small field `M₀`, there are a first stage `t₀` of jointly independent generic points of the
source and target loci and a second stage `t₁` of generic points of the parameter locus over
`k(t₀)`, jointly fresh from `M₀`, such that the domain `D_G` over `k(t₀, t₁)` is constructible over
`k(t₀, t₁)`, and for every generic point `y₀` the stabiliser of `ι(y₀)` in `D_G` is constructible
over `k(t₀, t₁, y₀)`. The sample bounds serve the other relations of the presentation. -/
theorem exists_fresh_isConstructibleOver_pairDomain_stabilizer [Fintype ι]
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
      IsConstructibleOver (↥(adjoin k (S₀ ∪ ⋃ i, range (t₁ i))))
        (F.pairDomain (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) c a a') ∧
      ∀ (y₀ : ι → K) (hy₀ : IsGen k a y₀),
        IsConstructibleOver (↥(adjoin k ((S₀ ∪ ⋃ i, range (t₁ i)) ∪ range y₀)))
          {d | ∃ (hd : d ∈ F.pairDomain (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) c a a')
              (hmem : F.pairDomainGerm (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) c a a' ⟨d, hd⟩ ∈
                Germ.IsHW.prodSet δ₀),
            (hb.isHW hδ₀).ofMem hmem • (hb.isHW hδ₀).iota hy₀ = (hb.isHW hδ₀).iota hy₀} := by
  obtain ⟨S₀, t₁, hS₀, hfresh₀, hT, hsa, hsa', ht₁, ht₁L, hadd, hfresh, hrk, hfield⟩ :=
    exists_groupSamples M₀ hM₀ a a' c (8 * Fintype.card μ) (Fintype.card μ)
      (2 * (6 * Fintype.card μ + Fintype.card ι) + 1)
  have hL₀ : IsSmall k ((adjoin k S₀ : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite hS₀).racl.mono (adjoin_le_racl k S₀)
  have hsrc : HasGenericSamples (adjoin k S₀) a (Fintype.card (((μ ⊕ μ) ⊕ μ) ⊕ μ)) :=
    hsa.of_le (by simp only [Fintype.card_sum]; omega)
  have hr : 2 * Fintype.card ((μ ⊕ μ) ⊕ ι) + 1 ≤
      Fintype.card (Fin (2 * (6 * Fintype.card μ + Fintype.card ι) + 1)) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hrD : 2 * Fintype.card (μ ⊕ μ) + 1 ≤
      Fintype.card (Fin (2 * (6 * Fintype.card μ + Fintype.card ι) + 1)) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hD := F.isConstructibleOver_pairDomain hb hδ₀ hc hF hdim hL₀ hsa' hsrc t₁ ht₁L hadd hrD
  rw [hfield] at hD
  refine ⟨S₀, t₁, hS₀, hfresh₀, hT, hsa, hsa', ht₁, ht₁L, hadd, hfresh, hrk, hD, fun y₀ hy₀ ↦ ?_⟩
  have h := F.isConstructibleOver_pairStabilizer hb hδ₀ hc hF hdim hL₀ hsa' hsrc t₁ ht₁L hadd hr
    hy₀
  -- The final fields are generated by the coordinates of `t₀`, `t₁` and `y₀`.
  have hfield' : adjoin k (((adjoin k S₀ : Set K) ∪ ⋃ i, range (t₁ i)) ∪ range y₀) =
      adjoin k ((S₀ ∪ ⋃ i, range (t₁ i)) ∪ range y₀) := by
    refine le_antisymm (adjoin_le_iff.2 (union_subset (union_subset
      (adjoin.mono k _ _ (subset_union_left.trans subset_union_left))
      ((subset_union_right.trans subset_union_left).trans (subset_adjoin k _)))
      (subset_union_right.trans (subset_adjoin k _)))) ?_
    exact adjoin.mono k _ _ (union_subset_union_left _
      (union_subset_union_left _ (subset_adjoin k S₀)))
  rw [hfield, hfield'] at h
  exact h

/-- `thm:constructible`(1), with the samples chosen: for a Hrushovski–Weil datum of bijections
and any small field `M₀`, there are a first stage `t₀` of jointly independent generic points of the
source and target loci and a second stage `t₁` of generic points of the parameter locus over
`k(t₀)`, jointly fresh from `M₀`, such that the domain `D_G` over `k(t₀, t₁)` is constructible
over `k(t₀, t₁)`. The sample bounds serve the other relations of the presentation. -/
theorem exists_fresh_isConstructibleOver_pairDomain [Fintype ι] (F : QuasiRational k (μ ⊕ ι) κ)
    {f₀ : Germ k a a'} (hb : Germ.IsHWBij f₀) {δ₀ : Germ k a a} (hδ₀ : δ₀ ∈ Germ.diffSet f₀)
    {c : μ → K} (hc : adjoin k (range c) = f₀.cb)
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
      IsConstructibleOver (↥(adjoin k (S₀ ∪ ⋃ i, range (t₁ i))))
        (F.pairDomain (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) c a a') := by
  obtain ⟨S₀, t₁, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, hD, -⟩ :=
    F.exists_fresh_isConstructibleOver_pairDomain_stabilizer hb hδ₀ hc hF hdim M₀ hM₀
  exact ⟨S₀, t₁, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, hD⟩

end QuasiRational

end

end GroupConfig
