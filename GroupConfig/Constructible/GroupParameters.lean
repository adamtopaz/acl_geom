/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Constructible.AdmissibleWords
import GroupConfig.Constructible.GroupDomainMembership

/-!
# The actual group parameter domain

Blueprint `sources/group_configuration/09-constructibility.tex`.

The literal invertibly admissible pair domain, its generic stabilization condition,
actual group membership and surjection. Neither pair parameter is assumed generic.

**Status:** these parameter-domain claims of `thm:constructible` are proved under the genuine
Hrushovski–Weil family hypotheses. Constructibility is assembled in `GroupDomain`.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
  [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
  {μ ι κ : Type w} [Fintype μ] [Finite ι] [Finite κ]

namespace QuasiRational

variable (F : QuasiRational k (μ ⊕ ι) κ) (a : ι → K) (a' : κ → K)

/-- Both parameters are invertibly admissible. This is the ambient pair
condition in the actual source domain; the generic stabilization test is separate. -/
def IsInvertiblePair (d : (μ ⊕ μ) → K) : Prop :=
  (∃ hu : F.IsAdmissible a a' (d ∘ Sum.inl), Germ.IsInvertible (F.parameterGerm hu)) ∧
  (∃ hu : F.IsAdmissible a a' (d ∘ Sum.inr), Germ.IsInvertible (F.parameterGerm hu))

variable {a a'}

/-- The actual self-germ `g_u₁⁻¹ g_u₂` of an invertibly admissible pair. -/
def pairGerm {d : (μ ⊕ μ) → K} (hd : F.IsInvertiblePair a a' d) : Germ k a a :=
  Germ.comp (Classical.choose hd.1.choose_spec) (F.parameterGerm hd.2.choose)

/-- The typed word for that same pair, first the second letter and then the
inverse of the first. -/
def pairWord (hdim : erk k ∅ (range a) = erk k ∅ (range a')) : Word k (μ ⊕ μ) a a :=
  .inv (.fwd .nil a' F Sum.inr hdim) a F Sum.inl hdim

/-- The all-letter condition of the word is exactly invertible admissibility
of the two actual parameters. -/
theorem isInvertiblyAdmissible_pairWord_iff
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) (d : (μ ⊕ μ) → K) :
    (F.pairWord hdim).IsInvertiblyAdmissible d ↔ F.IsInvertiblePair a a' d := by
  simp only [pairWord, Word.IsInvertiblyAdmissible, IsInvertiblePair, true_and, and_comm]

/-- The word represents the actual pair germ; it assumes no group membership. -/
theorem isGerm_pairGerm (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    {d : (μ ⊕ μ) → K} (hd : F.IsInvertiblePair a a' d) :
    (F.pairWord hdim).IsGerm d (F.pairGerm hd) := by
  refine ⟨F.parameterGerm hd.2.choose, hd.1.choose, Classical.choose hd.1.choose_spec,
    ?_, Classical.choose_spec hd.1.choose_spec, rfl⟩
  exact ⟨Germ.id a, hd.2.choose, rfl, (Germ.comp_id _).symm⟩

/-- Every candidate pair germ is invertible, before imposing the group test. -/
theorem isInvertible_pairGerm {d : (μ ⊕ μ) → K} (hd : F.IsInvertiblePair a a' d) :
    Germ.IsInvertible (F.pairGerm hd) := by
  let g₁ := F.parameterGerm hd.1.choose
  let g₂ := F.parameterGerm hd.2.choose
  let h₁ := Classical.choose hd.1.choose_spec
  let h₂ := Classical.choose hd.2.choose_spec
  have hi₁ : Germ.IsInverse h₁ g₁ := Classical.choose_spec hd.1.choose_spec
  have hi₂ : Germ.IsInverse h₂ g₂ := Classical.choose_spec hd.2.choose_spec
  refine ⟨Germ.comp h₂ g₁, ?_, ?_⟩
  · change Germ.comp (Germ.comp h₂ g₁) (Germ.comp h₁ g₂) = Germ.id a
    rw [Germ.comp_assoc, ← Germ.comp_assoc g₁ h₁ g₂, hi₁.2, Germ.id_comp, hi₂.1]
  · change Germ.comp (Germ.comp h₁ g₂) (Germ.comp h₂ g₁) = Germ.id a
    rw [Germ.comp_assoc, ← Germ.comp_assoc g₂ h₂ g₁, hi₂.2, Germ.id_comp, hi₁.1]

/-- The candidate's canonical base is algebraic over the actual pair coordinates. -/
theorem cb_pairGerm_le (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    {d : (μ ⊕ μ) → K} (hd : F.IsInvertiblePair a a' d) :
    (F.pairGerm hd).cb ≤ racl k (range d) :=
  (F.isGerm_pairGerm hdim hd).cb_le


/-- The literal source domain: invertibly admissible pairs satisfying the
stabilization condition over the algebraic closure of the coefficient field
and the pair coordinates. Neither parameter is assumed generic. -/
def pairDomain (M : IntermediateField k K) (c : μ → K) (a : ι → K) (a' : κ → K) :
    Set ((μ ⊕ μ) → K) :=
  {d | ∃ hd : F.IsInvertiblePair a a' d,
    ∀ v, IsGenericOver (racl k ((M : Set K) ∪ range d)) c v →
      ∃ (hv : F.IsAdmissible a a' v) (u' : μ → K) (hu' : F.IsAdmissible a a' u'),
        InLocus (k := k) c u' ∧ Germ.IsInvertible (F.parameterGerm hu') ∧
        Germ.comp (F.parameterGerm hv) (F.pairGerm hd) = F.parameterGerm hu'}

/-- The source stabilization condition is exactly membership in the actual
Hrushovski–Weil group. This is a theorem about every candidate pair. -/
theorem mem_pairDomain_iff (M : IntermediateField k K) (hM : IsSmall k (M : Set K))
    {f₀ : Germ k a a'} (hb : Germ.IsHWBij f₀) {δ₀ : Germ k a a}
    (hδ₀ : δ₀ ∈ Germ.diffSet f₀) {c : μ → K}
    (hc : adjoin k (range c) = f₀.cb)
    (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
      F.parameterGerm hu = f₀.map σ)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    {d : (μ ⊕ μ) → K} (hd : F.IsInvertiblePair a a' d) :
    d ∈ F.pairDomain M c a a' ↔ F.pairGerm hd ∈ Germ.IsHW.prodSet δ₀ := by
  have hMd : IsSmall k ((racl k ((M : Set K) ∪ range d) : IntermediateField k K) : Set K) :=
    (hM.union (IsSmall.of_finite (finite_range d))).racl
  have hcb : (F.pairGerm hd).cb ≤ racl k ((M : Set K) ∪ range d) :=
    (F.cb_pairGerm_le hdim hd).trans (racl_mono subset_union_right)
  have hiff := hb.mem_prodSet_iff_forall_isGenericOver hδ₀ hc hF
    (F.isInvertible_pairGerm hd) hMd hcb
  exact ⟨fun ⟨_, hstar⟩ ↦ hiff.mpr hstar, fun hg ↦ ⟨hd, hiff.mp hg⟩⟩

/-- The actual source domain is independent of the small coefficient field
used in its generic quantifier. Named consumer: the final sampling field of
its constructible presentation. -/
theorem pairDomain_eq (M N : IntermediateField k K) (hM : IsSmall k (M : Set K))
    (hN : IsSmall k (N : Set K)) {f₀ : Germ k a a'} (hb : Germ.IsHWBij f₀)
    {δ₀ : Germ k a a} (hδ₀ : δ₀ ∈ Germ.diffSet f₀) {c : μ → K}
    (hc : adjoin k (range c) = f₀.cb)
    (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
      F.parameterGerm hu = f₀.map σ)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) :
    F.pairDomain M c a a' = F.pairDomain N c a a' := by
  ext d
  constructor
  · intro hd
    exact (F.mem_pairDomain_iff N hN hb hδ₀ hc hF hdim hd.choose).mpr
      ((F.mem_pairDomain_iff M hM hb hδ₀ hc hF hdim hd.choose).mp hd)
  · intro hd
    exact (F.mem_pairDomain_iff M hM hb hδ₀ hc hF hdim hd.choose).mpr
      ((F.mem_pairDomain_iff N hN hb hδ₀ hc hF hdim hd.choose).mp hd)

/-- The actual germ represented by a point of the source domain. -/
def pairDomainGerm (M : IntermediateField k K) (c : μ → K) (a : ι → K) (a' : κ → K)
    (d : F.pairDomain M c a a') : Germ k a a :=
  F.pairGerm d.property.choose

/-- Every point of the source domain maps into the actual group. -/
theorem pairDomainGerm_mem (M : IntermediateField k K) (hM : IsSmall k (M : Set K))
    {f₀ : Germ k a a'} (hb : Germ.IsHWBij f₀) {δ₀ : Germ k a a}
    (hδ₀ : δ₀ ∈ Germ.diffSet f₀) {c : μ → K}
    (hc : adjoin k (range c) = f₀.cb)
    (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
      F.parameterGerm hu = f₀.map σ)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) (d : F.pairDomain M c a a') :
    F.pairDomainGerm M c a a' d ∈ Germ.IsHW.prodSet δ₀ :=
  (F.mem_pairDomain_iff M hM hb hδ₀ hc hF hdim d.property.choose).mp d.property

/-- Every element of the actual group has a pair in the source domain. The
parameters are obtained from the actual orbit family, not from a presentation
certificate. -/
theorem exists_pairDomainGerm_eq (M : IntermediateField k K) (hM : IsSmall k (M : Set K))
    {f₀ : Germ k a a'} (hb : Germ.IsHWBij f₀) {δ₀ : Germ k a a}
    (hδ₀ : δ₀ ∈ Germ.diffSet f₀) {c : μ → K}
    (hc : adjoin k (range c) = f₀.cb)
    (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
      F.parameterGerm hu = f₀.map σ)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    {γ : Germ k a a} (hγ : γ ∈ Germ.IsHW.prodSet δ₀) :
    ∃ d : F.pairDomain M c a a', F.pairDomainGerm M c a a' d = γ := by
  obtain ⟨f₁, ⟨σ₁, rfl⟩, f₂, ⟨σ₂, rfl⟩, g₁, hg₁, hγeq⟩ :=
    (hb.mem_prodSet_iff hδ₀).mp hγ
  obtain ⟨hu₁, hu₁eq⟩ := hF σ₁
  obtain ⟨hu₂, hu₂eq⟩ := hF σ₂
  let d := Sum.elim (⇑σ₁ ∘ c) (⇑σ₂ ∘ c)
  have hd : F.IsInvertiblePair a a' d := by
    refine ⟨⟨hu₁, ?_⟩, ⟨hu₂, ?_⟩⟩
    · change Germ.IsInvertible (F.parameterGerm hu₁)
      rw [hu₁eq]
      exact Germ.isInvertible_of_mem_orbit hb.isInvertible ⟨σ₁, rfl⟩
    · change Germ.IsInvertible (F.parameterGerm hu₂)
      rw [hu₂eq]
      exact Germ.isInvertible_of_mem_orbit hb.isInvertible ⟨σ₂, rfl⟩
  have heq : F.pairGerm hd = γ := by
    have hi : Germ.IsInverse (Classical.choose hd.1.choose_spec) (f₀.map σ₁) := by
      rw [← hu₁eq]
      exact Classical.choose_spec hd.1.choose_spec
    change Germ.comp (Classical.choose hd.1.choose_spec) (F.parameterGerm hd.2.choose) = γ
    rw [hi.unique hg₁]
    exact (congrArg (Germ.comp g₁) hu₂eq).trans hγeq.symm
  have hdom : d ∈ F.pairDomain M c a a' :=
    (F.mem_pairDomain_iff M hM hb hδ₀ hc hF hdim hd).mpr (heq ▸ hγ)
  exact ⟨⟨d, hdom⟩, heq⟩

end QuasiRational

end

end GroupConfig
