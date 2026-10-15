/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.ConfigurationBaseChange
import GroupConfig.Constructible.AdmissibleWords

/-!
# The generic group stabilization relation

Blueprint `sources/group_configuration/09-constructibility.tex`.

The shared unprojected witness relation is constructible over actual sample fields.
Existential projection and generic quantification give the group stabilization test.
Named consumers: the actual group domain and the stabilizer parameter relation.

**Status:** relative constructibility of these actual witness and quantified relations is proved.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

universe u₁ u₂ u₃ v

variable {k : Type u₁} {K : Type u₂} [Field k] [Field K] [Algebra k K]
  [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
  {P : Type u₃} {ι κ μ : Type v} [Finite ι] [Finite κ] [Fintype P] [Fintype μ]
  {a : ι → K} {a' : κ → K}

/-- The literal inner group-stabilization formula in `(d,v)`: some locus
parameter with invertible germ equals the actual composite word, whose every
letter is required to be invertibly admissible. -/
def groupInner (F : QuasiRational k (μ ⊕ ι) κ) (c : μ → K) (w : Word k P a a)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) : Set ((P ⊕ μ) → K) :=
  {e | ∃ u' : μ → K, InLocus (k := k) c u' ∧
    (∃ hu : F.IsAdmissible a a' u', Germ.IsInvertible (F.parameterGerm hu)) ∧
    (stabWord w F hdim).IsInvertiblyAdmissible (Sum.elim e u') ∧
    ∃ hu' : F.IsAdmissible a a' u',
      (stabWord w F hdim).IsGerm (Sum.elim e u') (F.parameterGerm hu')}

/-- The source generic-stabilization test for an actual typed self-word. -/
def groupRel (M : IntermediateField k K) (F : QuasiRational k (μ ⊕ ι) κ)
    (c : μ → K) (w : Word k P a a)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) : Set (P → K) :=
  {d | ∀ v, IsGenericOver (racl k ((M : Set K) ∪ range d)) c v →
    Sum.elim d v ∈ groupInner F c w hdim}

/-- The actual unprojected witness for generic group stabilization.
Named consumers: the group inner relation and the stabilizer inner relation. -/
def groupWitness (F : QuasiRational k (μ ⊕ ι) κ) (c : μ → K) (w : Word k P a a)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) : Set (((P ⊕ μ) ⊕ μ) → K) :=
  {Z | InLocus (k := k) c (Z ∘ Sum.inr) ∧
    (∃ hu : F.IsAdmissible a a' (Z ∘ Sum.inr), Germ.IsInvertible (F.parameterGerm hu)) ∧
    (stabWord w F hdim).IsInvertiblyAdmissible Z ∧
    ∃ hu' : F.IsAdmissible a a' (Z ∘ Sum.inr),
      (stabWord w F hdim).IsGerm Z (F.parameterGerm hu')}

/-- The shared actual witness is constructible before projecting its final
parameter. Named consumers: the group and stabilizer inner formulas. -/
theorem isConstructibleOver_groupWitness (F : QuasiRational k (μ ⊕ ι) κ)
    (c : μ → K) (w : Word k P a a)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) {L₀ : IntermediateField k K}
    (hw : w.HasSamples L₀) (hFt : HasGenericSamples L₀ a' (Fintype.card μ))
    (hsrc : HasGenericSamples L₀ a (Fintype.card ((P ⊕ μ) ⊕ μ))) :
    IsConstructibleOver (↥L₀) (groupWitness F c w hdim) := by
  have hA : IsConstructibleOver (↥L₀) ((fun Z : ((P ⊕ μ) ⊕ μ) → K ↦ Z ∘ Sum.inr) ⁻¹'
      {u' | InLocus (k := k) c u'}) :=
    ((isConstructibleOver_inLocus c).preimage_comp Sum.inr).extend_base
  obtain ⟨n, t, ht, hind, hn, htL⟩ := hFt
  have hB := (IsConstructibleOver.of_le_intermediateField (adjoin_le_iff.2 (iUnion_subset htL))
    (F.isConstructibleOver_invertibleAdmissible a a' hdim t ht hind
      (by rwa [Fintype.card_fin]))).preimage_comp (Sum.inr : μ → ((P ⊕ μ) ⊕ μ))
  have hCD := (stabWord w F hdim).isConstructibleOver_eq_parameterGerm F Sum.inr hdim
    ⟨(w.hasSamples_mapParams_iff _).2 hw, n, t, ht, hind, hn, htL⟩
    ⟨n, t, ht, hind, hn, htL⟩ hsrc
  exact hA.inter (hB.inter hCD)

/-- The actual group inner relation is constructible over the field of word
and source samples. Named consumer: the actual two-parameter group domain. -/
theorem isConstructibleOver_groupInner (F : QuasiRational k (μ ⊕ ι) κ)
    (c : μ → K) (w : Word k P a a)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) {L₀ : IntermediateField k K}
    (hw : w.HasSamples L₀) (hFt : HasGenericSamples L₀ a' (Fintype.card μ))
    (hsrc : HasGenericSamples L₀ a (Fintype.card ((P ⊕ μ) ⊕ μ))) :
    IsConstructibleOver (↥L₀) (groupInner F c w hdim) := by
  let φ : ((P ⊕ μ) → K) → (μ → K) → Prop := fun e u' ↦
    InLocus (k := k) c u' ∧
    (∃ hu : F.IsAdmissible a a' u', Germ.IsInvertible (F.parameterGerm hu)) ∧
    (stabWord w F hdim).IsInvertiblyAdmissible (Sum.elim e u') ∧
    ∃ hu' : F.IsAdmissible a a' u',
      (stabWord w F hdim).IsGerm (Sum.elim e u') (F.parameterGerm hu')
  have hT : IsConstructibleOver (↥L₀)
      {Z : ((P ⊕ μ) ⊕ μ) → K | φ (Z ∘ Sum.inl) (Z ∘ Sum.inr)} := by
    convert isConstructibleOver_groupWitness F c w hdim hw hFt hsrc using 1
    ext Z
    have hZ : Sum.elim (Z ∘ Sum.inl) (Z ∘ Sum.inr) = Z := by
      funext q
      cases q <;> rfl
    simp only [φ, groupWitness, Set.mem_ofPred_eq, hZ]
  exact hT.exists (φ := φ)

/-- Generic quantification of the actual inner relation gives a constructible
group test after adjoining enough independent samples of the parameter locus. -/
theorem isConstructibleOver_groupRel (F : QuasiRational k (μ ⊕ ι) κ)
    (c : μ → K) (w : Word k P a a)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) {L₀ : IntermediateField k K}
    (hL₀ : IsSmall k (L₀ : Set K)) (hw : w.HasSamples L₀)
    (hFt : HasGenericSamples L₀ a' (Fintype.card μ))
    (hsrc : HasGenericSamples L₀ a (Fintype.card ((P ⊕ μ) ⊕ μ)))
    {α : Type*} [Fintype α] (t : α → μ → K) (ht : ∀ i, IsGenericOver L₀ c (t i))
    (hind : erk k (L₀ : Set K) (⋃ i, range (t i)) = ∑ i, erk k (L₀ : Set K) (range (t i)))
    (hr : 2 * Fintype.card P + 1 ≤ Fintype.card α) :
    IsConstructibleOver (↥(adjoin k ((L₀ : Set K) ∪ ⋃ i, range (t i))))
      (groupRel L₀ F c w hdim) := by
  have h := constructible_generic_quantifier L₀ hL₀ c t ht hind hr
    (isConstructibleOver_groupInner F c w hdim hw hFt hsrc)
  have hbase (S : Set K) : (racl (↥L₀) S).restrictScalars k = racl k ((L₀ : Set K) ∪ S) :=
    SetLike.coe_injective (racl_base_coe L₀ S)
  refine IsConstructibleOver.of_restrictScalars_eq (restrictScalars_adjoin k L₀ _) ?_
  convert h using 1
  ext d
  simp only [groupRel, Set.mem_ofPred_eq, hbase]

end

end GroupConfig
