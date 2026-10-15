/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Constructible.GroupParameters

/-!
# Relations on actual pair germs

Blueprint `sources/group_configuration/09-constructibility.tex`.

Actual pair and product words represent the specified germs, with every factor
invertibly admissible. Their equality, multiplication and inverse relations are constructible
over a common field of samples. Named consumer: the actual group presentation.

**Status:** these relative pair relations are proved; `GroupPresentation` restricts them to the
literal domain and presents the actual group.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
  [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
  {μ ι κ : Type w} [Fintype μ] [Finite ι] [Finite κ]
  {a : ι → K} {a' : κ → K}

namespace QuasiRational

variable (F : QuasiRational k (μ ⊕ ι) κ)

/-- The actual four-letter word for the product of two candidate pair germs:
first the right pair, then the left pair. Named consumer: the six-parameter
multiplication relation of the source constructible-group presentation. -/
def pairProductWord (hdim : erk k ∅ (range a) = erk k ∅ (range a')) :
    Word k ((μ ⊕ μ) ⊕ (μ ⊕ μ)) a a :=
  .inv (.fwd ((F.pairWord hdim).mapParams Sum.inr) a' F (Sum.inl ∘ Sum.inr) hdim)
    a F (Sum.inl ∘ Sum.inl) hdim

/-- The product word represents the product of the actual candidate germs,
without any group-membership assumption. -/
theorem isGerm_pairProductWord (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    {d : ((μ ⊕ μ) ⊕ (μ ⊕ μ)) → K}
    (hL : F.IsInvertiblePair a a' (d ∘ Sum.inl))
    (hR : F.IsInvertiblePair a a' (d ∘ Sum.inr)) :
    (F.pairProductWord hdim).IsGerm d (Germ.comp (F.pairGerm hL) (F.pairGerm hR)) := by
  refine ⟨Germ.comp (F.parameterGerm hL.2.choose) (F.pairGerm hR), hL.1.choose,
    Classical.choose hL.1.choose_spec, ?_, Classical.choose_spec hL.1.choose_spec, ?_⟩
  · refine ⟨F.pairGerm hR, hL.2.choose, ?_, rfl⟩
    exact ((F.pairWord hdim).isGerm_mapParams_iff Sum.inr d _).2
      (F.isGerm_pairGerm hdim hR)
  · exact Germ.comp_assoc _ _ _

/-- Every factor of the product word is invertible exactly when both actual
pairs are invertibly admissible. -/
theorem isInvertiblyAdmissible_pairProductWord_iff
    (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    (d : ((μ ⊕ μ) ⊕ (μ ⊕ μ)) → K) :
    (F.pairProductWord hdim).IsInvertiblyAdmissible d ↔
      F.IsInvertiblePair a a' (d ∘ Sum.inl) ∧ F.IsInvertiblePair a a' (d ∘ Sum.inr) := by
  simp only [pairProductWord, Word.IsInvertiblyAdmissible,
    Word.isInvertiblyAdmissible_mapParams_iff, isInvertiblyAdmissible_pairWord_iff]
  change ((_ ∧ _) ∧ _) ↔ ((_ ∧ _) ∧ _)
  exact ⟨fun ⟨⟨hR, h₂⟩, h₁⟩ ↦ ⟨⟨h₁, h₂⟩, hR⟩,
    fun ⟨⟨h₁, h₂⟩, hR⟩ ↦ ⟨⟨hR, h₂⟩, h₁⟩⟩

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] in
/-- The same target-locus samples serve both letters of the actual pair word.
Named consumers: kernel, inverse and product relations over one common field. -/
theorem hasSamples_pairWord (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    {L : IntermediateField k K} (h : HasGenericSamples L a' (Fintype.card μ)) :
    (F.pairWord hdim).HasSamples L :=
  ⟨⟨trivial, h⟩, h⟩

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] in
/-- The very same samples serve the product word; no additional field or
sampling certificate is introduced for its four factors. -/
theorem hasSamples_pairProductWord (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    {L : IntermediateField k K} (h : HasGenericSamples L a' (Fintype.card μ)) :
    (F.pairProductWord hdim).HasSamples L :=
  ⟨⟨((F.pairWord hdim).hasSamples_mapParams_iff Sum.inr).2
    (F.hasSamples_pairWord hdim h), h⟩, h⟩


/-- Equality of the actual germs represented by invertibly admissible pairs
is constructible over the common sample field. The source group kernel is
obtained by restricting both pairs to the actual domain. -/
theorem isConstructibleOver_pairKernel (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    {L : IntermediateField k K} (hFt : HasGenericSamples L a' (Fintype.card μ))
    (hsrc : HasGenericSamples L a (Fintype.card ((μ ⊕ μ) ⊕ (μ ⊕ μ)))) :
    IsConstructibleOver (↥L) {d : ((μ ⊕ μ) ⊕ (μ ⊕ μ)) → K |
      ∃ (hL : F.IsInvertiblePair a a' (d ∘ Sum.inl))
        (hR : F.IsInvertiblePair a a' (d ∘ Sum.inr)), F.pairGerm hL = F.pairGerm hR} := by
  let wL := (F.pairWord hdim).mapParams (Sum.inl : (μ ⊕ μ) → (μ ⊕ μ) ⊕ (μ ⊕ μ))
  let wR := (F.pairWord hdim).mapParams (Sum.inr : (μ ⊕ μ) → (μ ⊕ μ) ⊕ (μ ⊕ μ))
  have hsL : wL.HasSamples L :=
    ((F.pairWord hdim).hasSamples_mapParams_iff Sum.inl).2 (F.hasSamples_pairWord hdim hFt)
  have hsR : wR.HasSamples L :=
    ((F.pairWord hdim).hasSamples_mapParams_iff Sum.inr).2 (F.hasSamples_pairWord hdim hFt)
  convert (wL.isConstructibleOver_isInvertiblyAdmissible hsL).inter
    ((wR.isConstructibleOver_isInvertiblyAdmissible hsR).inter
      (Word.isConstructibleOver_germ_eq wL wR hsL hsR hsrc)) using 1
  ext d
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  have hInv (ρ : (μ ⊕ μ) → (μ ⊕ μ) ⊕ (μ ⊕ μ)) :
      ((F.pairWord hdim).mapParams ρ).IsInvertiblyAdmissible d ↔
        F.IsInvertiblePair a a' (d ∘ ρ) :=
    ((F.pairWord hdim).isInvertiblyAdmissible_mapParams_iff ρ d).trans
      (F.isInvertiblyAdmissible_pairWord_iff hdim (d ∘ ρ))
  have hG (ρ : (μ ⊕ μ) → (μ ⊕ μ) ⊕ (μ ⊕ μ))
      (hd : F.IsInvertiblePair a a' (d ∘ ρ)) :
      ((F.pairWord hdim).mapParams ρ).IsGerm d (F.pairGerm hd) :=
    ((F.pairWord hdim).isGerm_mapParams_iff ρ d _).2 (F.isGerm_pairGerm hdim hd)
  constructor
  · rintro ⟨hL, hR, heq⟩
    refine ⟨(hInv Sum.inl).2 hL, (hInv Sum.inr).2 hR, F.pairGerm hL, hG Sum.inl hL, ?_⟩
    rw [heq]
    exact hG Sum.inr hR
  · rintro ⟨hL, hR, g, hgL, hgR⟩
    let hdL := (hInv Sum.inl).1 hL
    let hdR := (hInv Sum.inr).1 hR
    exact ⟨hdL, hdR, ((hG Sum.inl hdL).unique hgL).trans ((hG Sum.inr hdR).unique hgR).symm⟩

/-- Swapping a candidate's two actual parameters represents its inverse.
Named consumer: the inverse relation of the constructible presentation. -/
theorem isInverse_pairGerm_swap {d : (μ ⊕ μ) → K} (hd : F.IsInvertiblePair a a' d) :
    Germ.IsInverse (F.pairGerm (d := d ∘ Sum.swap) ⟨hd.2, hd.1⟩) (F.pairGerm hd) := by
  let g₁ := F.parameterGerm hd.1.choose
  let g₂ := F.parameterGerm hd.2.choose
  let h₁ := Classical.choose hd.1.choose_spec
  let h₂ := Classical.choose hd.2.choose_spec
  have hi₁ : Germ.IsInverse h₁ g₁ := Classical.choose_spec hd.1.choose_spec
  have hi₂ : Germ.IsInverse h₂ g₂ := Classical.choose_spec hd.2.choose_spec
  constructor
  · change Germ.comp (Germ.comp h₂ g₁) (Germ.comp h₁ g₂) = Germ.id a
    rw [Germ.comp_assoc, ← Germ.comp_assoc g₁ h₁ g₂, hi₁.2, Germ.id_comp, hi₂.1]
  · change Germ.comp (Germ.comp h₁ g₂) (Germ.comp h₂ g₁) = Germ.id a
    rw [Germ.comp_assoc, ← Germ.comp_assoc g₂ h₂ g₁, hi₂.2, Germ.id_comp, hi₁.1]


/-- The actual multiplication relation of invertibly admissible pair germs is
constructible over the common sample field. Restricting its three pairs to
D_G gives the source group multiplication relation. -/
theorem isConstructibleOver_pairProduct (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    {L : IntermediateField k K} (hFt : HasGenericSamples L a' (Fintype.card μ))
    (hsrc : HasGenericSamples L a (Fintype.card (((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ)))) :
    IsConstructibleOver (↥L) {d : (((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ)) → K |
      ∃ (hL : F.IsInvertiblePair a a' ((d ∘ Sum.inl) ∘ Sum.inl))
        (hR : F.IsInvertiblePair a a' ((d ∘ Sum.inl) ∘ Sum.inr))
        (hT : F.IsInvertiblePair a a' (d ∘ Sum.inr)),
        Germ.comp (F.pairGerm hL) (F.pairGerm hR) = F.pairGerm hT} := by
  let wP := (F.pairProductWord hdim).mapParams
    (Sum.inl : ((μ ⊕ μ) ⊕ (μ ⊕ μ)) → ((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ))
  let wT := (F.pairWord hdim).mapParams
    (Sum.inr : (μ ⊕ μ) → ((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ))
  have hsP : wP.HasSamples L :=
    ((F.pairProductWord hdim).hasSamples_mapParams_iff Sum.inl).2
      (F.hasSamples_pairProductWord hdim hFt)
  have hsT : wT.HasSamples L :=
    ((F.pairWord hdim).hasSamples_mapParams_iff Sum.inr).2 (F.hasSamples_pairWord hdim hFt)
  convert (wP.isConstructibleOver_isInvertiblyAdmissible hsP).inter
    ((wT.isConstructibleOver_isInvertiblyAdmissible hsT).inter
      (Word.isConstructibleOver_germ_eq wP wT hsP hsT hsrc)) using 1
  ext d
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  have hP : wP.IsInvertiblyAdmissible d ↔
      F.IsInvertiblePair a a' ((d ∘ Sum.inl) ∘ Sum.inl) ∧
        F.IsInvertiblePair a a' ((d ∘ Sum.inl) ∘ Sum.inr) :=
    ((F.pairProductWord hdim).isInvertiblyAdmissible_mapParams_iff Sum.inl d).trans
      (F.isInvertiblyAdmissible_pairProductWord_iff hdim (d ∘ Sum.inl))
  have hT : wT.IsInvertiblyAdmissible d ↔ F.IsInvertiblePair a a' (d ∘ Sum.inr) :=
    ((F.pairWord hdim).isInvertiblyAdmissible_mapParams_iff Sum.inr d).trans
      (F.isInvertiblyAdmissible_pairWord_iff hdim (d ∘ Sum.inr))
  have hGP (hL : F.IsInvertiblePair a a' ((d ∘ Sum.inl) ∘ Sum.inl))
      (hR : F.IsInvertiblePair a a' ((d ∘ Sum.inl) ∘ Sum.inr)) :
      wP.IsGerm d (Germ.comp (F.pairGerm hL) (F.pairGerm hR)) :=
    ((F.pairProductWord hdim).isGerm_mapParams_iff Sum.inl d _).2
      (F.isGerm_pairProductWord hdim hL hR)
  have hGT (h : F.IsInvertiblePair a a' (d ∘ Sum.inr)) : wT.IsGerm d (F.pairGerm h) :=
    ((F.pairWord hdim).isGerm_mapParams_iff Sum.inr d _).2 (F.isGerm_pairGerm hdim h)
  constructor
  · rintro ⟨hL, hR, hTar, heq⟩
    refine ⟨hP.2 ⟨hL, hR⟩, hT.2 hTar, _, hGP hL hR, ?_⟩
    rw [heq]
    exact hGT hTar
  · rintro ⟨hProd, hTar, g, hgP, hgT⟩
    obtain ⟨hL, hR⟩ := hP.1 hProd
    let hTar' := hT.1 hTar
    exact ⟨hL, hR, hTar', ((hGP hL hR).unique hgP).trans ((hGT hTar').unique hgT).symm⟩

/-- The actual inverse relation of candidate pair germs is constructible:
swap the first pair's coordinates in the raw kernel relation. -/
theorem isConstructibleOver_pairInverse (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    {L : IntermediateField k K} (hFt : HasGenericSamples L a' (Fintype.card μ))
    (hsrc : HasGenericSamples L a (Fintype.card ((μ ⊕ μ) ⊕ (μ ⊕ μ)))) :
    IsConstructibleOver (↥L) {d : ((μ ⊕ μ) ⊕ (μ ⊕ μ)) → K |
      ∃ (hL : F.IsInvertiblePair a a' (d ∘ Sum.inl))
        (hR : F.IsInvertiblePair a a' (d ∘ Sum.inr)),
        Germ.IsInverse (F.pairGerm hR) (F.pairGerm hL)} := by
  let e : ((μ ⊕ μ) ⊕ (μ ⊕ μ)) → ((μ ⊕ μ) ⊕ (μ ⊕ μ)) :=
    Sum.elim (Sum.inl ∘ Sum.swap) Sum.inr
  convert (F.isConstructibleOver_pairKernel hdim hFt hsrc).preimage_comp e using 1
  ext d
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨hL, hR, hinv⟩
    refine ⟨⟨hL.2, hL.1⟩, hR, ?_⟩
    exact (F.isInverse_pairGerm_swap hL).unique hinv
  · rintro ⟨hL, hR, heq⟩
    let hOrig : F.IsInvertiblePair a a' (d ∘ Sum.inl) := ⟨hL.2, hL.1⟩
    have hinv : Germ.IsInverse (F.pairGerm hL) (F.pairGerm hOrig) :=
      F.isInverse_pairGerm_swap hOrig
    rw [heq] at hinv
    exact ⟨hOrig, hR, hinv⟩

end QuasiRational

end

end GroupConfig
