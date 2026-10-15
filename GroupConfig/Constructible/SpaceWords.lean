/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Constructible.PairRelations

/-!
# Words for the homogeneous space

Blueprint `sources/group_configuration/09-constructibility.tex`, `thm:constructible`(2): the
quotient `G/H` is presented by the domain `D_G` with the kernel relation `ρ(d)⁻¹ ρ(d') ∈ H` and
the action relation `ρ(t)⁻¹ ρ(g) ρ(x) ∈ H`. This module supplies the words for the two germs.

* Swapping the parameters of a pair preserves invertible admissibility
  (`GroupConfig.QuasiRational.isInvertiblePair_comp_swap_iff`).
* The kernel word on `(L, R)` represents `ρ(L)⁻¹ ρ(R)`
  (`GroupConfig.QuasiRational.isGerm_spaceKernelWord`).
* The action word on `((G, X), T)` represents `ρ(T)⁻¹ ρ(G) ρ(X)`
  (`GroupConfig.QuasiRational.isGerm_spaceActionWord`).
* All letters of each word are invertibly admissible exactly when the input pairs are, and the
  samples of the target locus serve every letter.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the words of the space kernel and action relations are complete. Their restriction
to the domain and the presentation of `G/H` are not part of this module.
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

/-- Swapping the two parameters of a pair preserves invertible admissibility. Named consumers:
the invertibility statements of the kernel and action words. -/
theorem isInvertiblePair_comp_swap_iff {x : (μ ⊕ μ) → K} :
    F.IsInvertiblePair a a' (x ∘ Sum.swap) ↔ F.IsInvertiblePair a a' x :=
  ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

/-- The word for `ρ(L)⁻¹ ρ(R)` on a pair of pairs `(L, R)`: the product word with the first pair
swapped. Named consumer: the kernel relation of the homogeneous space. -/
def spaceKernelWord (hdim : erk k ∅ (range a) = erk k ∅ (range a')) :
    Word k ((μ ⊕ μ) ⊕ (μ ⊕ μ)) a a :=
  (F.pairProductWord hdim).mapParams (Sum.elim (Sum.inl ∘ Sum.swap) Sum.inr)

/-- The kernel word represents `ρ(L)⁻¹ ρ(R)`. -/
theorem isGerm_spaceKernelWord (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    {d : ((μ ⊕ μ) ⊕ (μ ⊕ μ)) → K} (hL : F.IsInvertiblePair a a' (d ∘ Sum.inl))
    (hR : F.IsInvertiblePair a a' (d ∘ Sum.inr)) :
    (F.spaceKernelWord hdim).IsGerm d
      (Germ.comp (F.pairGerm (d := (d ∘ Sum.inl) ∘ Sum.swap) ⟨hL.2, hL.1⟩) (F.pairGerm hR)) :=
  ((F.pairProductWord hdim).isGerm_mapParams_iff _ d _).2
    (F.isGerm_pairProductWord hdim (d := d ∘ Sum.elim (Sum.inl ∘ Sum.swap) Sum.inr)
      ⟨hL.2, hL.1⟩ hR)

/-- Every letter of the kernel word is invertibly admissible exactly when both pairs are
invertibly admissible. -/
theorem isInvertiblyAdmissible_spaceKernelWord_iff
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) (d : ((μ ⊕ μ) ⊕ (μ ⊕ μ)) → K) :
    (F.spaceKernelWord hdim).IsInvertiblyAdmissible d ↔
      F.IsInvertiblePair a a' (d ∘ Sum.inl) ∧ F.IsInvertiblePair a a' (d ∘ Sum.inr) :=
  ((F.pairProductWord hdim).isInvertiblyAdmissible_mapParams_iff _ d).trans
    ((F.isInvertiblyAdmissible_pairProductWord_iff hdim _).trans
      (and_congr (F.isInvertiblePair_comp_swap_iff (x := d ∘ Sum.inl)) Iff.rfl))

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] in
/-- The samples of the target locus serve every letter of the kernel word. -/
theorem hasSamples_spaceKernelWord (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    {L : IntermediateField k K} (h : HasGenericSamples L a' (Fintype.card μ)) :
    (F.spaceKernelWord hdim).HasSamples L :=
  ((F.pairProductWord hdim).hasSamples_mapParams_iff _).2 (F.hasSamples_pairProductWord hdim h)

/-- The word for `ρ(T)⁻¹ ρ(G) ρ(X)` on `((G, X), T)`: the product word, followed by the letters of
`T` in reverse. Named consumer: the action relation of the homogeneous space. -/
def spaceActionWord (hdim : erk k ∅ (range a) = erk k ∅ (range a')) :
    Word k (((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ)) a a :=
  .inv (.fwd ((F.pairProductWord hdim).mapParams Sum.inl) a' F (Sum.inr ∘ Sum.inl) hdim)
    a F (Sum.inr ∘ Sum.inr) hdim

/-- The action word represents `ρ(T)⁻¹ ρ(G) ρ(X)`. -/
theorem isGerm_spaceActionWord (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    {d : (((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ)) → K}
    (hG : F.IsInvertiblePair a a' ((d ∘ Sum.inl) ∘ Sum.inl))
    (hX : F.IsInvertiblePair a a' ((d ∘ Sum.inl) ∘ Sum.inr))
    (hT : F.IsInvertiblePair a a' (d ∘ Sum.inr)) :
    (F.spaceActionWord hdim).IsGerm d
      (Germ.comp (F.pairGerm (d := (d ∘ Sum.inr) ∘ Sum.swap) ⟨hT.2, hT.1⟩)
        (Germ.comp (F.pairGerm hG) (F.pairGerm hX))) := by
  refine ⟨Germ.comp (F.parameterGerm hT.1.choose) (Germ.comp (F.pairGerm hG) (F.pairGerm hX)),
    hT.2.choose, Classical.choose hT.2.choose_spec, ?_, Classical.choose_spec hT.2.choose_spec,
    ?_⟩
  · refine ⟨Germ.comp (F.pairGerm hG) (F.pairGerm hX), hT.1.choose, ?_, rfl⟩
    exact ((F.pairProductWord hdim).isGerm_mapParams_iff Sum.inl d _).2
      (F.isGerm_pairProductWord hdim hG hX)
  · exact Germ.comp_assoc _ _ _

/-- Every letter of the action word is invertibly admissible exactly when the three pairs are
invertibly admissible. -/
theorem isInvertiblyAdmissible_spaceActionWord_iff
    (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    (d : (((μ ⊕ μ) ⊕ (μ ⊕ μ)) ⊕ (μ ⊕ μ)) → K) :
    (F.spaceActionWord hdim).IsInvertiblyAdmissible d ↔
      F.IsInvertiblePair a a' ((d ∘ Sum.inl) ∘ Sum.inl) ∧
        F.IsInvertiblePair a a' ((d ∘ Sum.inl) ∘ Sum.inr) ∧
        F.IsInvertiblePair a a' (d ∘ Sum.inr) := by
  have hP := (F.pairProductWord hdim).isInvertiblyAdmissible_mapParams_iff Sum.inl d
  constructor
  · rintro ⟨⟨hw, h₁⟩, h₂⟩
    obtain ⟨hG, hX⟩ := (F.isInvertiblyAdmissible_pairProductWord_iff hdim _).1 (hP.1 hw)
    exact ⟨hG, hX, h₁, h₂⟩
  · rintro ⟨hG, hX, h₁, h₂⟩
    exact ⟨⟨hP.2 ((F.isInvertiblyAdmissible_pairProductWord_iff hdim _).2 ⟨hG, hX⟩), h₁⟩, h₂⟩

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] in
/-- The samples of the target locus serve every letter of the action word. -/
theorem hasSamples_spaceActionWord (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    {L : IntermediateField k K} (h : HasGenericSamples L a' (Fintype.card μ)) :
    (F.spaceActionWord hdim).HasSamples L :=
  ⟨⟨((F.pairProductWord hdim).hasSamples_mapParams_iff Sum.inl).2
    (F.hasSamples_pairProductWord hdim h), h⟩, h⟩

end QuasiRational

end

end GroupConfig
