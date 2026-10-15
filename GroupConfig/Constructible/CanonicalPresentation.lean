/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Constructible.SpacePresentation
import GroupConfig.Germ.OrbitParameters
import GroupConfig.Germ.CanonicalCode

/-!
# The constructible group and homogeneous space, on the canonical code

Blueprint `sources/group_configuration/09-constructibility.tex`, `thm:constructible`, with the
family `F` of the source: `F(code f, y) = f(y)` for `f` in the generic set (`rem:code-param`),
evaluated on the actual canonical code tuple `code f₀` of the germ.

For a Hrushovski–Weil datum of bijections `f₀` and any small field `M₀`, the actual family `F`
on the canonical code is chosen by `GroupConfig.Germ.exists_orbit_admissibleFamily`, the equality
of dimensions is read off an inverse of `f₀`, and the samples are chosen by
`GroupConfig.QuasiRational.exists_fresh_constructibleGroupSpacePresentation`. The result
(`GroupConfig.Germ.IsHWBij.exists_fresh_canonicalGroupSpacePresentation`) is a constructible group
over the actual fresh field `k″ = k(t₀, t₁)`, presented by the literal domain of invertibly
admissible parameter pairs. For every generic point `y₀`, its stabiliser is constructible and
the homogeneous space has a constructible `G`-set presentation over `k″(y₀)`.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `thm:constructible` is complete on the canonical code, relative to a Hrushovski–Weil
datum of bijections.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
  [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]

namespace Germ

namespace IsHWBij

/-- `thm:constructible`, on the canonical code: for a Hrushovski–Weil datum of bijections `f₀`
and any small field `M₀`, an actual family `F` evaluating the orbit of `f₀` at the transports of
the canonical code `code f₀`, together with a first stage `t₀` of jointly independent generic
points of the source and target loci and a second stage `t₁` of generic points of the code locus
over `k(t₀)`, jointly fresh from `M₀`, such that the pair domain presents the group as a
constructible group over `k″ = k(t₀, t₁)`, and for every generic point `y₀` the stabiliser of
`ι(y₀)` is constructible over `k″(y₀)` and the homogeneous space is a constructible `G`-set over
`k″(y₀)`. -/
theorem exists_fresh_canonicalGroupSpacePresentation {ι κ : Type w} [Fintype ι] [Finite κ]
    {a : ι → K} {a' : κ → K} {f₀ : Germ k a a'} (hb : f₀.IsHWBij)
    [Fintype (CodeIndex (ι ⊕ κ) (genDeg f₀.graphIdeal))] {δ₀ : Germ k a a}
    (hδ₀ : δ₀ ∈ f₀.diffSet) (M₀ : IntermediateField k K) (hM₀ : IsSmall k (M₀ : Set K)) :
    ∃ (F : QuasiRational k (CodeIndex (ι ⊕ κ) (genDeg f₀.graphIdeal) ⊕ ι) κ)
      (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ f₀.code),
        F.parameterGerm hu = f₀.map σ)
      (hdim : erk k ∅ (range a) = erk k ∅ (range a')),
    ∃ (S₀ : Set K) (t₁ : Fin (2 * (6 * Fintype.card (CodeIndex (ι ⊕ κ) (genDeg f₀.graphIdeal)) +
        Fintype.card ι) + 1) → CodeIndex (ι ⊕ κ) (genDeg f₀.graphIdeal) → K),
      S₀.Finite ∧ IndepOver k ∅ S₀ (M₀ : Set K) ∧
      (∃ T : List (Σ τ : Type w, (τ → K) × (τ → K)),
        (∀ p ∈ T, ((⟨p.1, p.2.1⟩ : Σ τ : Type w, τ → K) = ⟨ι, a⟩ ∨
            (⟨p.1, p.2.1⟩ : Σ τ : Type w, τ → K) = ⟨κ, a'⟩) ∧
          IsGenericOver (⊥ : IntermediateField k K) p.2.1 p.2.2) ∧
        S₀ = (⋃ p ∈ T, range p.2.2) ∧
        erk k ∅ S₀ = (T.map fun p ↦ erk k ∅ (range p.2.2)).sum) ∧
      HasGenericSamples (adjoin k S₀) a
        (8 * Fintype.card (CodeIndex (ι ⊕ κ) (genDeg f₀.graphIdeal))) ∧
      HasGenericSamples (adjoin k S₀) a' (Fintype.card (CodeIndex (ι ⊕ κ) (genDeg f₀.graphIdeal))) ∧
      (∀ i, IsGenericOver (⊥ : IntermediateField k K) f₀.code (t₁ i)) ∧
      (∀ i, IsGenericOver (adjoin k S₀) f₀.code (t₁ i)) ∧
      erk k (adjoin k S₀ : Set K) (⋃ i, range (t₁ i)) =
        ∑ i, erk k (adjoin k S₀ : Set K) (range (t₁ i)) ∧
      IndepOver k ∅ (S₀ ∪ ⋃ i, range (t₁ i)) (M₀ : Set K) ∧
      erk k ∅ (S₀ ∪ ⋃ i, range (t₁ i)) = erk k ∅ S₀ + ∑ i, erk k ∅ (range (t₁ i)) ∧
      ∃ hL : IsSmall k ((adjoin k (S₀ ∪ ⋃ i, range (t₁ i)) : IntermediateField k K) : Set K),
        ConstructibleGroupPresentation (adjoin k (S₀ ∪ ⋃ i, range (t₁ i)))
          (F.pairDomain (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) f₀.code a a')
          (F.pairDomainMap (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) hL hb hδ₀ f₀.adjoin_range_code hF
            hdim) ∧
        ∀ (y₀ : ι → K) (hy₀ : IsGen k a y₀),
          IsConstructibleOver (↥(adjoin k ((S₀ ∪ ⋃ i, range (t₁ i)) ∪ range y₀)))
            {d | ∃ hd : d ∈ F.pairDomain (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) f₀.code a a',
              F.pairDomainMap (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) hL hb hδ₀ f₀.adjoin_range_code
                hF hdim
                ⟨d, hd⟩ • (hb.isHW hδ₀).iota hy₀ = (hb.isHW hδ₀).iota hy₀} ∧
          ConstructibleGSetPresentation (adjoin k ((S₀ ∪ ⋃ i, range (t₁ i)) ∪ range y₀))
            (F.pairDomain (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) f₀.code a a')
            (F.pairDomainMap (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) hL hb hδ₀ f₀.adjoin_range_code hF
              hdim)
            (F.pairDomain (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) f₀.code a a')
            (F.pairDomainSpaceMap (adjoin k (S₀ ∪ ⋃ i, range (t₁ i))) hL hb hδ₀ f₀.adjoin_range_code
              hF hdim hy₀) := by
  -- The actual family of the source on the canonical code.
  obtain ⟨F, hF⟩ := exists_orbit_admissibleFamily f₀ f₀.adjoin_range_code
  -- The loci have equal dimension, by an inverse of `f₀`.
  obtain ⟨h, hi⟩ := hb.isInvertible
  exact ⟨F, hF, hi.erk_eq, F.exists_fresh_constructibleGroupSpacePresentation hb hδ₀
    f₀.adjoin_range_code hF hi.erk_eq M₀ hM₀⟩

end IsHWBij

end Germ

end

end GroupConfig
