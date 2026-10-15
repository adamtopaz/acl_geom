/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.Triple
import GroupConfig.Constructible.Admissible

/-!
# The explicit representative of a germ from a triple

Blueprint `sources/group_configuration/04-germs.tex`, `lem:triple`(1), last clause.

Let `(b; y, z)` be a triple (`GroupConfig.IsTriple`) and `f` a quasi-rational expression over
`k` in the variables `(B, Y)` with `z = f(b, y)`. Then `f` is admissible at the parameter `b`,
and its parameter germ, the germ of the representative `(acl(b), f(b, ·))`, is the germ `g_b`
of the triple (`IsTriple.exists_parameterGerm_eq_germ`). For every automorphism `σ` the same
holds at `σ b`, with germ `σ g_b` (`IsTriple.exists_parameterGerm_eq`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the explicit-representative clause of `lem:triple`(1) complete.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

attribute [local instance] isAlgClosed_racl

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K] {ι κ μ : Type*} [Finite ι] [Finite κ] [Finite μ] {a : ι → K}
  {a' : κ → K} {b : μ → K} {y : ι → K} {z : κ → K}

namespace IsTriple

variable (h : IsTriple k a a' b y z)
include h

/-- `lem:triple`(1): an expression `f` over `k` with `z = f(b, y)` is admissible at `b`, and
the germ of the representative `(acl(b), f(b, ·))` is the germ of the triple. -/
theorem exists_parameterGerm_eq_germ (F : QuasiRational k (μ ⊕ ι) κ)
    (hF : F.IsDefinedAt (Sum.elim b y)) (hFz : F.eval (Sum.elim b y) = z) :
    ∃ hu : F.IsAdmissible a a' b, F.parameterGerm hu = h.germ := by
  have hy := h.isGenericOver_left
  have hz := h.isGenericOver_right
  have hu : F.IsAdmissible a a' b := by
    intro u hu
    obtain ⟨ρ, hρ⟩ := hy.exists_algEquiv hu
    -- The conjugation over `acl(b)` fixes `b` and moves `y` to `u`.
    have hθ : ⇑(ρ.restrictScalars k) ∘ Sum.elim b y = Sum.elim b u := by
      funext i
      cases i with
      | inl i => exact ρ.commutes ⟨b i, subset_racl k _ (mem_range_self i)⟩
      | inr i => exact hρ i
    refine ⟨?_, ?_⟩
    · rw [← hθ]
      exact (F.isDefinedAt_comp_iff _ _).2 hF
    · rw [← hθ, F.eval_comp, hFz]
      exact hz.comp ρ
  refine ⟨hu, h.eq_germ (F.cb_parameterGerm_le hu) ?_⟩
  have hM : IsSmall k ((racl k (range b) : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite (finite_range b)).racl
  rw [Germ.evalGen_eq _ hM (F.cb_parameterGerm_le hu) hy, F.eval_parameterGerm hu hy, hFz]

/-- `lem:triple`(1): for every automorphism `σ`, the expression is admissible at `σ b` and the
germ of `(acl(σ b), f(σ b, ·))` is `σ g_b`. -/
theorem exists_parameterGerm_eq (F : QuasiRational k (μ ⊕ ι) κ)
    (hF : F.IsDefinedAt (Sum.elim b y)) (hFz : F.eval (Sum.elim b y) = z) (σ : K ≃ₐ[k] K) :
    ∃ hu : F.IsAdmissible a a' (⇑σ ∘ b), F.parameterGerm hu = h.germ.map σ := by
  have hσ : ⇑σ ∘ Sum.elim b y = Sum.elim (⇑σ ∘ b) (⇑σ ∘ y) := Sum.comp_elim _ _ _
  rw [h.germ_map σ]
  refine (h.map σ).exists_parameterGerm_eq_germ F ?_ ?_
  · rw [← hσ]
    exact (F.isDefinedAt_comp_iff _ _).2 hF
  · rw [← hσ, F.eval_comp, hFz]

end IsTriple

end

end GroupConfig
