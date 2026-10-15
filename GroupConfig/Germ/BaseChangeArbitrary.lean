/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.BaseChangeGroup
import GroupConfig.Germ.Transport

/-!
# Base change of a Hrushovski–Weil datum to an arbitrary field

Blueprint `sources/group_configuration/08-proof.tex`, `lem:hw-basechange`, for an arbitrary tuple
`e`, i.e. an arbitrary small algebraically closed intermediate field `K₁ ⊇ K₀`.

`GroupConfig.Germ.BaseChangeHW` and `GroupConfig.Germ.BaseChangeGroup` treat the case where the
tuples `a`, `a'` representing `V`, `V'` are independent from `K₁` over `K₀`. In general the
`K₁`-varieties `V`, `V'` (with the same ideals) are represented by tuples `a₁`, `a'₁` generic
over `K₁` (`exists_idealOf_eq_indepOver`), and germs are first transported to these tuples
(`GroupConfig.Germ.transport`). A member of the generic set independent from `K₁` exists
(`Germ.exists_mem_orbit_indepOver`) and is again a Hrushovski–Weil datum
(`Germ.IsHWBij.of_mem_orbit`, `Germ.IsHW.of_mem_orbit`). Its transport and base change is a
Hrushovski–Weil datum over `K₁` whose generic set is the set of base changes of the members
independent from `K₁` (`Germ.IsHWBij.baseChange_transport`,
`Germ.baseChange_transport_mem_orbit`, `Germ.exists_of_mem_orbit_baseChange_transport`), whose
difference set is the set of transported base changes of the independent difference germs
(`Germ.baseChange_transport_mem_diffSet`, `Germ.exists_of_mem_diffSet_baseChange_transport`), with
the same group (`Germ.IsHW.baseChangeTransportGroupEquiv`) and homogeneous space
(`Germ.IsHW.baseChangeTransportSpaceEquiv`).

`K₁` is a small subfield, as in the universal-domain framework of the blueprint.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `lem:hw-basechange` for an arbitrary small algebraically closed `K₁` complete.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] {ι κ : Type*}
  [Finite ι] [Finite κ] {a : ι → K} {a' : κ → K}

namespace Germ

section Orbit

variable [IsAlgClosed k] [UniversalDomain k K]

/-- A member of the generic set of a Hrushovski–Weil datum of bijections is one. -/
theorem IsHWBij.of_mem_orbit {f₀ f : Germ k a a'} (hb : IsHWBij f₀) (hf : f ∈ orbit f₀) :
    IsHWBij f := by
  have ho := orbit_eq_of_mem hf
  have hd : diffSet f = diffSet f₀ := by
    unfold diffSet
    rw [ho]
  refine ⟨isInvertible_of_mem_orbit hb.isInvertible hf, ?_, ?_⟩
  · rw [ho]
    exact hb.trans
  · rw [hd, erk_cb_eq_of_mem_orbit hf]
    exact hb.rank

/-- A member of the generic set of a Hrushovski–Weil datum is one. -/
theorem IsHW.of_mem_orbit {g₀ g : Germ k a a} (hw : IsHW g₀) (hg : g ∈ orbit g₀) : IsHW g := by
  have ho := orbit_eq_of_mem hg
  refine ⟨isUnit_of_mem_orbit hw.isUnit hg, ?_, ?_, ?_⟩
  · rw [ho]
    exact hw.trans
  · rw [ho]
    exact hw.inv
  · rw [ho]
    exact hw.comp

end Orbit

variable (K₀ K₁ : IntermediateField k K) [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)]
  [UniversalDomain (↥K₀) K] [UniversalDomain (↥K₁) K] (h₀₁ : K₀ ≤ K₁)
  (hK₁ : IsSmall (↥K₀) (K₁ : Set K))

omit [IsAlgClosed (↥K₁)] [UniversalDomain (↥K₁) K] in
include hK₁ in
/-- A locus over `K₀` has a representing tuple, with the same ideal, independent from `K₁`. -/
theorem exists_idealOf_eq_indepOver (a : ι → K) :
    ∃ a₁ : ι → K, idealOf (↥K₀) a₁ = idealOf (↥K₀) a ∧
      IndepOver (↥K₀) ∅ (range a₁) (K₁ : Set K) := by
  obtain ⟨a₁, ha₁⟩ := exists_isGenericOver (k := ↥K₀) hK₁.racl a
  exact ⟨a₁, ha₁.isGen, ha₁.indepOver.mono_right (subset_racl (↥K₀) _)⟩

variable {a₁ : ι → K} {a'₁ : κ → K} (h : idealOf (↥K₀) a₁ = idealOf (↥K₀) a)
  (h' : idealOf (↥K₀) a'₁ = idealOf (↥K₀) a')
  (ha : IndepOver (↥K₀) ∅ (range a₁) (K₁ : Set K))
  (ha' : IndepOver (↥K₀) ∅ (range a'₁) (K₁ : Set K))

omit [IsAlgClosed (↥K₁)] [UniversalDomain (↥K₁) K] in
theorem indepOver_cb_transport_iff {g : Germ (↥K₀) a a'} :
    IndepOver (↥K₀) ∅ ((g.transport h h').cb : Set K) (K₁ : Set K) ↔
      IndepOver (↥K₀) ∅ (g.cb : Set K) (K₁ : Set K) := by
  rw [cb_transport]

/-- `lem:hw-basechange`, arbitrary `K₁`: transported base changes of members of the generic set
independent from `K₁` lie in the generic set of the transported base change. -/
theorem baseChange_transport_mem_orbit {f₀ g : Germ (↥K₀) a a'}
    (h₀ : IndepOver (↥K₀) ∅ (f₀.cb : Set K) (K₁ : Set K)) (hg : g ∈ orbit f₀)
    (hgK : IndepOver (↥K₀) ∅ (g.cb : Set K) (K₁ : Set K)) :
    (g.transport h h').baseChange K₀ K₁ h₀₁ hK₁ ha ha' ∈
      orbit ((f₀.transport h h').baseChange K₀ K₁ h₀₁ hK₁ ha ha') :=
  baseChange_mem_orbit K₀ K₁ h₀₁ hK₁ ha ha' ((indepOver_cb_transport_iff K₀ K₁ h h').2 h₀)
    ((transport_mem_orbit_iff h h').2 hg) ((indepOver_cb_transport_iff K₀ K₁ h h').2 hgK)

/-- `lem:hw-basechange`, arbitrary `K₁`: every member of the generic set of the transported base
change is the transported base change of a member independent from `K₁`. -/
theorem exists_of_mem_orbit_baseChange_transport {f₀ : Germ (↥K₀) a a'}
    (h₀ : IndepOver (↥K₀) ∅ (f₀.cb : Set K) (K₁ : Set K)) {f : Germ (↥K₁) a₁ a'₁}
    (hf : f ∈ orbit ((f₀.transport h h').baseChange K₀ K₁ h₀₁ hK₁ ha ha')) :
    ∃ g ∈ orbit f₀, IndepOver (↥K₀) ∅ (g.cb : Set K) (K₁ : Set K) ∧
      (g.transport h h').baseChange K₀ K₁ h₀₁ hK₁ ha ha' = f := by
  obtain ⟨g', hg', hgK, rfl⟩ := exists_of_mem_orbit_baseChange K₀ K₁ h₀₁ hK₁ ha ha'
    ((indepOver_cb_transport_iff K₀ K₁ h h').2 h₀) hf
  obtain ⟨g, hg, rfl⟩ := exists_of_mem_orbit_transport h h' hg'
  exact ⟨g, hg, (indepOver_cb_transport_iff K₀ K₁ h h').1 hgK, rfl⟩

/-- `lem:hw-basechange`, arbitrary `K₁`: transported base changes of difference germs independent
from `K₁` are difference germs of the transported base change. -/
theorem baseChange_transport_mem_diffSet {f₀ : Germ (↥K₀) a a'}
    (h₀ : IndepOver (↥K₀) ∅ (f₀.cb : Set K) (K₁ : Set K)) {δ : Germ (↥K₀) a a}
    (hδ : δ ∈ diffSet f₀) (hδK : IndepOver (↥K₀) ∅ (δ.cb : Set K) (K₁ : Set K)) :
    (δ.transport h h).baseChange K₀ K₁ h₀₁ hK₁ ha ha ∈
      diffSet ((f₀.transport h h').baseChange K₀ K₁ h₀₁ hK₁ ha ha') :=
  baseChange_mem_diffSet K₀ K₁ h₀₁ hK₁ ha ha' ((indepOver_cb_transport_iff K₀ K₁ h h').2 h₀)
    ((transport_mem_diffSet_iff h h').2 hδ) ((indepOver_cb_transport_iff K₀ K₁ h h).2 hδK)

/-- `lem:hw-basechange`, arbitrary `K₁`: every difference germ of the transported base change is
the transported base change of a difference germ independent from `K₁`. -/
theorem exists_of_mem_diffSet_baseChange_transport {f₀ : Germ (↥K₀) a a'}
    (hf₀ : IsInvertible f₀) (h₀ : IndepOver (↥K₀) ∅ (f₀.cb : Set K) (K₁ : Set K))
    {δ : Germ (↥K₁) a₁ a₁}
    (hδ : δ ∈ diffSet ((f₀.transport h h').baseChange K₀ K₁ h₀₁ hK₁ ha ha')) :
    ∃ δ₀ ∈ diffSet f₀, IndepOver (↥K₀) ∅ (δ₀.cb : Set K) (K₁ : Set K) ∧
      (δ₀.transport h h).baseChange K₀ K₁ h₀₁ hK₁ ha ha = δ := by
  obtain ⟨δ', hδ', hδ'K, rfl⟩ := exists_of_mem_diffSet_baseChange K₀ K₁ h₀₁ hK₁ ha ha'
    ((isInvertible_transport_iff h h').2 hf₀) ((indepOver_cb_transport_iff K₀ K₁ h h').2 h₀) hδ
  obtain ⟨δ₀, hδ₀, rfl⟩ := exists_of_mem_diffSet_transport h h' hδ'
  exact ⟨δ₀, hδ₀, (indepOver_cb_transport_iff K₀ K₁ h h).1 hδ'K, rfl⟩

/-- `lem:hw-basechange`, arbitrary `K₁`: a member of the generic set of a Hrushovski–Weil datum
of bijections independent from `K₁`, transported to representing tuples independent from `K₁`
and base-changed, is a Hrushovski–Weil datum of bijections over `K₁`. -/
theorem IsHWBij.baseChange_transport {f₀ f₁ : Germ (↥K₀) a a'} (hb : IsHWBij f₀)
    (hf₁ : f₁ ∈ orbit f₀) (h₁ : IndepOver (↥K₀) ∅ (f₁.cb : Set K) (K₁ : Set K)) :
    IsHWBij ((f₁.transport h h').baseChange K₀ K₁ h₀₁ hK₁ ha ha') :=
  ((hb.of_mem_orbit hf₁).transport h h').baseChange K₀ K₁ h₀₁ hK₁ ha ha'
    ((indepOver_cb_transport_iff K₀ K₁ h h').2 h₁)

/-- `lem:hw-basechange`, arbitrary `K₁`, for a Hrushovski–Weil datum on `V`. -/
theorem IsHW.baseChange_transport {g₀ g₁ : Germ (↥K₀) a a} (hw : IsHW g₀)
    (hg₁ : g₁ ∈ orbit g₀) (h₁ : IndepOver (↥K₀) ∅ (g₁.cb : Set K) (K₁ : Set K)) :
    IsHW ((g₁.transport h h).baseChange K₀ K₁ h₀₁ hK₁ ha ha) :=
  ((hw.of_mem_orbit hg₁).transport h).baseChange K₀ K₁ h₀₁ hK₁ ha
    ((indepOver_cb_transport_iff K₀ K₁ h h).2 h₁)

namespace IsHW

variable {g₀ : Germ (↥K₀) a a} (hw : IsHW g₀)
  (h₀ : IndepOver (↥K₀) ∅ (g₀.cb : Set K) (K₁ : Set K))

/-- `lem:hw-basechange`, arbitrary `K₁`: the group generated by the generic set over `K₁` is the
group `G`. -/
def baseChangeTransportGroupEquiv : ↥hw.prodSubgroup ≃*
    ↥((hw.transport h).baseChange K₀ K₁ h₀₁ hK₁ ha
      ((indepOver_cb_transport_iff K₀ K₁ h h).2 h₀)).prodSubgroup :=
  (hw.transportGroupEquiv h).trans (prodSubgroupEquiv K₀ K₁ h₀₁ hK₁ ha (hw.transport h)
    ((indepOver_cb_transport_iff K₀ K₁ h h).2 h₀))

theorem val_baseChangeTransportGroupEquiv (δ : ↥hw.prodSubgroup) :
    ((hw.transport h).baseChange K₀ K₁ h₀₁ hK₁ ha
      ((indepOver_cb_transport_iff K₀ K₁ h h).2 h₀)).val
        (baseChangeTransportGroupEquiv K₀ K₁ h₀₁ hK₁ h ha hw h₀ δ) =
      ((hw.val δ).transport h h).baseChange K₀ K₁ h₀₁ hK₁ ha ha := rfl

/-- `lem:hw-basechange`, arbitrary `K₁`: the homogeneous space over `K₁` is the homogeneous space
`S`. -/
def baseChangeTransportSpaceEquiv :
    ((hw.transport h).baseChange K₀ K₁ h₀₁ hK₁ ha
      ((indepOver_cb_transport_iff K₀ K₁ h h).2 h₀)).Space ≃ hw.Space :=
  (spaceEquiv K₀ K₁ h₀₁ hK₁ ha (hw.transport h)
    ((indepOver_cb_transport_iff K₀ K₁ h h).2 h₀)).trans (hw.transportSpaceEquiv h).symm

/-- `lem:hw-basechange`, arbitrary `K₁`: the identification of homogeneous spaces is equivariant
along the identification of groups. -/
theorem baseChangeTransportSpaceEquiv_smul (δ : ↥hw.prodSubgroup)
    (s : ((hw.transport h).baseChange K₀ K₁ h₀₁ hK₁ ha
      ((indepOver_cb_transport_iff K₀ K₁ h h).2 h₀)).Space) :
    baseChangeTransportSpaceEquiv K₀ K₁ h₀₁ hK₁ h ha hw h₀
        (baseChangeTransportGroupEquiv K₀ K₁ h₀₁ hK₁ h ha hw h₀ δ • s) =
      δ • baseChangeTransportSpaceEquiv K₀ K₁ h₀₁ hK₁ h ha hw h₀ s := by
  simp only [baseChangeTransportSpaceEquiv, baseChangeTransportGroupEquiv, Equiv.trans_apply,
    MulEquiv.trans_apply]
  rw [spaceEquiv_smul, Equiv.symm_apply_eq, transportSpaceEquiv_smul, Equiv.apply_symm_apply]

/-- `lem:hw-basechange`, arbitrary `K₁`: the identification of homogeneous spaces is compatible
with the embeddings of the generic points. -/
theorem baseChangeTransportSpaceEquiv_iota {y : ι → K} (hy : IsGen (↥K₁) a₁ y) :
    baseChangeTransportSpaceEquiv K₀ K₁ h₀₁ hK₁ h ha hw h₀
        (((hw.transport h).baseChange K₀ K₁ h₀₁ hK₁ ha
          ((indepOver_cb_transport_iff K₀ K₁ h h).2 h₀)).iota hy) =
      hw.iota ((isGen_iff_of_idealOf_eq h y).1 ((isGen_base_iff K₀ K₁ h₀₁ hK₁ ha).1 hy).1) := by
  simp only [baseChangeTransportSpaceEquiv, Equiv.trans_apply]
  rw [spaceEquiv_iota, Equiv.symm_apply_eq, transportSpaceEquiv_iota]

end IsHW

end Germ

end

end GroupConfig
