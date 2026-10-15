/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Constructible.Admissible
import GroupConfig.Germ.CompCodes
import GroupConfig.Germ.GroupStructure

/-!
# Membership in the group through generic parameters

Blueprint `sources/group_configuration/09-constructibility.tex`, `thm:constructible`(1): the
condition `(∗)` characterises `G` inside the invertible germs.

Let `f₀` be a Hrushovski–Weil datum of bijections (`thm:hw-bij`) with generic set `𝓕` and group
`G`, let `c` generate `Cb(f₀)`, and let `F` be an actual family whose parameter germ at every
transport `σ c` is `σ f₀` (as produced by `GroupConfig.Germ.exists_orbit_admissibleFamily`).
Write `W` for the locus of `c`.

* Every generic point `v` of `W` is an admissible parameter whose germ `g_v` lies in `𝓕`
  (`GroupConfig.QuasiRational.exists_parameterGerm_mem_orbit_of_isGen`).
* A point `u'` of `W` at which `F` is admissible, with a germ of rank at least `rk Cb(f₀)`, is
  generic, so `g_{u'}` lies in `𝓕` (`GroupConfig.QuasiRational.parameterGerm_mem_orbit_of_inLocus`).
* An invertible germ `γ` with `Cb(γ) ⊆ M` lies in `G` exactly when, for every `v` generic in
  `W` over `M`, some `u' ∈ W(K)` with an admissible invertible germ has `g_v γ = g_{u'}`
  (`GroupConfig.Germ.IsHWBij.mem_prodSet_iff_forall_isGenericOver`). For the converse one such
  `v` suffices and the witness need not be invertible
  (`GroupConfig.Germ.IsHWBij.mem_prodSet_of_isGenericOver`). The witness is not assumed generic:
  its rank is forced by `rk(g_v γ / γ) = rk(g_v / γ)`, and `γ` is then `g_v⁻¹ (g_v γ)`.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the characterisation of `G` by `(∗)` in `thm:constructible`(1) is complete for an
arbitrary invertible germ. The domain `D_G` and its constructibility are not part of this
module.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K] {ι κ μ : Type*} [Finite ι] [Finite κ] [Finite μ] {a : ι → K}
  {a' : κ → K}

attribute [local instance] isAlgClosed_racl

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite μ] in
/-- A generic point of a locus over `k` is a point of the locus. -/
theorem IsGen.inLocus {c u : μ → K} (h : IsGen k c u) : InLocus (k := k) c u := by
  change locusIdeal k c ≤ idealOf K u
  have h1 : locusIdeal k u = locusIdeal k c := by
    unfold locusIdeal
    rw [show idealOf k u = idealOf k c from h]
  rw [← h1]
  exact inLocus_self (k := k) u

namespace QuasiRational

variable {f₀ : Germ k a a'} {F : QuasiRational k (μ ⊕ ι) κ} {c : μ → K}

omit [Finite κ] in
/-- Every generic point of the locus of `c` is an admissible parameter of `F` whose germ lies
in the orbit of `f₀`. -/
theorem exists_parameterGerm_mem_orbit_of_isGen
    (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
      F.parameterGerm hu = f₀.map σ)
    {v : μ → K} (hv : IsGen k c v) :
    ∃ hv' : F.IsAdmissible a a' v, F.parameterGerm hv' ∈ Germ.orbit f₀ := by
  obtain ⟨σ, -, hσ⟩ := exists_ambientAutomorphism_of_idealOf_eq (k := k)
    (show idealOf k c = idealOf k v from hv.symm)
  obtain ⟨hu, hug⟩ := hF σ
  obtain rfl : ⇑σ ∘ c = v := funext hσ
  exact ⟨hu, σ, hug.symm⟩

/-- `thm:constructible`(1), the rank argument: a point `u'` of the locus of `c` at which `F`
is admissible with a germ of rank at least that of `f₀` is generic, so its germ lies in the
orbit of `f₀`. -/
theorem parameterGerm_mem_orbit_of_inLocus (hc : adjoin k (range c) = f₀.cb)
    (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
      F.parameterGerm hu = f₀.map σ)
    {u' : μ → K} (hu' : F.IsAdmissible a a' u') (hV : InLocus (k := k) c u')
    (hrk : erk k ∅ (f₀.cb : Set K) ≤ erk k ∅ ((F.parameterGerm hu').cb : Set K)) :
    F.parameterGerm hu' ∈ Germ.orbit f₀ := by
  have hs : IsSmall k ((racl k (∅ : Set K) : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite finite_empty).racl
  have hle := erk_le_of_inLocus hs hV
  rw [erk_racl_base] at hle
  have hge : erk k ∅ (range c) ≤ erk k ∅ (range u') :=
    calc erk k ∅ (range c) = erk k ∅ (f₀.cb : Set K) := by rw [← hc, erk_adjoin_eq]
      _ ≤ erk k ∅ ((F.parameterGerm hu').cb : Set K) := hrk
      _ ≤ erk k ∅ (racl k (∅ ∪ range u') : Set K) := erk_mono k _ fun x hx ↦ by
          rw [empty_union]
          exact F.cb_parameterGerm_le hu' hx
      _ = erk k ∅ (range u') := erk_racl k _ _
  have hgen : IsGenericOver (racl k (∅ : Set K)) c u' := by
    refine (isGenericOver_iff_erk_eq hs hV).2 ?_
    rw [erk_racl_base]
    exact le_antisymm hle hge
  obtain ⟨hu'', hmem⟩ := exists_parameterGerm_mem_orbit_of_isGen hF hgen.isGen
  exact hmem

end QuasiRational

namespace Germ

namespace IsHWBij

variable {f₀ : Germ k a a'} (hb : IsHWBij f₀) {δ₀ : Germ k a a} (hδ₀ : δ₀ ∈ diffSet f₀)
  {F : QuasiRational k (μ ⊕ ι) κ} {c : μ → K}

/-- The germ at a parameter generic over a field containing `Cb(γ)` is in the generic set and
independent from `γ`. -/
private theorem exists_indepOver_of_isGenericOver
    (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
      F.parameterGerm hu = f₀.map σ)
    {γ : Germ k a a} {M : IntermediateField k K} (hγM : γ.cb ≤ M) {v : μ → K}
    (hv : IsGenericOver M c v) :
    ∃ hv' : F.IsAdmissible a a' v, F.parameterGerm hv' ∈ orbit f₀ ∧
      IndepOver k ∅ (γ.cb : Set K) ((F.parameterGerm hv').cb : Set K) := by
  obtain ⟨hv', hmem⟩ := QuasiRational.exists_parameterGerm_mem_orbit_of_isGen hF hv.isGen
  refine ⟨hv', hmem, ?_⟩
  have h := indepOver_racl_left_iff.2 hv.indepOver
  rw [empty_union] at h
  exact ((h.mono_left (F.cb_parameterGerm_le hv')).mono_right hγM).symm

include hb hδ₀

/-- `thm:constructible`(1), `(∗)` for elements of `G`: for `γ ∈ G` and every `v` generic in
the locus of `c` over a field containing `Cb(γ)`, some point `u'` of the locus with an
admissible invertible germ has `g_v γ = g_{u'}`. -/
theorem forall_isGenericOver_of_mem_prodSet
    (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
      F.parameterGerm hu = f₀.map σ)
    {γ : Germ k a a} (hγ : γ ∈ IsHW.prodSet δ₀) {M : IntermediateField k K} (hγM : γ.cb ≤ M) :
    ∀ v, IsGenericOver M c v → ∃ (hv : F.IsAdmissible a a' v) (u' : μ → K)
      (hu' : F.IsAdmissible a a' u'), InLocus (k := k) c u' ∧
        IsInvertible (F.parameterGerm hu') ∧
        Germ.comp (F.parameterGerm hv) γ = F.parameterGerm hu' := by
  intro v hv
  obtain ⟨hv', hmem, hind⟩ := exists_indepOver_of_isGenericOver hF hγM hv
  obtain ⟨⟨τ, hτ⟩, -⟩ := hb.comp_mem_orbit hδ₀ hmem hγ hind
  obtain ⟨hu', hu'g⟩ := hF τ
  exact ⟨hv', ⇑τ ∘ c, hu', IsGen.inLocus (IsGen.map (rfl : IsGen k c c) τ),
    isInvertible_of_mem_orbit hb.isInvertible ⟨τ, hu'g.symm⟩, (hu'g.trans hτ).symm⟩

/-- `thm:constructible`(1), the converse of `(∗)`: an invertible germ `γ` lies in `G` as soon
as, for one `v` generic in the locus of `c` over a field containing `Cb(γ)`, some point `u'` of
the locus at which `F` is admissible has `g_v γ = g_{u'}`. The witness is not assumed generic
and `γ` is not assumed in `G`. -/
theorem mem_prodSet_of_isGenericOver (hc : adjoin k (range c) = f₀.cb)
    (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
      F.parameterGerm hu = f₀.map σ)
    {γ : Germ k a a} (hγinv : IsInvertible γ) {M : IntermediateField k K} (hγM : γ.cb ≤ M)
    {v : μ → K} (hv : IsGenericOver M c v)
    (hwit : ∃ (hv : F.IsAdmissible a a' v) (u' : μ → K) (hu' : F.IsAdmissible a a' u'),
      InLocus (k := k) c u' ∧ Germ.comp (F.parameterGerm hv) γ = F.parameterGerm hu') :
    γ ∈ IsHW.prodSet δ₀ := by
  obtain ⟨hv', hmem, hind⟩ := exists_indepOver_of_isGenericOver hF hγM hv
  obtain ⟨hv₀, u', hu', hV, hcomp⟩ := hwit
  have hcomp' : Germ.comp (F.parameterGerm hv') γ = F.parameterGerm hu' := hcomp
  obtain ⟨γ', hγ'⟩ := hγinv
  -- `rk(g_v γ / γ) = rk(g_v / γ) = rk(g_v)`, the rank of the generic set.
  have hrk : erk k ∅ (f₀.cb : Set K) ≤ erk k ∅ ((F.parameterGerm hu').cb : Set K) := by
    rw [← hcomp']
    calc erk k ∅ (f₀.cb : Set K) = erk k ∅ ((F.parameterGerm hv').cb : Set K) :=
          (erk_cb_eq_of_mem_orbit hmem).symm
      _ = erk k (∅ ∪ γ.cb) ((F.parameterGerm hv').cb : Set K) :=
          (erk_cb_eq_of_indepOver hind.symm).symm
      _ = erk k (∅ ∪ γ.cb) ((Germ.comp (F.parameterGerm hv') γ).cb : Set K) :=
          (erk_cb_comp_eq_of_isInverse ∅ hγ' _).symm
      _ ≤ erk k ∅ ((Germ.comp (F.parameterGerm hv') γ).cb : Set K) :=
          erk_base_mono k (empty_subset _) _
  have hfγ := QuasiRational.parameterGerm_mem_orbit_of_inLocus hc hF hu' hV hrk
  rw [← hcomp'] at hfγ
  obtain ⟨g₁, hg₁⟩ := isInvertible_of_mem_orbit hb.isInvertible hmem
  refine (hb.mem_prodSet_iff hδ₀).2 ⟨_, hmem, _, hfγ, g₁, hg₁, ?_⟩
  rw [← comp_assoc, hg₁.1, id_comp]

/-- `thm:constructible`(1): an invertible germ `γ` with `Cb(γ)` in a small field `M` lies in
`G` exactly when, for every `v` generic in the locus of `c` over `M`, some point `u'` of the
locus with an admissible invertible germ has `g_v γ = g_{u'}`. -/
theorem mem_prodSet_iff_forall_isGenericOver (hc : adjoin k (range c) = f₀.cb)
    (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
      F.parameterGerm hu = f₀.map σ)
    {γ : Germ k a a} (hγinv : IsInvertible γ) {M : IntermediateField k K}
    (hM : IsSmall k (M : Set K)) (hγM : γ.cb ≤ M) :
    γ ∈ IsHW.prodSet δ₀ ↔ ∀ v, IsGenericOver M c v → ∃ (hv : F.IsAdmissible a a' v)
      (u' : μ → K) (hu' : F.IsAdmissible a a' u'), InLocus (k := k) c u' ∧
        IsInvertible (F.parameterGerm hu') ∧
        Germ.comp (F.parameterGerm hv) γ = F.parameterGerm hu' := by
  refine ⟨fun hγ ↦ hb.forall_isGenericOver_of_mem_prodSet hδ₀ hF hγ hγM, fun h ↦ ?_⟩
  obtain ⟨v, hv⟩ := exists_isGenericOver hM c
  obtain ⟨hv', u', hu', hV, -, hcomp⟩ := h v hv
  exact hb.mem_prodSet_of_isGenericOver hδ₀ hc hF hγinv hγM hv ⟨hv', u', hu', hV, hcomp⟩

end IsHWBij

end Germ

end

end GroupConfig
