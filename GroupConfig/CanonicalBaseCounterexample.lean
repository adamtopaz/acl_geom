/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.CanonicalBase
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# A canonical base outside the algebraic closure of the point

Blueprint `sources/group_configuration/02-fields-of-definition.tex`, `rem:cb-not-acl`: in general
`Cb(a/L) ⊄ acl(a)`. For independent `s, s', t`, let `a = (t, st + s')` and `L = acl(s, s')`:

* the locus of `a` over `L` is the line `X₂ = s X₁ + s'`
  (`GroupConfig.locusIdeal_line`);
* its canonical base is `k(s, s')` (`GroupConfig.canonicalBase_line`);
* `rk(a) = 2` (`GroupConfig.erk_line`) and `s ∉ acl(a)` (`GroupConfig.not_mem_racl_line`);
* hence `Cb(a/L) ⊄ acl(a)` (`GroupConfig.canonicalBase_line_not_subset_racl`).

The locus and canonical-base computations hold over any field `L` containing `s, s'` over which
`t` is transcendental (`GroupConfig.locusIdeal_affineLine`, `GroupConfig.canonicalBase_affineLine`);
other finite index types reduce to these by `GroupConfig.canonicalBase_comp_equiv`.

So the hypothesis (GC4) of a group configuration, `a ⊆ acl(Cb(xy/acl(a)))`, is a genuine
condition.

The source coordinates `X₁, X₂` are `X 0, X 1` here. The only hypothesis is that `s, s', t` have
rank three over `k`; neither algebraic closedness nor a universal domain is needed.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the example of `rem:cb-not-acl` is complete.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### Ranks -/

section Rank

variable {s s' t : K}

/-- `s`, `s'` and `t` are algebraic over `t`, `st + s'` and `s`. Named consumers: `erk_line` and
`not_mem_racl_line`. -/
private theorem subset_racl_line :
    ({s, s', t} : Set K) ⊆ racl k (range ![t, s * t + s'] ∪ {s}) := by
  have ht : t ∈ racl k (range ![t, s * t + s'] ∪ {s}) :=
    subset_racl k _ (Or.inl ⟨0, by simp⟩)
  have hst : s * t + s' ∈ racl k (range ![t, s * t + s'] ∪ {s}) :=
    subset_racl k _ (Or.inl ⟨1, by simp⟩)
  have hs : s ∈ racl k (range ![t, s * t + s'] ∪ {s}) := subset_racl k _ (Or.inr rfl)
  have hs' : s' ∈ racl k (range ![t, s * t + s'] ∪ {s}) := by
    have h := sub_mem hst (mul_mem hs ht)
    rwa [add_sub_cancel_left] at h
  rintro x (rfl | rfl | rfl)
  exacts [hs, hs', ht]

variable (hind : erk k ∅ ({s, s', t} : Set K) = 3)
include hind

/-- The rank of `a`, together with `s`, is three. -/
private theorem three_le_erk_line : 3 ≤ erk k ∅ (range ![t, s * t + s'] ∪ {s}) := by
  rw [← hind, ← erk_racl k ∅ (range ![t, s * t + s'] ∪ {s}), empty_union]
  exact erk_mono k ∅ subset_racl_line

/-- `rem:cb-not-acl`: the point `a = (t, st + s')` has rank two. -/
theorem erk_line : erk k ∅ (range ![t, s * t + s']) = 2 := by
  have hpair : range ![t, s * t + s'] = {t, s * t + s'} := by
    ext x
    simp only [mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      mem_insert_iff, mem_singleton_iff]
    tauto
  have hle : erk k ∅ (range ![t, s * t + s']) ≤ 2 := by
    refine (erk_le_encard k ∅ _).trans ?_
    rw [hpair]
    exact (encard_insert_le _ _).trans (by rw [encard_singleton]; norm_num)
  have hs1 : erk k ∅ ({s} : Set K) ≤ 1 := (erk_le_encard k ∅ _).trans (by simp)
  have h3 : (2 : ℕ∞) + 1 ≤ erk k ∅ (range ![t, s * t + s']) + 1 :=
    calc (2 : ℕ∞) + 1 = 3 := by norm_num
      _ ≤ _ := three_le_erk_line hind
      _ ≤ _ := erk_union_le k ∅ _ _
      _ ≤ _ := add_le_add_right hs1 _
  exact le_antisymm hle ((ENat.add_le_add_iff_right ENat.one_ne_top).1 h3)

/-- `rem:cb-not-acl`: `s` is not algebraic over `a = (t, st + s')`. -/
theorem not_mem_racl_line : s ∉ racl k (range ![t, s * t + s']) := by
  intro hs
  have hsub : range ![t, s * t + s'] ∪ {s} ⊆ racl k (∅ ∪ range ![t, s * t + s']) := by
    rw [empty_union]
    exact union_subset (subset_racl k _) (singleton_subset_iff.2 hs)
  have hle := (erk_mono k ∅ hsub).trans_eq (erk_racl k ∅ _)
  rw [erk_line hind] at hle
  have h := (three_le_erk_line hind).trans hle
  norm_num at h

end Rank

/-! ### The locus -/

section Line

variable {s s' t : K}

/-- `t` is transcendental over `acl(s, s')`. Named consumer: `locusIdeal_line`. -/
private theorem transcendental_line (hind : erk k ∅ ({s, s', t} : Set K) = 3) :
    Transcendental (↥(racl k ({s, s'} : Set K))) t := by
  intro halg
  have ht : t ∈ racl k ({s, s'} : Set K) := by
    rw [← racl_racl k ({s, s'} : Set K)]
    refine (mem_racl_iff k).2 ?_
    rw [adjoin_self]
    exact halg
  have hsub : ({s, s', t} : Set K) ⊆ racl k (∅ ∪ ({s, s'} : Set K)) := by
    rw [empty_union]
    rintro x (rfl | rfl | rfl)
    exacts [subset_racl k _ (Or.inl rfl), subset_racl k _ (Or.inr rfl), ht]
  have h := (erk_mono k ∅ hsub).trans_eq (erk_racl k ∅ _)
  rw [hind] at h
  have h2 : (3 : ℕ∞) ≤ 1 + 1 := h.trans ((erk_le_encard k ∅ _).trans
    ((encard_insert_le _ _).trans (by rw [encard_singleton])))
  norm_num at h2

variable (L : IntermediateField k K) (hs : s ∈ L) (hs' : s' ∈ L)

/-- The line `X₁ = s X₀ + s'` over `L`. -/
private def lineL : MvPolynomial (Fin 2) L := X 1 - C ⟨s, hs⟩ * X 0 - C ⟨s', hs'⟩

/-- The affine change of variables taking the line to `X₀ = 0`. -/
private def shiftL : MvPolynomial (Fin 2) L →ₐ[L] MvPolynomial (Fin 2) L :=
  aeval ![X 1, X 0 + C ⟨s, hs⟩ * X 1 + C ⟨s', hs'⟩]

/-- The inverse change of variables. -/
private def unshiftL : MvPolynomial (Fin 2) L →ₐ[L] MvPolynomial (Fin 2) L :=
  aeval ![lineL L hs hs', X 0]

private theorem unshiftL_comp_shiftL :
    (unshiftL L hs hs').comp (shiftL L hs hs') = AlgHom.id L _ := by
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  fin_cases i
  · simp [shiftL, unshiftL, lineL]
  · simp [shiftL, unshiftL, lineL]
    ring

private theorem aeval_comp_shiftL :
    (aeval ![(0 : K), t]).comp (shiftL L hs hs') = aeval ![t, s * t + s'] := by
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  fin_cases i <;> simp [shiftL]

/-- Killing `X₀` changes a polynomial by a multiple of `X₀`. Named consumer:
`X_zero_dvd_of_aeval_eq_zero`. -/
private theorem X_zero_dvd_sub_aeval (q : MvPolynomial (Fin 2) L) :
    X 0 ∣ q - aeval ![(0 : MvPolynomial (Fin 2) L), X 1] q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p i hp =>
    fin_cases i
    · simp only [map_mul, aeval_X, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, mul_zero,
        sub_zero]
      exact dvd_mul_left _ _
    · simp only [map_mul, aeval_X, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      rw [← sub_mul]
      exact dvd_mul_of_dvd_left hp _

/-- A polynomial vanishing at `(0, t)`, for `t` transcendental over `L`, is divisible by `X₀`. -/
private theorem X_zero_dvd_of_aeval_eq_zero (ht : Transcendental L t)
    {q : MvPolynomial (Fin 2) L} (hq : aeval ![(0 : K), t] q = 0) : X 0 ∣ q := by
  -- Killing `X₀` gives a polynomial in `X₁` alone.
  have hcomp : (aeval ![(0 : MvPolynomial (Fin 2) L), X 1] :
      MvPolynomial (Fin 2) L →ₐ[L] MvPolynomial (Fin 2) L) =
        (rename fun _ : Fin 1 ↦ (1 : Fin 2)).comp
          (aeval ![(0 : MvPolynomial (Fin 1) L), X 0]) := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    fin_cases i <;> simp
  have hkill : (aeval ![(0 : K), t]).comp
      (aeval ![(0 : MvPolynomial (Fin 2) L), X 1]) = aeval ![(0 : K), t] := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    fin_cases i <;> simp
  have hr : aeval ![t] (aeval ![(0 : MvPolynomial (Fin 1) L), X 0] q) = 0 := by
    have h1 : aeval ![(0 : K), t] (rename (fun _ : Fin 1 ↦ (1 : Fin 2))
        (aeval ![(0 : MvPolynomial (Fin 1) L), X 0] q)) =
          aeval ![t] (aeval ![(0 : MvPolynomial (Fin 1) L), X 0] q) := by
      have hf : (![(0 : K), t] ∘ fun _ : Fin 1 ↦ (1 : Fin 2)) = ![t] := by
        funext i
        fin_cases i
        rfl
      rw [aeval_rename, hf]
    rw [← h1, ← AlgHom.comp_apply (rename _), ← hcomp, ← AlgHom.comp_apply, hkill, hq]
  have hinj : Function.Injective (aeval ![t] : MvPolynomial (Fin 1) L →ₐ[L] K) :=
    (algebraicIndependent_unique_type_iff (x := ![t])).2 ht
  have hr0 := hinj (hr.trans (map_zero _).symm)
  have h := X_zero_dvd_sub_aeval L q
  rwa [hcomp, AlgHom.comp_apply, hr0, map_zero, sub_zero] at h

/-- The ideal of `a = (t, st + s')` over `L` is generated by the line. -/
private theorem idealOf_line (ht : Transcendental L t) :
    idealOf (↥L) ![t, s * t + s'] = Ideal.span {lineL L hs hs'} := by
  refine le_antisymm (fun p hp ↦ ?_) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
  · rw [Ideal.mem_span_singleton]
    have hq : aeval ![(0 : K), t] (shiftL L hs hs' p) = 0 := by
      rw [← AlgHom.comp_apply, aeval_comp_shiftL]
      exact (mem_idealOf_iff _).1 hp
    have h := map_dvd (unshiftL L hs hs') (X_zero_dvd_of_aeval_eq_zero L ht hq)
    rwa [← AlgHom.comp_apply (unshiftL L hs hs'), unshiftL_comp_shiftL, AlgHom.id_apply,
      show unshiftL L hs hs' (X 0) = lineL L hs hs' by simp [unshiftL]] at h
  · rw [mem_idealOf_iff]
    simp [lineL]

end Line

/-- The locus of `(t, st + s')` over any field `L` containing `s, s'`, over which `t` is
transcendental, is the line `X₂ = s X₁ + s'`. Named consumers: `GroupConfig.locusIdeal_line` and
`GroupConfig.canonicalBase_affineLine`. -/
theorem locusIdeal_affineLine {s s' t : K} (L : IntermediateField k K) (hs : s ∈ L)
    (hs' : s' ∈ L) (ht : Transcendental (↥L) t) :
    locusIdeal (↥L) ![t, s * t + s'] = Ideal.span {X 1 - C s * X 0 - C s'} := by
  unfold locusIdeal
  rw [idealOf_line L hs hs' ht, Ideal.map_span, Set.image_singleton]
  simp [lineL]

/-- `rem:cb-not-acl`: the locus of `a = (t, st + s')` over `L = acl(s, s')` is the line
`X₂ = s X₁ + s'`. -/
theorem locusIdeal_line {s s' t : K} (hind : erk k ∅ ({s, s', t} : Set K) = 3) :
    locusIdeal (↥(racl k ({s, s'} : Set K))) ![t, s * t + s'] =
      Ideal.span {X 1 - C s * X 0 - C s'} :=
  locusIdeal_affineLine _ (subset_racl k _ (Or.inl rfl)) (subset_racl k _ (Or.inr rfl))
    (transcendental_line hind)

/-! ### The canonical base -/

section CanonicalBase

variable {s s' : K}

/-- The coefficients of the line `X₁ - s X₀ - s'`. Named consumer: `canonicalBase_line`. -/
private theorem coeff_line (m : Fin 2 →₀ ℕ) :
    (X 1 - C s * X 0 - C s' : MvPolynomial (Fin 2) K).coeff m =
      (if Finsupp.single 1 1 = m then 1 else 0) -
        s * (if Finsupp.single 0 1 = m then 1 else 0) - (if 0 = m then s' else 0) := by
  simp only [coeff_sub, coeff_C_mul, coeff_X, coeff_C]

private theorem coeff_line_one :
    (X 1 - C s * X 0 - C s' : MvPolynomial (Fin 2) K).coeff (Finsupp.single 1 1) = 1 := by
  have h : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := (Finsupp.single_ne_zero.2 one_ne_zero).symm
  rw [coeff_line]
  simp [Finsupp.single_left_inj, h]

private theorem coeff_line_zero :
    (X 1 - C s * X 0 - C s' : MvPolynomial (Fin 2) K).coeff (Finsupp.single 0 1) = -s := by
  have h : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 1 := (Finsupp.single_ne_zero.2 one_ne_zero).symm
  rw [coeff_line]
  simp [Finsupp.single_left_inj, h]

private theorem coeff_line_const :
    (X 1 - C s * X 0 - C s' : MvPolynomial (Fin 2) K).coeff 0 = -s' := by
  rw [coeff_line]
  simp

end CanonicalBase

/-- The canonical base of `(t, st + s')` over any field `L` containing `s, s'`, over which `t`
is transcendental, is `k(s, s')`. Named consumer: `GroupConfig.canonicalBase_line`. -/
theorem canonicalBase_affineLine {s s' t : K} (L : IntermediateField k K) (hs : s ∈ L)
    (hs' : s' ∈ L) (ht : Transcendental (↥L) t) :
    canonicalBase L ![t, s * t + s'] = adjoin k ({s, s'} : Set K) := by
  unfold canonicalBase
  rw [locusIdeal_affineLine L hs hs' ht]
  have hg1 := coeff_line_one (s := s) (s' := s')
  have hg0 := coeff_line_zero (s := s) (s' := s')
  have hgc := coeff_line_const (s := s) (s' := s')
  have hgdeg : (X 1 - C s * X 0 - C s' : MvPolynomial (Fin 2) K).totalDegree ≤ 1 := by
    refine (totalDegree_sub _ _).trans (max_le ((totalDegree_sub _ _).trans (max_le ?_ ?_)) ?_)
    · simp [totalDegree_X]
    · exact (totalDegree_mul _ _).trans (by simp [totalDegree_X, totalDegree_C])
    · simp [totalDegree_C]
  have hgdeg1 : 1 ≤ (X 1 - C s * X 0 - C s' : MvPolynomial (Fin 2) K).totalDegree := by
    have h := le_totalDegree (s := Finsupp.single 1 1)
      (p := (X 1 - C s * X 0 - C s' : MvPolynomial (Fin 2) K))
      (by rw [mem_support_iff, hg1]; exact one_ne_zero)
    simpa using h
  have hg0' : (X 1 - C s * X 0 - C s' : MvPolynomial (Fin 2) K) ≠ 0 := by
    intro h
    simp [h] at hg1
  refine le_antisymm (adjoin_le_iff.2 ?_) (adjoin_le_iff.2 ?_)
  · -- The line has coefficients in `k(s, s')`.
    have hs : s ∈ adjoin k ({s, s'} : Set K) := subset_adjoin k _ (Or.inl rfl)
    have hs' : s' ∈ adjoin k ({s, s'} : Set K) := subset_adjoin k _ (Or.inr rfl)
    have hdef : IdealDefinedOver (adjoin k ({s, s'} : Set K)).toSubfield
        (Ideal.span {(X 1 - C s * X 0 - C s' : MvPolynomial (Fin 2) K)}) := by
      refine idealDefinedOver_of_le_span _ (Ideal.span_le.2 ?_)
      rintro _ rfl
      refine Ideal.subset_span ⟨Ideal.subset_span rfl, fun m ↦ ?_⟩
      rw [coeff_line]
      refine sub_mem (sub_mem ?_ (mul_mem hs ?_)) ?_ <;> split_ifs <;>
        first | exact one_mem _ | exact zero_mem _ | exact hs'
    exact fun x hx ↦ idealDefinedOver_iff.1 hdef hx
  · -- Every field of definition of the line contains `s` and `s'`.
    set I := Ideal.span {(X 1 - C s * X 0 - C s' : MvPolynomial (Fin 2) K)} with hI
    have hF : degSubspace I 1 = Submodule.span K
        {v | v ∈ degSubspace I 1 ∧ ∀ ν, v ν ∈ idealFod I} :=
      degSubspace_definedOver _ (idealDefinedOver_idealFod I) 1
    have hw₀ : coeffVec 1 (X 1 - C s * X 0 - C s' : MvPolynomial (Fin 2) K) ∈ degSubspace I 1 :=
      coeffVec_mem_degSubspace (Ideal.subset_span rfl) hgdeg
    let m₁ : Monomials (Fin 2) 1 := ⟨Finsupp.single 1 1, by simp⟩
    let m₀ : Monomials (Fin 2) 1 := ⟨Finsupp.single 0 1, by simp⟩
    let mc : Monomials (Fin 2) 1 := ⟨0, by simp⟩
    obtain ⟨v, ⟨hvW, hvF⟩, hv0⟩ :
        ∃ v ∈ {v | v ∈ degSubspace I 1 ∧ ∀ ν, v ν ∈ idealFod I}, v ≠ 0 := by
      by_contra hne
      push Not at hne
      have hbot : degSubspace I 1 = ⊥ := by
        rw [hF, Submodule.span_eq_bot]
        exact hne
      have h1 := congrFun (show coeffVec 1 (X 1 - C s * X 0 - C s' : MvPolynomial (Fin 2) K) = 0
        from (Submodule.mem_bot K).1 (hbot ▸ hw₀)) m₁
      rw [coeffVec_apply, hg1] at h1
      exact one_ne_zero h1
    obtain ⟨f, hfI, hfdeg, rfl⟩ := mem_degSubspace_iff.1 hvW
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hfI
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hv0 (by rw [zero_mul, map_zero])
    have hcdeg : c.totalDegree = 0 := by
      rw [totalDegree_mul_of_isDomain hc0 hg0'] at hfdeg
      omega
    obtain ⟨c₀, rfl⟩ : ∃ c₀, c = C c₀ := ⟨_, totalDegree_eq_zero_iff_eq_C.1 hcdeg⟩
    have hv : ∀ ν : Monomials (Fin 2) 1, coeffVec 1 (C c₀ * (X 1 - C s * X 0 - C s')) ν =
        c₀ * (X 1 - C s * X 0 - C s' : MvPolynomial (Fin 2) K).coeff ν.1 := fun ν ↦ by
      rw [coeffVec_apply, coeff_C_mul]
    have h₁ := hvF m₁
    have h₀ := hvF m₀
    have hc := hvF mc
    rw [hv, hg1, mul_one] at h₁
    rw [hv, hg0] at h₀
    rw [hv, hgc] at hc
    have hc' : c₀ ≠ 0 := by
      rintro rfl
      exact hc0 (map_zero _)
    have hsF : s ∈ idealFod I := by
      have h := (idealFod I).div_mem (neg_mem h₀) h₁
      rwa [mul_neg, neg_neg, mul_div_cancel_left₀ _ hc'] at h
    have hs'F : s' ∈ idealFod I := by
      have h := (idealFod I).div_mem (neg_mem hc) h₁
      rwa [mul_neg, neg_neg, mul_div_cancel_left₀ _ hc'] at h
    rintro x (rfl | rfl)
    exacts [subset_adjoin k _ hsF, subset_adjoin k _ hs'F]

/-- `rem:cb-not-acl`: the canonical base of `a = (t, st + s')` over `L = acl(s, s')` is
`k(s, s')`. -/
theorem canonicalBase_line {s s' t : K} (hind : erk k ∅ ({s, s', t} : Set K) = 3) :
    canonicalBase (racl k ({s, s'} : Set K)) ![t, s * t + s'] =
      adjoin k ({s, s'} : Set K) :=
  canonicalBase_affineLine _ (subset_racl k _ (Or.inl rfl)) (subset_racl k _ (Or.inr rfl))
    (transcendental_line hind)

/-- `rem:cb-not-acl`: the canonical base of `a = (t, st + s')` over `L = acl(s, s')` is not
contained in `acl(a)`. -/
theorem canonicalBase_line_not_subset_racl {s s' t : K}
    (hind : erk k ∅ ({s, s', t} : Set K) = 3) :
    ¬ ((canonicalBase (racl k ({s, s'} : Set K)) ![t, s * t + s'] : Set K) ⊆
      racl k (range ![t, s * t + s'])) := by
  intro h
  refine not_mem_racl_line hind (h ?_)
  rw [canonicalBase_line hind]
  exact subset_adjoin k _ (Or.inl rfl)

end

end GroupConfig
