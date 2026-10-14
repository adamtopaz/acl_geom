/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Constructible.Admissible

/-!
# Invertible admissible parameters

Blueprint `sources/group_configuration/09-constructibility.tex`, the invertibility part of
`lem:adm-constructible`.

Let `F` be an actual quasi-rational expression in parameter coordinates `μ` and source
coordinates `ι`, between loci of equal rank. At an admissible parameter `u`, the germ of `F`
is invertible exactly when every generic target point `w` over `acl(k, u)` has a unique
preimage `y` on the source locus at which `F(u, ·)` is defined
(`QuasiRational.isInvertible_parameterGerm_iff`). Definedness is required at every point of
the fibre, not only at generic points.

The set of parameters at which `F` is admissible with an invertible germ is constructible
after adjoining a finite independent family of generic target samples
(`QuasiRational.isConstructibleOver_invertibleAdmissible`). The sample hypotheses are those of
`QuasiRational.isConstructibleOver_admissible`.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the invertibility criterion and the constructibility of the invertible admissible
parameters are complete; the remaining constructibility claims of `thm:constructible` are open.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K μ ι κ : Type*} [Field k] [Field K] [Algebra k K]

/-- Reindexing coordinates preserves constructibility. -/
theorem IsConstructibleOver.preimage_comp {ι' : Type*} (f : ι' → ι) {s : Set (ι' → K)}
    (hs : IsConstructibleOver k s) :
    IsConstructibleOver k ((fun x : ι → K ↦ x ∘ f) ⁻¹' s) := by
  convert hs.preimage_polynomial (fun i ↦ (X (f i) : MvPolynomial ι k)) using 1
  ext x
  simp only [Set.mem_preimage, aeval_X, Function.comp_def]

namespace QuasiRational

variable [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
  [Finite μ] [Finite ι] [Finite κ]

attribute [local instance] isAlgClosed_racl

/-- A defined source-locus preimage of a generic target point is the value there of an inverse
of the parameter germ. -/
theorem eq_eval_of_isInverse (F : QuasiRational k (μ ⊕ ι) κ) {a : ι → K} {a' : κ → K}
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) {u : μ → K} (hu : F.IsAdmissible a a' u)
    {h : Germ k a' a} (hi : Germ.IsInverse h (F.parameterGerm hu)) {w : κ → K}
    (hw : IsGenericOver (racl k (range u)) a' w) {y : ι → K} (hyV : InLocus (k := k) a y)
    (hyD : F.IsDefinedAt (Sum.elim u y)) (hyw : F.eval (Sum.elim u y) = w) :
    y = h.eval (racl k (range u)) w := by
  have hM : IsSmall k ((racl k (range u) : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite (finite_range u)).racl
  have hcb := F.cb_parameterGerm_le hu
  have hcbh : h.cb ≤ racl k (range u) := hi.cb_le.trans (racl_le_of_isAlgClosed hcb)
  -- The preimage is generic, so the inverse undoes the parameter germ there.
  have hyg := F.isGenericOver_of_eval_eq hdim hw hyV hyD hyw
  rw [← hyw, ← F.eval_parameterGerm hu hyg, ← Germ.comp_eval h _ hM hcb hcbh hyg, hi.1,
    Germ.eval_id hM hyg]

/-- The value at a generic target point of an inverse of the parameter germ is a defined
source-locus preimage of that point. -/
theorem mem_fibre_eval_of_isInverse (F : QuasiRational k (μ ⊕ ι) κ) {a : ι → K} {a' : κ → K}
    {u : μ → K} (hu : F.IsAdmissible a a' u) {h : Germ k a' a}
    (hi : Germ.IsInverse h (F.parameterGerm hu)) {w : κ → K}
    (hw : IsGenericOver (racl k (range u)) a' w) :
    InLocus (k := k) a (h.eval (racl k (range u)) w) ∧
      F.IsDefinedAt (Sum.elim u (h.eval (racl k (range u)) w)) ∧
      F.eval (Sum.elim u (h.eval (racl k (range u)) w)) = w := by
  have hM : IsSmall k ((racl k (range u) : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite (finite_range u)).racl
  have hcb := F.cb_parameterGerm_le hu
  have hcbh : h.cb ≤ racl k (range u) := hi.cb_le.trans (racl_le_of_isAlgClosed hcb)
  have hy := h.isGenericOver_eval hM hcbh hw
  refine ⟨hy.inLocus, (hu _ hy).1, ?_⟩
  rw [← F.eval_parameterGerm hu hy, ← Germ.comp_eval _ h hM hcbh hcb hw, hi.2, Germ.eval_id hM hw]

/-- An admissible parameter gives an invertible germ exactly when every generic target point
has a unique defined preimage on the source locus. -/
theorem isInvertible_parameterGerm_iff (F : QuasiRational k (μ ⊕ ι) κ) {a : ι → K}
    {a' : κ → K} (hdim : erk k ∅ (range a) = erk k ∅ (range a')) {u : μ → K}
    (hu : F.IsAdmissible a a' u) :
    Germ.IsInvertible (F.parameterGerm hu) ↔
      ∀ w : κ → K, IsGenericOver (racl k (range u)) a' w →
        ∃! y : ι → K, InLocus (k := k) a y ∧ F.IsDefinedAt (Sum.elim u y) ∧
          F.eval (Sum.elim u y) = w := by
  have hM : IsSmall k ((racl k (range u) : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite (finite_range u)).racl
  have hcb := F.cb_parameterGerm_le hu
  constructor
  · rintro ⟨h, hi⟩ w hw
    -- Every defined preimage of `w` is the value of the inverse at `w`.
    have hinv (y : ι → K) (hy : InLocus (k := k) a y ∧ F.IsDefinedAt (Sum.elim u y) ∧
        F.eval (Sum.elim u y) = w) : y = h.eval (racl k (range u)) w :=
      F.eq_eval_of_isInverse hdim hu hi hw hy.1 hy.2.1 hy.2.2
    obtain ⟨y, hy⟩ := (F.isAdmissible_iff_generic_surjective a a' hdim u).1 hu w hw
    exact ⟨y, hy, fun y' hy' ↦ (hinv y' hy').trans (hinv y hy).symm⟩
  · intro huniq
    obtain ⟨y, hy⟩ := exists_isGenericOver hM a
    have hw := (hu y hy).2
    refine ((F.parameterGerm hu).isInvertible_iff_mem_dclAdjoin hM hcb hy).2 fun i ↦ ?_
    rw [F.eval_parameterGerm hu hy]
    unfold dclAdjoin
    refine mem_dcl_iff_forall_fixed.2 fun σ ↦ ?_
    -- An automorphism over the parameter closure and `w` moves `y` inside the fibre of `w`.
    let σM : K ≃ₐ[↥(racl k (range u))] K :=
      { σ.toRingEquiv with
        commutes' := fun r ↦ σ.commutes ⟨r, (mem_restrictScalars k).2
          (IntermediateField.algebraMap_mem
            (adjoin (↥(racl k (range u))) (range (F.eval (Sum.elim u y)))) r)⟩ }
    have hσw (j : κ) : σM (F.eval (Sum.elim u y) j) = F.eval (Sum.elim u y) j :=
      σ.commutes ⟨_, (mem_restrictScalars k).2 (subset_adjoin _ _ (mem_range_self j))⟩
    have hfy : (F.specialize u).IsDefinedAt y := (F.specialize_isDefinedAt_iff u y).2 (hu y hy).1
    have hσy : InLocus (k := k) a (⇑σM ∘ y) ∧ F.IsDefinedAt (Sum.elim u (⇑σM ∘ y)) ∧
        F.eval (Sum.elim u (⇑σM ∘ y)) = F.eval (Sum.elim u y) := by
      refine ⟨(hy.comp σM).inLocus, (F.specialize_isDefinedAt_iff u _).1
        (((F.specialize u).isDefinedAt_comp_iff σM y).2 hfy), ?_⟩
      rw [← F.specialize_eval, (F.specialize u).eval_comp σM, F.specialize_eval]
      exact funext hσw
    exact congrFun ((huniq _ hw).unique hσy ⟨hy.inLocus, (hu y hy).1, rfl⟩) i

/-- `lem:adm-constructible`, invertibility part: the parameters at which the actual expression
is admissible with an invertible germ form a constructible set after adjoining a finite
independent family of generic target samples. -/
theorem isConstructibleOver_invertibleAdmissible [Fintype μ] {α : Type*} [Fintype α]
    (F : QuasiRational k (μ ⊕ ι) κ) (a : ι → K) (a' : κ → K)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) (t : α → κ → K)
    (ht : ∀ i, IsGenericOver (⊥ : IntermediateField k K) a' (t i))
    (hind : erk k ((⊥ : IntermediateField k K) : Set K) (⋃ i, range (t i)) =
      ∑ i, erk k ((⊥ : IntermediateField k K) : Set K) (range (t i)))
    (hr : 2 * Fintype.card μ + 1 ≤ Fintype.card α) :
    IsConstructibleOver (↥(adjoin k (⋃ i, range (t i))))
      {u : μ → K | ∃ hu : F.IsAdmissible a a' u, Germ.IsInvertible (F.parameterGerm hu)} := by
  /- The fibre over a parameter and a target point has at most one point. -/
  let Q : ((μ ⊕ κ) → K) → (ι → K) → Prop := fun v y ↦ InLocus (k := k) a y ∧
    F.IsDefinedAt (Sum.elim (v ∘ Sum.inl) y) ∧ F.eval (Sum.elim (v ∘ Sum.inl) y) = v ∘ Sum.inr
  have hR : IsConstructibleOver k {z : ((μ ⊕ κ) ⊕ ι) → K | Q (z ∘ Sum.inl) (z ∘ Sum.inr)} :=
    F.isConstructibleOver_fibre a
  have hEq : IsConstructibleOver k {z : ((μ ⊕ κ) ⊕ (ι ⊕ ι)) → K |
      (z ∘ Sum.inr) ∘ Sum.inl = (z ∘ Sum.inr) ∘ Sum.inr} := by
    convert IsConstructibleOver.iInter fun i : ι ↦ IsConstructibleOver.polynomial_zero (K := K)
      (X (Sum.inr (Sum.inl i)) - X (Sum.inr (Sum.inr i)) :
        MvPolynomial ((μ ⊕ κ) ⊕ (ι ⊕ ι)) k) using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, map_sub, aeval_X, sub_eq_zero, funext_iff,
      Function.comp_apply]
  have hT : IsConstructibleOver k {z : ((μ ⊕ κ) ⊕ (ι ⊕ ι)) → K |
      (fun (v : (μ ⊕ κ) → K) (p : (ι ⊕ ι) → K) ↦
        Q v (p ∘ Sum.inl) ∧ Q v (p ∘ Sum.inr) ∧ p ∘ Sum.inl ≠ p ∘ Sum.inr)
        (z ∘ Sum.inl) (z ∘ Sum.inr)} :=
    (hR.preimage_comp (Sum.map _root_.id Sum.inl)).inter
      ((hR.preimage_comp (Sum.map _root_.id Sum.inr)).inter hEq.compl)
  have hs : IsConstructibleOver k {v : (μ ⊕ κ) → K | ∀ y y' : ι → K, Q v y → Q v y' → y = y'} := by
    convert (hT.exists (φ := fun v p ↦
      Q v (p ∘ Sum.inl) ∧ Q v (p ∘ Sum.inr) ∧ p ∘ Sum.inl ≠ p ∘ Sum.inr)).compl using 1
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists]
    constructor
    · rintro h p ⟨h₁, h₂, hne⟩
      exact hne (h _ _ h₁ h₂)
    · intro h y y' hy hy'
      by_contra hne
      exact h (Sum.elim y y') ⟨hy, hy', hne⟩
  have h := (F.isConstructibleOver_admissible a a' hdim t ht hind hr).inter
    (isConstructibleOver_forall_generic a' t ht hind hr hs)
  convert h using 1
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Q, Sum.elim_comp_inl, Sum.elim_comp_inr]
  constructor
  · rintro ⟨hu, hinv⟩
    exact ⟨hu, fun w hw y y' hy hy' ↦
      ((F.isInvertible_parameterGerm_iff hdim hu).1 hinv w hw).unique hy hy'⟩
  · rintro ⟨hu, huniq⟩
    refine ⟨hu, (F.isInvertible_parameterGerm_iff hdim hu).2 fun w hw ↦ ?_⟩
    obtain ⟨y, hy⟩ := (F.isAdmissible_iff_generic_surjective a a' hdim u).1 hu w hw
    exact ⟨y, hy, fun y' hy' ↦ huniq w hw y' y hy' hy⟩

end QuasiRational

end

end GroupConfig
