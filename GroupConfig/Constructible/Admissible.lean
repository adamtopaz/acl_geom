/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import GroupConfig.Constructible.QuasiRational
import GroupConfig.Constructible.Generic
import GroupConfig.Germ.Definable

/-!
# Actual admissible parameters of quasi-rational expressions

Supplemental `sources/group_configuration/09-constructibility.tex`,
`def:admissible` and the admissibility part of `lem:adm-constructible`.
Specializing the parameters gives an actual expression over their algebraic
closure. Admissibility means definedness and target genericity at every generic
source point. For equal-dimensional loci, the actual defined graph covers the
generic target points exactly when the parameter is admissible.

Ordinary fibre relations are constructible, and the generic majority quantifier
makes the actual admissible parameter set constructible over a finite sampling
field. Named consumers are invertible admissibility, actual word relations and
the constructible-group presentation.

**Status:** specialization, the admissibility criterion and constructibility
under explicit generic-sample hypotheses are proved. Fresh sample existence
is in `Constructible.FreshSamples`. The constructible group and homogeneous-space
presentations are proved in `Constructible.CanonicalPresentation`.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K μ ι κ : Type*} [Field k] [Field K] [Algebra k K]

/-- Points of a finite-coordinate represented locus form a constructible set. -/
theorem isConstructibleOver_inLocus [Finite ι] (a : ι → K) :
    IsConstructibleOver k {y : ι → K | InLocus (k := k) a y} := by
  classical
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian (idealOf k a)
  have h := IsConstructibleOver.iInter fun p : ↥S ↦
    IsConstructibleOver.polynomial_zero (K := K) p.1
  convert h using 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  unfold InLocus locusIdeal
  rw [← hS, Ideal.map_span, Ideal.span_le, Set.image_subset_iff]
  simp only [Set.subset_def, Set.mem_preimage, SetLike.mem_coe, mem_idealOf_iff,
    MvPolynomial.aeval_map_algebraMap]
  constructor
  · intro hy p
    exact hy p.1 p.2
  · intro hy p hp
    exact hy ⟨p, hp⟩

namespace QuasiRational

-- The sole consumer is specialization and its admissibility criterion below.
private def specializeMap (u : μ → K) :
    MvPolynomial (μ ⊕ ι) k →ₐ[k] MvPolynomial ι (↥(racl k (range u))) :=
  MvPolynomial.aeval (Sum.elim
    (fun i ↦ C (⟨u i, subset_racl k _ (mem_range_self i)⟩ : ↥(racl k (range u))))
    (fun j ↦ X j))

private theorem aeval_specializeMap (u : μ → K) (y : ι → K)
    (P : MvPolynomial (μ ⊕ ι) k) :
    aeval y (specializeMap u P) = aeval (Sum.elim u y) P := by
  unfold specializeMap
  change ((MvPolynomial.aeval y).restrictScalars k) (MvPolynomial.aeval _ P) = _
  rw [MvPolynomial.comp_aeval_apply]
  refine congrArg (fun v ↦ aeval v P) (funext fun i ↦ ?_)
  cases i <;> simp only [Sum.elim_inl, Sum.elim_inr, AlgHom.restrictScalars_apply, aeval_C,
    aeval_X]
  rfl

/-- Substitute the parameter coordinates into an expression. Its remaining
coefficients lie in the algebraic closure of the parameter field. -/
def specialize (F : QuasiRational k (μ ⊕ ι) κ) (u : μ → K) :
    QuasiRational (↥(racl k (range u))) ι κ :=
  ⟨F.e, fun j ↦ specializeMap u (F.num j), fun j ↦ specializeMap u (F.den j)⟩

theorem specialize_isDefinedAt_iff [PerfectField K]
    (F : QuasiRational k (μ ⊕ ι) κ) (u : μ → K) (y : ι → K) :
    (F.specialize u).IsDefinedAt y ↔ F.IsDefinedAt (Sum.elim u y) := by
  unfold IsDefinedAt specialize
  simp only [aeval_specializeMap]

theorem specialize_eval [PerfectField K]
    (F : QuasiRational k (μ ⊕ ι) κ) (u : μ → K) (y : ι → K) :
    (F.specialize u).eval y = F.eval (Sum.elim u y) := by
  funext j
  simp only [eval, specialize, aeval_specializeMap]

variable [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
  [Finite μ] [Finite ι] [Finite κ]

attribute [local instance] isAlgClosed_racl

/-- An actual expression is admissible at a parameter when it is defined on
all independent generic source points and sends them to generic target points. -/
def IsAdmissible (F : QuasiRational k (μ ⊕ ι) κ)
    (a : ι → K) (a' : κ → K) (u : μ → K) : Prop :=
  ∀ y, IsGenericOver (racl k (range u)) a y →
    F.IsDefinedAt (Sum.elim u y) ∧
      IsGenericOver (racl k (range u)) a' (F.eval (Sum.elim u y))

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] in
private theorem isSmall_parameterClosure (u : μ → K) :
    IsSmall k ((racl k (range u) : IntermediateField k K) : Set K) :=
  (IsSmall.of_finite (finite_range u)).racl

/-- Admissibility constructs an actual germ representative over the parameter closure. -/
def representative (F : QuasiRational k (μ ⊕ ι) κ) {a : ι → K} {a' : κ → K}
    {u : μ → K} (hu : F.IsAdmissible a a' u) : Representative k K a a' where
  M := racl k (range u)
  isAlgClosed := isAlgClosed_racl _
  isSmall := isSmall_parameterClosure u
  f := F.specialize u
  isDefinedAt y hy := (F.specialize_isDefinedAt_iff u y).2 (hu y hy).1
  isGenericOver y hy := by
    rw [F.specialize_eval]
    exact (hu y hy).2

/-- The actual germ determined by an admissible parameter. -/
def parameterGerm (F : QuasiRational k (μ ⊕ ι) κ) {a : ι → K} {a' : κ → K}
    {u : μ → K} (hu : F.IsAdmissible a a' u) : Germ k a a' :=
  ⟦F.representative hu⟧

/-- Its canonical base lies in the parameter closure. -/
theorem cb_parameterGerm_le (F : QuasiRational k (μ ⊕ ι) κ) {a : ι → K} {a' : κ → K}
    {u : μ → K} (hu : F.IsAdmissible a a' u) :
    (F.parameterGerm hu).cb ≤ racl k (range u) := Germ.cb_mk_le _

/-- Evaluation of the parameter germ agrees with the original expression. -/
theorem eval_parameterGerm (F : QuasiRational k (μ ⊕ ι) κ) {a : ι → K} {a' : κ → K}
    {u : μ → K} (hu : F.IsAdmissible a a' u) {y : ι → K}
    (hy : IsGenericOver (racl k (range u)) a y) :
    (F.parameterGerm hu).eval (racl k (range u)) y = F.eval (Sum.elim u y) :=
  (Germ.eval_eq_rep (F.representative hu) (isSmall_parameterClosure u)
    (F.cb_parameterGerm_le hu) le_rfl hy).trans (F.specialize_eval u y)

omit [Finite κ] in
/-- For equal-dimensional loci, a defined source-locus preimage of a generic target
point is generic over the parameter closure. -/
theorem isGenericOver_of_eval_eq (F : QuasiRational k (μ ⊕ ι) κ) {a : ι → K} {a' : κ → K}
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) {u : μ → K} {w : κ → K}
    (hw : IsGenericOver (racl k (range u)) a' w) {y : ι → K} (hyV : InLocus (k := k) a y)
    (hyD : F.IsDefinedAt (Sum.elim u y)) (hyw : F.eval (Sum.elim u y) = w) :
    IsGenericOver (racl k (range u)) a y := by
  let M := racl k (range u)
  have hM : IsSmall k (M : Set K) := isSmall_parameterClosure u
  let f := F.specialize u
  have hf : f.IsDefinedAt y := (F.specialize_isDefinedAt_iff u y).2 hyD
  have hfw : f.eval y = w := (F.specialize_eval u y).trans hyw
  have hwy : range w ⊆ racl k ((M : Set K) ∪ range y) := by
    rintro _ ⟨j, rfl⟩
    rw [← congrFun hfw j]
    exact dclAdjoin_le_racl M y (f.eval_mem_dclAdjoin hf j)
  have hrw : erk k (M : Set K) (range w) = erk k ∅ (range a) := by
    rw [hw.erk_coe_eq, hw.erk_empty_eq, hdim]
  refine (isGenericOver_iff_erk_eq hM hyV).2 (le_antisymm (erk_le_of_inLocus hM hyV) ?_)
  rw [← hrw]
  exact (erk_mono k (M : Set K) hwy).trans (erk_racl k (M : Set K) (range y)).le

/-- For equal-dimensional loci, admissibility is equivalent to the generic target
being covered by the actual defined graph on source-locus points. Definedness is
explicit in every fibre; expression evaluation alone is insufficient. -/
theorem isAdmissible_iff_generic_surjective (F : QuasiRational k (μ ⊕ ι) κ)
    (a : ι → K) (a' : κ → K)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) (u : μ → K) :
    F.IsAdmissible a a' u ↔
      ∀ w : κ → K, IsGenericOver (racl k (range u)) a' w →
        ∃ y : ι → K, InLocus (k := k) a y ∧
          F.IsDefinedAt (Sum.elim u y) ∧ F.eval (Sum.elim u y) = w := by
  let M := racl k (range u)
  have hM : IsSmall k (M : Set K) := isSmall_parameterClosure u
  let f := F.specialize u
  constructor
  · intro hu w hw
    obtain ⟨y, hy⟩ := exists_isGenericOver hM a
    have hz : IsGenericOver M a' (f.eval y) := by
      rw [F.specialize_eval]
      exact (hu y hy).2
    obtain ⟨σ, hσ⟩ := hz.exists_algEquiv hw
    have hyσ : IsGenericOver M a (⇑σ ∘ y) := hy.comp σ
    refine ⟨⇑σ ∘ y, hyσ.inLocus, (hu _ hyσ).1, ?_⟩
    rw [← F.specialize_eval, f.eval_comp σ]
    exact funext hσ
  · intro hcover
    obtain ⟨w, hw⟩ := exists_isGenericOver hM a'
    obtain ⟨y₀, hy₀V, hy₀D, hy₀w⟩ := hcover w hw
    have hf₀ : f.IsDefinedAt y₀ := (F.specialize_isDefinedAt_iff u y₀).2 hy₀D
    have hfw : f.eval y₀ = w := (F.specialize_eval u y₀).trans hy₀w
    have hy₀ : IsGenericOver M a y₀ := F.isGenericOver_of_eval_eq hdim hw hy₀V hy₀D hy₀w
    intro y hy
    obtain ⟨σ, hσ⟩ := hy₀.exists_algEquiv hy
    have hσy : ⇑σ ∘ y₀ = y := funext hσ
    have hfy : f.IsDefinedAt y := by
      rw [← hσy]
      exact (f.isDefinedAt_comp_iff σ y₀).2 hf₀
    refine ⟨(F.specialize_isDefinedAt_iff u y).1 hfy, ?_⟩
    rw [← F.specialize_eval, ← hσy, f.eval_comp σ y₀, hfw]
    exact hw.comp σ

omit [IsAlgClosed k] [UniversalDomain k K] [Finite μ] in
/-- The actual fibre relation of an expression over its source locus is constructible.
Its points are a parameter, a target point and a defined source-locus preimage.
Named consumers: the admissible and invertible-admissible parameter sets. -/
theorem isConstructibleOver_fibre (F : QuasiRational k (μ ⊕ ι) κ) (a : ι → K) :
    IsConstructibleOver k {z : ((μ ⊕ κ) ⊕ ι) → K |
      InLocus (k := k) a (z ∘ Sum.inr) ∧
      F.IsDefinedAt (Sum.elim ((z ∘ Sum.inl) ∘ Sum.inl) (z ∘ Sum.inr)) ∧
      F.eval (Sum.elim ((z ∘ Sum.inl) ∘ Sum.inl) (z ∘ Sum.inr)) =
        (z ∘ Sum.inl) ∘ Sum.inr} := by
  let q : ((μ ⊕ ι) ⊕ κ) → MvPolynomial ((μ ⊕ κ) ⊕ ι) k :=
    Sum.elim (Sum.elim
      (fun i ↦ X (Sum.inl (Sum.inl i))) (fun j ↦ X (Sum.inr j)))
      (fun j ↦ X (Sum.inl (Sum.inr j)))
  have hgraph := (F.isConstructibleOver_graph (K := K)).preimage_polynomial q
  have hlocus := (isConstructibleOver_inLocus a).preimage_polynomial
    (fun j ↦ (X (Sum.inr j) : MvPolynomial ((μ ⊕ κ) ⊕ ι) k))
  have hpoint (z : ((μ ⊕ κ) ⊕ ι) → K) :
      (fun j ↦ aeval z (q j)) =
        Sum.elim (Sum.elim ((z ∘ Sum.inl) ∘ Sum.inl) (z ∘ Sum.inr))
          ((z ∘ Sum.inl) ∘ Sum.inr) := by
    funext i
    rcases i with (i | j) | j <;>
      simp only [q, Sum.elim_inl, Sum.elim_inr, aeval_X, Function.comp_apply]
  convert hlocus.inter hgraph using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, hpoint,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr, aeval_X]

omit [Finite μ] in
/-- The generic-quantifier majority locus over the base field: for a constructible
condition on parameters and target points, the parameters at which it holds at every
generic target point form a constructible set after adjoining a finite independent
family of generic target samples.
Named consumers: the admissible and invertible-admissible parameter sets. -/
theorem isConstructibleOver_forall_generic [Fintype μ] {α : Type*} [Fintype α]
    (a' : κ → K) (t : α → κ → K)
    (ht : ∀ i, IsGenericOver (⊥ : IntermediateField k K) a' (t i))
    (hind : erk k ((⊥ : IntermediateField k K) : Set K) (⋃ i, range (t i)) =
      ∑ i, erk k ((⊥ : IntermediateField k K) : Set K) (range (t i)))
    (hr : 2 * Fintype.card μ + 1 ≤ Fintype.card α) {s : Set ((μ ⊕ κ) → K)}
    (hs : IsConstructibleOver k s) :
    IsConstructibleOver (↥(adjoin k (⋃ i, range (t i))))
      {u : μ → K | ∀ w, IsGenericOver (racl k (range u)) a' w → Sum.elim u w ∈ s} := by
  let M : IntermediateField k K := ⊥
  have hM : IsSmall k (M : Set K) :=
    ((IsSmall.of_finite (finite_empty : (∅ : Set K).Finite)).racl).mono
      (bot_le : (⊥ : IntermediateField k K) ≤ racl k (∅ : Set K))
  have hfield : (adjoin (↥M) (⋃ i, range (t i))).restrictScalars k =
      adjoin k (⋃ i, range (t i)) := by
    rw [restrictScalars_adjoin, adjoin_union, adjoin_self]
    exact bot_sup_eq _
  have h := IsConstructibleOver.of_restrictScalars_eq hfield
    (constructible_generic_quantifier M hM a' t ht hind hr hs.extend_base)
  convert h using 1
  ext u
  have hadj : (adjoin (↥M) (range u)).restrictScalars k = adjoin k (range u) := by
    rw [restrictScalars_adjoin, adjoin_union, adjoin_self]
    exact bot_sup_eq _
  have hbase : (racl (↥M) (range u)).restrictScalars k = racl k (range u) := by
    ext x
    rw [mem_restrictScalars, mem_racl_iff (↥M), mem_racl_iff k, ← hadj]
    exact Iff.rfl
  simp only [Set.mem_ofPred_eq, hbase]

/-- The actual admissible-parameter set is constructible after adjoining a finite
independent family of generic target samples. The sample hypotheses are the
genuine majority-quantifier hypotheses, not assumed admissibility or group data. -/
theorem isConstructibleOver_admissible [Fintype μ] {α : Type*} [Fintype α]
    (F : QuasiRational k (μ ⊕ ι) κ) (a : ι → K) (a' : κ → K)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) (t : α → κ → K)
    (ht : ∀ i, IsGenericOver (⊥ : IntermediateField k K) a' (t i))
    (hind : erk k ((⊥ : IntermediateField k K) : Set K) (⋃ i, range (t i)) =
      ∑ i, erk k ((⊥ : IntermediateField k K) : Set K) (range (t i)))
    (hr : 2 * Fintype.card μ + 1 ≤ Fintype.card α) :
    IsConstructibleOver (↥(adjoin k (⋃ i, range (t i))))
      {u : μ → K | F.IsAdmissible a a' u} := by
  have h := isConstructibleOver_forall_generic a' t ht hind hr
    ((F.isConstructibleOver_fibre a).exists (φ := fun v y ↦ InLocus (k := k) a y ∧
      F.IsDefinedAt (Sum.elim (v ∘ Sum.inl) y) ∧ F.eval (Sum.elim (v ∘ Sum.inl) y) = v ∘ Sum.inr))
  convert h using 1
  ext u
  simpa only [Set.mem_ofPred_eq, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
    using F.isAdmissible_iff_generic_surjective a a' hdim u

end QuasiRational

end

end GroupConfig
