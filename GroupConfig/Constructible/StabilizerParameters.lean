/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.ConfigurationBaseChange
import GroupConfig.Constructible.AdmissibleWords
import GroupConfig.Constructible.GroupDomainFormula
import GroupConfig.Constructible.GroupDomainMembership
import GroupConfig.Germ.BijectionStabilizer

/-!
# The stabiliser parameter relation

Blueprint `sources/group_configuration/09-constructibility.tex`, `thm:constructible`(2), the
claim and the constructibility of the stabiliser.

Let `F` be an actual quasi-rational family from the locus of `a` to the locus of `a'`, with
parameters in the locus `W` of a tuple `c`, and let `w` be a word from the locus of `a` to
itself with parameters `d`, standing for a group element `γ`. The word `g_v γ`
(`GroupConfig.stabWord`) appends the letter `F` at a parameter `v` to `w`; its parameters are
read off `((d, v), u')` through `GroupConfig.Word.mapParams`.

* `GroupConfig.stabilizerInner` is the relation of the source in `((d, y₀), v)`: some
  `u' ∈ W(K) ∩ Adm^×` has every letter of `g_v γ` invertibly admissible, `g_v γ = g_{u'}`, and
  `F(u', y₀) = F(v, y₀)` with both sides defined.
* `GroupConfig.stabilizerRel M` asks for this for every `v` generic in `W` over
  `acl(M, d, y₀)`.

The inner relation is constructible over a field containing the samples of the word `g_v γ`
and of the source locus (`GroupConfig.isConstructibleOver_stabilizerInner`). After adjoining
generic points of `W` independent over a small such field `L₀`, the relation over `L₀` is
constructible (`GroupConfig.isConstructibleOver_stabilizerRel`), and so is its fibre at a fixed
point `y₀` (`GroupConfig.isConstructibleOver_stabilizerFibre`). Enlarging the field of the
quantifier does not change the relation (`GroupConfig.stabilizerRel_eq_of_le`).

For an actual family representing the generic set of a Hrushovski–Weil datum of bijections at
the transports of a tuple `c` generating its canonical base, and a parameter `d` of a word for
`γ`, the pair `(d, y₀)` is in the relation exactly when `γ` fixes `ι(y₀)`
(`GroupConfig.mem_stabilizerRel_iff`). No independence of `y₀` from `d` is assumed: the rank
argument of the source shows that `y₀` is generic over every witness `u'`.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the claim of `thm:constructible`(2) and the constructibility of the stabiliser
parameter relation and of its fibres are complete, relative to fields containing the required
generic samples. The choice of the samples and the presentations of `G` and of `G/H` are not
part of this module.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

universe u₁ u₂ u₃ v

variable {k : Type u₁} {K : Type u₂} [Field k] [Field K] [Algebra k K] {P : Type u₃}
  {ι : Type v} {a : ι → K}

variable [Finite ι] {κ μ : Type v} [Finite κ] {a' : κ → K}

omit [Finite ι] in
/-- The values of `F` at two parameters and one point are defined and equal on a constructible
set over `k`: both are the end of a common graph point. -/
private theorem isConstructibleOver_eval_eq [IsAlgClosed K] {X : Type*} [Finite X]
    (F : QuasiRational k (μ ⊕ ι) κ) (e₁ e₂ : μ → X) (e : ι → X) :
    IsConstructibleOver k {Z : X → K | F.IsDefinedAt (Sum.elim (Z ∘ e₁) (Z ∘ e)) ∧
      F.IsDefinedAt (Sum.elim (Z ∘ e₂) (Z ∘ e)) ∧
      F.eval (Sum.elim (Z ∘ e₁) (Z ∘ e)) = F.eval (Sum.elim (Z ∘ e₂) (Z ∘ e))} := by
  have hG : IsConstructibleOver k {z : (X ⊕ κ) → K |
      (F.IsDefinedAt (Sum.elim ((z ∘ Sum.inl) ∘ e₁) ((z ∘ Sum.inl) ∘ e)) ∧
        F.eval (Sum.elim ((z ∘ Sum.inl) ∘ e₁) ((z ∘ Sum.inl) ∘ e)) = z ∘ Sum.inr) ∧
      (F.IsDefinedAt (Sum.elim ((z ∘ Sum.inl) ∘ e₂) ((z ∘ Sum.inl) ∘ e)) ∧
        F.eval (Sum.elim ((z ∘ Sum.inl) ∘ e₂) ((z ∘ Sum.inl) ∘ e)) = z ∘ Sum.inr)} :=
    (F.isConstructibleOver_graph_comp (Sum.inl ∘ e₁) (Sum.inl ∘ e) Sum.inr).inter
      (F.isConstructibleOver_graph_comp (Sum.inl ∘ e₂) (Sum.inl ∘ e) Sum.inr)
  convert hG.exists (φ := fun Z s ↦
    (F.IsDefinedAt (Sum.elim (Z ∘ e₁) (Z ∘ e)) ∧ F.eval (Sum.elim (Z ∘ e₁) (Z ∘ e)) = s) ∧
    (F.IsDefinedAt (Sum.elim (Z ∘ e₂) (Z ∘ e)) ∧ F.eval (Sum.elim (Z ∘ e₂) (Z ∘ e)) = s))
    using 1
  ext Z
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨_, ⟨h₁, rfl⟩, h₂, h₃.symm⟩
  · rintro ⟨s, ⟨h₁, rfl⟩, h₂, h₃⟩
    exact ⟨h₁, h₂, h₃.symm⟩

variable [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]

attribute [local instance] isAlgClosed_racl

/-- The relation of the claim of `thm:constructible`(2), in the coordinates `((d, y₀), v)`: some
`u'` in the locus `W` of `c` has an invertible admissible germ, every letter of `g_v γ` is
invertibly admissible, `g_v γ = g_{u'}`, and `F(u', y₀) = F(v, y₀)` with both sides defined. -/
def stabilizerInner [Fintype μ] (F : QuasiRational k (μ ⊕ ι) κ) (c : μ → K) (w : Word k P a a)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) : Set (((P ⊕ ι) ⊕ μ) → K) :=
  {z | ∃ u' : μ → K, InLocus (k := k) c u' ∧
    (∃ hu : F.IsAdmissible a a' u', Germ.IsInvertible (F.parameterGerm hu)) ∧
    (stabWord w F hdim).IsInvertiblyAdmissible
      (Sum.elim (Sum.elim ((z ∘ Sum.inl) ∘ Sum.inl) (z ∘ Sum.inr)) u') ∧
    (∃ hu' : F.IsAdmissible a a' u', (stabWord w F hdim).IsGerm
      (Sum.elim (Sum.elim ((z ∘ Sum.inl) ∘ Sum.inl) (z ∘ Sum.inr)) u') (F.parameterGerm hu')) ∧
    F.IsDefinedAt (Sum.elim u' ((z ∘ Sum.inl) ∘ Sum.inr)) ∧
    F.IsDefinedAt (Sum.elim (z ∘ Sum.inr) ((z ∘ Sum.inl) ∘ Sum.inr)) ∧
    F.eval (Sum.elim u' ((z ∘ Sum.inl) ∘ Sum.inr)) =
      F.eval (Sum.elim (z ∘ Sum.inr) ((z ∘ Sum.inl) ∘ Sum.inr))}

/-- The stabiliser parameter relation of `thm:constructible`(2) over a field `M`: the inner
relation holds at `((d, y₀), v)` for every `v` generic in the locus of `c` over
`acl(M, d, y₀)`. -/
def stabilizerRel [Fintype μ] (M : IntermediateField k K) (F : QuasiRational k (μ ⊕ ι) κ)
    (c : μ → K) (w : Word k P a a) (hdim : erk k ∅ (range a) = erk k ∅ (range a')) :
    Set ((P ⊕ ι) → K) :=
  {e | ∀ v, IsGenericOver (racl k ((M : Set K) ∪ range e)) c v →
    Sum.elim e v ∈ stabilizerInner F c w hdim}

/-! ### Constructibility -/

/-- `thm:constructible`(2): the inner relation is constructible over a field containing the
samples of the word `g_v γ` and samples of the source locus for its parameters. -/
theorem isConstructibleOver_stabilizerInner [Fintype P] [Fintype μ] (F : QuasiRational k (μ ⊕ ι) κ)
    (c : μ → K) (w : Word k P a a) (hdim : erk k ∅ (range a) = erk k ∅ (range a'))
    {L₀ : IntermediateField k K} (hw : w.HasSamples L₀)
    (hFt : HasGenericSamples L₀ a' (Fintype.card μ))
    (hsrc : HasGenericSamples L₀ a (Fintype.card ((P ⊕ μ) ⊕ μ))) :
    IsConstructibleOver (↥L₀) (stabilizerInner F c w hdim) := by
  let φ : (((P ⊕ ι) ⊕ μ) → K) → (μ → K) → Prop := fun z u' ↦
    InLocus (k := k) c u' ∧
    (∃ hu : F.IsAdmissible a a' u', Germ.IsInvertible (F.parameterGerm hu)) ∧
    (stabWord w F hdim).IsInvertiblyAdmissible
      (Sum.elim (Sum.elim ((z ∘ Sum.inl) ∘ Sum.inl) (z ∘ Sum.inr)) u') ∧
    (∃ hu' : F.IsAdmissible a a' u', (stabWord w F hdim).IsGerm
      (Sum.elim (Sum.elim ((z ∘ Sum.inl) ∘ Sum.inl) (z ∘ Sum.inr)) u') (F.parameterGerm hu')) ∧
    F.IsDefinedAt (Sum.elim u' ((z ∘ Sum.inl) ∘ Sum.inr)) ∧
    F.IsDefinedAt (Sum.elim (z ∘ Sum.inr) ((z ∘ Sum.inl) ∘ Sum.inr)) ∧
    F.eval (Sum.elim u' ((z ∘ Sum.inl) ∘ Sum.inr)) =
      F.eval (Sum.elim (z ∘ Sum.inr) ((z ∘ Sum.inl) ∘ Sum.inr))
  -- The coordinates are `(((d, y₀), v), u')`; `π` reads the word parameters `((d, v), u')`.
  let π : ((P ⊕ μ) ⊕ μ) → (((P ⊕ ι) ⊕ μ) ⊕ μ) :=
    Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inr)) Sum.inr
  have hπ (Z : (((P ⊕ ι) ⊕ μ) ⊕ μ) → K) : Z ∘ π =
      Sum.elim (Sum.elim (((Z ∘ Sum.inl) ∘ Sum.inl) ∘ Sum.inl) ((Z ∘ Sum.inl) ∘ Sum.inr))
        (Z ∘ Sum.inr) := by
    funext q
    rcases q with (p | m) | m <;> rfl
  have hW := (isConstructibleOver_groupWitness F c w hdim hw hFt hsrc).preimage_comp π
  have hE := (isConstructibleOver_eval_eq (K := K) F (Sum.inr : μ → ((P ⊕ ι) ⊕ μ) ⊕ μ)
    (Sum.inl ∘ Sum.inr) (Sum.inl ∘ Sum.inl ∘ Sum.inr)).extend_base (L := ↥L₀)
  have hT : IsConstructibleOver (↥L₀)
      {Z : (((P ⊕ ι) ⊕ μ) ⊕ μ) → K | φ (Z ∘ Sum.inl) (Z ∘ Sum.inr)} := by
    convert hW.inter hE using 1
    ext Z
    simp only [φ, groupWitness, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    rw [hπ Z]
    simp only [and_assoc, Sum.elim_comp_inr]
    rfl
  exact hT.exists (φ := φ)

/-- `thm:constructible`(2): after adjoining generic points of the locus of `c`, enough for the
parameters `(d, y₀)` and independent over a small field `L₀` containing the samples of the
words, the stabiliser parameter relation over `L₀` is constructible. -/
theorem isConstructibleOver_stabilizerRel [Fintype P] [Fintype ι] [Fintype μ]
    (F : QuasiRational k (μ ⊕ ι) κ) (c : μ → K) (w : Word k P a a)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) {L₀ : IntermediateField k K}
    (hL₀ : IsSmall k (L₀ : Set K)) (hw : w.HasSamples L₀)
    (hFt : HasGenericSamples L₀ a' (Fintype.card μ))
    (hsrc : HasGenericSamples L₀ a (Fintype.card ((P ⊕ μ) ⊕ μ)))
    {α : Type*} [Fintype α] (t : α → μ → K) (ht : ∀ i, IsGenericOver L₀ c (t i))
    (hind : erk k (L₀ : Set K) (⋃ i, range (t i)) = ∑ i, erk k (L₀ : Set K) (range (t i)))
    (hr : 2 * Fintype.card (P ⊕ ι) + 1 ≤ Fintype.card α) :
    IsConstructibleOver (↥(adjoin k ((L₀ : Set K) ∪ ⋃ i, range (t i))))
      (stabilizerRel L₀ F c w hdim) := by
  have h := constructible_generic_quantifier L₀ hL₀ c t ht hind hr
    (isConstructibleOver_stabilizerInner F c w hdim hw hFt hsrc)
  have hbase (S : Set K) : (racl (↥L₀) S).restrictScalars k = racl k ((L₀ : Set K) ∪ S) :=
    SetLike.coe_injective (racl_base_coe L₀ S)
  refine IsConstructibleOver.of_restrictScalars_eq (restrictScalars_adjoin k L₀ _) ?_
  convert h using 1
  ext e
  simp only [stabilizerRel, Set.mem_ofPred_eq, hbase]

/-- `thm:constructible`(2): the fibre of the stabiliser parameter relation at a point `y₀` is
constructible over the field generated by `L₀`, the samples of the locus of `c`, and `y₀`. -/
theorem isConstructibleOver_stabilizerFibre [Fintype P] [Fintype ι] [Fintype μ]
    (F : QuasiRational k (μ ⊕ ι) κ) (c : μ → K) (w : Word k P a a)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) {L₀ : IntermediateField k K}
    (hL₀ : IsSmall k (L₀ : Set K)) (hw : w.HasSamples L₀)
    (hFt : HasGenericSamples L₀ a' (Fintype.card μ))
    (hsrc : HasGenericSamples L₀ a (Fintype.card ((P ⊕ μ) ⊕ μ)))
    {α : Type*} [Fintype α] (t : α → μ → K) (ht : ∀ i, IsGenericOver L₀ c (t i))
    (hind : erk k (L₀ : Set K) (⋃ i, range (t i)) = ∑ i, erk k (L₀ : Set K) (range (t i)))
    (hr : 2 * Fintype.card (P ⊕ ι) + 1 ≤ Fintype.card α) (y₀ : ι → K) :
    IsConstructibleOver (↥(adjoin k (((L₀ : Set K) ∪ ⋃ i, range (t i)) ∪ range y₀)))
      {d : P → K | Sum.elim d y₀ ∈ stabilizerRel L₀ F c w hdim} := by
  let E := adjoin k (((L₀ : Set K) ∪ ⋃ i, range (t i)) ∪ range y₀)
  have h : IsConstructibleOver (↥E) (stabilizerRel L₀ F c w hdim) :=
    IsConstructibleOver.of_le_intermediateField (adjoin.mono k _ _ subset_union_left)
      (isConstructibleOver_stabilizerRel F c w hdim hL₀ hw hFt hsrc t ht hind hr)
  -- Substitute the coordinates of `y₀`, which lie in `E`.
  let q : (P ⊕ ι) → MvPolynomial P ↥E := Sum.elim MvPolynomial.X
    fun j ↦ MvPolynomial.C ⟨y₀ j, subset_adjoin k _ (Or.inr ⟨j, rfl⟩)⟩
  convert h.preimage_polynomial q using 1
  ext d
  have hq : (fun i ↦ MvPolynomial.aeval d (q i)) = Sum.elim d y₀ := by
    funext i
    rcases i with i | i
    · exact MvPolynomial.aeval_X _ _
    · exact MvPolynomial.aeval_C _ _
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, hq]

/-- `lem:gen-constructible`(2) for the stabiliser relation: when the inner relation is
constructible over `L₀`, quantifying over the points generic over `acl(L₁, d, y₀)` for a larger
small field `L₁` gives the same relation. -/
theorem stabilizerRel_eq_of_le [Finite P] [Fintype μ] {F : QuasiRational k (μ ⊕ ι) κ} {c : μ → K}
    {w : Word k P a a} {hdim : erk k ∅ (range a) = erk k ∅ (range a')}
    {L₀ L₁ : IntermediateField k K} (hL₀₁ : L₀ ≤ L₁) (hL₁ : IsSmall k (L₁ : Set K))
    (hin : IsConstructibleOver (↥L₀) (stabilizerInner F c w hdim)) :
    stabilizerRel L₀ F c w hdim = stabilizerRel L₁ F c w hdim := by
  ext e
  have hle : racl k ((L₀ : Set K) ∪ range e) ≤ racl k ((L₁ : Set K) ∪ range e) :=
    racl_mono (k := k) (union_subset_union_left _ hL₀₁)
  constructor
  · intro h v hv
    exact h v (hv.of_le hle)
  · intro h v hv
    have hs : IsSmall k ((racl k ((L₁ : Set K) ∪ range e) : IntermediateField k K) : Set K) :=
      (hL₁.union (IsSmall.of_finite (finite_range e))).racl
    -- A point generic over the larger field is conjugate to `v` over `acl(L₀, d, y₀)`.
    obtain ⟨v', hv'⟩ := exists_isGenericOver hs c
    obtain ⟨σ, hσ⟩ := (hv'.of_le hle).exists_algEquiv hv
    let σ₀ : K ≃ₐ[↥L₀] K :=
      { σ.toRingEquiv with
        commutes' := fun x ↦ σ.commutes ⟨x, subset_racl k _ (Or.inl x.2)⟩ }
    have he : ⇑σ₀ ∘ Sum.elim e v' = Sum.elim e v := by
      funext i
      rcases i with i | i
      · exact σ.commutes ⟨e i, subset_racl k _ (Or.inr ⟨i, rfl⟩)⟩
      · exact hσ i
    rw [← he]
    exact (hin.mem_comp_algEquiv_iff σ₀ _).2 (h v' hv')

/-! ### The claim -/

/-- The value of an admissible expression at a point generic over the closure of its parameter
is the value of its parameter germ. -/
private theorem eval_eq_evalGen [Finite μ] (F : QuasiRational k (μ ⊕ ι) κ) {u : μ → K}
    (hu : F.IsAdmissible a a' u) {y : ι → K} (hy : IsGenericOver (racl k (range u)) a y) :
    F.eval (Sum.elim u y) = (F.parameterGerm hu).evalGen y :=
  (F.eval_parameterGerm hu hy).symm.trans ((F.parameterGerm hu).evalGen_eq
    (IsSmall.of_finite (finite_range u)).racl (F.cb_parameterGerm_le hu) hy).symm

/-- The rank argument of `thm:constructible`(2): if a point `u` of the locus of `c` carries a
member `g` of the orbit of `f₀`, where `c` generates `Cb(f₀)` and `Cb(g) ⊆ acl(u)`, then every
generic point independent from `Cb(g)` is generic over `acl(u)`. -/
private theorem isGenericOver_racl_of_mem_orbit [Finite μ] {f₀ g : Germ k a a'}
    (hg : g ∈ Germ.orbit f₀)
    {c u : μ → K} (hc : adjoin k (range c) = f₀.cb) (hu : InLocus (k := k) c u)
    (hcb : g.cb ≤ racl k (range u)) {y : ι → K} (hy : IsGen k a y)
    (hind : IndepOver k ∅ (g.cb : Set K) (range y)) :
    IsGenericOver (racl k (range u)) a y := by
  refine hy.isGenericOver_racl (IsSmall.of_finite (finite_range u))
    (indepOver_of_erk_eq (finite_range u)
      (le_antisymm (erk_base_mono k (empty_subset _) _) ?_)).symm
  have hle := erk_le_of_inLocus (IsSmall.of_finite (k := k) finite_empty).racl hu
  rw [erk_racl_base] at hle
  calc erk k ∅ (range u) ≤ erk k ∅ (range c) := hle
    _ = erk k ∅ (f₀.cb : Set K) := by rw [← hc, erk_adjoin_eq]
    _ = erk k ∅ (g.cb : Set K) := (Germ.erk_cb_eq_of_mem_orbit hg).symm
    _ = erk k (∅ ∪ range y) (g.cb : Set K) := (Germ.erk_cb_eq_of_indepOver hind).symm
    _ ≤ erk k (∅ ∪ range y) (racl k ((∅ ∪ range y) ∪ range u) : Set K) :=
      erk_mono k _ fun x hx ↦ racl_mono (k := k) subset_union_right (hcb hx)
    _ = erk k (∅ ∪ range y) (range u) := erk_racl k _ _

/-- `thm:constructible`(2), the claim: let `F` represent the generic set of a Hrushovski–Weil
datum of bijections `f₀` at the transports of a tuple `c` generating `Cb(f₀)`, and let `d` be a
parameter of a word for `γ` with every letter invertibly admissible. For every small field `M`
and every generic point `y₀`, the pair `(d, y₀)` is in the stabiliser relation over `M` exactly
when `γ` fixes `ι(y₀)`. -/
theorem mem_stabilizerRel_iff [Finite P] [Fintype μ] {M : IntermediateField k K}
    (hM : IsSmall k (M : Set K)) {f₀ : Germ k a a'} (hb : Germ.IsHWBij f₀) {δ₀ : Germ k a a}
    (hδ₀ : δ₀ ∈ Germ.diffSet f₀) (hw : Germ.IsHW δ₀) (γ : ↥hw.prodSubgroup)
    {F : QuasiRational k (μ ⊕ ι) κ} {c : μ → K} (hc : adjoin k (range c) = f₀.cb)
    (hF : ∀ σ : K ≃ₐ[k] K, ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c),
      F.parameterGerm hu = f₀.map σ)
    (hdim : erk k ∅ (range a) = erk k ∅ (range a')) {w : Word k P a a} {d : P → K}
    (hd : w.IsGerm d (hw.val γ)) (hdInv : w.IsInvertiblyAdmissible d) {y₀ : ι → K}
    (hy₀ : IsGen k a y₀) :
    Sum.elim d y₀ ∈ stabilizerRel M F c w hdim ↔ γ • hw.iota hy₀ = hw.iota hy₀ := by
  have hG := hw.val_mem γ
  have hcb : ((hw.val γ).cb : Set K) ∪ range y₀ ⊆
      (racl k ((M : Set K) ∪ range (Sum.elim d y₀)) : Set K) :=
    union_subset (fun x hx ↦ racl_mono (k := k)
      (show range d ⊆ (M : Set K) ∪ range (Sum.elim d y₀) from
        fun _ ⟨i, hi⟩ ↦ Or.inr ⟨Sum.inl i, hi⟩) (hd.cb_le hx))
      fun _ ⟨i, hi⟩ ↦ subset_racl k _ (Or.inr ⟨Sum.inr i, hi⟩)
  have hs : IsSmall k
      ((racl k ((M : Set K) ∪ range (Sum.elim d y₀)) : IntermediateField k K) : Set K) :=
    (hM.union (IsSmall.of_finite (finite_range _))).racl
  /- The germ at a parameter `v` generic over `acl(M, d, y₀)` lies in the generic set and is
  independent from `γ` and `y₀`. -/
  have key (v : μ → K) (hv : IsGenericOver (racl k ((M : Set K) ∪ range (Sum.elim d y₀))) c v) :
      ∃ hv' : F.IsAdmissible a a' v, F.parameterGerm hv' ∈ Germ.orbit f₀ ∧
        IndepOver k ∅ ((F.parameterGerm hv').cb : Set K) (((hw.val γ).cb : Set K) ∪ range y₀) := by
    obtain ⟨hu, hmem⟩ := QuasiRational.exists_parameterGerm_mem_orbit_of_isGen hF hv.isGen
    refine ⟨hu, hmem, ((indepOver_racl_left_iff.2 hv.indepOver).mono_left ?_).mono_right hcb⟩
    rw [empty_union]
    exact F.cb_parameterGerm_le hu
  constructor
  · intro hrel
    obtain ⟨v, hv⟩ := exists_isGenericOver hs c
    obtain ⟨hv', hvo, hvind⟩ := key v hv
    obtain ⟨u', hu'V, -, -, ⟨hu', g₀, hv'', hg₀, hgeq⟩, -, -, heq⟩ := hrel v hv
    obtain rfl : g₀ = hw.val γ := ((w.isGerm_mapParams_iff _ _ _).1 hg₀).unique hd
    have hgeq' : F.parameterGerm hu' = Germ.comp (F.parameterGerm hv') (hw.val γ) := hgeq
    have hgo : F.parameterGerm hu' ∈ Germ.orbit f₀ := hgeq' ▸
      (hb.comp_mem_orbit hδ₀ hvo hG (hvind.mono_right subset_union_left).symm).1
    have hgind : IndepOver k ∅ ((F.parameterGerm hu').cb : Set K) (range y₀) := by
      rw [hgeq']
      exact (hb.indepOver_cb_comp hδ₀ hw hvo hG hvind).mono_right subset_union_right
    have hy₁ := isGenericOver_racl_of_mem_orbit hgo hc hu'V (F.cb_parameterGerm_le hu') hy₀
      hgind
    have hy₂ := isGenericOver_racl_of_mem_orbit hvo hc hv.inLocus (F.cb_parameterGerm_le hv')
      hy₀ (hvind.mono_right subset_union_right)
    rw [hb.smul_iota_eq_iff hδ₀ hw γ hy₀ hvo hvind, ← hgeq', ← eval_eq_evalGen F hu' hy₁,
      ← eval_eq_evalGen F hv' hy₂]
    exact heq
  · intro hfix v hv
    obtain ⟨hv', hvo, hvind⟩ := key v hv
    obtain ⟨⟨τ, hτ⟩, -⟩ :=
      hb.comp_mem_orbit hδ₀ hvo hG (hvind.mono_right subset_union_left).symm
    obtain ⟨hu', hu'g⟩ := hF τ
    have hgeq : F.parameterGerm hu' = Germ.comp (F.parameterGerm hv') (hw.val γ) :=
      hu'g.trans hτ
    have hgo : F.parameterGerm hu' ∈ Germ.orbit f₀ := ⟨τ, hu'g.symm⟩
    have hgind : IndepOver k ∅ ((F.parameterGerm hu').cb : Set K) (range y₀) := by
      rw [hgeq]
      exact (hb.indepOver_cb_comp hδ₀ hw hvo hG hvind).mono_right subset_union_right
    have hu'V : InLocus (k := k) c (⇑τ ∘ c) := IsGen.inLocus (IsGen.map (rfl : IsGen k c c) τ)
    have hy₁ := isGenericOver_racl_of_mem_orbit hgo hc hu'V (F.cb_parameterGerm_le hu') hy₀
      hgind
    have hy₂ := isGenericOver_racl_of_mem_orbit hvo hc hv.inLocus (F.cb_parameterGerm_le hv')
      hy₀ (hvind.mono_right subset_union_right)
    have hval : F.eval (Sum.elim (⇑τ ∘ c) y₀) = F.eval (Sum.elim v y₀) := by
      rw [eval_eq_evalGen F hu' hy₁, eval_eq_evalGen F hv' hy₂, hgeq]
      exact (hb.smul_iota_eq_iff hδ₀ hw γ hy₀ hvo hvind).1 hfix
    exact ⟨⇑τ ∘ c, hu'V, ⟨hu', Germ.isInvertible_of_mem_orbit hb.isInvertible hgo⟩,
      ⟨(w.isInvertiblyAdmissible_mapParams_iff _ _).2 hdInv, hv',
        Germ.isInvertible_of_mem_orbit hb.isInvertible hvo⟩,
      ⟨hu', hw.val γ, hv', (w.isGerm_mapParams_iff _ _ _).2 hd, hgeq⟩,
      (hu' y₀ hy₁).1, (hv' y₀ hy₂).1, hval⟩

end

end GroupConfig
