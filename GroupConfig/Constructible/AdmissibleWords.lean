/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Constructible.InvertibleAdmissible

/-!
# Words in admissible parameter germs

Blueprint `sources/group_configuration/09-constructibility.tex`, `lem:adm-constructible`, the
paragraph on words.

A typed word (`GroupConfig.Word`) is a finite composite of actual quasi-rational letters
`F_{u ∘ ρ}` and of inverses `F_{u ∘ ρ}⁻¹` of such letters, between loci of equal rank. All letters
read their parameters from one tuple `u` through reindexings `ρ`, so letters may share
parameters.

* The chain relation `R_w(u; y, z)` (`Word.Chain`) asks for intermediate points in the
  prescribed loci, each step in the actual graph of its letter or of its transpose, with every
  expression defined at its argument.
* `Word.IsGerm w u g` says that every forward letter is admissible at its parameter, every
  inverse letter is invertibly admissible, and `g` is the composite germ. It determines `g`
  (`Word.IsGerm.unique`), and `Cb(g) ⊆ acl(k, u)` (`Word.IsGerm.cb_le`).
* At a point generic over `acl(k, u)` the chain is unique and ends at the value of the composite
  germ (`Word.IsGerm.chain_iff`). Two composite germs agree exactly when the chains of their words
  from every generic point have a common end (`Word.IsGerm.eq_iff`); the relation
  `w(u) = g_{u'}` of the source is the case of a one-letter second word.
* The chain relation is constructible over `k` (`Word.isConstructibleOver_chain`). After
  adjoining generic samples (`HasGenericSamples`, `Word.HasSamples`), the parameters of
  admissible words (`Word.isConstructibleOver_isGerm`), the equality relation of two words
  (`Word.isConstructibleOver_germ_eq`) and the relation of the source, in which every letter
  is invertibly admissible (`Word.IsInvertiblyAdmissible`) and the word equals the germ of a
  further admissible parameter (`Word.isConstructibleOver_eq_parameterGerm`), are
  constructible.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the word paragraph of `lem:adm-constructible` is complete, relative to a field
containing the required generic samples. The existence of such samples independent over a
prescribed small field is not part of this module.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

universe u₁ u₂ u₃ v

/-- Typed finite words in actual quasi-rational letters with parameters in `P`, from the locus of
`a`. A forward letter `F_{u ∘ ρ}` and an inverse letter `F_{u ∘ ρ}⁻¹` each carry the
equal-rank hypothesis of their loci. -/
inductive Word (k : Type u₁) {K : Type u₂} [Field k] [Field K] [Algebra k K] (P : Type u₃)
    {ι : Type v} (a : ι → K) : {κ : Type v} → (κ → K) → Type (max u₁ u₂ u₃ (v + 1))
  /-- The empty word. -/
  | nil : Word k P a a
  /-- Append a forward quasi-rational letter, reading parameters through `ρ`. -/
  | fwd {κ τ μ : Type v} [Finite κ] [Finite τ] [Fintype μ] {b : κ → K} (w : Word k P a b)
      (c : τ → K) (F : QuasiRational k (μ ⊕ κ) τ) (ρ : μ → P)
      (hdim : erk k ∅ (range b) = erk k ∅ (range c)) : Word k P a c
  /-- Append the inverse symbol of a quasi-rational letter. -/
  | inv {κ τ μ : Type v} [Finite κ] [Finite τ] [Fintype μ] {b : κ → K} (w : Word k P a b)
      (c : τ → K) (F : QuasiRational k (μ ⊕ τ) κ) (ρ : μ → P)
      (hdim : erk k ∅ (range c) = erk k ∅ (range b)) : Word k P a c

variable {k : Type u₁} {K : Type u₂} [Field k] [Field K] [Algebra k K] {P : Type u₃}
  {ι : Type v} {a : ι → K}

/-- `L` contains `2N + 1` generic points over `k` of the locus of `a`, independent over `k`.
These are the sample hypotheses of the generic quantifier with `N` parameter coordinates. -/
def HasGenericSamples (L : IntermediateField k K) {κ : Type*} (b : κ → K) (N : ℕ) : Prop :=
  ∃ (n : ℕ) (t : Fin n → κ → K), (∀ i, IsGenericOver (⊥ : IntermediateField k K) b (t i)) ∧
    erk k ((⊥ : IntermediateField k K) : Set K) (⋃ i, range (t i)) =
      ∑ i, erk k ((⊥ : IntermediateField k K) : Set K) (range (t i)) ∧
    2 * N + 1 ≤ n ∧ ∀ i, range (t i) ⊆ L

-- Sole consumer: the constructibility theorems below, which work over a field of samples.
private theorem isConstructibleOver_of_le {E E' : IntermediateField k K} (h : E ≤ E')
    {X : Type*} {s : Set (X → K)} (hs : IsConstructibleOver (↥E) s) :
    IsConstructibleOver (↥E') s := by
  let _ : Algebra ↥E ↥E' := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower ↥E ↥E' K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact hs.extend_base

-- Sole consumer: the chain relation below. The graph of an expression read off arbitrary
-- coordinates of a point.
private theorem isConstructibleOver_graph_comp [IsAlgClosed K] {μ κ τ X : Type*} [Finite τ]
    (F : QuasiRational k (μ ⊕ κ) τ) (e₁ : μ → X) (e₂ : κ → X) (e₃ : τ → X) :
    IsConstructibleOver k {z : X → K | F.IsDefinedAt (Sum.elim (z ∘ e₁) (z ∘ e₂)) ∧
      F.eval (Sum.elim (z ∘ e₁) (z ∘ e₂)) = z ∘ e₃} := by
  convert (F.isConstructibleOver_graph (K := K)).preimage_comp
    (Sum.elim (Sum.elim e₁ e₂) e₃) using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Sum.comp_elim, Sum.elim_comp_inl,
    Sum.elim_comp_inr]

namespace Word

/-- The samples a word needs: for each forward letter, samples of its target locus; for each
inverse letter `F⁻¹`, samples of the target locus of `F`; each for the parameters of the
letter. -/
def HasSamples (L : IntermediateField k K) : {κ : Type v} → {b : κ → K} → Word k P a b → Prop
  | _, _, nil => True
  | _, _, fwd (μ := μ) w c _ _ _ => w.HasSamples L ∧ HasGenericSamples L c (Fintype.card μ)
  | _, _, inv (μ := μ) (b := b) w _ _ _ _ =>
    w.HasSamples L ∧ HasGenericSamples L b (Fintype.card μ)

variable [IsAlgClosed K]

/-- The chain relation `R_w(u; y, z)`: points `y = y₀, …, y_l = z` in the prescribed loci, each
step in the graph of its letter (forward) or of its transpose (inverse), with the expression
defined at its argument. -/
def Chain : {κ : Type v} → {b : κ → K} → Word k P a b → (P → K) → (ι → K) → (κ → K) → Prop
  | _, _, nil, _, y, z => InLocus (k := k) a y ∧ z = y
  | _, _, fwd w c F ρ _, u, y, z => ∃ x, w.Chain u y x ∧ InLocus (k := k) c z ∧
      F.IsDefinedAt (Sum.elim (u ∘ ρ) x) ∧ F.eval (Sum.elim (u ∘ ρ) x) = z
  | _, _, inv w c F ρ _, u, y, z => ∃ x, w.Chain u y x ∧ InLocus (k := k) c z ∧
      F.IsDefinedAt (Sum.elim (u ∘ ρ) z) ∧ F.eval (Sum.elim (u ∘ ρ) z) = x

variable [IsAlgClosed k] [UniversalDomain k K] [Finite ι]

/-- `g` is the composite germ of `w` at `u`: forward letters are admissible at their
parameters, inverse letters are invertibly admissible, and `g` is their composite. -/
def IsGerm : {κ : Type v} → {b : κ → K} → Word k P a b → (P → K) → Germ k a b → Prop
  | _, _, nil, _, g => g = Germ.id a
  | _, _, fwd (b := b) w c F ρ _, u, g => ∃ (g₀ : Germ k a b) (hu : F.IsAdmissible b c (u ∘ ρ)),
      w.IsGerm u g₀ ∧ g = Germ.comp (F.parameterGerm hu) g₀
  | _, _, inv (b := b) w c F ρ _, u, g => ∃ (g₀ : Germ k a b) (hu : F.IsAdmissible c b (u ∘ ρ))
      (h : Germ k b c), w.IsGerm u g₀ ∧ Germ.IsInverse h (F.parameterGerm hu) ∧
        g = Germ.comp h g₀

/-- Every letter of `w`, forward or inverse, is invertibly admissible at its parameter: the
condition `u_j ∈ Adm^×_j` of the source relation. -/
def IsInvertiblyAdmissible : {κ : Type v} → {b : κ → K} → Word k P a b → (P → K) → Prop
  | _, _, nil, _ => True
  | _, _, fwd (b := b) w c F ρ _, u => w.IsInvertiblyAdmissible u ∧
      ∃ hu : F.IsAdmissible b c (u ∘ ρ), Germ.IsInvertible (F.parameterGerm hu)
  | _, _, inv (b := b) w c F ρ _, u => w.IsInvertiblyAdmissible u ∧
      ∃ hu : F.IsAdmissible c b (u ∘ ρ), Germ.IsInvertible (F.parameterGerm hu)

attribute [local instance] isAlgClosed_racl

variable [Finite P]

/-- The canonical base of a composite germ lies in the closure of the parameters. -/
theorem IsGerm.cb_le {κ : Type v} {b : κ → K} {w : Word k P a b} [hκ : Finite κ] {u : P → K}
    {g : Germ k a b} (hg : w.IsGerm u g) : g.cb ≤ racl k (range u) := by
  have hM : IsSmall k ((racl k (range u) : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite (finite_range u)).racl
  -- The finiteness of the target is generalized along with the target.
  revert hκ
  induction w with
  | nil =>
    intro _
    obtain rfl : g = Germ.id a := hg
    exact Germ.cb_id_le a _
  | fwd w c F ρ hdim ih =>
    intro _
    obtain ⟨g₀, hu, hg₀, rfl⟩ := hg
    exact Germ.cb_comp_le _ _ hM (ih hg₀)
      ((F.cb_parameterGerm_le hu).trans (racl_mono (k := k) (range_comp_subset_range ρ u)))
  | inv w c F ρ hdim ih =>
    intro _
    obtain ⟨g₀, hu, h, hg₀, hi, rfl⟩ := hg
    exact Germ.cb_comp_le _ _ hM (ih hg₀) (hi.cb_le.trans (racl_le_of_isAlgClosed
      ((F.cb_parameterGerm_le hu).trans (racl_mono (k := k) (range_comp_subset_range ρ u)))))

/-- At a point generic over the closure of the parameters, the chain of a word is unique and
ends at the value of its composite germ. -/
theorem IsGerm.chain_iff {κ : Type v} {b : κ → K} {w : Word k P a b} [hκ : Finite κ] {u : P → K}
    {g : Germ k a b} (hg : w.IsGerm u g) {y : ι → K}
    (hy : IsGenericOver (racl k (range u)) a y) (z : κ → K) :
    w.Chain u y z ↔ z = g.eval (racl k (range u)) y := by
  have hM : IsSmall k ((racl k (range u) : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite (finite_range u)).racl
  revert hκ
  induction w with
  | nil =>
    intro _
    obtain rfl : g = Germ.id a := hg
    change InLocus (k := k) a y ∧ z = y ↔ _
    rw [Germ.eval_id hM hy]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hy.inLocus, h⟩⟩
  | @fwd κ' τ μ _ _ _ b w c F ρ hdim ih =>
    intro _
    obtain ⟨g₀, hu, hg₀, rfl⟩ := hg
    have hcb₀ := hg₀.cb_le
    have hle : racl k (range (u ∘ ρ)) ≤ racl k (range u) :=
      racl_mono (k := k) (range_comp_subset_range ρ u)
    have hM' : IsSmall k ((racl k (range (u ∘ ρ)) : IntermediateField k K) : Set K) :=
      (IsSmall.of_finite (finite_range _)).racl
    have hx₀ := g₀.isGenericOver_eval hM hcb₀ hy
    have hx₀' := hx₀.of_le hle
    have hval : F.eval (Sum.elim (u ∘ ρ) (g₀.eval (racl k (range u)) y)) =
        (Germ.comp (F.parameterGerm hu) g₀).eval (racl k (range u)) y := by
      rw [Germ.comp_eval _ _ hM hcb₀ ((F.cb_parameterGerm_le hu).trans hle) hy,
        ← Germ.eval_eq_of_le _ hM' hM (F.cb_parameterGerm_le hu) hle hx₀,
        F.eval_parameterGerm hu hx₀']
    change (∃ x, w.Chain u y x ∧ InLocus (k := k) c z ∧ F.IsDefinedAt (Sum.elim (u ∘ ρ) x) ∧
      F.eval (Sum.elim (u ∘ ρ) x) = z) ↔ _
    constructor
    · rintro ⟨x, hx, -, -, rfl⟩
      obtain rfl := (ih hg₀ x).1 hx
      exact hval
    · rintro rfl
      refine ⟨_, (ih hg₀ _).2 rfl, ?_, (hu _ hx₀').1, hval⟩
      rw [← hval]
      exact (hu _ hx₀').2.inLocus
  | @inv κ' τ μ _ _ _ b w c F ρ hdim ih =>
    intro _
    obtain ⟨g₀, hu, h, hg₀, hi, rfl⟩ := hg
    have hcb₀ := hg₀.cb_le
    have hle : racl k (range (u ∘ ρ)) ≤ racl k (range u) :=
      racl_mono (k := k) (range_comp_subset_range ρ u)
    have hM' : IsSmall k ((racl k (range (u ∘ ρ)) : IntermediateField k K) : Set K) :=
      (IsSmall.of_finite (finite_range _)).racl
    have hcbh : h.cb ≤ racl k (range (u ∘ ρ)) :=
      hi.cb_le.trans (racl_le_of_isAlgClosed (F.cb_parameterGerm_le hu))
    have hx₀ := g₀.isGenericOver_eval hM hcb₀ hy
    have hx₀' := hx₀.of_le hle
    have hval : h.eval (racl k (range (u ∘ ρ))) (g₀.eval (racl k (range u)) y) =
        (Germ.comp h g₀).eval (racl k (range u)) y := by
      rw [Germ.comp_eval _ _ hM hcb₀ (hcbh.trans hle) hy,
        Germ.eval_eq_of_le _ hM' hM hcbh hle hx₀]
    change (∃ x, w.Chain u y x ∧ InLocus (k := k) c z ∧ F.IsDefinedAt (Sum.elim (u ∘ ρ) z) ∧
      F.eval (Sum.elim (u ∘ ρ) z) = x) ↔ _
    rw [← hval]
    constructor
    · rintro ⟨x, hx, hzV, hzD, hzx⟩
      obtain rfl := (ih hg₀ x).1 hx
      exact F.eq_eval_of_isInverse hdim hu hi hx₀' hzV hzD hzx
    · rintro rfl
      exact ⟨_, (ih hg₀ _).2 rfl, F.mem_fibre_eval_of_isInverse hu hi hx₀'⟩

/-- Two composite germs of words with the same source and target agree exactly when, from every
point generic over the closure of the parameters, their chains have a common end. -/
theorem IsGerm.eq_iff {κ : Type v} {b : κ → K} {w₁ w₂ : Word k P a b} [Finite κ] {u : P → K}
    {g₁ g₂ : Germ k a b} (h₁ : w₁.IsGerm u g₁) (h₂ : w₂.IsGerm u g₂) :
    g₁ = g₂ ↔ ∀ y, IsGenericOver (racl k (range u)) a y →
      ∃ z, w₁.Chain u y z ∧ w₂.Chain u y z := by
  have hM : IsSmall k ((racl k (range u) : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite (finite_range u)).racl
  constructor
  · rintro rfl y hy
    exact ⟨_, (h₁.chain_iff hy _).2 rfl, (h₂.chain_iff hy _).2 rfl⟩
  · intro h
    obtain ⟨y, hy⟩ := exists_isGenericOver hM a
    obtain ⟨z, hz₁, hz₂⟩ := h y hy
    exact Germ.eq_of_eval_eq hM h₁.cb_le h₂.cb_le hy
      (((h₁.chain_iff hy z).1 hz₁).symm.trans ((h₂.chain_iff hy z).1 hz₂))

/-- A word has at most one composite germ at a parameter. -/
theorem IsGerm.unique {κ : Type v} {b : κ → K} {w : Word k P a b} [Finite κ] {u : P → K}
    {g g' : Germ k a b} (hg : w.IsGerm u g) (hg' : w.IsGerm u g') : g = g' :=
  (hg.eq_iff hg').2 fun _ hy ↦ ⟨_, (hg.chain_iff hy _).2 rfl, (hg.chain_iff hy _).2 rfl⟩

omit [IsAlgClosed k] [UniversalDomain k K] in
/-- The chain relation of a word is constructible over `k`. -/
theorem isConstructibleOver_chain {κ : Type v} {b : κ → K} (w : Word k P a b) :
    IsConstructibleOver k {v : ((P ⊕ ι) ⊕ κ) → K |
      w.Chain ((v ∘ Sum.inl) ∘ Sum.inl) ((v ∘ Sum.inl) ∘ Sum.inr) (v ∘ Sum.inr)} := by
  induction w with
  | nil =>
    have hEq : IsConstructibleOver k {v : ((P ⊕ ι) ⊕ ι) → K |
        v ∘ Sum.inr = (v ∘ Sum.inl) ∘ Sum.inr} := by
      convert IsConstructibleOver.iInter fun i : ι ↦ IsConstructibleOver.polynomial_zero (K := K)
        (X (Sum.inr i) - X (Sum.inl (Sum.inr i)) : MvPolynomial ((P ⊕ ι) ⊕ ι) k) using 1
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, map_sub, aeval_X, sub_eq_zero, funext_iff,
        Function.comp_apply]
    exact ((isConstructibleOver_inLocus a).preimage_comp (Sum.inl ∘ Sum.inr)).inter hEq
  | @fwd κ' τ μ _ _ _ b w c F ρ hdim ih =>
    have hT : IsConstructibleOver k {z : (((P ⊕ ι) ⊕ τ) ⊕ κ') → K |
        w.Chain (((z ∘ Sum.inl) ∘ Sum.inl) ∘ Sum.inl) (((z ∘ Sum.inl) ∘ Sum.inl) ∘ Sum.inr)
          (z ∘ Sum.inr) ∧ InLocus (k := k) c ((z ∘ Sum.inl) ∘ Sum.inr) ∧
        F.IsDefinedAt (Sum.elim ((((z ∘ Sum.inl) ∘ Sum.inl) ∘ Sum.inl) ∘ ρ) (z ∘ Sum.inr)) ∧
        F.eval (Sum.elim ((((z ∘ Sum.inl) ∘ Sum.inl) ∘ Sum.inl) ∘ ρ) (z ∘ Sum.inr)) =
          (z ∘ Sum.inl) ∘ Sum.inr} :=
      (ih.preimage_comp (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr)).inter
        (((isConstructibleOver_inLocus c).preimage_comp (Sum.inl ∘ Sum.inr)).inter
          (isConstructibleOver_graph_comp F (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ ρ) Sum.inr
            (Sum.inl ∘ Sum.inr)))
    exact hT.exists (φ := fun v x ↦
      w.Chain ((v ∘ Sum.inl) ∘ Sum.inl) ((v ∘ Sum.inl) ∘ Sum.inr) x ∧
      InLocus (k := k) c (v ∘ Sum.inr) ∧
      F.IsDefinedAt (Sum.elim (((v ∘ Sum.inl) ∘ Sum.inl) ∘ ρ) x) ∧
      F.eval (Sum.elim (((v ∘ Sum.inl) ∘ Sum.inl) ∘ ρ) x) = v ∘ Sum.inr)
  | @inv κ' τ μ _ _ _ b w c F ρ hdim ih =>
    have hT : IsConstructibleOver k {z : (((P ⊕ ι) ⊕ τ) ⊕ κ') → K |
        w.Chain (((z ∘ Sum.inl) ∘ Sum.inl) ∘ Sum.inl) (((z ∘ Sum.inl) ∘ Sum.inl) ∘ Sum.inr)
          (z ∘ Sum.inr) ∧ InLocus (k := k) c ((z ∘ Sum.inl) ∘ Sum.inr) ∧
        F.IsDefinedAt (Sum.elim ((((z ∘ Sum.inl) ∘ Sum.inl) ∘ Sum.inl) ∘ ρ)
          ((z ∘ Sum.inl) ∘ Sum.inr)) ∧
        F.eval (Sum.elim ((((z ∘ Sum.inl) ∘ Sum.inl) ∘ Sum.inl) ∘ ρ)
          ((z ∘ Sum.inl) ∘ Sum.inr)) = z ∘ Sum.inr} :=
      (ih.preimage_comp (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr)).inter
        (((isConstructibleOver_inLocus c).preimage_comp (Sum.inl ∘ Sum.inr)).inter
          (isConstructibleOver_graph_comp F (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ ρ)
            (Sum.inl ∘ Sum.inr) Sum.inr))
    exact hT.exists (φ := fun v x ↦
      w.Chain ((v ∘ Sum.inl) ∘ Sum.inl) ((v ∘ Sum.inl) ∘ Sum.inr) x ∧
      InLocus (k := k) c (v ∘ Sum.inr) ∧
      F.IsDefinedAt (Sum.elim (((v ∘ Sum.inl) ∘ Sum.inl) ∘ ρ) (v ∘ Sum.inr)) ∧
      F.eval (Sum.elim (((v ∘ Sum.inl) ∘ Sum.inl) ∘ ρ) (v ∘ Sum.inr)) = x)

omit [Finite P] in
/-- The parameters at which every forward letter of a word is admissible and every inverse letter
is invertibly admissible form a constructible set over a field containing the samples of the
word. -/
theorem isConstructibleOver_isGerm {κ : Type v} {b : κ → K} (w : Word k P a b)
    {L : IntermediateField k K} (hL : w.HasSamples L) :
    IsConstructibleOver (↥L) {u : P → K | ∃ g, w.IsGerm u g} := by
  induction w with
  | nil =>
    convert (IsConstructibleOver.univ : IsConstructibleOver (↥L) (univ : Set (P → K))) using 1
    exact eq_univ_of_forall fun u ↦ ⟨Germ.id a, rfl⟩
  | @fwd κ' τ μ _ _ _ b w c F ρ hdim ih =>
    obtain ⟨hw, n, t, ht, hind, hn, htL⟩ := hL
    have hA := isConstructibleOver_of_le (adjoin_le_iff.2 (iUnion_subset htL))
      (F.isConstructibleOver_admissible b c hdim t ht hind (by rwa [Fintype.card_fin]))
    convert (ih hw).inter (hA.preimage_comp ρ) using 1
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨_, g₀, hu, hg₀, -⟩
      exact ⟨⟨g₀, hg₀⟩, hu⟩
    · rintro ⟨⟨g₀, hg₀⟩, hu⟩
      exact ⟨_, g₀, hu, hg₀, rfl⟩
  | @inv κ' τ μ _ _ _ b w c F ρ hdim ih =>
    obtain ⟨hw, n, t, ht, hind, hn, htL⟩ := hL
    have hA := isConstructibleOver_of_le (adjoin_le_iff.2 (iUnion_subset htL))
      (F.isConstructibleOver_invertibleAdmissible c b hdim t ht hind (by rwa [Fintype.card_fin]))
    convert (ih hw).inter (hA.preimage_comp ρ) using 1
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨_, g₀, hu, h, hg₀, hi, -⟩
      exact ⟨⟨g₀, hg₀⟩, hu, h, hi⟩
    · rintro ⟨⟨g₀, hg₀⟩, hu, h, hi⟩
      exact ⟨_, g₀, hu, h, hg₀, hi, rfl⟩

/-- `lem:adm-constructible`, words: the parameters at which two words with the same source and
target are admissible with equal composite germs form a constructible set over a field
containing their samples and samples of the source locus. -/
theorem isConstructibleOver_germ_eq [Fintype P] {κ : Type v} [Finite κ] {b : κ → K}
    (w₁ w₂ : Word k P a b) {L : IntermediateField k K} (h₁ : w₁.HasSamples L)
    (h₂ : w₂.HasSamples L) (ha : HasGenericSamples L a (Fintype.card P)) :
    IsConstructibleOver (↥L) {u : P → K | ∃ g, w₁.IsGerm u g ∧ w₂.IsGerm u g} := by
  have hS := (w₁.isConstructibleOver_chain.inter w₂.isConstructibleOver_chain).exists
    (φ := fun (v : (P ⊕ ι) → K) (z : κ → K) ↦
      w₁.Chain (v ∘ Sum.inl) (v ∘ Sum.inr) z ∧ w₂.Chain (v ∘ Sum.inl) (v ∘ Sum.inr) z)
  obtain ⟨n, t, ht, hind, hn, htL⟩ := ha
  have hQ := isConstructibleOver_of_le (adjoin_le_iff.2 (iUnion_subset htL))
    (QuasiRational.isConstructibleOver_forall_generic a t ht hind (by rwa [Fintype.card_fin]) hS)
  convert ((w₁.isConstructibleOver_isGerm h₁).inter (w₂.isConstructibleOver_isGerm h₂)).inter hQ
    using 1
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Sum.elim_comp_inl, Sum.elim_comp_inr]
  constructor
  · rintro ⟨g, hg₁, hg₂⟩
    exact ⟨⟨⟨g, hg₁⟩, ⟨g, hg₂⟩⟩, (hg₁.eq_iff hg₂).1 rfl⟩
  · rintro ⟨⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩, hq⟩
    obtain rfl := (hg₁.eq_iff hg₂).2 hq
    exact ⟨g₁, hg₁, hg₂⟩

omit [Finite P] [Finite ι] in
/-- The parameters at which every letter of a word is invertibly admissible form a
constructible set over a field containing the samples of the word. -/
theorem isConstructibleOver_isInvertiblyAdmissible {κ : Type v} {b : κ → K}
    (w : Word k P a b) {L : IntermediateField k K} (hL : w.HasSamples L) :
    IsConstructibleOver (↥L) {u : P → K | w.IsInvertiblyAdmissible u} := by
  induction w with
  | nil => exact IsConstructibleOver.univ
  | @fwd κ' τ μ _ _ _ b w c F ρ hdim ih =>
    obtain ⟨hw, n, t, ht, hind, hn, htL⟩ := hL
    have hA := isConstructibleOver_of_le (adjoin_le_iff.2 (iUnion_subset htL))
      (F.isConstructibleOver_invertibleAdmissible b c hdim t ht hind (by rwa [Fintype.card_fin]))
    exact (ih hw).inter (hA.preimage_comp ρ)
  | @inv κ' τ μ _ _ _ b w c F ρ hdim ih =>
    obtain ⟨hw, n, t, ht, hind, hn, htL⟩ := hL
    have hA := isConstructibleOver_of_le (adjoin_le_iff.2 (iUnion_subset htL))
      (F.isConstructibleOver_invertibleAdmissible c b hdim t ht hind (by rwa [Fintype.card_fin]))
    exact (ih hw).inter (hA.preimage_comp ρ)

/-- `lem:adm-constructible`, words, in the source's form: the parameters `u` at which every
letter of `w` is invertibly admissible, the parameter `u ∘ ρ'` of a further expression `F'` is
admissible, and the composite germ `w(u)` equals `g_{u ∘ ρ'}`, form a constructible set over a
field containing the samples. -/
theorem isConstructibleOver_eq_parameterGerm [Fintype P] {κ : Type v} [Finite κ] {b : κ → K}
    (w : Word k P a b) {μ' : Type v} [Fintype μ'] (F' : QuasiRational k (μ' ⊕ ι) κ)
    (ρ' : μ' → P) (hdim' : erk k ∅ (range a) = erk k ∅ (range b))
    {L : IntermediateField k K} (hw : w.HasSamples L)
    (hF' : HasGenericSamples L b (Fintype.card μ'))
    (ha : HasGenericSamples L a (Fintype.card P)) :
    IsConstructibleOver (↥L) {u : P → K | w.IsInvertiblyAdmissible u ∧
      ∃ hu' : F'.IsAdmissible a b (u ∘ ρ'), w.IsGerm u (F'.parameterGerm hu')} := by
  convert (w.isConstructibleOver_isInvertiblyAdmissible hw).inter
    (isConstructibleOver_germ_eq w (fwd nil b F' ρ' hdim') hw ⟨trivial, hF'⟩ ha) using 1
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hinv, hu', hg⟩
    exact ⟨hinv, _, hg, _, hu', rfl, (Germ.comp_id _).symm⟩
  · rintro ⟨hinv, g, hg, g₀, hu', rfl, rfl⟩
    refine ⟨hinv, hu', ?_⟩
    rwa [Germ.comp_id] at hg

end Word

end

end GroupConfig
