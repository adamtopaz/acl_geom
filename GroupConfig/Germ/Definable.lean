/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.DefinableClosure
import GroupConfig.Germ.Difference

/-!
# Germs and definable closure

Blueprint `sources/group_configuration/04-germs.tex`, `lem:eval`(2) (definability of
values) and (3), `lem:inverse`(2) and `lem:eval-dcl`.

A quasi-rational expression over a small algebraically closed field which is defined at one
generic point and maps it to a generic point is a representative
(`GroupConfig.Representative.ofQuasiRational`).  The value of a germ at a generic point is
definable over the canonical base and the point (`Germ.evalGen_mem_dclAdjoin`,
`Germ.eval_mem_dclAdjoin`), a germ has a representative over every small algebraically
closed field containing its canonical base (`Germ.exists_rep_M_eq`), and a germ is
invertible iff a generic point is definable over the base field and its value
(`Germ.isInvertible_iff_mem_dclAdjoin`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `lem:eval`(2),(3), `lem:inverse`(2) and `lem:eval-dcl` complete. `lem:eval-dcl` is
stated with the canonical base, or any finite tuple generating it, in place of the code tuple.
Its clause for composite words is stated for germs invariant under the automorphisms fixing such
a tuple. That class contains the germs themselves (`Germ.map_eq_of_cb_le`) and is closed under
composition and inverses (`Germ.comp_map_eq_of_map_eq`, `Germ.IsInverse.map_eq_of_map_eq`).
The module also proves `lem:comp-codes`(2) at individually generic points
(`Germ.evalGen_comp_of_indepOver`).
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K] {ι κ : Type*} [Finite ι] [Finite κ] {a : ι → K} {a' : κ → K}

/-- A representative from a quasi-rational expression over a small algebraically closed
field which is defined at one generic point and maps it to a generic point. -/
def Representative.ofQuasiRational {M : IntermediateField k K} (hM : IsAlgClosed ↥M)
    (hMs : IsSmall k (M : Set K)) (f : QuasiRational (↥M) ι κ) {y : ι → K}
    (hy : IsGenericOver M a y) (hf : f.IsDefinedAt y) (hfy : IsGenericOver M a' (f.eval y)) :
    Representative k K a a' where
  M := M
  isAlgClosed := hM
  isSmall := hMs
  f := f
  isDefinedAt y' hy' := by
    obtain ⟨σ, hσ⟩ := hy.exists_algEquiv hy'
    have : y' = ⇑σ ∘ y := funext fun i ↦ (hσ i).symm
    rw [this, f.isDefinedAt_comp_iff]
    exact hf
  isGenericOver y' hy' := by
    obtain ⟨σ, hσ⟩ := hy.exists_algEquiv hy'
    have : y' = ⇑σ ∘ y := funext fun i ↦ (hσ i).symm
    rw [this, f.eval_comp]
    exact hfy.comp σ

namespace Germ

/-- The canonical base of a germ fixed by all automorphisms over `L` lies in `dcl L`. -/
theorem cb_le_dcl_of_forall_map_eq (g : Germ k a a') {L : IntermediateField k K}
    (h : ∀ σ : K ≃ₐ[↥L] K, g.map (σ.restrictScalars k) = g) : g.cb ≤ dcl L :=
  fun x hx ↦ mem_dcl_iff_forall_fixed.2 fun σ ↦ (map_eq_self_iff _ _).1 (h σ) x hx

/-- `lem:eval-dcl` (Galois form): the value of a germ at a generic point independent from its
canonical base is definable over any field whose definable closure contains the canonical
base, together with the point. -/
theorem evalGen_mem_dclAdjoin_of_cb_le_dcl (g : Germ k a a') {L : IntermediateField k K}
    (hL : g.cb ≤ dcl L) {y : ι → K} (hy : IsGen k a y)
    (h : IndepOver k ∅ (range y) (g.cb : Set K)) (j : κ) :
    g.evalGen y j ∈ dclAdjoin L y := by
  unfold dclAdjoin
  refine mem_dcl_iff_forall_fixed.2 fun σ ↦ ?_
  have hfixL : ∀ x ∈ L, (σ.restrictScalars k) x = x := fun x hx ↦ by
    change σ x = x
    exact σ.commutes
      ⟨x, (mem_restrictScalars k).2 (IntermediateField.algebraMap_mem _ (⟨x, hx⟩ : ↥L))⟩
  have hfixy : ⇑(σ.restrictScalars k) ∘ y = y := funext fun i ↦ by
    change σ (y i) = y i
    exact σ.commutes
      ⟨y i, (mem_restrictScalars k).2 (subset_adjoin (↥L) _ (mem_range_self i))⟩
  have hg : g.map (σ.restrictScalars k) = g :=
    (map_eq_self_iff _ _).2 fun x hx ↦ apply_eq_self_of_mem_dcl_of_fixes _ hfixL (hL hx)
  have e := evalGen_map (σ.restrictScalars k) g hy h
  rw [hg, hfixy] at e
  exact (congrFun e j).symm

/-- `lem:eval-dcl`: `g(y) ∈ dcl(Cb g, y)`. -/
theorem evalGen_mem_dclAdjoin (g : Germ k a a') {y : ι → K} (hy : IsGen k a y)
    (h : IndepOver k ∅ (range y) (g.cb : Set K)) (j : κ) :
    g.evalGen y j ∈ dclAdjoin g.cb y :=
  g.evalGen_mem_dclAdjoin_of_cb_le_dcl (le_dcl _) hy h j

/-! ### Composite words -/

/-- A germ whose canonical base lies in `L` is fixed by every automorphism over `L`. -/
theorem map_eq_of_cb_le (g : Germ k a a') {L : IntermediateField k K} (hL : g.cb ≤ L)
    (σ : K ≃ₐ[↥L] K) : g.map (σ.restrictScalars k) = g :=
  (map_eq_self_iff _ _).2 fun x hx ↦ by
    change σ x = x
    exact σ.commutes ⟨x, hL hx⟩

/-- A composite of germs fixed by an automorphism is fixed by it. -/
theorem comp_map_eq_of_map_eq {μ : Type*} [Finite μ] {a'' : μ → K} {g' : Germ k a' a''}
    {g : Germ k a a'} {σ : K ≃ₐ[k] K} (hg' : g'.map σ = g') (hg : g.map σ = g) :
    (Germ.comp g' g).map σ = Germ.comp g' g := by
  rw [Germ.comp_map, hg', hg]

/-- The inverse of a germ fixed by an automorphism is fixed by it. -/
theorem IsInverse.map_eq_of_map_eq {h : Germ k a' a} {g : Germ k a a'} (hi : IsInverse h g)
    {σ : K ≃ₐ[k] K} (hg : g.map σ = g) : h.map σ = h := by
  have h' := hi.map σ
  rw [hg] at h'
  exact h'.unique hi

/-- `lem:eval-dcl`, composite words. Let `w` be a germ fixed by every automorphism over the
field generated by a finite tuple `c`. This holds, for instance, for every composite of germs
whose canonical bases lie in `k(c)` and of their inverses (`map_eq_of_cb_le`,
`comp_map_eq_of_map_eq`, `IsInverse.map_eq_of_map_eq`). Then every generic point `y`
independent from `c` is in the domain of `w`, and `w(y) ∈ dcl(c, y)`. -/
theorem evalGen_mem_dclAdjoin_of_forall_map_eq {μ : Type*} {c : μ → K} (w : Germ k a a')
    (hw : ∀ σ : K ≃ₐ[↥(adjoin k (range c))] K, w.map (σ.restrictScalars k) = w) {y : ι → K}
    (hy : IsGen k a y) (hind : IndepOver k ∅ (range y) (range c)) :
    IndepOver k ∅ (range y) (w.cb : Set K) ∧
      ∀ j, w.evalGen y j ∈ dclAdjoin (adjoin k (range c)) y := by
  have hcb := w.cb_le_dcl_of_forall_map_eq hw
  have hcbr : (w.cb : Set K) ⊆ racl k (∅ ∪ range c) := fun x hx ↦ by
    rw [empty_union]
    exact racl_le_of_subset_racl (adjoin_le_racl k _) (dcl_le_racl _ (hcb hx))
  have hyw : IndepOver k ∅ (range y) (w.cb : Set K) :=
    (indepOver_racl_right_iff.2 hind).mono_right hcbr
  exact ⟨hyw, fun j ↦ w.evalGen_mem_dclAdjoin_of_cb_le_dcl hcb hy hyw j⟩

/-- `lem:eval`(2): `g(y) ∈ dcl(F, y)` for `F ⊇ Cb g` and `y` generic over `F`. -/
theorem eval_mem_dclAdjoin (g : Germ k a a') {F : IntermediateField k K} [IsAlgClosed ↥F]
    (hF : IsSmall k (F : Set K)) (hcb : g.cb ≤ F) {y : ι → K} (hy : IsGenericOver F a y)
    (j : κ) : g.eval F y j ∈ dclAdjoin F y := by
  rw [← evalGen_eq g hF hcb hy]
  exact dclAdjoin_mono hcb y (g.evalGen_mem_dclAdjoin hy.isGen (hy.indepOver.mono_right hcb) j)

/-- `lem:eval`(3): a germ has a representative over every small algebraically closed field
containing its canonical base. -/
theorem exists_rep_M_eq (g : Germ k a a') {F : IntermediateField k K} [IsAlgClosed ↥F]
    (hF : IsSmall k (F : Set K)) (hcb : g.cb ≤ F) :
    ∃ r : Representative k K a a', (⟦r⟧ : Germ k a a') = g ∧ r.M = F := by
  obtain ⟨y, hy⟩ := exists_isGenericOver hF a
  obtain ⟨f, hf, hfy⟩ := exists_quasiRational_of_mem_dclAdjoin (g.eval_mem_dclAdjoin hF hcb hy)
  have hgen : IsGenericOver F a' (f.eval y) := by
    rw [hfy]
    exact g.isGenericOver_eval hF hcb hy
  obtain ⟨r, hr⟩ : ∃ r : Representative k K a a',
      r = Representative.ofQuasiRational ‹IsAlgClosed ↥F› hF f hy hf hgen := ⟨_, rfl⟩
  have hrM : r.M = F := by
    subst hr
    rfl
  have hrf : r.f.eval y = f.eval y := by
    subst hr
    rfl
  have hyM : IsGenericOver r.M a y := by
    rw [hrM]
    exact hy
  have hcbr : Germ.cb (⟦r⟧ : Germ k a a') ≤ F := hrM ▸ cb_mk_le r
  refine ⟨r, ?_, hrM⟩
  exact eq_of_eval_eq hF hcbr hcb hy ((eval_eq_rep r hF hcbr hrM.ge hyM).trans (hrf.trans hfy))

/-- `lem:inverse`(2): a germ is invertible iff a generic point over a small algebraically
closed field containing the canonical base is definable over that field and its value. -/
theorem isInvertible_iff_mem_dclAdjoin (g : Germ k a a') {F : IntermediateField k K}
    [IsAlgClosed ↥F] (hF : IsSmall k (F : Set K)) (hcb : g.cb ≤ F) {y : ι → K}
    (hy : IsGenericOver F a y) :
    IsInvertible g ↔ ∀ i, y i ∈ dclAdjoin F (g.eval F y) := by
  have hz : IsGenericOver F a' (g.eval F y) := g.isGenericOver_eval hF hcb hy
  constructor
  · rintro ⟨h, hi⟩ i
    have hcbh : h.cb ≤ F := hi.cb_le.trans (racl_le_of_isAlgClosed hcb)
    have : h.eval F (g.eval F y) = y :=
      (comp_eval h g hF hcb hcbh hy).symm.trans (by
        rw [hi.1]
        exact eval_id hF hy)
    exact (congrArg (fun z ↦ z ∈ dclAdjoin F (g.eval F y)) (congrFun this i)).mp
      (h.eval_mem_dclAdjoin hF hcbh hz i)
  · intro hdef
    obtain ⟨f', hf', hf'z⟩ := exists_quasiRational_of_mem_dclAdjoin hdef
    have hgen : IsGenericOver F a (f'.eval (g.eval F y)) := by
      rw [hf'z]
      exact hy
    obtain ⟨r', hr'⟩ : ∃ r' : Representative k K a' a,
        r' = Representative.ofQuasiRational ‹IsAlgClosed ↥F› hF f' hz hf' hgen := ⟨_, rfl⟩
    have hrM : r'.M = F := by
      subst hr'
      rfl
    have hrf : r'.f.eval (g.eval F y) = f'.eval (g.eval F y) := by
      subst hr'
      rfl
    have hzM : IsGenericOver r'.M a' (g.eval F y) := by
      rw [hrM]
      exact hz
    have hcbh : Germ.cb (⟦r'⟧ : Germ k a' a) ≤ F := hrM ▸ cb_mk_le r'
    have hr'' : Germ.eval (⟦r'⟧ : Germ k a' a) F (g.eval F y) = y :=
      (eval_eq_rep r' hF hcbh hrM.ge hzM).trans (hrf.trans hf'z)
    refine ⟨⟦r'⟧, ?_⟩
    constructor
    · exact eq_of_eval_eq hF (cb_comp_le _ _ hF hcb hcbh) (cb_id_le a F) hy
        ((comp_eval _ _ hF hcb hcbh hy).trans (hr''.trans (eval_id hF hy).symm))
    · exact eq_of_eval_eq hF (cb_comp_le _ _ hF hcbh hcb) (cb_id_le a' F) hz
        ((comp_eval _ _ hF hcbh hcb hz).trans
          ((congrArg (g.eval F) hr'').trans (eval_id hF hz).symm))

/-! ### Composition at individually generic points -/

/-- The generic value of the germ of a representative is the value of its expression. -/
theorem evalGen_mk_eq (r : Representative k K a a') {u : ι → K} (hu : IsGenericOver r.M a u) :
    Germ.evalGen (⟦r⟧ : Germ k a a') u = r.f.eval u := by
  have _ := r.isAlgClosed
  exact (evalGen_eq _ r.isSmall (cb_mk_le r) hu).trans
    (eval_eq_rep r r.isSmall (cb_mk_le r) le_rfl hu)

/-- `lem:comp-codes`(2): `(h g)(y) = h(g(y))` for a generic point `y` in the domains of `g` and
of `h g` with `g(y)` in the domain of `h`. The point need not be generic over both canonical
bases at once: the expressions of `h g` and of `h ∘ g` agree at a point generic over
`acl(Cb g, Cb h)`, hence at every point of the locus where both are defined
(`lem:qr-agree`). -/
theorem evalGen_comp_of_indepOver {μ : Type*} [Finite μ] {a'' : μ → K} (h : Germ k a' a'')
    (g : Germ k a a') {y : ι → K} (hy : IsGen k a y)
    (hyg : IndepOver k ∅ (range y) (g.cb : Set K))
    (hyhg : IndepOver k ∅ (range y) ((Germ.comp h g).cb : Set K))
    (hz : IndepOver k ∅ (range (g.evalGen y)) (h.cb : Set K)) :
    (Germ.comp h g).evalGen y = h.evalGen (g.evalGen y) := by
  classical
  have _ := Fintype.ofFinite κ
  have _ : IsAlgClosed ↥(racl k ((Germ.comp h g).cb : Set K)) := isAlgClosed_racl _
  have _ : IsAlgClosed ↥(racl k (g.cb : Set K)) := isAlgClosed_racl _
  have _ : IsAlgClosed ↥(racl k (h.cb : Set K)) := isAlgClosed_racl _
  /- Representatives over the closures of the three canonical bases. -/
  obtain ⟨r₁, hr₁, hr₁M⟩ := (Germ.comp h g).exists_rep_M_eq (Germ.comp h g).isSmall_cb.racl
    fun x hx ↦ subset_racl k _ hx
  obtain ⟨r₂, hr₂, hr₂M⟩ := g.exists_rep_M_eq g.isSmall_cb.racl fun x hx ↦ subset_racl k _ hx
  obtain ⟨r₃, hr₃, hr₃M⟩ := h.exists_rep_M_eq h.isSmall_cb.racl fun x hx ↦ subset_racl k _ hx
  /- A common field `N = acl(Cb g, Cb h)` and the composite expression over it. -/
  obtain ⟨N, hN⟩ : ∃ N : IntermediateField k K, N = racl k ((g.cb : Set K) ∪ h.cb) := ⟨_, rfl⟩
  have _ : IsAlgClosed ↥N := hN ▸ isAlgClosed_racl _
  have hNs : IsSmall k (N : Set K) := hN ▸ (g.isSmall_cb.union h.isSmall_cb).racl
  have h₁N : r₁.M ≤ N := by
    rw [hr₁M, hN]
    exact racl_le_of_subset_racl (cb_comp_le_racl h g)
  have h₂N : r₂.M ≤ N := by
    rw [hr₂M, hN]
    exact racl_mono subset_union_left
  have h₃N : r₃.M ≤ N := by
    rw [hr₃M, hN]
    exact racl_mono subset_union_right
  have _ : ExpChar (↥N) (ringExpChar K) := expChar_of_algebra (↥N) K
  obtain ⟨f₂, hf₂⟩ : ∃ f, f = r₂.f.map (IntermediateField.inclusion h₂N).toRingHom := ⟨_, rfl⟩
  obtain ⟨f₃, hf₃⟩ : ∃ f, f = r₃.f.map (IntermediateField.inclusion h₃N).toRingHom := ⟨_, rfl⟩
  have hf₂def : ∀ u, f₂.IsDefinedAt u ↔ r₂.f.IsDefinedAt u := fun u ↦ by
    rw [hf₂]
    exact QuasiRational.isDefinedAt_map_iff h₂N r₂.f u
  have hf₃def : ∀ u, f₃.IsDefinedAt u ↔ r₃.f.IsDefinedAt u := fun u ↦ by
    rw [hf₃]
    exact QuasiRational.isDefinedAt_map_iff h₃N r₃.f u
  have hf₂eval : ∀ u, f₂.eval u = r₂.f.eval u := fun u ↦ by
    rw [hf₂]
    exact QuasiRational.eval_map h₂N r₂.f u
  have hf₃eval : ∀ u, f₃.eval u = r₃.f.eval u := fun u ↦ by
    rw [hf₃]
    exact QuasiRational.eval_map h₃N r₃.f u
  /- The composite expression is defined at, and computes, `h(g(u))` wherever `u` is in the
  domain of `g` and `g(u)` in the domain of `h`. -/
  have hcomp : ∀ u, IsGenericOver r₂.M a u → IsGenericOver r₃.M a' (r₂.f.eval u) →
      (f₃.comp (ringExpChar K) f₂).IsDefinedAt u ∧
        (f₃.comp (ringExpChar K) f₂).eval u = h.evalGen (g.evalGen u) := fun u hu hgu ↦ by
    have hdef₂ : f₂.IsDefinedAt u := (hf₂def u).2 (r₂.isDefinedAt u hu)
    have hdef₃ : f₃.IsDefinedAt (f₂.eval u) := by
      rw [hf₂eval, hf₃def]
      exact r₃.isDefinedAt _ hgu
    refine ⟨QuasiRational.isDefinedAt_comp f₃ f₂ hdef₂ hdef₃, ?_⟩
    rw [QuasiRational.comp_eval f₃ f₂ hdef₂, hf₂eval, hf₃eval, ← evalGen_mk_eq r₃ hgu,
      ← evalGen_mk_eq r₂ hu, hr₂, hr₃]
  /- Agreement at a generic point over `N`. -/
  obtain ⟨y₀, hy₀⟩ := exists_isGenericOver hNs a
  have hy₀₂ : IsGenericOver r₂.M a y₀ := hy₀.of_le h₂N
  have hgy₀ : IsGenericOver r₃.M a' (r₂.f.eval y₀) := by
    have hg₀ : g.cb ≤ N := by
      rw [hN]
      exact fun x hx ↦ subset_racl k _ (Or.inl hx)
    have e : r₂.f.eval y₀ = g.eval N y₀ := by
      rw [← evalGen_mk_eq r₂ hy₀₂, hr₂, evalGen_eq g hNs hg₀ hy₀]
    rw [e]
    exact (g.isGenericOver_eval hNs hg₀ hy₀).of_le h₃N
  have hind₀ : IndepOver k ∅ (range y₀) ((h.cb : Set K) ∪ g.cb) := by
    refine hy₀.indepOver.mono_right ?_
    rw [hN]
    exact union_subset (fun x hx ↦ subset_racl k _ (Or.inr hx))
      (fun x hx ↦ subset_racl k _ (Or.inl hx))
  obtain ⟨hF₀, hFe₀⟩ := hcomp y₀ hy₀₂ hgy₀
  have heq₀ : r₁.f.eval y₀ = (f₃.comp (ringExpChar K) f₂).eval y₀ := by
    rw [hFe₀, ← evalGen_mk_eq r₁ (hy₀.of_le h₁N), hr₁]
    exact evalGen_comp h g hy₀.isGen hind₀
  /- Transfer to `y`. -/
  have hy₁ : IsGenericOver r₁.M a y := by
    rw [hr₁M]
    exact hy.isGenericOver_racl (Germ.comp h g).isSmall_cb hyhg
  have hy₂ : IsGenericOver r₂.M a y := by
    rw [hr₂M]
    exact hy.isGenericOver_racl g.isSmall_cb hyg
  have hgy : IsGenericOver r₃.M a' (r₂.f.eval y) := by
    rw [← evalGen_mk_eq r₂ hy₂, hr₂, hr₃M]
    exact (g.isGen_evalGen hy hyg).isGenericOver_racl h.isSmall_cb hz
  obtain ⟨hF, hFe⟩ := hcomp y hy₂ hgy
  have := QuasiRational.eval_eq_of_eval_eq h₁N le_rfl hy₀ hy₂.inLocus
    (r₁.isDefinedAt y₀ (hy₀.of_le h₁N)) hF₀ (r₁.isDefinedAt y hy₁) hF heq₀
  rw [← hr₁, evalGen_mk_eq r₁ hy₁, this, hFe]

end Germ

end

end GroupConfig
