/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.Action

/-!
# Evaluation of germs

Blueprint `sources/group_configuration/04-germs.tex`, `lem:eval` (1), (2), (4), (5) and
`def:dom`.

A tuple `w` is a *generic point of the graph* of `g` over `F` if its locus over `F` is
the graph ideal (`Germ.IsGraphGeneric`).  For a small algebraically closed `F` containing
the canonical base and a generic point `y` of the source locus over `F`, there is a unique
`z` with `(y, z)` generic for the graph over `F` (`Germ.exists_isGraphGeneric`,
`Germ.IsGraphGeneric.eq_eval`); this `z` is the value `Germ.eval g F y`.  The value is
computed by any representative whose field is independent from `y` over `F`
(`Germ.exists_rep`, via `lem:fresh-conj`, and `Germ.eval_eq_rep`), is a generic point of
the target locus (`Germ.isGenericOver_eval`), does not depend on `F`
(`Germ.eval_eq_of_le`), is equivariant (`Germ.eval_map`) and determines the germ
(`Germ.eq_of_eval_eq`).

The clauses of `lem:eval` involving the definable closure, and the existence of a
representative over `F` (`lem:eval`(3)), need the definable-closure module and are not
proved here.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `lem:eval`(1), (4), (5) and the parts of (2) other than definability are complete.
The definability clause of (2) and clause (3) await integration of
`GroupConfig.Germ.Definable`.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] {ι κ : Type*}
  {a : ι → K} {a' : κ → K}

variable [IsAlgClosed k] [UniversalDomain k K] [Finite ι] [Finite κ]

namespace Germ

/-- A generic point of the graph of `g` over `F`: a tuple whose locus over `F` is the graph
ideal. -/
def IsGraphGeneric (g : Germ k a a') (F : IntermediateField k K) (w : (ι ⊕ κ) → K) : Prop :=
  locusIdeal (↥F) w = g.graphIdeal

/-- The graph point of a generic point is generic for the graph over the field of the
representative. -/
theorem isGraphGeneric_graphPoint (r : Representative k K a a') {y : ι → K}
    (hy : IsGenericOver r.M a y) :
    IsGraphGeneric (⟦r⟧ : Germ k a a') r.M (r.graphPoint y) :=
  (r.graphIdeal_eq hy).symm

/-- Generic points of the graph over a larger field are generic over a smaller field
containing the canonical base (`lem:genexists`, last clause). -/
theorem IsGraphGeneric.of_le {g : Germ k a a'} {F F' : IntermediateField k K} (hF : g.cb ≤ F)
    (hFF' : F ≤ F') {w : (ι ⊕ κ) → K} (h : g.IsGraphGeneric F' w) : g.IsGraphGeneric F w := by
  unfold IsGraphGeneric at h ⊢
  rw [← h]
  exact locusIdeal_eq_of_idealDefinedOver hFF' (h ▸ g.idealDefinedOver_graphIdeal hF)

/-- `lem:graph`(2) for germs: the graph ideal contracts to the locus of `a`. -/
theorem comap_rename_inl_graphIdeal (g : Germ k a a') :
    g.graphIdeal.comap
        (rename (Sum.inl : ι → ι ⊕ κ) : MvPolynomial ι K →ₐ[K] MvPolynomial (ι ⊕ κ) K) =
      locusIdeal k a := by
  induction g using Quotient.inductionOn with
  | h r => exact r.comap_rename_inl_graphIdeal

/-- `lem:graph`(2) for germs: the graph ideal contracts to the locus of `a'`. -/
theorem comap_rename_inr_graphIdeal (g : Germ k a a') :
    g.graphIdeal.comap
        (rename (Sum.inr : κ → ι ⊕ κ) : MvPolynomial κ K →ₐ[K] MvPolynomial (ι ⊕ κ) K) =
      locusIdeal k a' := by
  induction g using Quotient.inductionOn with
  | h r => exact r.comap_rename_inr_graphIdeal

/-- The first component of a generic point of the graph is a generic point of the source. -/
theorem IsGraphGeneric.isGenericOver_fst {g : Germ k a a'} {F : IntermediateField k K}
    {y : ι → K} {z : κ → K} (h : g.IsGraphGeneric F (Sum.elim y z)) : IsGenericOver F a y := by
  rw [isGenericOver_iff_locusIdeal_eq, ← g.comap_rename_inl_graphIdeal, ← h]
  unfold locusIdeal
  rw [comap_rename_map_eq _ Sum.inl_injective, Representative.comap_rename_inl_idealOf]

/-- The second component of a generic point of the graph is a generic point of the
target. -/
theorem IsGraphGeneric.isGenericOver_snd {g : Germ k a a'} {F : IntermediateField k K}
    {y : ι → K} {z : κ → K} (h : g.IsGraphGeneric F (Sum.elim y z)) : IsGenericOver F a' z := by
  rw [isGenericOver_iff_locusIdeal_eq, ← g.comap_rename_inr_graphIdeal, ← h]
  unfold locusIdeal
  rw [comap_rename_map_eq _ Sum.inr_injective, Representative.comap_rename_inr_idealOf]

/-! ### Representatives independent from a given set -/

/-- `lem:fresh-conj` for germs: a germ has a representative over a field containing `F` whose
field is independent over `F` from any given small set. -/
theorem exists_rep (g : Germ k a a') {F : IntermediateField k K} [IsAlgClosed (↥F)]
    (hF : IsSmall k (F : Set K)) (hcb : g.cb ≤ F) {W : Set K} (hW : IsSmall k W) :
    ∃ r : Representative k K a a',
      (⟦r⟧ : Germ k a a') = g ∧ F ≤ r.M ∧ IndepOver k (F : Set K) (r.M : Set K) W := by
  obtain ⟨r₀, rfl⟩ := Quotient.exists_rep g
  -- Enlarge the field to contain `F`.
  have hM₁ : IsAlgClosed ↥(racl k ((F : Set K) ∪ r₀.M)) := isAlgClosed_racl _
  have hM₁s : IsSmall k ((racl k ((F : Set K) ∪ r₀.M) : IntermediateField k K) : Set K) :=
    (hF.union r₀.isSmall).racl
  have hle : r₀.M ≤ racl k ((F : Set K) ∪ r₀.M) := subset_union_right.trans (subset_racl k _)
  have hFle : F ≤ racl k ((F : Set K) ∪ r₀.M) := subset_union_left.trans (subset_racl k _)
  have hr₁ : (⟦r₀.extend hM₁ hM₁s hle⟧ : Germ k a a') = ⟦r₀⟧ :=
    Quotient.sound (r₀.extend_equivalent hM₁ hM₁s hle)
  -- A finite set generating the enlarged field, and a conjugate of it independent from `W`.
  obtain ⟨S, -, hSfin, hS⟩ := hM₁s.exists_finite_racl_eq
  have hM₁eq : racl k S = racl k ((F : Set K) ∪ r₀.M) := by rw [hS, racl_racl]
  have _ : Finite ↥S := hSfin.to_subtype
  obtain ⟨τ, hτ⟩ := exists_algEquiv_indepOver (M := F) hF (fun s : S ↦ (s : K)) hW
  let τ' : K ≃ₐ[k] K := τ.restrictScalars k
  have hτF : ∀ x ∈ F, τ' x = x := fun x hx ↦ τ.commutes ⟨x, hx⟩
  refine ⟨(r₀.extend hM₁ hM₁s hle).map τ', ?_, ?_, ?_⟩
  · rw [← Germ.map_mk, hr₁]
    rw [← hr₁]
    exact (Germ.map_eq_self_iff τ' _).2 fun x hx ↦ hτF x (hcb (hr₁ ▸ hx))
  · intro x hx
    exact ⟨x, hFle hx, hτF x hx⟩
  · -- The image field is the closure of `F ∪ τ S`.
    have himage : (((r₀.extend hM₁ hM₁s hle).map τ').M : Set K) =
        racl k ((F : Set K) ∪ ⇑τ' '' S) := by
      rw [Representative.map_M, coe_map, AlgEquiv.coe_toAlgHom]
      change ⇑τ' '' ((racl k ((F : Set K) ∪ r₀.M) : IntermediateField k K) : Set K) = _
      rw [← hM₁eq, ← AlgEquiv.coe_toAlgHom, ← coe_map, racl_map, AlgEquiv.coe_toAlgHom]
      congr 1
      refine le_antisymm (racl_mono (k := k) subset_union_right)
        (racl_le_of_subset_racl (union_subset ?_ (subset_racl k _)))
      intro x hx
      have hxS : x ∈ racl k S := hM₁eq ▸ hFle hx
      have : τ' x ∈ (racl k S).map τ'.toAlgHom := ⟨x, hxS, rfl⟩
      rw [racl_map] at this
      rwa [hτF x hx] at this
    rw [himage]
    refine indepOver_racl_left_iff.2 ?_
    rw [image_eq_range]
    exact hτ

/-- For a representative whose field is independent from `(y, z)` over `F`, a generic point
`(y, z)` of the graph over `F` is the graph point of `y`. -/
theorem IsGraphGeneric.eq_graphPoint {r : Representative k K a a'} {F : IntermediateField k K}
    [IsAlgClosed (↥F)] (hF : IsSmall k (F : Set K)) (hFM : F ≤ r.M) {y : ι → K} {z : κ → K}
    (hind : IndepOver k (F : Set K) (range y ∪ range z) (r.M : Set K))
    (h : IsGraphGeneric (⟦r⟧ : Germ k a a') F (Sum.elim y z)) : z = r.f.eval y := by
  have _ := r.isAlgClosed
  rw [← Sum.elim_range] at hind
  -- `(y, z)` is a generic point of the graph over `M`.
  have hM : IsGraphGeneric (⟦r⟧ : Germ k a a') r.M (Sum.elim y z) := by
    unfold IsGraphGeneric
    rw [locusIdeal_eq_of_indepOver hF r.isSmall hFM hind]
    exact h
  have hyM : IsGenericOver r.M a y := hM.isGenericOver_fst
  -- It is conjugate over `M` to the graph point of `y`, by an automorphism fixing `y`.
  have hloc : locusIdeal (↥r.M) (Sum.elim y z) = locusIdeal (↥r.M) (r.graphPoint y) := by
    rw [hM, Germ.graphIdeal_mk, r.graphIdeal_eq hyM]
  obtain ⟨σ, hσ⟩ := (locusIdeal_eq_iff_exists_algEquiv _ _ _).1 hloc
  have hy : ⇑σ ∘ y = y := funext fun i ↦ hσ (Sum.inl i)
  have hz : ⇑σ ∘ r.f.eval y = z := funext fun j ↦ hσ (Sum.inr j)
  rw [← hz, ← r.f.eval_comp σ y, hy]

/-! ### Evaluation -/

/-- `lem:eval`(2): the value of a germ at `y`, the unique `z` with `(y, z)` generic for the
graph over `F`. -/
def eval (g : Germ k a a') (F : IntermediateField k K) (y : ι → K) : κ → K :=
  Classical.epsilon fun z ↦ g.IsGraphGeneric F (Sum.elim y z)

/-- `lem:eval`(2), existence. -/
theorem exists_isGraphGeneric (g : Germ k a a') {F : IntermediateField k K} [IsAlgClosed (↥F)]
    (hF : IsSmall k (F : Set K)) (hcb : g.cb ≤ F) {y : ι → K} (hy : IsGenericOver F a y) :
    ∃ z, g.IsGraphGeneric F (Sum.elim y z) := by
  obtain ⟨r, rfl, hFM, hind⟩ := g.exists_rep hF hcb (IsSmall.of_finite (finite_range y))
  have _ := r.isAlgClosed
  have hyM : IsGenericOver r.M a y :=
    (hy.isGenericOver_iff_indepOver hF r.isSmall hFM).2 hind.symm
  exact ⟨r.f.eval y, (isGraphGeneric_graphPoint r hyM).of_le hcb hFM⟩

theorem isGraphGeneric_eval (g : Germ k a a') {F : IntermediateField k K} [IsAlgClosed (↥F)]
    (hF : IsSmall k (F : Set K)) (hcb : g.cb ≤ F) {y : ι → K} (hy : IsGenericOver F a y) :
    g.IsGraphGeneric F (Sum.elim y (g.eval F y)) :=
  Classical.epsilon_spec (g.exists_isGraphGeneric hF hcb hy)

/-- `lem:eval`(1): uniqueness of the second coordinate of a generic point of the graph. -/
theorem IsGraphGeneric.eq_eval {g : Germ k a a'} {F : IntermediateField k K} [IsAlgClosed (↥F)]
    (hF : IsSmall k (F : Set K)) (hcb : g.cb ≤ F) {y : ι → K} {z : κ → K}
    (h : g.IsGraphGeneric F (Sum.elim y z)) : z = g.eval F y := by
  have hy : IsGenericOver F a y := h.isGenericOver_fst
  have h' := g.isGraphGeneric_eval hF hcb hy
  obtain ⟨r, hr, hFM, hind⟩ := g.exists_rep hF hcb
    (W := range y ∪ range z ∪ range (g.eval F y))
    (((IsSmall.of_finite (finite_range y)).union (IsSmall.of_finite (finite_range z))).union
      (IsSmall.of_finite (finite_range _)))
  subst hr
  rw [h.eq_graphPoint hF hFM (hind.symm.mono_left subset_union_left),
    h'.eq_graphPoint hF hFM (hind.symm.mono_left ?_)]
  exact union_subset (subset_union_left.trans subset_union_left) subset_union_right

/-- `lem:eval`(2): the value is computed by any representative over a field containing `F`
over which `y` is generic. -/
theorem eval_eq_rep (r : Representative k K a a') {F : IntermediateField k K}
    [IsAlgClosed (↥F)] (hF : IsSmall k (F : Set K)) (hcb : Germ.cb (⟦r⟧ : Germ k a a') ≤ F)
    (hFM : F ≤ r.M) {y : ι → K} (hy : IsGenericOver r.M a y) :
    Germ.eval (⟦r⟧ : Germ k a a') F y = r.f.eval y :=
  (((isGraphGeneric_graphPoint r hy).of_le hcb hFM).eq_eval hF hcb).symm

/-- `lem:eval`(2): the value is a generic point of the target. -/
theorem isGenericOver_eval (g : Germ k a a') {F : IntermediateField k K} [IsAlgClosed (↥F)]
    (hF : IsSmall k (F : Set K)) (hcb : g.cb ≤ F) {y : ι → K} (hy : IsGenericOver F a y) :
    IsGenericOver F a' (g.eval F y) :=
  (g.isGraphGeneric_eval hF hcb hy).isGenericOver_snd

/-- `lem:eval`(2): the value does not depend on the field. -/
theorem eval_eq_of_le (g : Germ k a a') {F F' : IntermediateField k K} [IsAlgClosed (↥F)]
    [IsAlgClosed (↥F')] (hF : IsSmall k (F : Set K)) (hF' : IsSmall k (F' : Set K))
    (hcb : g.cb ≤ F) (hFF' : F ≤ F') {y : ι → K} (hy : IsGenericOver F' a y) :
    g.eval F y = g.eval F' y :=
  (((g.isGraphGeneric_eval hF' (hcb.trans hFF') hy).of_le hcb hFF').eq_eval hF hcb).symm

/-- Graph-genericity is equivariant. -/
theorem IsGraphGeneric.map {g : Germ k a a'} {F : IntermediateField k K} {w : (ι ⊕ κ) → K}
    (σ : K ≃ₐ[k] K) (h : g.IsGraphGeneric F w) :
    (g.map σ).IsGraphGeneric (F.map σ.toAlgHom) (⇑σ ∘ w) := by
  unfold IsGraphGeneric at h ⊢
  rw [← locusIdeal_map, h, graphIdeal_map]

/-- `lem:eval`(4): evaluation is equivariant. -/
theorem eval_map (g : Germ k a a') (σ : K ≃ₐ[k] K) {F : IntermediateField k K}
    [IsAlgClosed (↥F)] (hF : IsSmall k (F : Set K)) (hcb : g.cb ≤ F) {y : ι → K}
    (hy : IsGenericOver F a y) :
    (g.map σ).eval (F.map σ.toAlgHom) (⇑σ ∘ y) = ⇑σ ∘ g.eval F y := by
  have _ : IsAlgClosed ↥(F.map σ.toAlgHom) :=
    IsAlgClosed.of_ringEquiv (↥F) _ (intermediateFieldMap σ F).toRingEquiv
  have hFs : IsSmall k ((F.map σ.toAlgHom : IntermediateField k K) : Set K) := by
    have := hF
    unfold IsSmall at this ⊢
    rwa [coe_map, AlgEquiv.coe_toAlgHom, ← image_empty ⇑σ, erk_image]
  have hcb' : (g.map σ).cb ≤ F.map σ.toAlgHom := by
    rw [cb_map]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hcb hx, rfl⟩
  have h := (g.isGraphGeneric_eval hF hcb hy).map σ
  have hsum : ⇑σ ∘ Sum.elim y (g.eval F y) = Sum.elim (⇑σ ∘ y) (⇑σ ∘ g.eval F y) := by
    funext i
    cases i <;> rfl
  rw [hsum] at h
  exact (h.eq_eval hFs hcb').symm

/-- `lem:eval`(5): a germ is determined by its value at one generic point over a field
containing both canonical bases. -/
theorem eq_of_eval_eq {g g' : Germ k a a'} {F : IntermediateField k K} [IsAlgClosed (↥F)]
    (hF : IsSmall k (F : Set K)) (hcb : g.cb ≤ F) (hcb' : g'.cb ≤ F) {y : ι → K}
    (hy : IsGenericOver F a y) (h : g.eval F y = g'.eval F y) : g = g' := by
  apply graphIdeal_injective
  have h1 := g.isGraphGeneric_eval hF hcb hy
  have h2 := g'.isGraphGeneric_eval hF hcb' hy
  unfold IsGraphGeneric at h1 h2
  rw [← h1, ← h2, h]

end Germ

end

end GroupConfig
