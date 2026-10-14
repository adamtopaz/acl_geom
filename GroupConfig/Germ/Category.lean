/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.Composition

/-!
# Identity germs, associativity and equivariance of composition

Blueprint `sources/group_configuration/04-germs.tex`, `lem:comp` (identities, associativity
and equivariance of composition).

The identity germ is represented by the identity expression over `acl(k) = racl k ∅`, the
relative algebraic closure of the base field in `K` (`Germ.id`). It evaluates to the identity
(`Germ.eval_id`) and is a two-sided identity for composition (`Germ.comp_id`,
`Germ.id_comp`).  Composition is associative
(`Germ.comp_assoc`) and equivariant under automorphisms over `k` (`Germ.comp_map`); all
three are proved by evaluating at a generic point over a field containing all the
canonical bases involved (`Germ.eq_of_eval_eq`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the identity, associativity and equivariance claims of `lem:comp` are complete.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {ι κ μ ν : Type*}

/-! ### The identity expression -/

/-- The identity quasi-rational expression. -/
def QuasiRational.id (L : Type*) [Field L] (ι : Type*) : QuasiRational L ι ι :=
  ⟨0, fun i ↦ X i, fun _ ↦ 1⟩

theorem pRoot_zero [PerfectField K] (x : K) : pRoot K 0 x = x :=
  pRoot_eq_of_pow_eq (by simp)

theorem QuasiRational.id_isDefinedAt {L : Type*} [Field L] [PerfectField K] [Algebra L K]
    (u : ι → K) : (QuasiRational.id L ι).IsDefinedAt u := fun _ ↦ by
  simp [QuasiRational.id]

theorem QuasiRational.id_eval {L : Type*} [Field L] [PerfectField K] [Algebra L K] (u : ι → K) :
    (QuasiRational.id L ι).eval u = u := by
  funext i
  simp [QuasiRational.eval, QuasiRational.id, pRoot_zero]

/-! ### Transport of fields along automorphisms -/

theorem isAlgClosed_map (σ : K ≃ₐ[k] K) (F : IntermediateField k K) [IsAlgClosed (↥F)] :
    IsAlgClosed ↥(F.map σ.toAlgHom) :=
  IsAlgClosed.of_ringEquiv (↥F) _ (intermediateFieldMap σ F).toRingEquiv

theorem isSmall_map (σ : K ≃ₐ[k] K) {F : IntermediateField k K} (hF : IsSmall k (F : Set K)) :
    IsSmall k ((F.map σ.toAlgHom : IntermediateField k K) : Set K) := by
  unfold IsSmall at hF ⊢
  rwa [coe_map, AlgEquiv.coe_toAlgHom, ← image_empty ⇑σ, erk_image]

/-! ### The identity representative, over the closure of the base field -/

variable [IsAlgClosed K]

/-- The identity representative, over the relative algebraic closure `racl k ∅` of the base
field. -/
def Representative.id (a : ι → K) : Representative k K a a where
  M := racl k ∅
  isAlgClosed := isAlgClosed_racl _
  isSmall := (IsSmall.of_finite finite_empty).racl
  f := QuasiRational.id ↥(racl k (∅ : Set K)) ι
  isDefinedAt y _ := QuasiRational.id_isDefinedAt y
  isGenericOver y hy := by
    rw [QuasiRational.id_eval]
    exact hy

variable [IsAlgClosed k] [UniversalDomain k K] [Finite ι] [Finite κ] [Finite μ] [Finite ν]
  {a : ι → K} {a' : κ → K} {a'' : μ → K} {a''' : ν → K}

namespace Germ

theorem cb_map_le (σ : K ≃ₐ[k] K) {g : Germ k a a'} {F : IntermediateField k K} (h : g.cb ≤ F) :
    (g.map σ).cb ≤ F.map σ.toAlgHom := by
  rw [cb_map]
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

/-! ### The identity germ -/

/-- `lem:comp`: the identity germ. -/
def id (a : ι → K) : Germ k a a := ⟦Representative.id a⟧

theorem cb_id_le (a : ι → K) (F : IntermediateField k K) [IsAlgClosed (↥F)] :
    (Germ.id a).cb ≤ F :=
  (cb_mk_le _).trans (racl_le_of_isAlgClosed (empty_subset _))

/-- The identity germ evaluates to the identity. -/
theorem eval_id {F : IntermediateField k K} [IsAlgClosed (↥F)] (hF : IsSmall k (F : Set K))
    {y : ι → K} (hy : IsGenericOver F a y) : (Germ.id a).eval F y = y := by
  obtain ⟨r, hr, hFM, hind⟩ :=
    (Germ.id a).exists_rep hF (cb_id_le a F) (IsSmall.of_finite (finite_range y))
  have _ := r.isAlgClosed
  have hyM : IsGenericOver r.M a y :=
    (hy.isGenericOver_iff_indepOver hF r.isSmall hFM).2 hind.symm
  have heq : r.Equivalent (Representative.id a) := Quotient.exact hr
  have hM : racl k ((r.M : Set K) ∪ ((racl k (∅ : Set K) : IntermediateField k K) : Set K)) =
      r.M :=
    le_antisymm (racl_le_of_isAlgClosed
      (union_subset le_rfl (racl_le_of_isAlgClosed (empty_subset _))))
      (subset_union_left.trans (subset_racl k _))
  rw [← hr, eval_eq_rep r hF (by rw [hr]; exact cb_id_le a F) hFM hyM,
    heq y (by
      change IsGenericOver (racl k ((r.M : Set K) ∪ ((racl k (∅ : Set K) :
        IntermediateField k K) : Set K))) a y
      rw [hM]
      exact hyM)]
  exact QuasiRational.id_eval y

/-- `lem:comp`: the identity germ is a right identity. -/
theorem comp_id (g : Germ k a a') : Germ.comp g (Germ.id a) = g := by
  have hF : IsSmall k ((racl k (g.cb : Set K) : IntermediateField k K) : Set K) :=
    g.isSmall_cb.racl
  have _ : IsAlgClosed ↥(racl k (g.cb : Set K)) := isAlgClosed_racl _
  have hcb : g.cb ≤ racl k (g.cb : Set K) := subset_racl k _
  obtain ⟨y, hy⟩ := exists_isGenericOver hF a
  refine eq_of_eval_eq hF (cb_comp_le _ _ hF (cb_id_le a _) hcb) hcb hy ?_
  rw [comp_eval _ _ hF (cb_id_le a _) hcb hy, eval_id hF hy]

/-- `lem:comp`: the identity germ is a left identity. -/
theorem id_comp (g : Germ k a a') : Germ.comp (Germ.id a') g = g := by
  have hF : IsSmall k ((racl k (g.cb : Set K) : IntermediateField k K) : Set K) :=
    g.isSmall_cb.racl
  have _ : IsAlgClosed ↥(racl k (g.cb : Set K)) := isAlgClosed_racl _
  have hcb : g.cb ≤ racl k (g.cb : Set K) := subset_racl k _
  obtain ⟨y, hy⟩ := exists_isGenericOver hF a
  refine eq_of_eval_eq hF (cb_comp_le _ _ hF hcb (cb_id_le a' _)) hcb hy ?_
  rw [comp_eval _ _ hF hcb (cb_id_le a' _) hy, eval_id hF (g.isGenericOver_eval hF hcb hy)]

/-! ### Associativity -/

/-- `lem:comp`: composition is associative. -/
theorem comp_assoc (g'' : Germ k a'' a''') (g' : Germ k a' a'') (g : Germ k a a') :
    Germ.comp (Germ.comp g'' g') g = Germ.comp g'' (Germ.comp g' g) := by
  have hF : IsSmall k ((racl k ((g.cb : Set K) ∪ g'.cb ∪ g''.cb) : IntermediateField k K) :
      Set K) :=
    ((g.isSmall_cb.union g'.isSmall_cb).union g''.isSmall_cb).racl
  have _ : IsAlgClosed ↥(racl k ((g.cb : Set K) ∪ g'.cb ∪ g''.cb)) := isAlgClosed_racl _
  have hcb : g.cb ≤ racl k ((g.cb : Set K) ∪ g'.cb ∪ g''.cb) :=
    (subset_union_left.trans subset_union_left).trans (subset_racl k _)
  have hcb' : g'.cb ≤ racl k ((g.cb : Set K) ∪ g'.cb ∪ g''.cb) :=
    (subset_union_right.trans subset_union_left).trans (subset_racl k _)
  have hcb'' : g''.cb ≤ racl k ((g.cb : Set K) ∪ g'.cb ∪ g''.cb) :=
    subset_union_right.trans (subset_racl k _)
  obtain ⟨y, hy⟩ := exists_isGenericOver hF a
  refine eq_of_eval_eq hF (cb_comp_le _ _ hF hcb (cb_comp_le _ _ hF hcb' hcb''))
    (cb_comp_le _ _ hF (cb_comp_le _ _ hF hcb hcb') hcb'') hy ?_
  rw [comp_eval _ _ hF hcb (cb_comp_le _ _ hF hcb' hcb'') hy,
    comp_eval _ _ hF hcb' hcb'' (g.isGenericOver_eval hF hcb hy),
    comp_eval _ _ hF (cb_comp_le _ _ hF hcb hcb') hcb'' hy, comp_eval _ _ hF hcb hcb' hy]

/-! ### Equivariance -/

/-- `lem:comp`: composition is equivariant under automorphisms over `k`. -/
theorem comp_map (σ : K ≃ₐ[k] K) (g' : Germ k a' a'') (g : Germ k a a') :
    (Germ.comp g' g).map σ = Germ.comp (g'.map σ) (g.map σ) := by
  have hF : IsSmall k ((racl k ((g.cb : Set K) ∪ g'.cb) : IntermediateField k K) : Set K) :=
    (g.isSmall_cb.union g'.isSmall_cb).racl
  have _ : IsAlgClosed ↥(racl k ((g.cb : Set K) ∪ g'.cb)) := isAlgClosed_racl _
  have hcb : g.cb ≤ racl k ((g.cb : Set K) ∪ g'.cb) := subset_union_left.trans (subset_racl k _)
  have hcb' : g'.cb ≤ racl k ((g.cb : Set K) ∪ g'.cb) :=
    subset_union_right.trans (subset_racl k _)
  have hcomp := cb_comp_le g' g hF hcb hcb'
  have _ := isAlgClosed_map σ (racl k ((g.cb : Set K) ∪ g'.cb))
  have hF' := isSmall_map σ hF
  obtain ⟨y, hy⟩ := exists_isGenericOver hF a
  have hy' : IsGenericOver ((racl k ((g.cb : Set K) ∪ g'.cb)).map σ.toAlgHom) a (⇑σ ∘ y) :=
    (isGenericOver_map_iff σ _ a y).2 hy
  refine eq_of_eval_eq hF' (cb_map_le σ hcomp)
    (cb_comp_le _ _ hF' (cb_map_le σ hcb) (cb_map_le σ hcb')) hy' ?_
  rw [eval_map _ σ hF hcomp hy, comp_eval _ _ hF hcb hcb' hy,
    comp_eval _ _ hF' (cb_map_le σ hcb) (cb_map_le σ hcb') hy', eval_map g σ hF hcb hy,
    eval_map g' σ hF hcb' (g.isGenericOver_eval hF hcb hy)]

end Germ

end

end GroupConfig
