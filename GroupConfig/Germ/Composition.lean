/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.Eval

/-!
# Composition of germs

Blueprint `sources/group_configuration/04-germs.tex`, `lem:comp` (existence and value of
the composite, bound on its canonical base) and the weak form `g(y) ∈ acl(F, y)` of
`lem:eval`(2).

Two representatives are composed after enlarging both to the algebraic closure of the
join of their fields (`Representative.comp`); the composite respects equivalence
(`Representative.comp_equivalent`), so germs compose (`Germ.comp`).  The value of the
composite at a generic point is the composite of the values (`Germ.comp_eval`), and its
canonical base lies in every algebraically closed small field containing both canonical
bases (`Germ.cb_comp_le`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** for `lem:comp`, the existence of the composite, its value at generic points and the
bound on its canonical base are complete. Uniqueness is `lem:eval`(5) (`Germ.eq_of_eval_eq`).
Identities, associativity and equivariance are in `GroupConfig.Germ.Category`.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] {ι κ μ : Type*}
  {a : ι → K} {a' : κ → K} {a'' : μ → K}

namespace Representative

theorem extend_f [UniversalDomain k K] [Finite ι] [Finite κ] (r : Representative k K a a')
    {M₁ : IntermediateField k K} (hM₁ : IsAlgClosed (↥M₁)) (hsmall : IsSmall k (M₁ : Set K))
    (h : r.M ≤ M₁) :
    (r.extend hM₁ hsmall h).f = r.f.map (IntermediateField.inclusion h).toRingHom := rfl

theorem extend_eval [UniversalDomain k K] [Finite ι] [Finite κ] (r : Representative k K a a')
    {M₁ : IntermediateField k K} (hM₁ : IsAlgClosed (↥M₁)) (hsmall : IsSmall k (M₁ : Set K))
    (h : r.M ≤ M₁) (u : ι → K) : (r.extend hM₁ hsmall h).f.eval u = r.f.eval u :=
  QuasiRational.eval_map h r.f u

/-- The closure of the join of the fields of two representatives. -/
abbrev joinField (r' : Representative k K a' a'') (r : Representative k K a a') :
    IntermediateField k K :=
  racl k ((r.M : Set K) ∪ r'.M)

theorem isSmall_joinField (r' : Representative k K a' a'') (r : Representative k K a a') :
    IsSmall k (joinField r' r : Set K) :=
  (r.isSmall.union r'.isSmall).racl

theorem le_joinField_left (r' : Representative k K a' a'') (r : Representative k K a a') :
    r.M ≤ joinField r' r :=
  subset_union_left.trans (subset_racl k _)

theorem le_joinField_right (r' : Representative k K a' a'') (r : Representative k K a a') :
    r'.M ≤ joinField r' r :=
  subset_union_right.trans (subset_racl k _)

variable [Finite κ]

/-- The composite of two expressions over a common field `N`, as a representative. -/
def compOver {N : IntermediateField k K} (hN : IsAlgClosed (↥N)) (hNs : IsSmall k (N : Set K))
    (f : QuasiRational (↥N) ι κ) (f' : QuasiRational (↥N) κ μ)
    (hf : ∀ y, IsGenericOver N a y → f.IsDefinedAt y)
    (hfg : ∀ y, IsGenericOver N a y → IsGenericOver N a' (f.eval y))
    (hf' : ∀ z, IsGenericOver N a' z → f'.IsDefinedAt z)
    (hf'g : ∀ z, IsGenericOver N a' z → IsGenericOver N a'' (f'.eval z)) :
    Representative k K a a'' where
  M := N
  isAlgClosed := hN
  isSmall := hNs
  f := haveI := Fintype.ofFinite κ; haveI := expChar_of_algebra (↥N) K; f'.comp (ringExpChar K) f
  isDefinedAt y hy := by
    let _ := Fintype.ofFinite κ
    have := expChar_of_algebra (↥N) K
    exact QuasiRational.isDefinedAt_comp f' f (hf y hy) (hf' _ (hfg y hy))
  isGenericOver y hy := by
    let _ := Fintype.ofFinite κ
    have := expChar_of_algebra (↥N) K
    change IsGenericOver N a'' ((f'.comp (ringExpChar K) f).eval y)
    rw [QuasiRational.comp_eval f' f (hf y hy)]
    exact hf'g _ (hfg y hy)

theorem compOver_eval {N : IntermediateField k K} (hN : IsAlgClosed (↥N))
    (hNs : IsSmall k (N : Set K)) (f : QuasiRational (↥N) ι κ) (f' : QuasiRational (↥N) κ μ)
    (hf : ∀ y, IsGenericOver N a y → f.IsDefinedAt y)
    (hfg : ∀ y, IsGenericOver N a y → IsGenericOver N a' (f.eval y))
    (hf' : ∀ z, IsGenericOver N a' z → f'.IsDefinedAt z)
    (hf'g : ∀ z, IsGenericOver N a' z → IsGenericOver N a'' (f'.eval z)) {y : ι → K}
    (hy : IsGenericOver N a y) :
    (compOver hN hNs f f' hf hfg hf' hf'g).f.eval y = f'.eval (f.eval y) := by
  let _ := Fintype.ofFinite κ
  have := expChar_of_algebra (↥N) K
  exact QuasiRational.comp_eval f' f (hf y hy)

variable [UniversalDomain k K] [Finite ι] [Finite μ]

/-- `lem:comp`: the composite of two representatives, over the closure of the join of their
fields. -/
def comp (r' : Representative k K a' a'') (r : Representative k K a a') :
    Representative k K a a'' :=
  compOver (isAlgClosed_racl _) (isSmall_joinField r' r)
    (r.extend (isAlgClosed_racl _) (isSmall_joinField r' r) (le_joinField_left r' r)).f
    (r'.extend (isAlgClosed_racl _) (isSmall_joinField r' r) (le_joinField_right r' r)).f
    (r.extend _ _ _).isDefinedAt (r.extend _ _ _).isGenericOver
    (r'.extend _ _ _).isDefinedAt (r'.extend _ _ _).isGenericOver

theorem comp_M (r' : Representative k K a' a'') (r : Representative k K a a') :
    (r'.comp r).M = joinField r' r := rfl

theorem comp_eval (r' : Representative k K a' a'') (r : Representative k K a a') {y : ι → K}
    (hy : IsGenericOver (joinField r' r) a y) :
    (r'.comp r).f.eval y = r'.f.eval (r.f.eval y) := by
  refine (compOver_eval _ _ _ _ _ _ _ _ hy).trans ?_
  exact (extend_eval r' _ _ _ _).trans (congrArg _ (extend_eval r _ _ _ _))

/-- `lem:comp`: composition respects equivalence. -/
theorem comp_equivalent {r₁ r₂ : Representative k K a a'} {r₁' r₂' : Representative k K a' a''}
    (h : r₁.Equivalent r₂) (h' : r₁'.Equivalent r₂') :
    (r₁'.comp r₁).Equivalent (r₂'.comp r₂) := by
  intro y hy
  have hB : IsAlgClosed ↥(racl k (((r₁'.comp r₁).M : Set K) ∪ (r₂'.comp r₂).M)) :=
    isAlgClosed_racl _
  have hBs : IsSmall k ((racl k (((r₁'.comp r₁).M : Set K) ∪ (r₂'.comp r₂).M) :
      IntermediateField k K) : Set K) :=
    ((r₁'.comp r₁).isSmall.union (r₂'.comp r₂).isSmall).racl
  have h1 : (r₁'.comp r₁).M ≤ racl k (((r₁'.comp r₁).M : Set K) ∪ (r₂'.comp r₂).M) :=
    subset_union_left.trans (subset_racl k _)
  have h2 : (r₂'.comp r₂).M ≤ racl k (((r₁'.comp r₁).M : Set K) ∪ (r₂'.comp r₂).M) :=
    subset_union_right.trans (subset_racl k _)
  rw [comp_eval _ _ (hy.of_le h1), comp_eval _ _ (hy.of_le h2)]
  -- The value of `r₁` at `y` is generic over the big field.
  have hz : IsGenericOver (racl k (((r₁'.comp r₁).M : Set K) ∪ (r₂'.comp r₂).M)) a'
      (r₁.f.eval y) := by
    have := (r₁.extend hB hBs ((le_joinField_left r₁' r₁).trans h1)).isGenericOver y hy
    rwa [extend_eval] at this
  have hle12 : racl k ((r₁.M : Set K) ∪ r₂.M) ≤
      racl k (((r₁'.comp r₁).M : Set K) ∪ (r₂'.comp r₂).M) :=
    racl_le_of_subset_racl (union_subset ((le_joinField_left r₁' r₁).trans h1)
      ((le_joinField_left r₂' r₂).trans h2))
  have hle12' : racl k ((r₁'.M : Set K) ∪ r₂'.M) ≤
      racl k (((r₁'.comp r₁).M : Set K) ∪ (r₂'.comp r₂).M) :=
    racl_le_of_subset_racl (union_subset ((le_joinField_right r₁' r₁).trans h1)
      ((le_joinField_right r₂' r₂).trans h2))
  rw [h' _ (hz.of_le hle12'), h y (hy.of_le hle12)]

end Representative

namespace Germ

variable [IsAlgClosed k] [UniversalDomain k K] [Finite ι] [Finite κ]

/-! ### Values are algebraic over the field and the point -/

/-- A generic point of the graph over `F` has rank over `F` equal to the dimension of the
source locus. -/
theorem IsGraphGeneric.erk_eq {g : Germ k a a'} {F : IntermediateField k K} [IsAlgClosed (↥F)]
    (hF : IsSmall k (F : Set K)) (hcb : g.cb ≤ F) {y : ι → K} {z : κ → K}
    (h : g.IsGraphGeneric F (Sum.elim y z)) :
    erk k (F : Set K) (range (Sum.elim y z)) = erk k ∅ (range a) := by
  obtain ⟨r, rfl, hFM, hind⟩ :=
    g.exists_rep hF hcb (IsSmall.of_finite (finite_range (Sum.elim y z)))
  have _ := r.isAlgClosed
  have hind' : IndepOver k (F : Set K) (range (Sum.elim y z)) (r.M : Set K) := hind.symm
  have hz : z = r.f.eval y := h.eq_graphPoint hF hFM (by rwa [← Sum.elim_range])
  have hM : IsGraphGeneric (⟦r⟧ : Germ k a a') r.M (Sum.elim y z) := by
    unfold IsGraphGeneric
    rw [locusIdeal_eq_of_indepOver hF r.isSmall hFM hind']
    exact h
  have hyM : IsGenericOver r.M a y := hM.isGenericOver_fst
  have hrk := hind' (subset_refl _) (finite_range _)
  rw [union_eq_right.2 (SetLike.coe_subset_coe.2 hFM)] at hrk
  rw [← hrk, hz]
  exact r.erk_graphPoint le_rfl hyM

/-- `lem:eval`(2), weak form: the value of a germ is algebraic over the field and the
point. -/
theorem eval_mem_racl (g : Germ k a a') {F : IntermediateField k K} [IsAlgClosed (↥F)]
    (hF : IsSmall k (F : Set K)) (hcb : g.cb ≤ F) {y : ι → K} (hy : IsGenericOver F a y)
    (j : κ) : g.eval F y j ∈ racl k ((F : Set K) ∪ range y) := by
  have h1 := (g.isGraphGeneric_eval hF hcb hy).erk_eq hF hcb
  rw [Sum.elim_range, erk_union_eq, hy.erk_coe_eq, hy.erk_empty_eq] at h1
  have hne : erk k ∅ (range a) ≠ ⊤ := erk_ne_top k (finite_range a) _
  have h2 : erk k ((F : Set K) ∪ range y) (range (g.eval F y)) = 0 := by
    refine nonpos_iff_eq_zero.1 ((ENat.add_le_add_iff_left hne).1 ?_)
    rw [add_zero]
    exact h1.le
  exact (erk_eq_zero_iff k).1 h2 (mem_range_self j)

/-! ### Composition of germs -/

variable [Finite μ]

/-- Composition of a representative with a germ. -/
def compRep (r' : Representative k K a' a'') (g : Germ k a a') : Germ k a a'' :=
  Quotient.lift (fun r ↦ (⟦r'.comp r⟧ : Germ k a a''))
    (fun _ _ h ↦
      Quotient.sound (Representative.comp_equivalent h (Representative.equivalent_refl r')))
    g

theorem compRep_mk (r' : Representative k K a' a'') (r : Representative k K a a') :
    compRep r' (⟦r⟧ : Germ k a a') = ⟦r'.comp r⟧ := rfl

theorem compRep_congr {r₁' r₂' : Representative k K a' a''} (h' : r₁'.Equivalent r₂')
    (g : Germ k a a') : compRep r₁' g = compRep r₂' g := by
  induction g using Quotient.inductionOn with
  | h r =>
    exact Quotient.sound (Representative.comp_equivalent (Representative.equivalent_refl r) h')

/-- `lem:comp`: composition of germs. -/
def comp (g' : Germ k a' a'') (g : Germ k a a') : Germ k a a'' :=
  Quotient.lift (fun r' ↦ compRep r' g) (fun _ _ h' ↦ compRep_congr h' g) g'

theorem comp_mk (r' : Representative k K a' a'') (r : Representative k K a a') :
    Germ.comp (⟦r'⟧ : Germ k a' a'') (⟦r⟧ : Germ k a a') = ⟦r'.comp r⟧ := rfl

/-- `lem:comp`: the canonical base of a composite lies in every algebraically closed small
field containing both canonical bases. -/
theorem cb_comp_le (g' : Germ k a' a'') (g : Germ k a a') {F : IntermediateField k K}
    [IsAlgClosed (↥F)] (hF : IsSmall k (F : Set K)) (hcb : g.cb ≤ F) (hcb' : g'.cb ≤ F) :
    (Germ.comp g' g).cb ≤ F := by
  obtain ⟨y, hy⟩ := exists_isGenericOver hF a
  obtain ⟨r, rfl, hFM, hind⟩ := g.exists_rep hF hcb (IsSmall.of_finite (finite_range y))
  obtain ⟨r', rfl, hFM', hind'⟩ :=
    g'.exists_rep hF hcb' (r.isSmall.union (IsSmall.of_finite (finite_range y)))
  have _ := r.isAlgClosed
  have _ := r'.isAlgClosed
  have hyM : IsGenericOver r.M a y :=
    (hy.isGenericOver_iff_indepOver hF r.isSmall hFM).2 hind.symm
  -- `y` is generic over the join field.
  have hN := Representative.isSmall_joinField r' r
  have hFN : F ≤ Representative.joinField r' r :=
    hFM.trans (Representative.le_joinField_left r' r)
  have hyind : IndepOver k (F : Set K) (range y) (Representative.joinField r' r : Set K) := by
    have h1 : IndepOver k (F : Set K) (range y) ((r.M : Set K) ∪ r'.M) :=
      hind.symm.union_right (by rw [union_comm]; exact hind'.symm)
    have h2 := indepOver_racl_right_iff.2 h1
    rwa [union_eq_right.2 (fun x hx ↦ subset_union_left (hFM hx) : (F : Set K) ⊆ ↑r.M ∪ ↑r'.M)]
      at h2
  have hyN : IsGenericOver (Representative.joinField r' r) a y :=
    (hy.isGenericOver_iff_indepOver hF hN hFN).2 hyind
  -- The value of `r` at `y` is generic over the join field, hence over `r'.M`.
  have hz : IsGenericOver (Representative.joinField r' r) a' (r.f.eval y) := by
    have := (r.extend (isAlgClosed_racl _) hN (Representative.le_joinField_left r' r)).isGenericOver
      y hyN
    rwa [Representative.extend_eval] at this
  have hzM' : IsGenericOver r'.M a' (r.f.eval y) :=
    hz.of_le (Representative.le_joinField_right r' r)
  have _ : IsAlgClosed ↥(Representative.joinField r' r) := isAlgClosed_racl _
  -- The graph point of the composite lies in the closure of `F ∪ y`.
  have hgraph : range ((r'.comp r).graphPoint y) ⊆ racl k ((F : Set K) ∪ range y) := by
    unfold Representative.graphPoint
    rw [Sum.elim_range, Representative.comp_eval _ _ hyN]
    refine union_subset (subset_union_right.trans (subset_racl k _)) ?_
    rintro _ ⟨j, rfl⟩
    have hval : r'.f.eval (r.f.eval y) j ∈ racl k ((F : Set K) ∪ range (r.f.eval y)) := by
      rw [← eval_eq_rep r' hF hcb' hFM' hzM']
      exact eval_mem_racl _ hF hcb' (hz.of_le hFN) j
    refine racl_le_of_subset_racl (union_subset (subset_union_left.trans (subset_racl k _)) ?_)
      hval
    rintro _ ⟨i, rfl⟩
    rw [← eval_eq_rep r hF hcb hFM hyM]
    exact eval_mem_racl _ hF hcb hy i
  rw [comp_mk, cb_mk_eq_canonicalBase (r'.comp r) hyN]
  refine (indepOver_iff_canonicalBase_le hN hFN _).1 ?_
  exact (indepOver_racl_left_iff.2 hyind).mono_left hgraph

/-- `lem:comp`: the composite evaluates to the composite of the values. -/
theorem comp_eval (g' : Germ k a' a'') (g : Germ k a a') {F : IntermediateField k K}
    [IsAlgClosed (↥F)] (hF : IsSmall k (F : Set K)) (hcb : g.cb ≤ F) (hcb' : g'.cb ≤ F)
    {y : ι → K} (hy : IsGenericOver F a y) :
    (Germ.comp g' g).eval F y = g'.eval F (g.eval F y) := by
  have hcomp := cb_comp_le g' g hF hcb hcb'
  obtain ⟨r, rfl, hFM, hind⟩ := g.exists_rep hF hcb (IsSmall.of_finite (finite_range y))
  obtain ⟨r', rfl, hFM', hind'⟩ :=
    g'.exists_rep hF hcb' (r.isSmall.union (IsSmall.of_finite (finite_range y)))
  have _ := r.isAlgClosed
  have _ := r'.isAlgClosed
  have hyM : IsGenericOver r.M a y :=
    (hy.isGenericOver_iff_indepOver hF r.isSmall hFM).2 hind.symm
  have hN := Representative.isSmall_joinField r' r
  have hFN : F ≤ Representative.joinField r' r :=
    hFM.trans (Representative.le_joinField_left r' r)
  have hyind : IndepOver k (F : Set K) (range y) (Representative.joinField r' r : Set K) := by
    have h1 : IndepOver k (F : Set K) (range y) ((r.M : Set K) ∪ r'.M) :=
      hind.symm.union_right (by rw [union_comm]; exact hind'.symm)
    have h2 := indepOver_racl_right_iff.2 h1
    rwa [union_eq_right.2 (fun x hx ↦ subset_union_left (hFM hx) : (F : Set K) ⊆ ↑r.M ∪ ↑r'.M)]
      at h2
  have hyN : IsGenericOver (Representative.joinField r' r) a y :=
    (hy.isGenericOver_iff_indepOver hF hN hFN).2 hyind
  have hz : IsGenericOver (Representative.joinField r' r) a' (r.f.eval y) := by
    have := (r.extend (isAlgClosed_racl _) hN (Representative.le_joinField_left r' r)).isGenericOver
      y hyN
    rwa [Representative.extend_eval] at this
  have hzM' : IsGenericOver r'.M a' (r.f.eval y) :=
    hz.of_le (Representative.le_joinField_right r' r)
  rw [comp_mk] at hcomp ⊢
  rw [eval_eq_rep (r'.comp r) hF hcomp hFN hyN, Representative.comp_eval _ _ hyN,
    eval_eq_rep r hF hcb hFM hyM, eval_eq_rep r' hF hcb' hFM' hzM']

end Germ

end

end GroupConfig
