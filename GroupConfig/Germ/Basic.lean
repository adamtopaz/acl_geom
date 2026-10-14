/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.QuasiRational

/-!
# Germs of quasi-rational maps: representatives and the germ quotient

Blueprint `sources/group_configuration/04-germs.tex`, `def:germ` and the discussion
following it.

A *representative* of a germ from the locus of `a` to the locus of `a'` is a small
algebraically closed subfield `M` together with a quasi-rational expression over `M`
which is defined at every generic point `y` of the locus of `a` over `M` and sends it to
a generic point of the locus of `a'` over `M` (`Representative`).  Two representatives
are *equivalent* if they agree at every generic point over the algebraic closure of the
join of their fields (`Representative.Equivalent`); this is an equivalence relation
(transitivity by `lem:qr-agree`), and a *germ* is an equivalence class (`Germ`).
Enlarging the field of a representative gives an equivalent representative
(`Representative.extend`, `Representative.extend_equivalent`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the representative relation, its equivalence proof, the germ quotient
and equivalent extension are proved for represented loci. Generic evaluation,
composition and the group-extraction theorem are developed in later modules.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable (k K : Type*) [Field k] [Field K] [Algebra k K] [IsAlgClosed K] {ι κ : Type*}

/-- `def:germ`: a representative of a germ from the locus of `a` to the locus of `a'`. -/
structure Representative (a : ι → K) (a' : κ → K) where
  /-- The small algebraically closed field of definition. -/
  M : IntermediateField k K
  /-- The coefficient field is algebraically closed. -/
  isAlgClosed : IsAlgClosed (↥M)
  /-- The coefficient field is small relative to the universal ambient. -/
  isSmall : IsSmall k (M : Set K)
  /-- The quasi-rational expression. -/
  f : QuasiRational (↥M) ι κ
  /-- The expression is defined at every generic source point over `M`. -/
  isDefinedAt : ∀ y, IsGenericOver M a y → f.IsDefinedAt y
  /-- Every such source point maps to a generic target point over `M`. -/
  isGenericOver : ∀ y, IsGenericOver M a y → IsGenericOver M a' (f.eval y)

variable {k K}

namespace Representative

variable {a : ι → K} {a' : κ → K}

/-- `def:germ`: two representatives are equivalent if they agree at every generic point over
the algebraic closure of the join of their fields. -/
def Equivalent (r r' : Representative k K a a') : Prop :=
  ∀ y, IsGenericOver (racl k ((r.M : Set K) ∪ r'.M)) a y → r.f.eval y = r'.f.eval y

theorem equivalent_refl (r : Representative k K a a') : r.Equivalent r := fun _ _ ↦ rfl

theorem Equivalent.symm {r r' : Representative k K a a'} (h : r.Equivalent r') :
    r'.Equivalent r := by
  intro y hy
  rw [union_comm] at hy
  exact (h y hy).symm

theorem Equivalent.trans [IsAlgClosed k] [UniversalDomain k K] [Finite ι]
    {r r' r'' : Representative k K a a'} (h : r.Equivalent r') (h' : r'.Equivalent r'') :
    r.Equivalent r'' := by
  intro y hy
  -- A generic point over the closure of all three fields.
  have hsmall : IsSmall k
      ((racl k ((r.M : Set K) ∪ r'.M ∪ r''.M) : IntermediateField k K) : Set K) :=
    ((r.isSmall.union r'.isSmall).union r''.isSmall).racl
  obtain ⟨y', hy'⟩ := exists_isGenericOver hsmall a
  have h1 : IsGenericOver (racl k ((r.M : Set K) ∪ r'.M)) a y' :=
    hy'.of_le (racl_mono (k := k) subset_union_left)
  have h2 : IsGenericOver (racl k ((r'.M : Set K) ∪ r''.M)) a y' :=
    hy'.of_le (racl_mono (k := k)
      (union_subset (subset_union_right.trans subset_union_left) subset_union_right))
  have heq : r.f.eval y' = r''.f.eval y' := (h y' h1).trans (h' y' h2)
  have hMN : r.M ≤ racl k ((r.M : Set K) ∪ r'.M ∪ r''.M) :=
    (subset_union_left.trans subset_union_left).trans (subset_racl k _)
  have hM''N : r''.M ≤ racl k ((r.M : Set K) ∪ r'.M ∪ r''.M) :=
    subset_union_right.trans (subset_racl k _)
  have hMy : r.M ≤ racl k ((r.M : Set K) ∪ r''.M) := subset_union_left.trans (subset_racl k _)
  have hM''y : r''.M ≤ racl k ((r.M : Set K) ∪ r''.M) :=
    subset_union_right.trans (subset_racl k _)
  exact QuasiRational.eval_eq_of_eval_eq hMN hM''N hy' hy.inLocus
    (r.isDefinedAt y' (hy'.of_le hMN)) (r''.isDefinedAt y' (hy'.of_le hM''N))
    (r.isDefinedAt y (hy.of_le hMy)) (r''.isDefinedAt y (hy.of_le hM''y)) heq

/-- Equivalence of representatives is an equivalence relation. -/
instance setoid [IsAlgClosed k] [UniversalDomain k K] [Finite ι] :
    Setoid (Representative k K a a') :=
  ⟨Equivalent, ⟨equivalent_refl, Equivalent.symm, Equivalent.trans⟩⟩

/-- Values of a representative at generic points are algebraic over the field and the point. -/
theorem eval_mem_racl (r : Representative k K a a') {y : ι → K} (hy : IsGenericOver r.M a y)
    (j : κ) : r.f.eval y j ∈ racl k ((r.M : Set K) ∪ range y) := by
  have hdef := r.isDefinedAt y hy j
  have hle : r.M ≤ racl k ((r.M : Set K) ∪ range y) := subset_union_left.trans (subset_racl k _)
  -- Polynomial expressions in `y` over `M` lie in the closure.
  have hpoly : ∀ P : MvPolynomial ι (↥r.M), aeval y P ∈ racl k ((r.M : Set K) ∪ range y) := by
    intro P
    have hmem : aeval y P ∈ Algebra.adjoin (↥r.M) (range y) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨P, rfl⟩
    exact (Algebra.adjoin_le (S := (extendScalars hle).toSubalgebra)
      (subset_union_right.trans (subset_racl k _))) hmem
  have hp : ringExpChar K ≠ 0 := by
    unfold ringExpChar
    exact Nat.one_le_iff_ne_zero.1 (le_max_right _ _)
  refine (isRAC_racl _).mem_of_pow_mem (m := ringExpChar K ^ r.f.e) (pow_ne_zero _ hp) ?_
  rw [QuasiRational.eval_apply, pRoot_pow]
  exact div_mem (hpoly _) (hpoly _)

/-- Enlarging the field of a representative. -/
def extend [UniversalDomain k K] [Finite ι] [Finite κ] (r : Representative k K a a')
    {M₁ : IntermediateField k K} (hM₁ : IsAlgClosed (↥M₁)) (hsmall : IsSmall k (M₁ : Set K))
    (h : r.M ≤ M₁) : Representative k K a a' where
  M := M₁
  isAlgClosed := hM₁
  isSmall := hsmall
  f := r.f.map (IntermediateField.inclusion h).toRingHom
  isDefinedAt y hy := by
    rw [QuasiRational.isDefinedAt_map_iff]
    exact r.isDefinedAt y (hy.of_le h)
  isGenericOver y hy := by
    rw [QuasiRational.eval_map]
    have _ := r.isAlgClosed
    have hyM : IsGenericOver r.M a y := hy.of_le h
    have hz := r.isGenericOver y hyM
    refine (hz.isGenericOver_iff_indepOver r.isSmall hsmall h).2 ?_
    have hyind : IndepOver k (r.M : Set K) (range y) (M₁ : Set K) :=
      (hyM.isGenericOver_iff_indepOver r.isSmall hsmall h).1 hy
    refine (indepOver_racl_left_iff.2 hyind).mono_left ?_
    rintro _ ⟨j, rfl⟩
    exact r.eval_mem_racl hyM j

/-- Enlarging the field gives an equivalent representative. -/
theorem extend_equivalent [UniversalDomain k K] [Finite ι] [Finite κ]
    (r : Representative k K a a') {M₁ : IntermediateField k K} (hM₁ : IsAlgClosed (↥M₁))
    (hsmall : IsSmall k (M₁ : Set K)) (h : r.M ≤ M₁) :
    (r.extend hM₁ hsmall h).Equivalent r :=
  fun y _ ↦ QuasiRational.eval_map h r.f y

end Representative

variable (k) in
/-- `def:germ`: germs from the locus of `a` to the locus of `a'`, the equivalence classes of
representatives. -/
def Germ [IsAlgClosed k] [UniversalDomain k K] [Finite ι] (a : ι → K) (a' : κ → K) : Type _ :=
  Quotient (Representative.setoid (k := k) (K := K) (a := a) (a' := a'))

end

end GroupConfig
