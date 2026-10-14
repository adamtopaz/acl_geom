/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.Basic
import GroupConfig.Contraction

/-!
# The graph ideal of a germ

Blueprint `sources/group_configuration/04-germs.tex`, `def:graph` and `lem:graph`.

The *graph ideal* of a representative `(M, f)` is the locus over `M` of the graph point
`(y, f(y))` of a generic point `y` over `M`.  It does not depend on the generic point
(`Representative.locusIdeal_graphPoint_eq`, by conjugacy and equivariance), nor on the
representative within its germ (`Representative.graphIdeal_eq_of_equivalent`, since the
graph point is independent from a larger field over which `y` is generic), so it descends
to germs (`Germ.graphIdeal`).  Its contractions to the two groups of variables are the
loci of `a` and of `a'` (`lem:graph`(2)), and the rank of its generic graph point equals
the dimension of the source locus (`Representative.erk_graphPoint`). The graph ideal
determines the germ (`lem:graph`(3), `Germ.graphIdeal_injective`): two representatives
with the same graph ideal have conjugate graph points over the join of their fields, and
the conjugating automorphism fixes the generic point, hence the values.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** representative-independent graph ideals, both coordinate projections,
the rank of a generic graph point and graph-ideal injectivity are proved.
The statements concern represented loci. A separate abstract graph-ideal
dimension/primality package is not claimed here; the germ code and evaluation
layers are developed subsequently.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] {ι κ : Type*}
  {a : ι → K} {a' : κ → K}

namespace Representative

/-- The graph point `(y, f(y))` of a representative at `y`. -/
def graphPoint (r : Representative k K a a') (y : ι → K) : (ι ⊕ κ) → K :=
  Sum.elim y (r.f.eval y)

/-- Automorphisms over `M` act on graph points. -/
theorem graphPoint_comp (r : Representative k K a a') (σ : K ≃ₐ[↥r.M] K) (y : ι → K) :
    r.graphPoint (⇑σ ∘ y) = ⇑σ ∘ r.graphPoint y := by
  unfold graphPoint
  rw [r.f.eval_comp σ y]
  funext i
  cases i <;> rfl

/-- The locus of the graph point does not depend on the generic point. -/
theorem locusIdeal_graphPoint_eq [Finite ι] [Finite κ] (r : Representative k K a a')
    {y z : ι → K} (hy : IsGenericOver r.M a y) (hz : IsGenericOver r.M a z) :
    locusIdeal (↥r.M) (r.graphPoint y) = locusIdeal (↥r.M) (r.graphPoint z) := by
  obtain ⟨σ, hσ⟩ := hy.exists_algEquiv hz
  have hyz : ⇑σ ∘ y = z := funext hσ
  rw [← hyz, graphPoint_comp]
  exact ((locusIdeal_eq_iff_exists_algEquiv r.M _ _).2 ⟨σ, fun _ ↦ rfl⟩).symm

/-- `def:graph`: the graph ideal of a representative, the locus over `M` of the graph point
of a generic point over `M`. -/
def graphIdeal [IsAlgClosed k] [UniversalDomain k K] [Finite ι] (r : Representative k K a a') :
    Ideal (MvPolynomial (ι ⊕ κ) K) :=
  locusIdeal (↥r.M) (r.graphPoint (Classical.choose (exists_isGenericOver r.isSmall a)))

theorem graphIdeal_eq [IsAlgClosed k] [UniversalDomain k K] [Finite ι] [Finite κ]
    (r : Representative k K a a') {y : ι → K} (hy : IsGenericOver r.M a y) :
    r.graphIdeal = locusIdeal (↥r.M) (r.graphPoint y) :=
  locusIdeal_graphPoint_eq r (Classical.choose_spec (exists_isGenericOver r.isSmall a)) hy

/-- The graph point of a generic point over a field `N ⊇ M` has the rank of the locus of
`a`. -/
theorem erk_graphPoint [Finite ι] (r : Representative k K a a') {N : IntermediateField k K}
    (hMN : r.M ≤ N) {y : ι → K} (hy : IsGenericOver N a y) :
    erk k (N : Set K) (range (r.graphPoint y)) = erk k ∅ (range a) := by
  unfold graphPoint
  rw [Sum.elim_range, erk_union_eq_of_subset_racl k ?_, hy.erk_coe_eq, hy.erk_empty_eq]
  rintro _ ⟨j, rfl⟩
  exact racl_mono (k := k) (union_subset_union_left _ hMN) (r.eval_mem_racl (hy.of_le hMN) j)

/-- `lem:graph`(1): the locus of the graph point over `M` equals its locus over any larger
small field over which `y` is generic. -/
theorem locusIdeal_graphPoint_eq_of_le [UniversalDomain k K] [Finite ι] [Finite κ]
    (r : Representative k K a a') {N : IntermediateField k K} (hN : IsSmall k (N : Set K))
    (hMN : r.M ≤ N) {y : ι → K} (hy : IsGenericOver N a y) :
    locusIdeal (↥N) (r.graphPoint y) = locusIdeal (↥r.M) (r.graphPoint y) := by
  have _ := r.isAlgClosed
  refine locusIdeal_eq_of_indepOver r.isSmall hN hMN ?_
  refine indepOver_of_erk_eq (finite_range _) ?_
  rw [union_eq_right.2 (SetLike.coe_subset_coe.2 hMN), erk_graphPoint r hMN hy,
    erk_graphPoint r le_rfl (hy.of_le hMN)]

/-- `lem:graph`(1): equivalent representatives have the same graph ideal. -/
theorem graphIdeal_eq_of_equivalent [IsAlgClosed k] [UniversalDomain k K] [Finite ι] [Finite κ]
    {r r' : Representative k K a a'} (h : r.Equivalent r') : r.graphIdeal = r'.graphIdeal := by
  have hN : IsSmall k ((racl k ((r.M : Set K) ∪ r'.M) : IntermediateField k K) : Set K) :=
    (r.isSmall.union r'.isSmall).racl
  obtain ⟨y, hy⟩ := exists_isGenericOver hN a
  have hMN : r.M ≤ racl k ((r.M : Set K) ∪ r'.M) := subset_union_left.trans (subset_racl k _)
  have hM'N : r'.M ≤ racl k ((r.M : Set K) ∪ r'.M) :=
    subset_union_right.trans (subset_racl k _)
  have hpt : r.graphPoint y = r'.graphPoint y := by
    unfold graphPoint
    rw [h y hy]
  rw [r.graphIdeal_eq (hy.of_le hMN), r'.graphIdeal_eq (hy.of_le hM'N),
    ← r.locusIdeal_graphPoint_eq_of_le hN hMN hy, ← r'.locusIdeal_graphPoint_eq_of_le hN hM'N hy,
    hpt]

omit [IsAlgClosed K] in
/-- Contracting the vanishing ideal of a pair to the first group of variables. -/
theorem comap_rename_inl_idealOf (L : Type*) [Field L] [Algebra L K] (w₁ : ι → K)
    (w₂ : κ → K) :
    (idealOf L (Sum.elim w₁ w₂)).comap
        (rename (Sum.inl : ι → ι ⊕ κ) : MvPolynomial ι L →ₐ[L] MvPolynomial (ι ⊕ κ) L) =
      idealOf L w₁ := by
  ext P
  rw [Ideal.mem_comap, mem_idealOf_iff, mem_idealOf_iff, aeval_rename, Sum.elim_comp_inl]

omit [IsAlgClosed K] in
/-- Contracting the vanishing ideal of a pair to the second group of variables. -/
theorem comap_rename_inr_idealOf (L : Type*) [Field L] [Algebra L K] (w₁ : ι → K)
    (w₂ : κ → K) :
    (idealOf L (Sum.elim w₁ w₂)).comap
        (rename (Sum.inr : κ → ι ⊕ κ) : MvPolynomial κ L →ₐ[L] MvPolynomial (ι ⊕ κ) L) =
      idealOf L w₂ := by
  ext P
  rw [Ideal.mem_comap, mem_idealOf_iff, mem_idealOf_iff, aeval_rename, Sum.elim_comp_inr]

/-- `lem:graph`(2): the graph ideal contracts to the locus of `a` in the variables `Y`. -/
theorem comap_rename_inl_graphIdeal [IsAlgClosed k] [UniversalDomain k K] [Finite ι] [Finite κ]
    (r : Representative k K a a') :
    r.graphIdeal.comap
        (rename (Sum.inl : ι → ι ⊕ κ) : MvPolynomial ι K →ₐ[K] MvPolynomial (ι ⊕ κ) K) =
      locusIdeal k a := by
  obtain ⟨y, hy⟩ := exists_isGenericOver r.isSmall a
  rw [r.graphIdeal_eq hy, graphPoint, locusIdeal, comap_rename_map_eq _ Sum.inl_injective,
    comap_rename_inl_idealOf]
  exact hy.locusIdeal_eq

/-- `lem:graph`(2): the graph ideal contracts to the locus of `a'` in the variables `Z`. -/
theorem comap_rename_inr_graphIdeal [IsAlgClosed k] [UniversalDomain k K] [Finite ι] [Finite κ]
    (r : Representative k K a a') :
    r.graphIdeal.comap
        (rename (Sum.inr : κ → ι ⊕ κ) : MvPolynomial κ K →ₐ[K] MvPolynomial (ι ⊕ κ) K) =
      locusIdeal k a' := by
  obtain ⟨y, hy⟩ := exists_isGenericOver r.isSmall a
  rw [r.graphIdeal_eq hy, graphPoint, locusIdeal, comap_rename_map_eq _ Sum.inr_injective,
    comap_rename_inr_idealOf]
  exact (r.isGenericOver y hy).locusIdeal_eq

/-- `lem:graph`(3): the graph ideal determines the germ. -/
theorem equivalent_of_graphIdeal_eq [IsAlgClosed k] [UniversalDomain k K] [Finite ι] [Finite κ]
    {r r' : Representative k K a a'} (h : r.graphIdeal = r'.graphIdeal) : r.Equivalent r' := by
  intro y hy
  have hN : IsSmall k ((racl k ((r.M : Set K) ∪ r'.M) : IntermediateField k K) : Set K) :=
    (r.isSmall.union r'.isSmall).racl
  have hMN : r.M ≤ racl k ((r.M : Set K) ∪ r'.M) := subset_union_left.trans (subset_racl k _)
  have hM'N : r'.M ≤ racl k ((r.M : Set K) ∪ r'.M) :=
    subset_union_right.trans (subset_racl k _)
  -- The two graph points are generic points over the join of the same locus.
  have h1 : locusIdeal (↥(racl k ((r.M : Set K) ∪ r'.M))) (r'.graphPoint y) =
      locusIdeal (↥(racl k ((r.M : Set K) ∪ r'.M))) (r.graphPoint y) := by
    rw [r.locusIdeal_graphPoint_eq_of_le hN hMN hy, r'.locusIdeal_graphPoint_eq_of_le hN hM'N hy,
      ← r.graphIdeal_eq (hy.of_le hMN), ← r'.graphIdeal_eq (hy.of_le hM'N), h]
  obtain ⟨σ, hσ⟩ := (locusIdeal_eq_iff_exists_algEquiv _ _ _).1 h1
  have hy' : ⇑σ ∘ y = y := funext fun i ↦ hσ (Sum.inl i)
  have hz : ⇑σ ∘ r.f.eval y = r'.f.eval y := funext fun j ↦ hσ (Sum.inr j)
  -- The conjugating automorphism is over `M`, so it commutes with `f`.
  have hcomp : r.f.eval (⇑σ ∘ y) = ⇑σ ∘ r.f.eval y := by
    rw [← QuasiRational.eval_map hMN, ← QuasiRational.eval_map hMN, QuasiRational.eval_comp]
  rw [← hz, ← hcomp, hy']

end Representative

namespace Germ

variable [IsAlgClosed k] [UniversalDomain k K] [Finite ι] [Finite κ]

/-- `def:graph`: the graph ideal of a germ. -/
def graphIdeal (g : Germ k a a') : Ideal (MvPolynomial (ι ⊕ κ) K) :=
  Quotient.lift Representative.graphIdeal
    (fun _ _ h ↦ Representative.graphIdeal_eq_of_equivalent h) g

theorem graphIdeal_mk (r : Representative k K a a') :
    Germ.graphIdeal (⟦r⟧ : Germ k a a') = r.graphIdeal := rfl

/-- `lem:graph`(3): the graph ideal determines the germ. -/
theorem graphIdeal_injective : Function.Injective (graphIdeal : Germ k a a' → _) := by
  intro g g' h
  induction g using Quotient.inductionOn with
  | h r =>
    induction g' using Quotient.inductionOn with
    | h r' => exact Quotient.sound (Representative.equivalent_of_graphIdeal_eq h)

end Germ

end

end GroupConfig
