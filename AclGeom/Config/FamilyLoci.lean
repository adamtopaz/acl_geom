/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import AclGeom.Config.ParameterField
import AclGeom.Geometry.PointTuples
import AclGeom.Correspondence.LocusJointComponent

/-!
# Selected parameter-family locus identities

For an actual six-point partial quadrangle, the chosen composition incidence and the
U-family pulled back to the parameter locus are literal irreducible components of dimension
three. Their parameter locus and original U-family have dimension two. For an actual Ψ witness,
the analogous components have dimension five, the parameter locus dimension four and the
C-family dimension three. The source hypotheses supply all ranks and closure statements.

The full tuple locus maps densely, by the actual coordinate-forgetting maps of literal quotient
spectra, to both components, the parameter locus and the original U- or C-family. Its generated
field is finite over each component field under the canonical inclusion. These assertions work
over arbitrary base and ambient fields; no algebraic closure or genericity conclusion is an input.

The companion results in ParameterField contract each selected scalar composite ideal to
exactly the parameter-family joint ideal used here. The polynomial map first joins the two
parameter index blocks and then evaluates their actual generators. Relations among the parameters
are allowed; no injective localization of the raw parameter polynomial ring is asserted.

This proves the selected generic-component locus forms of blueprint (8.4c) and (8.6).
Coherent triples of branches, their common normal cover and the original group statements
remain obligations. No finite morphism of the entire affine loci or classification of all
parameter-family components is asserted.

**Status:** selected parameter-family components, dense projections, finite function fields and
their scalar contraction bridge proved (#5).
-/

namespace AclGeom

open MvPolynomial Set IntermediateField GroupConfig

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Consumed by the two actual source-family component producers. -/
private theorem trdeg_of_closed_span {ι : Type*} (v : ι → K) {E : ClosedIF k K} {n : ℕ}
    (hv : racl k (range v) = E.1) (hE : RankEq n E) :
    Algebra.trdeg k (adjoin k (range v)) = n := by
  apply Cardinal.toENat_eq_natCast.mp
  rw [← erk_empty_eq_toENat_trdeg]
  exact ClosedIF.erk_eq_of_racl_eq hv hE

/-- The exact closed span of a tuple, from both inclusions. -/
private theorem racl_range_eq_of_le {ι : Type*} (v : ι → K) (T : ClosedIF k K)
    (hle : ∀ i, v i ∈ T.1) (hge : T ≤ ⟨racl k (range v), isRAC_racl _⟩) :
    racl k (range v) = T.1 :=
  le_antisymm ((racl_mono (Set.range_subset_iff.2 hle)).trans_eq (isRAC_iff_racl_eq.mp T.2))
    (ClosedIF.le_iff.1 hge)

/-- A point represented in a tuple lies below the closure of the tuple. -/
private theorem point_le_racl_range {ι : Type*} (v : ι → K) (P : Point k K) (i : ι)
    (hi : v i = P.rep) : P.1 ≤ ⟨racl k (range v), isRAC_racl _⟩ := by
  rw [← P.point_rep]
  exact ClosedIF.point_le_iff.2 (subset_racl k _ ⟨i, hi⟩)

/-- Consumed by the partial-quadrangle family component producer. -/
private theorem racl_three_points (P Q R : Point k K) :
    racl k {P.rep, Q.rep, R.rep} = (P.1 ⊔ (Q.1 ⊔ R.1)).1 := by
  simpa only [P.point_rep, Q.point_rep, R.point_rep] using
    (coe_sup_point₃ (k := k) P.rep Q.rep R.rep).symm

/-- A tuple containing the free S,T,S-prime triple spans the whole partial quadrangle.
Consumed by both actual source and parameter-family rank computations. -/
private theorem partialQuad_tuple_span {ι : Type*} {f : Fin 6 → Point k K}
    (h : IsPartialQuadrangle f) (v : ι → K)
    (hsub : range v ⊆ range (fun i ↦ (f i).rep))
    (hfreeMem : {(f 0).rep, (f 1).rep, (f 3).rep} ⊆ range v) :
    racl k (range v) = (Finset.univ.sup fun i ↦ (f i).1).1 := by
  let T : ClosedIF k K := Finset.univ.sup fun i ↦ (f i).1
  let C : ClosedIF k K := ⟨racl k (range v), isRAC_racl _⟩
  have hpt (i : Fin 6) : (f i).1 ≤ T :=
    Finset.le_sup (f := fun j : Fin 6 ↦ (f j).1) (Finset.mem_univ i)
  have hmem (i : Fin 6) : (f i).rep ∈ T.1 := ClosedIF.le_iff.1 (hpt i) (f i).mem_rep
  have hCT : C ≤ T := by
    apply ClosedIF.le_iff.2
    refine (racl_mono ?_).trans_eq (isRAC_iff_racl_eq.mp T.2)
    intro a ha
    obtain ⟨i, rfl⟩ := hsub ha
    exact hmem i
  have htoC (i : Fin 6) (hi : (f i).rep ∈ range v) : (f i).1 ≤ C := by
    rw [← (f i).point_rep]
    exact ClosedIF.point_le_iff.2 (subset_racl k _ hi)
  have hfree : RankEq 3 ((f 0).1 ⊔ ((f 1).1 ⊔ (f 3).1)) := by
    simpa [Finset.sup_insert] using h.rank_free {0, 1, 3} (by decide) (by decide)
  have heq : (f 0).1 ⊔ ((f 1).1 ⊔ (f 3).1) = T :=
    RankEq.eq_of_le (sup_le (hpt 0) (sup_le (hpt 1) (hpt 3))) hfree h.rank_total
  have hTC : T ≤ C := by
    rw [← heq]
    exact sup_le (htoC 0 (hfreeMem (by simp)))
      (sup_le (htoC 1 (hfreeMem (by simp))) (htoC 3 (hfreeMem (by simp))))
  exact congrArg Subtype.val (le_antisymm hCT hTC)

/-- Consumed by the actual six-point family component producer. -/
private theorem partialQuad_family_ranks {f : Fin 6 → Point k K} (h : IsPartialQuadrangle f) :
    let x : Fin 2 → K := ![(f 1).rep, (f 3).rep]
    let y : Fin 1 → K := ![(f 5).rep]
    let z : Fin 2 → K := ![(f 0).rep, (f 4).rep]
    Algebra.trdeg k (adjoin k (range (Sum.elim (Sum.elim x y) z))) = 3 ∧
      Algebra.trdeg k (adjoin k (range y)) = 1 ∧
      Algebra.trdeg k (adjoin k (range (Sum.elim x y))) = 2 ∧
      Algebra.trdeg k (adjoin k (range (Sum.elim y z))) = 2 ∧
      (f 2).rep ∈ racl k (range (Sum.elim (Sum.elim x y) z)) := by
  let x : Fin 2 → K := ![(f 1).rep, (f 3).rep]
  let y : Fin 1 → K := ![(f 5).rep]
  let z : Fin 2 → K := ![(f 0).rep, (f 4).rep]
  let v := Sum.elim (Sum.elim x y) z
  have hspan : racl k (range v) = (Finset.univ.sup fun i ↦ (f i).1).1 :=
    partialQuad_tuple_span h v
      (by
        rintro _ ⟨i, rfl⟩
        rcases i with (i | i) | i
        · fin_cases i <;> exact ⟨_, rfl⟩
        · fin_cases i; exact ⟨_, rfl⟩
        · fin_cases i <;> exact ⟨_, rfl⟩)
      (by
        intro a ha
        rcases ha with rfl | rfl | ha
        · exact ⟨Sum.inr 0, rfl⟩
        · exact ⟨Sum.inl (Sum.inl 0), rfl⟩
        · have : a = (f 3).rep := Set.mem_singleton_iff.1 ha
          subst a
          exact ⟨Sum.inl (Sum.inl 1), rfl⟩)
  have hxy : racl k (range (Sum.elim x y)) = ((f 1).1 ⊔ ((f 3).1 ⊔ (f 5).1)).1 := by
    have hr : range (Sum.elim x y) = {(f 1).rep, (f 3).rep, (f 5).rep} := by
      ext a
      simp [x, y, Set.Sum.elim_range]
      tauto
    rw [hr]
    exact racl_three_points _ _ _
  have hyz : racl k (range (Sum.elim y z)) = ((f 5).1 ⊔ ((f 0).1 ⊔ (f 4).1)).1 := by
    have hr : range (Sum.elim y z) = {(f 5).rep, (f 0).rep, (f 4).rep} := by
      ext a
      simp [y, z, Set.Sum.elim_range]
      tauto
    rw [hr]
    exact racl_three_points _ _ _
  have hy : racl k (range y) = (f 5).1.1 := by
    simpa [y] using (f 5).racl_repTuple
  have hryz : RankEq 2 ((f 5).1 ⊔ ((f 0).1 ⊔ (f 4).1)) := by
    simpa only [sup_assoc, sup_left_comm, sup_comm] using h.rank_STU'
  exact ⟨trdeg_of_closed_span v hspan h.rank_total,
    trdeg_of_closed_span y hy (f 5).rankEq_one,
    trdeg_of_closed_span (Sum.elim x y) hxy h.rank_S'TU',
    trdeg_of_closed_span (Sum.elim y z) hyz hryz,
    by
      rw [hspan]
      exact ClosedIF.le_iff.1
        (Finset.le_sup (f := fun j : Fin 6 ↦ (f j).1) (Finset.mem_univ 2)) (f 2).mem_rep⟩


/-- Used by the actual source and parameter-family projections. -/
private theorem locusProjection_dense {ι κ : Type*} {a : ι → K} {b : κ → K} {g : κ → ι}
    (h : a ∘ g = b) :
    DenseRange (PrimeSpectrum.comap
      (Ideal.quotientMapₐ (idealOf k a) (rename g)
        (idealOf_eq_comap_rename h).le).toRingHom) := by
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
  have hinj := Ideal.quotientMap_injective'
    (H := (idealOf_eq_comap_rename (k := k) h).le)
    (idealOf_eq_comap_rename (k := k) h).ge
  have hker : RingHom.ker (Ideal.quotientMapₐ (idealOf k a) (rename g)
      (idealOf_eq_comap_rename h).le).toRingHom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hinj
  rw [hker]
  exact bot_le

/-- Used by both actual family consumers to express components as literal tuple loci. -/
private theorem jointIdeal_minimal_of_rank {α β γ : Type*} [Finite α] [Finite β] [Finite γ]
    (x : α → K) (y : β → K) (z : γ → K)
    (hrank :
      Algebra.trdeg k (adjoin k (range (Sum.elim (Sum.elim x y) z))) +
          Algebra.trdeg k (adjoin k (range y)) =
        Algebra.trdeg k (adjoin k (range (Sum.elim x y))) +
          Algebra.trdeg k (adjoin k (range (Sum.elim y z)))) :
    idealOf k (Sum.elim (Sum.elim x y) z) ∈
      (Ideal.map (rename (Sum.inl : α ⊕ β → (α ⊕ β) ⊕ γ) :
        MvPolynomial (α ⊕ β) k →ₐ[k] MvPolynomial ((α ⊕ β) ⊕ γ) k)
          (idealOf k (Sum.elim x y)) ⊔
        Ideal.map (rename (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr :
          β ⊕ γ → (α ⊕ β) ⊕ γ) :
          MvPolynomial (β ⊕ γ) k →ₐ[k] MvPolynomial ((α ⊕ β) ⊕ γ) k)
          (idealOf k (Sum.elim y z))).minimalPrimes := by
  have hmin := (locusIncidence_jointPrime_dominating_of_rank (k := k) x y z hrank).1
  rw [Ideal.minimalPrimes_eq_comap]
  refine ⟨_, hmin, ?_⟩
  ext p
  rw [Ideal.mem_comap, RingHom.mem_ker, mem_idealOf_iff]
  rfl


/-- Consumed by the actual U-family pullback component of (8.4c). -/
private theorem partialQuad_parameter_family_ranks {f : Fin 6 → Point k K}
    (h : IsPartialQuadrangle f) :
    let x : Fin 2 → K := ![(f 0).rep, (f 1).rep]
    let y : Fin 1 → K := ![(f 2).rep]
    let z : Fin 2 → K := ![(f 3).rep, (f 4).rep]
    Algebra.trdeg k (adjoin k (range (Sum.elim (Sum.elim x y) z))) = 3 ∧
      Algebra.trdeg k (adjoin k (range y)) = 1 ∧
      Algebra.trdeg k (adjoin k (range (Sum.elim x y))) = 2 ∧
      Algebra.trdeg k (adjoin k (range (Sum.elim y z))) = 2 ∧
      (f 5).rep ∈ racl k (range (Sum.elim (Sum.elim x y) z)) := by
  let x : Fin 2 → K := ![(f 0).rep, (f 1).rep]
  let y : Fin 1 → K := ![(f 2).rep]
  let z : Fin 2 → K := ![(f 3).rep, (f 4).rep]
  let v := Sum.elim (Sum.elim x y) z
  have hspan : racl k (range v) = (Finset.univ.sup fun i ↦ (f i).1).1 :=
    partialQuad_tuple_span h v
      (by
        rintro _ ⟨i, rfl⟩
        rcases i with (i | i) | i
        · fin_cases i <;> exact ⟨_, rfl⟩
        · fin_cases i; exact ⟨_, rfl⟩
        · fin_cases i <;> exact ⟨_, rfl⟩)
      (by
        intro a ha
        rcases ha with rfl | rfl | ha
        · exact ⟨Sum.inl (Sum.inl 0), rfl⟩
        · exact ⟨Sum.inl (Sum.inl 1), rfl⟩
        · have : a = (f 3).rep := Set.mem_singleton_iff.1 ha
          subst a
          exact ⟨Sum.inr 0, rfl⟩)
  have hxy : racl k (range (Sum.elim x y)) = ((f 0).1 ⊔ ((f 1).1 ⊔ (f 2).1)).1 := by
    have hr : range (Sum.elim x y) = {(f 0).rep, (f 1).rep, (f 2).rep} := by
      ext a
      simp [x, y, Set.Sum.elim_range]
      tauto
    rw [hr]
    exact racl_three_points _ _ _
  have hyz : racl k (range (Sum.elim y z)) = ((f 2).1 ⊔ ((f 3).1 ⊔ (f 4).1)).1 := by
    have hr : range (Sum.elim y z) = {(f 2).rep, (f 3).rep, (f 4).rep} := by
      ext a
      simp [y, z, Set.Sum.elim_range]
      tauto
    rw [hr]
    exact racl_three_points _ _ _
  have hy : racl k (range y) = (f 2).1.1 := by
    simpa [y] using (f 2).racl_repTuple
  have hryz : RankEq 2 ((f 2).1 ⊔ ((f 3).1 ⊔ (f 4).1)) := by
    simpa only [sup_assoc, sup_left_comm, sup_comm] using h.rank_S'T'U
  exact ⟨trdeg_of_closed_span v hspan h.rank_total,
    trdeg_of_closed_span y hy (f 2).rankEq_one,
    trdeg_of_closed_span (Sum.elim x y) hxy h.rank_STU,
    trdeg_of_closed_span (Sum.elim y z) hyz hryz,
    by
      rw [hspan]
      exact ClosedIF.le_iff.1
        (Finset.le_sup (f := fun j : Fin 6 ↦ (f j).1) (Finset.mem_univ 5)) (f 5).mem_rep⟩


/-- Used by both actual full-tuple covers. The scalar action is the actual inclusion of
the smaller generated field into the full tuple field. -/
private theorem finite_field_cover {ι κ : Type*} [Finite κ] (a : ι → K) (b : κ → K)
    (hsub : range a ⊆ range b) (halg : ∀ j, b j ∈ racl k (range a)) :
    FiniteDimensional (adjoin k (range a))
      (extendScalars (adjoin.mono k _ _ hsub)) := by
  have heq : extendScalars (adjoin.mono k _ _ hsub) =
      adjoin (adjoin k (range a)) (range b) := by
    apply restrictScalars_injective k
    rw [extendScalars_restrictScalars, restrictScalars_adjoin_eq_sup, sup_eq_right.2
      (adjoin.mono k _ _ hsub)]
  rw [heq]
  exact finiteDimensional_adjoin
    (Set.forall_mem_range.2 fun j ↦ ((mem_racl_iff k).1 (halg j)).isIntegral)

/-- Used by the actual component consumers to report their source rank as Krull dimension. -/
private theorem tuple_dimension_eq {ι : Type*} [Finite ι] (v : ι → K) {n : ℕ}
    (h : Algebra.trdeg k (adjoin k (range v)) = n) :
    ringKrullDim (MvPolynomial ι k ⧸ idealOf k v) = n := by
  obtain ⟨d, hd, ht⟩ := exists_locusCoordinateRing_dimension (k := k) v
  have heq : d = n := by exact_mod_cast ht.symm.trans h
  simpa only [heq] using hd

/-- The actual source composite and the pulled-back U-family are components of their literal
incidence loci, of dimension three; the parameter locus and original U-family have dimension
two. Only the genuine partial quadrangle is assumed, over arbitrary fields.
The dense common cover and its finite function fields are separate clauses. -/
theorem IsPartialQuadrangle.parameter_family_components {f : Fin 6 → Point k K}
    (h : IsPartialQuadrangle f) :
    let x : Fin 2 → K := ![(f 1).rep, (f 3).rep]
    let y : Fin 1 → K := ![(f 5).rep]
    let z : Fin 2 → K := ![(f 0).rep, (f 4).rep]
    let p : Fin 2 → K := ![(f 0).rep, (f 1).rep]
    let q : Fin 1 → K := ![(f 2).rep]
    let r : Fin 2 → K := ![(f 3).rep, (f 4).rep]
    idealOf k (Sum.elim (Sum.elim x y) z) ∈
      (Ideal.map (rename (Sum.inl : Fin 2 ⊕ Fin 1 → (Fin 2 ⊕ Fin 1) ⊕ Fin 2) :
          MvPolynomial (Fin 2 ⊕ Fin 1) k →ₐ[k]
            MvPolynomial ((Fin 2 ⊕ Fin 1) ⊕ Fin 2) k) (idealOf k (Sum.elim x y)) ⊔
        Ideal.map (rename (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr :
          Fin 1 ⊕ Fin 2 → (Fin 2 ⊕ Fin 1) ⊕ Fin 2) :
          MvPolynomial (Fin 1 ⊕ Fin 2) k →ₐ[k]
            MvPolynomial ((Fin 2 ⊕ Fin 1) ⊕ Fin 2) k) (idealOf k (Sum.elim y z))).minimalPrimes ∧
    idealOf k (Sum.elim (Sum.elim p q) r) ∈
      (Ideal.map (rename (Sum.inl : Fin 2 ⊕ Fin 1 → (Fin 2 ⊕ Fin 1) ⊕ Fin 2) :
          MvPolynomial (Fin 2 ⊕ Fin 1) k →ₐ[k]
            MvPolynomial ((Fin 2 ⊕ Fin 1) ⊕ Fin 2) k) (idealOf k (Sum.elim p q)) ⊔
        Ideal.map (rename (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr :
          Fin 1 ⊕ Fin 2 → (Fin 2 ⊕ Fin 1) ⊕ Fin 2) :
          MvPolynomial (Fin 1 ⊕ Fin 2) k →ₐ[k]
            MvPolynomial ((Fin 2 ⊕ Fin 1) ⊕ Fin 2) k) (idealOf k (Sum.elim q r))).minimalPrimes ∧
    ringKrullDim (MvPolynomial ((Fin 2 ⊕ Fin 1) ⊕ Fin 2) k ⧸
      idealOf k (Sum.elim (Sum.elim x y) z)) = 3 ∧
    ringKrullDim (MvPolynomial ((Fin 2 ⊕ Fin 1) ⊕ Fin 2) k ⧸
      idealOf k (Sum.elim (Sum.elim p q) r)) = 3 ∧
    ringKrullDim (MvPolynomial (Fin 2 ⊕ Fin 1) k ⧸
      idealOf k (Sum.elim p q)) = 2 ∧
    ringKrullDim (MvPolynomial (Fin 1 ⊕ Fin 2) k ⧸
      idealOf k (Sum.elim q r)) = 2 := by
  let x : Fin 2 → K := ![(f 1).rep, (f 3).rep]
  let y : Fin 1 → K := ![(f 5).rep]
  let z : Fin 2 → K := ![(f 0).rep, (f 4).rep]
  let p : Fin 2 → K := ![(f 0).rep, (f 1).rep]
  let q : Fin 1 → K := ![(f 2).rep]
  let r : Fin 2 → K := ![(f 3).rep, (f 4).rep]
  obtain ⟨hs, hy, hxy, hyz, -⟩ := partialQuad_family_ranks h
  obtain ⟨ht, hq, hpq, hqr, -⟩ := partialQuad_parameter_family_ranks h
  have hsource := jointIdeal_minimal_of_rank (k := k) x y z
    (by rw [hs, hy, hxy, hyz]; norm_num)
  have htarget := jointIdeal_minimal_of_rank (k := k) p q r
    (by rw [ht, hq, hpq, hqr]; norm_num)
  exact ⟨hsource, htarget, tuple_dimension_eq _ hs, tuple_dimension_eq _ ht,
    tuple_dimension_eq _ hpq, tuple_dimension_eq _ hqr⟩

/-- The full six-point locus maps densely to both chosen components, the parameter locus
and the U-family locus. Its literal generated field is finite over each component field,
with the scalar actions induced by the actual inclusions. Only the genuine partial
quadrangle is assumed, over arbitrary fields. -/
theorem IsPartialQuadrangle.family_common_function_field_cover {f : Fin 6 → Point k K}
    (h : IsPartialQuadrangle f) :
    let x : Fin 2 → K := ![(f 1).rep, (f 3).rep]
    let y : Fin 1 → K := ![(f 5).rep]
    let z : Fin 2 → K := ![(f 0).rep, (f 4).rep]
    let p : Fin 2 → K := ![(f 0).rep, (f 1).rep]
    let q : Fin 1 → K := ![(f 2).rep]
    let r : Fin 2 → K := ![(f 3).rep, (f 4).rep]
    let W : Fin 6 → K := fun i ↦ (f i).rep
    let gS : ((Fin 2 ⊕ Fin 1) ⊕ Fin 2) → Fin 6 :=
      Sum.elim (Sum.elim ![1, 3] ![5]) ![0, 4]
    let gT : ((Fin 2 ⊕ Fin 1) ⊕ Fin 2) → Fin 6 :=
      Sum.elim (Sum.elim ![0, 1] ![2]) ![3, 4]
    let gM : (Fin 2 ⊕ Fin 1) → Fin 6 := Sum.elim ![0, 1] ![2]
    let gΓ : (Fin 1 ⊕ Fin 2) → Fin 6 := Sum.elim ![2] ![3, 4]
    ∃ (hS : W ∘ gS = Sum.elim (Sum.elim x y) z)
      (hT : W ∘ gT = Sum.elim (Sum.elim p q) r)
      (hM : W ∘ gM = Sum.elim p q) (hΓ : W ∘ gΓ = Sum.elim q r),
      DenseRange (PrimeSpectrum.comap
        (Ideal.quotientMapₐ (idealOf k W) (rename gS)
          (idealOf_eq_comap_rename hS).le).toRingHom) ∧
      DenseRange (PrimeSpectrum.comap
        (Ideal.quotientMapₐ (idealOf k W) (rename gT)
          (idealOf_eq_comap_rename hT).le).toRingHom) ∧
      DenseRange (PrimeSpectrum.comap
        (Ideal.quotientMapₐ (idealOf k W) (rename gM)
          (idealOf_eq_comap_rename hM).le).toRingHom) ∧
      DenseRange (PrimeSpectrum.comap
        (Ideal.quotientMapₐ (idealOf k W) (rename gΓ)
          (idealOf_eq_comap_rename hΓ).le).toRingHom) ∧
      FiniteDimensional (adjoin k (range (Sum.elim (Sum.elim x y) z)))
        (extendScalars (adjoin.mono k (range (Sum.elim (Sum.elim x y) z)) (range W)
          (Set.range_subset_iff.2 fun i ↦ ⟨gS i, congrFun hS i⟩))) ∧
      FiniteDimensional (adjoin k (range (Sum.elim (Sum.elim p q) r)))
        (extendScalars (adjoin.mono k (range (Sum.elim (Sum.elim p q) r)) (range W)
          (Set.range_subset_iff.2 fun i ↦ ⟨gT i, congrFun hT i⟩))) := by
  intro x y z p q r W gS gT gM gΓ
  have hS : W ∘ gS = Sum.elim (Sum.elim x y) z := by
    funext i
    rcases i with (i | i) | i
    · fin_cases i <;> rfl
    · fin_cases i; rfl
    · fin_cases i <;> rfl
  have hT : W ∘ gT = Sum.elim (Sum.elim p q) r := by
    funext i
    rcases i with (i | i) | i
    · fin_cases i <;> rfl
    · fin_cases i; rfl
    · fin_cases i <;> rfl
  have hM : W ∘ gM = Sum.elim p q := by
    funext i
    rcases i with i | i
    · fin_cases i <;> rfl
    · fin_cases i; rfl
  have hΓ : W ∘ gΓ = Sum.elim q r := by
    funext i
    rcases i with i | i
    · fin_cases i; rfl
    · fin_cases i <;> rfl
  obtain ⟨-, -, -, -, hu⟩ := partialQuad_family_ranks h
  obtain ⟨-, -, -, -, hu'⟩ := partialQuad_parameter_family_ranks h
  have hbS : ∀ i, W i ∈ racl k (range (Sum.elim (Sum.elim x y) z)) := by
    intro i
    fin_cases i
    · exact subset_racl k _ ⟨Sum.inr 0, rfl⟩
    · exact subset_racl k _ ⟨Sum.inl (Sum.inl 0), rfl⟩
    · exact hu
    · exact subset_racl k _ ⟨Sum.inl (Sum.inl 1), rfl⟩
    · exact subset_racl k _ ⟨Sum.inr 1, rfl⟩
    · exact subset_racl k _ ⟨Sum.inl (Sum.inr 0), rfl⟩
  have hbT : ∀ i, W i ∈ racl k (range (Sum.elim (Sum.elim p q) r)) := by
    intro i
    fin_cases i
    · exact subset_racl k _ ⟨Sum.inl (Sum.inl 0), rfl⟩
    · exact subset_racl k _ ⟨Sum.inl (Sum.inl 1), rfl⟩
    · exact subset_racl k _ ⟨Sum.inl (Sum.inr 0), rfl⟩
    · exact subset_racl k _ ⟨Sum.inr 0, rfl⟩
    · exact subset_racl k _ ⟨Sum.inr 1, rfl⟩
    · exact hu'
  exact ⟨hS, hT, hM, hΓ, locusProjection_dense hS, locusProjection_dense hT,
    locusProjection_dense hM, locusProjection_dense hΓ,
    finite_field_cover _ W (Set.range_subset_iff.2 fun i ↦ ⟨gS i, congrFun hS i⟩) hbS,
    finite_field_cover _ W (Set.range_subset_iff.2 fun i ↦ ⟨gT i, congrFun hT i⟩) hbT⟩

namespace QWitness

variable {w : QWitness k K}

/-- **Ranks of the source family of (8.6).** For `x = (a₁, a₂, X)`, `y = Y` and
`z = (b₁, b₂, Z)`, the joint tuple has rank five, the middle rank one and both pairs rank three,
so `5 + 1 = 3 + 3`; both representatives of `C` are algebraic over the joint tuple. -/
private theorem Psi.source_family_ranks (hw : w.Psi) :
    let x : Fin 3 → K := ![w.A₁.rep, w.A₂.rep, w.X.rep]
    let y : Fin 1 → K := ![w.Y.rep]
    let z : Fin 3 → K := ![w.B₁.rep, w.B₂.rep, w.Z.rep]
    Algebra.trdeg k (adjoin k (range (Sum.elim (Sum.elim x y) z))) = 5 ∧
      Algebra.trdeg k (adjoin k (range y)) = 1 ∧
      Algebra.trdeg k (adjoin k (range (Sum.elim x y))) = 3 ∧
      Algebra.trdeg k (adjoin k (range (Sum.elim y z))) = 3 ∧
      w.C₁.rep ∈ racl k (range (Sum.elim (Sum.elim x y) z)) ∧
      w.C₂.rep ∈ racl k (range (Sum.elim (Sum.elim x y) z)) := by
  intro x y z
  have hmem (T : ClosedIF k K) (P : Point k K) (h : P.1 ≤ T) : P.rep ∈ T.1 :=
    ClosedIF.le_iff.1 h P.mem_rep
  have hYAB : ¬ w.Y.1 ≤ w.A ⊔ w.B := fun h ↦ hw.Y_notLe (h.trans le_sup_left)
  have hYA : ¬ w.Y.1 ≤ w.A := fun h ↦ hYAB (h.trans le_sup_left)
  have hYB : ¬ w.Y.1 ≤ w.B := fun h ↦ hYAB (h.trans le_sup_right)
  have h5 : RankEq 5 (w.A ⊔ w.B ⊔ w.Y.1) := hw.rank_AB.sup_point_of_not_le hYAB
  have h3A : RankEq 3 (w.A ⊔ w.Y.1) := (Psi.rankEq_A hw).sup_point_of_not_le hYA
  have h3B : RankEq 3 (w.B ⊔ w.Y.1) := (Psi.rankEq_B hw).sup_point_of_not_le hYB
  have hXAY : w.X.1 ≤ w.A ⊔ w.Y.1 := hw.X_le
  have hZBY : w.Z.1 ≤ w.B ⊔ w.Y.1 := hw.Z_le.trans inf_le_left
  have hCAB : w.C ≤ w.A ⊔ w.B := by
    have h := RankEq.eq_of_le le_sup_left hw.rank_AB hw.rank_ABC
    rw [h]
    exact le_sup_right
  let v := Sum.elim (Sum.elim x y) z
  have hv : racl k (range v) = (w.A ⊔ w.B ⊔ w.Y.1).1 := by
    refine racl_range_eq_of_le v _ (fun i ↦ ?_) ?_
    · rcases i with (i | i) | i
      · fin_cases i
        · exact hmem _ w.A₁ (le_sup_left.trans (le_sup_left.trans le_sup_left))
        · exact hmem _ w.A₂ (le_sup_right.trans (le_sup_left.trans le_sup_left))
        · exact hmem _ w.X (hXAY.trans (sup_le_sup_right le_sup_left _))
      · fin_cases i
        exact hmem _ w.Y le_sup_right
      · fin_cases i
        · exact hmem _ w.B₁ (le_sup_left.trans (le_sup_right.trans le_sup_left))
        · exact hmem _ w.B₂ (le_sup_right.trans (le_sup_right.trans le_sup_left))
        · exact hmem _ w.Z (hZBY.trans (sup_le_sup_right le_sup_right _))
    · exact sup_le (sup_le
        (sup_le (point_le_racl_range v w.A₁ (Sum.inl (Sum.inl 0)) rfl)
          (point_le_racl_range v w.A₂ (Sum.inl (Sum.inl 1)) rfl))
        (sup_le (point_le_racl_range v w.B₁ (Sum.inr 0) rfl)
          (point_le_racl_range v w.B₂ (Sum.inr 1) rfl)))
        (point_le_racl_range v w.Y (Sum.inl (Sum.inr 0)) rfl)
  have hxy : racl k (range (Sum.elim x y)) = (w.A ⊔ w.Y.1).1 := by
    refine racl_range_eq_of_le (Sum.elim x y) _ (fun i ↦ ?_) ?_
    · rcases i with i | i
      · fin_cases i
        · exact hmem _ w.A₁ (le_sup_left.trans le_sup_left)
        · exact hmem _ w.A₂ (le_sup_right.trans le_sup_left)
        · exact hmem _ w.X hXAY
      · fin_cases i
        exact hmem _ w.Y le_sup_right
    · exact sup_le
        (sup_le (point_le_racl_range (Sum.elim x y) w.A₁ (Sum.inl 0) rfl)
          (point_le_racl_range (Sum.elim x y) w.A₂ (Sum.inl 1) rfl))
        (point_le_racl_range (Sum.elim x y) w.Y (Sum.inr 0) rfl)
  have hyz : racl k (range (Sum.elim y z)) = (w.B ⊔ w.Y.1).1 := by
    refine racl_range_eq_of_le (Sum.elim y z) _ (fun i ↦ ?_) ?_
    · rcases i with i | i
      · fin_cases i
        exact hmem _ w.Y le_sup_right
      · fin_cases i
        · exact hmem _ w.B₁ (le_sup_left.trans le_sup_left)
        · exact hmem _ w.B₂ (le_sup_right.trans le_sup_left)
        · exact hmem _ w.Z hZBY
    · exact sup_le
        (sup_le (point_le_racl_range (Sum.elim y z) w.B₁ (Sum.inr 0) rfl)
          (point_le_racl_range (Sum.elim y z) w.B₂ (Sum.inr 1) rfl))
        (point_le_racl_range (Sum.elim y z) w.Y (Sum.inl 0) rfl)
  have hy : racl k (range y) = w.Y.1.1 := by
    simpa [y] using w.Y.racl_repTuple
  have hC (P : Point k K) (hP : P.1 ≤ w.C) : P.rep ∈ racl k (range v) := by
    rw [hv]
    exact hmem _ P (hP.trans (hCAB.trans le_sup_left))
  exact ⟨trdeg_of_closed_span v hv h5, trdeg_of_closed_span y hy w.Y.rankEq_one,
    trdeg_of_closed_span (Sum.elim x y) hxy h3A, trdeg_of_closed_span (Sum.elim y z) hyz h3B,
    hC w.C₁ le_sup_left, hC w.C₂ le_sup_right⟩

/-- **Ranks of the parameter family of (8.6).** For `x = (a₁, a₂, b₁, b₂)`, `y = (c₁, c₂)` and
`z = (X, Z)`, the joint tuple has rank five, the middle rank two, the parameter locus rank four
and the `C`-family locus rank three, so `5 + 2 = 4 + 3`; the representative of `Y` is algebraic
over the joint tuple. -/
private theorem Psi.parameter_family_ranks (hw : w.Psi) :
    let x : Fin 4 → K := ![w.A₁.rep, w.A₂.rep, w.B₁.rep, w.B₂.rep]
    let y : Fin 2 → K := ![w.C₁.rep, w.C₂.rep]
    let z : Fin 2 → K := ![w.X.rep, w.Z.rep]
    Algebra.trdeg k (adjoin k (range (Sum.elim (Sum.elim x y) z))) = 5 ∧
      Algebra.trdeg k (adjoin k (range y)) = 2 ∧
      Algebra.trdeg k (adjoin k (range (Sum.elim x y))) = 4 ∧
      Algebra.trdeg k (adjoin k (range (Sum.elim y z))) = 3 ∧
      w.Y.rep ∈ racl k (range (Sum.elim (Sum.elim x y) z)) := by
  intro x y z
  have hmem (T : ClosedIF k K) (P : Point k K) (h : P.1 ≤ T) : P.rep ∈ T.1 :=
    ClosedIF.le_iff.1 h P.mem_rep
  have hXAB : ¬ w.X.1 ≤ w.A ⊔ w.B := fun h ↦ hw.X_notLe (h.trans le_sup_left)
  have hXC : ¬ w.X.1 ≤ w.C := fun h ↦ hw.X_notLe (h.trans le_sup_right)
  have hYAB : ¬ w.Y.1 ≤ w.A ⊔ w.B := fun h ↦ hw.Y_notLe (h.trans le_sup_left)
  have h5X : RankEq 5 (w.A ⊔ w.B ⊔ w.X.1) := hw.rank_AB.sup_point_of_not_le hXAB
  have h5Y : RankEq 5 (w.A ⊔ w.B ⊔ w.Y.1) := hw.rank_AB.sup_point_of_not_le hYAB
  have h3 : RankEq 3 (w.C ⊔ w.X.1) := (Psi.rankEq_C hw).sup_point_of_not_le hXC
  have hXAY : w.X.1 ≤ w.A ⊔ w.Y.1 := hw.X_le
  have hZCX : w.Z.1 ≤ w.C ⊔ w.X.1 := hw.Z_le.trans inf_le_right
  have hCAB : w.C ≤ w.A ⊔ w.B := by
    have h := RankEq.eq_of_le le_sup_left hw.rank_AB hw.rank_ABC
    rw [h]
    exact le_sup_right
  let v := Sum.elim (Sum.elim x y) z
  have hv : racl k (range v) = (w.A ⊔ w.B ⊔ w.X.1).1 := by
    refine racl_range_eq_of_le v _ (fun i ↦ ?_) ?_
    · rcases i with (i | i) | i
      · fin_cases i
        · exact hmem _ w.A₁ (le_sup_left.trans (le_sup_left.trans le_sup_left))
        · exact hmem _ w.A₂ (le_sup_right.trans (le_sup_left.trans le_sup_left))
        · exact hmem _ w.B₁ (le_sup_left.trans (le_sup_right.trans le_sup_left))
        · exact hmem _ w.B₂ (le_sup_right.trans (le_sup_right.trans le_sup_left))
      · fin_cases i
        · exact hmem _ w.C₁ (le_sup_left.trans (hCAB.trans le_sup_left))
        · exact hmem _ w.C₂ (le_sup_right.trans (hCAB.trans le_sup_left))
      · fin_cases i
        · exact hmem _ w.X le_sup_right
        · exact hmem _ w.Z (hZCX.trans (sup_le_sup_right hCAB _))
    · exact sup_le (sup_le
        (sup_le (point_le_racl_range v w.A₁ (Sum.inl (Sum.inl 0)) rfl)
          (point_le_racl_range v w.A₂ (Sum.inl (Sum.inl 1)) rfl))
        (sup_le (point_le_racl_range v w.B₁ (Sum.inl (Sum.inl 2)) rfl)
          (point_le_racl_range v w.B₂ (Sum.inl (Sum.inl 3)) rfl)))
        (point_le_racl_range v w.X (Sum.inr 0) rfl)
  have hxy : racl k (range (Sum.elim x y)) = (w.A ⊔ w.B).1 := by
    refine racl_range_eq_of_le (Sum.elim x y) _ (fun i ↦ ?_) ?_
    · rcases i with i | i
      · fin_cases i
        · exact hmem _ w.A₁ (le_sup_left.trans le_sup_left)
        · exact hmem _ w.A₂ (le_sup_right.trans le_sup_left)
        · exact hmem _ w.B₁ (le_sup_left.trans le_sup_right)
        · exact hmem _ w.B₂ (le_sup_right.trans le_sup_right)
      · fin_cases i
        · exact hmem _ w.C₁ (le_sup_left.trans hCAB)
        · exact hmem _ w.C₂ (le_sup_right.trans hCAB)
    · exact sup_le
        (sup_le (point_le_racl_range (Sum.elim x y) w.A₁ (Sum.inl 0) rfl)
          (point_le_racl_range (Sum.elim x y) w.A₂ (Sum.inl 1) rfl))
        (sup_le (point_le_racl_range (Sum.elim x y) w.B₁ (Sum.inl 2) rfl)
          (point_le_racl_range (Sum.elim x y) w.B₂ (Sum.inl 3) rfl))
  have hyz : racl k (range (Sum.elim y z)) = (w.C ⊔ w.X.1).1 := by
    refine racl_range_eq_of_le (Sum.elim y z) _ (fun i ↦ ?_) ?_
    · rcases i with i | i
      · fin_cases i
        · exact hmem _ w.C₁ (le_sup_left.trans le_sup_left)
        · exact hmem _ w.C₂ (le_sup_right.trans le_sup_left)
      · fin_cases i
        · exact hmem _ w.X le_sup_right
        · exact hmem _ w.Z hZCX
    · exact sup_le
        (sup_le (point_le_racl_range (Sum.elim y z) w.C₁ (Sum.inl 0) rfl)
          (point_le_racl_range (Sum.elim y z) w.C₂ (Sum.inl 1) rfl))
        (point_le_racl_range (Sum.elim y z) w.X (Sum.inr 0) rfl)
  have hy : racl k (range y) = w.C.1 := by
    refine racl_range_eq_of_le y _ (fun i ↦ ?_) ?_
    · fin_cases i
      · exact hmem _ w.C₁ le_sup_left
      · exact hmem _ w.C₂ le_sup_right
    · exact sup_le (point_le_racl_range y w.C₁ 0 rfl) (point_le_racl_range y w.C₂ 1 rfl)
  -- `Y` lies in the joint closure: both joins with `A ∨ B` have rank five.
  have hY : w.Y.rep ∈ racl k (range v) := by
    have hle : w.A ⊔ w.B ⊔ w.X.1 ≤ w.A ⊔ w.B ⊔ w.Y.1 :=
      sup_le le_sup_left (hXAY.trans (sup_le_sup_right le_sup_left _))
    have heq := RankEq.eq_of_le hle h5X h5Y
    rw [hv, heq]
    exact hmem _ w.Y le_sup_right
  exact ⟨trdeg_of_closed_span v hv h5X, trdeg_of_closed_span y hy (Psi.rankEq_C hw),
    trdeg_of_closed_span (Sum.elim x y) hxy hw.rank_AB,
    trdeg_of_closed_span (Sum.elim y z) hyz h3, hY⟩

/-- **The actual (8.6) family incidence components.** The source family, the fibre product of
the loci of `(α, X, Y)` and `(β, Y, Z)` over `Y`, and the parameter family, the fibre product of
the loci of `(α, β, γ)` and `(γ, X, Z)` over `γ`, are components of their literal incidence loci,
both of dimension five; the parameter locus has dimension four and the `C`-family locus has
dimension three. Only the actual Ψ witness is assumed, over arbitrary fields. The dense common
cover and its finite function fields are separate clauses. -/
theorem Psi.parameter_family_components (hw : w.Psi) :
    let x : Fin 3 → K := ![w.A₁.rep, w.A₂.rep, w.X.rep]
    let y : Fin 1 → K := ![w.Y.rep]
    let z : Fin 3 → K := ![w.B₁.rep, w.B₂.rep, w.Z.rep]
    let p : Fin 4 → K := ![w.A₁.rep, w.A₂.rep, w.B₁.rep, w.B₂.rep]
    let q : Fin 2 → K := ![w.C₁.rep, w.C₂.rep]
    let r : Fin 2 → K := ![w.X.rep, w.Z.rep]
    idealOf k (Sum.elim (Sum.elim x y) z) ∈
      (Ideal.map (rename (Sum.inl : Fin 3 ⊕ Fin 1 → (Fin 3 ⊕ Fin 1) ⊕ Fin 3) :
          MvPolynomial (Fin 3 ⊕ Fin 1) k →ₐ[k]
            MvPolynomial ((Fin 3 ⊕ Fin 1) ⊕ Fin 3) k) (idealOf k (Sum.elim x y)) ⊔
        Ideal.map (rename (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr :
          Fin 1 ⊕ Fin 3 → (Fin 3 ⊕ Fin 1) ⊕ Fin 3) :
          MvPolynomial (Fin 1 ⊕ Fin 3) k →ₐ[k]
            MvPolynomial ((Fin 3 ⊕ Fin 1) ⊕ Fin 3) k) (idealOf k (Sum.elim y z))).minimalPrimes ∧
    idealOf k (Sum.elim (Sum.elim p q) r) ∈
      (Ideal.map (rename (Sum.inl : Fin 4 ⊕ Fin 2 → (Fin 4 ⊕ Fin 2) ⊕ Fin 2) :
          MvPolynomial (Fin 4 ⊕ Fin 2) k →ₐ[k]
            MvPolynomial ((Fin 4 ⊕ Fin 2) ⊕ Fin 2) k) (idealOf k (Sum.elim p q)) ⊔
        Ideal.map (rename (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr :
          Fin 2 ⊕ Fin 2 → (Fin 4 ⊕ Fin 2) ⊕ Fin 2) :
          MvPolynomial (Fin 2 ⊕ Fin 2) k →ₐ[k]
            MvPolynomial ((Fin 4 ⊕ Fin 2) ⊕ Fin 2) k) (idealOf k (Sum.elim q r))).minimalPrimes ∧
    ringKrullDim (MvPolynomial ((Fin 3 ⊕ Fin 1) ⊕ Fin 3) k ⧸
      idealOf k (Sum.elim (Sum.elim x y) z)) = 5 ∧
    ringKrullDim (MvPolynomial ((Fin 4 ⊕ Fin 2) ⊕ Fin 2) k ⧸
      idealOf k (Sum.elim (Sum.elim p q) r)) = 5 ∧
    ringKrullDim (MvPolynomial (Fin 4 ⊕ Fin 2) k ⧸
      idealOf k (Sum.elim p q)) = 4 ∧
    ringKrullDim (MvPolynomial (Fin 2 ⊕ Fin 2) k ⧸
      idealOf k (Sum.elim q r)) = 3 := by
  let x : Fin 3 → K := ![w.A₁.rep, w.A₂.rep, w.X.rep]
  let y : Fin 1 → K := ![w.Y.rep]
  let z : Fin 3 → K := ![w.B₁.rep, w.B₂.rep, w.Z.rep]
  let p : Fin 4 → K := ![w.A₁.rep, w.A₂.rep, w.B₁.rep, w.B₂.rep]
  let q : Fin 2 → K := ![w.C₁.rep, w.C₂.rep]
  let r : Fin 2 → K := ![w.X.rep, w.Z.rep]
  obtain ⟨hs, hy, hxy, hyz, -, -⟩ := Psi.source_family_ranks hw
  obtain ⟨ht, hq, hpq, hqr, -⟩ := Psi.parameter_family_ranks hw
  have hsource := jointIdeal_minimal_of_rank (k := k) x y z
    (by rw [hs, hy, hxy, hyz]; norm_num)
  have htarget := jointIdeal_minimal_of_rank (k := k) p q r
    (by rw [ht, hq, hpq, hqr]; norm_num)
  exact ⟨hsource, htarget, tuple_dimension_eq _ hs, tuple_dimension_eq _ ht,
    tuple_dimension_eq _ hpq, tuple_dimension_eq _ hqr⟩

/-- **A common finite function-field cover of the two (8.6) family components.** Put
`W = (a₁, a₂, b₁, b₂, c₁, c₂, X, Y, Z)`. Its coordinate-forgetting maps `gS`, `gT`, `gM`, `gΓ`
select the source joint tuple, the parameter joint tuple, the parameter tuple `(α, β, γ)` and the
`C`-family tuple `(γ, X, Z)`. The projections from the locus of `W` to these four loci are dense,
and the field generated by `W` is a finite extension of the function fields of both joint
components under the canonical inclusions. Only the actual Ψ witness is assumed, over arbitrary
fields. This is a finite function-field cover; no finite morphism of affine schemes,
normalization, common normal cover or statement about all components is asserted. -/
theorem Psi.family_common_function_field_cover (hw : w.Psi) :
    let x : Fin 3 → K := ![w.A₁.rep, w.A₂.rep, w.X.rep]
    let y : Fin 1 → K := ![w.Y.rep]
    let z : Fin 3 → K := ![w.B₁.rep, w.B₂.rep, w.Z.rep]
    let p : Fin 4 → K := ![w.A₁.rep, w.A₂.rep, w.B₁.rep, w.B₂.rep]
    let q : Fin 2 → K := ![w.C₁.rep, w.C₂.rep]
    let r : Fin 2 → K := ![w.X.rep, w.Z.rep]
    let W : Fin 9 → K :=
      ![w.A₁.rep, w.A₂.rep, w.B₁.rep, w.B₂.rep, w.C₁.rep, w.C₂.rep, w.X.rep, w.Y.rep, w.Z.rep]
    let gS : (Fin 3 ⊕ Fin 1) ⊕ Fin 3 → Fin 9 := Sum.elim (Sum.elim ![0, 1, 6] ![7]) ![2, 3, 8]
    let gT : (Fin 4 ⊕ Fin 2) ⊕ Fin 2 → Fin 9 := Sum.elim (Sum.elim ![0, 1, 2, 3] ![4, 5]) ![6, 8]
    let gM : Fin 4 ⊕ Fin 2 → Fin 9 := Sum.elim ![0, 1, 2, 3] ![4, 5]
    let gΓ : Fin 2 ⊕ Fin 2 → Fin 9 := Sum.elim ![4, 5] ![6, 8]
    ∃ (hS : W ∘ gS = Sum.elim (Sum.elim x y) z) (hT : W ∘ gT = Sum.elim (Sum.elim p q) r)
      (hM : W ∘ gM = Sum.elim p q) (hΓ : W ∘ gΓ = Sum.elim q r),
      DenseRange (PrimeSpectrum.comap (Ideal.quotientMapₐ (idealOf k W) (rename gS)
        (idealOf_eq_comap_rename hS).le).toRingHom) ∧
      DenseRange (PrimeSpectrum.comap (Ideal.quotientMapₐ (idealOf k W) (rename gT)
        (idealOf_eq_comap_rename hT).le).toRingHom) ∧
      DenseRange (PrimeSpectrum.comap (Ideal.quotientMapₐ (idealOf k W) (rename gM)
        (idealOf_eq_comap_rename hM).le).toRingHom) ∧
      DenseRange (PrimeSpectrum.comap (Ideal.quotientMapₐ (idealOf k W) (rename gΓ)
        (idealOf_eq_comap_rename hΓ).le).toRingHom) ∧
      FiniteDimensional (adjoin k (range (Sum.elim (Sum.elim x y) z)))
        (extendScalars (adjoin.mono k (range (Sum.elim (Sum.elim x y) z)) (range W)
          (Set.range_subset_iff.2 fun i ↦ ⟨gS i, congrFun hS i⟩))) ∧
      FiniteDimensional (adjoin k (range (Sum.elim (Sum.elim p q) r)))
        (extendScalars (adjoin.mono k (range (Sum.elim (Sum.elim p q) r)) (range W)
          (Set.range_subset_iff.2 fun i ↦ ⟨gT i, congrFun hT i⟩))) := by
  intro x y z p q r W gS gT gM gΓ
  obtain ⟨-, -, -, -, hc₁, hc₂⟩ := Psi.source_family_ranks hw
  obtain ⟨-, -, -, -, hY⟩ := Psi.parameter_family_ranks hw
  have hS : W ∘ gS = Sum.elim (Sum.elim x y) z := by
    funext i
    rcases i with (i | i) | i <;> fin_cases i <;> rfl
  have hT : W ∘ gT = Sum.elim (Sum.elim p q) r := by
    funext i
    rcases i with (i | i) | i <;> fin_cases i <;> rfl
  have hM : W ∘ gM = Sum.elim p q := by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  have hΓ : W ∘ gΓ = Sum.elim q r := by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  -- Every coordinate of `W` is algebraic over each joint tuple.
  have hbS : ∀ j, W j ∈ racl k (range (Sum.elim (Sum.elim x y) z)) := by
    intro j
    fin_cases j
    · exact subset_racl k _ ⟨Sum.inl (Sum.inl 0), rfl⟩
    · exact subset_racl k _ ⟨Sum.inl (Sum.inl 1), rfl⟩
    · exact subset_racl k _ ⟨Sum.inr 0, rfl⟩
    · exact subset_racl k _ ⟨Sum.inr 1, rfl⟩
    · exact hc₁
    · exact hc₂
    · exact subset_racl k _ ⟨Sum.inl (Sum.inl 2), rfl⟩
    · exact subset_racl k _ ⟨Sum.inl (Sum.inr 0), rfl⟩
    · exact subset_racl k _ ⟨Sum.inr 2, rfl⟩
  have hbT : ∀ j, W j ∈ racl k (range (Sum.elim (Sum.elim p q) r)) := by
    intro j
    fin_cases j
    · exact subset_racl k _ ⟨Sum.inl (Sum.inl 0), rfl⟩
    · exact subset_racl k _ ⟨Sum.inl (Sum.inl 1), rfl⟩
    · exact subset_racl k _ ⟨Sum.inl (Sum.inl 2), rfl⟩
    · exact subset_racl k _ ⟨Sum.inl (Sum.inl 3), rfl⟩
    · exact subset_racl k _ ⟨Sum.inl (Sum.inr 0), rfl⟩
    · exact subset_racl k _ ⟨Sum.inl (Sum.inr 1), rfl⟩
    · exact subset_racl k _ ⟨Sum.inr 0, rfl⟩
    · exact hY
    · exact subset_racl k _ ⟨Sum.inr 1, rfl⟩
  exact ⟨hS, hT, hM, hΓ, locusProjection_dense hS, locusProjection_dense hT,
    locusProjection_dense hM, locusProjection_dense hΓ,
    finite_field_cover _ W (Set.range_subset_iff.2 fun i ↦ ⟨gS i, congrFun hS i⟩) hbS,
    finite_field_cover _ W (Set.range_subset_iff.2 fun i ↦ ⟨gT i, congrFun hT i⟩) hbT⟩

end QWitness

end AclGeom
