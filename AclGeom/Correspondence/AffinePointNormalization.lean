/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import AclGeom.Correspondence.AffineLocusCommutation
import Mathlib.Combinatorics.Pigeonhole
import AclGeom.Correspondence.FiniteCurveLoci
import AclGeom.Correspondence.AffineRelocation
import AclGeom.Correspondence.DifferenceCocycle
import AclGeom.Correspondence.BaseChange

/-!
# Normalizing the point `P` from a supplied fresh input family

The meet-elimination producer of the corrected blueprint Lemma `affine-grid-extraction` (#27).
Let `a, b, x, c` be independent, `p ∈ acl(a, b) \ acl(a)`, `δ ∈ acl(a, x) ∩ acl(p, a x + b)`
outside `acl(a)`, and `f ∈ acl(c, δ) ∩ acl(a c, x)` outside `acl(a c)`.  Over algebraically closed
`k` and `K`:

* `racl_normalized_P_of_supplied_fresh_inputs`: there is a prime equation `F` of the multiplier
  curve of `(a c, x)` over `k(f)`, fixed before any input choice, such that every family of
  `2 · totalDegree F + 1` inputs fresh over `a, b, x, c` and each other yields a constant `κ ∈ k`
  with `acl(p) = acl(b + (a - 1) κ)`.

The proof constructs literal fixed-five relocations from the inputs, derives the sequential
freshness of their multipliers, colours the multiplier points by the degree-bounded curve loci
over one common relatively closed field, selects an equal-colour triple, and derives its pairwise
difference cocycles, its concurrence and a common centre algebraic over `k`.  The centre is then
a constant in `k`, and the actual joint vanishing ideal transports the relocated normalization of
`P` back to the original presentation.  The same producer serves the reciprocal `Q` side with
`(a, b, x, c, p, δ, f) = (c, d, b, (a c)⁻¹, q, g, h⁻¹)`.

**Status:** conditional `P` normalization proved for supplied fresh inputs (#27, P3a).
Actual PRIVATE consumers derive reciprocal `Q` normalization and the nested two-family
`P`/`D,F,R`/`Q` chain under explicit base/ambient algebraic closedness and raw non-memberships.
Both original prime curves precede all corresponding supplied input choices. Input existence
(which may fail at small transcendence degree), ambient enlargement/descent, the remaining
`E,G,H,I` meets, the combined generator presentation, the initial action chart, extraction
and completeness remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open MvPolynomial IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A scale outside a relatively closed coefficient field gives the actual generic dependent
multiplier pair over that field; every coefficient membership is explicit. -/
private theorem generic_multiplier_pair (S : Set K) {a c x f : K}
    (ha : a ∈ racl k S) (ha0 : a ≠ 0) (hf : f ∈ racl k S)
    (hc : c ∉ racl k S) (hx : x ∈ racl k ({a * c, f} : Set K)) :
    Transcendental ↥(racl k S) (a * c) ∧ x ∈ racl ↥(racl k S) ({a * c} : Set K) := by
  have hm : Transcendental ↥(racl k S) (a * c) := by
    intro halg
    have hmem : a * c ∈ racl k (racl k S : Set K) := by
      rw [mem_racl_iff, adjoin_self]
      exact halg
    rw [racl_racl] at hmem
    have h := mul_mem hmem (inv_mem ha)
    have heq : (a * c) * a⁻¹ = c := by
      rw [mul_comm a c, mul_inv_cancel_right₀ ha0]
    rw [heq] at h
    exact hc h
  have hf' : f ∈ racl ↥(racl k S) ({a * c} : Set K) :=
    (racl ↥(racl k S) ({a * c} : Set K)).algebraMap_mem ⟨f, hf⟩
  have hx' := racl_subset_racl_base (racl k S) ({a * c, f} : Set K) hx
  refine ⟨hm, racl_le_of_subset_racl ?_ hx'⟩
  exact Set.insert_subset_iff.2 ⟨subset_racl _ _ rfl, Set.singleton_subset_iff.2 hf'⟩

/-- A supplied fresh literal-relocation family has genuine degree-bounded curve colors over ONE
final relatively closed coefficient field. No ambient freshness existence is assumed implicitly. -/
private theorem colors_of_fresh_literal_relocations {a b x c p δ f : K}
    (F : MvPolynomial (Fin 2) ↥(adjoin k ({f} : Set K))) (hF : Prime F)
    (hspan : idealOf ↥(adjoin k ({f} : Set K)) ![a * c, x] = Ideal.span {F})
    (a' b' x' : ℕ → K) (n : ℕ)
    (hind : AlgebraicIndependent k ![a, b, x, c])
    (hfm : f ∈ racl k ({a * c, x} : Set K)) (hfu : f ∉ racl k ({a * c} : Set K))
    (hfresh : ∀ i < n, a' i ∉ racl k ({a, b, x, c} ∪ a' '' Set.Iio i))
    (hJ : ∀ i < n, idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a' i, b' i, x' i]) =
      idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x])) :
    let L := racl k ({a, f} ∪ a' '' Set.Iio n)
    ∃ S : Finset (Ideal (MvPolynomial (Fin 2) ↥L)), S.card ≤ F.totalDegree ∧
      ∀ i < n, idealOf ↥L ![a' i * c, x' i] ∈ S := by
  let T : Set K := {a, f} ∪ a' '' Set.Iio n
  let L := racl k T
  let E := adjoin k ({f} : Set K)
  change ∃ S : Finset (Ideal (MvPolynomial (Fin 2) ↥L)), S.card ≤ F.totalDegree ∧
    ∀ i < n, idealOf ↥L ![a' i * c, x' i] ∈ S
  have hc : c ∉ L := scale_notMem_racl_of_fresh_multipliers hind hfm hfu hfresh
  have hfL : f ∈ L := subset_racl k T (by simp [T])
  have hEL : E ≤ L := adjoin_le_iff.2 (Set.singleton_subset_iff.2 hfL)
  let : Algebra ↥E ↥L := (IntermediateField.inclusion hEL).toAlgebra
  let : IsScalarTower ↥E ↥L K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let G : MvPolynomial (Fin 2) ↥L := MvPolynomial.map (algebraMap ↥E ↥L) F
  have hG : G ≠ 0 := by
    intro h
    exact hF.ne_zero ((MvPolynomial.map_injective _ (algebraMap ↥E ↥L).injective)
      (h.trans (map_zero _).symm))
  have hdeg : G.totalDegree = F.totalDegree := by
    classical
    simp only [G, MvPolynomial.totalDegree,
      MvPolynomial.support_map_of_injective F (algebraMap ↥E ↥L).injective]
  obtain ⟨S, hcard, hS⟩ := exists_curve_ideal_colors ↥L K G hG
  refine ⟨S, hdeg ▸ hcard, ?_⟩
  intro i hi
  have haL : a' i ∈ L := subset_racl k T (Set.mem_union_right _ ⟨i, hi, rfl⟩)
  have ha0 : a' i ≠ 0 := by
    intro h
    apply hfresh i hi
    rw [h]
    exact zero_mem _
  obtain ⟨_, _, _, hxi⟩ := affine_multiplier_curve_of_joint_ideal (hJ i hi) hfm hfu
  obtain ⟨hm, hx⟩ := generic_multiplier_pair T haL ha0 hfL hc hxi
  have hzero : MvPolynomial.aeval ![a' i * c, x' i] G = 0 := by
    obtain ⟨Fi, _, hold, hnew⟩ := exists_prime_multiplier_curve_of_joint_ideal
      hind (hJ i hi) hfm hfu
    have hmem : F ∈ idealOf ↥E ![a' i * c, x' i] := by
      rw [hnew.trans hold.symm, hspan]
      exact Ideal.subset_span rfl
    have heval := (mem_idealOf_iff ↥E).1 hmem
    simpa only [G, MvPolynomial.aeval_def, MvPolynomial.eval₂_map,
      ← IsScalarTower.algebraMap_eq] using heval
  exact hS _ _ hm hx hzero

/-- Upfront supplied fresh inputs construct literal relocations with sequentially fresh outputs.
Their controlled algebraicity supplies the earlier-output inclusion, with no recursion oracle. -/
private theorem constructed_fresh_literal_relocations [IsAlgClosed K] {a b x c p δ f : K}
    (hind : AlgebraicIndependent k ![a, b, x, c])
    (hp : p ∈ racl k ({a, b} : Set K)) (hpa : p ∉ racl k ({a} : Set K))
    (hδx : δ ∈ racl k ({a, x} : Set K)) (hδy : δ ∈ racl k ({p, a * x + b} : Set K))
    (hf : f ∈ racl k ({c, δ} : Set K)) (t : ℕ → K) (n : ℕ)
    (ht : ∀ i < n, t i ∉ racl k ({a, b, x, c} ∪ t '' Set.Iio i)) :
    ∃ a' b' x' : ℕ → K,
      (∀ i < n, a' i ∉ racl k ({a, b, x, c} ∪ a' '' Set.Iio i)) ∧
      ∀ i < n,
        idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a' i, b' i, x' i]) =
          idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x]) ∧
        a' i ∈ racl k ({p, a * x + b, c, t i} : Set K) ∧
        p ∈ racl k ({a' i, b' i} : Set K) ∧ δ ∈ racl k ({a' i, x' i} : Set K) ∧
        a' i * x' i + b' i = a * x + b := by
  classical
  have hpyc : ({p, a * x + b, c} : Set K) ⊆ racl k ({a, b, x, c} : Set K) := by
    have ha : a ∈ racl k ({a, b, x, c} : Set K) := subset_racl k _ (by simp)
    have hb : b ∈ racl k ({a, b, x, c} : Set K) := subset_racl k _ (by simp)
    have hx : x ∈ racl k ({a, b, x, c} : Set K) := subset_racl k _ (by simp)
    have hc : c ∈ racl k ({a, b, x, c} : Set K) := subset_racl k _ (by simp)
    have hp4 : p ∈ racl k ({a, b, x, c} : Set K) :=
      racl_le_of_subset_racl (Set.insert_subset_iff.2 ⟨ha, Set.singleton_subset_iff.2 hb⟩) hp
    exact Set.insert_subset_iff.2 ⟨hp4, Set.insert_subset_iff.2
      ⟨add_mem (mul_mem ha hx) hb, Set.singleton_subset_iff.2 hc⟩⟩
  have H : ∀ i : ℕ, ∃ a' b' x' : K, i < n →
      idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a', b', x']) =
        idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x]) ∧
      a' ∈ racl k ({p, a * x + b, c, t i} : Set K) ∧
      a' ∉ racl k ({a, b, x, c} ∪ t '' Set.Iio i) ∧
      p ∈ racl k ({a', b'} : Set K) ∧ δ ∈ racl k ({a', x'} : Set K) ∧
      a' * x' + b' = a * x + b := by
    intro i
    by_cases hi : i < n
    · obtain ⟨a', b', x', h⟩ := exists_affine_relocation_fresh_over
        (t '' Set.Iio i) hind hp hpa hδx hδy hf (ht i hi)
      exact ⟨a', b', x', fun _ ↦ h⟩
    · exact ⟨0, 0, 0, fun h ↦ (hi h).elim⟩
  choose a' b' x' H using H
  refine ⟨a', b', x', ?_, fun i hi ↦ ?_⟩
  · intro i hi hbad
    refine (H i hi).2.2.1 (racl_le_of_subset_racl ?_ hbad)
    refine Set.union_subset (fun z hz ↦ subset_racl k _ (Set.mem_union_left _ hz)) ?_
    rintro _ ⟨j, hj, rfl⟩
    have hpyci : ({p, a * x + b, c} : Set K) ⊆
        racl k ({a, b, x, c} ∪ t '' Set.Iio i) :=
      fun z hz ↦ racl_mono Set.subset_union_left (hpyc hz)
    refine racl_le_of_subset_racl ?_ (H j (lt_trans hj hi)).2.1
    exact Set.insert_subset_iff.2 ⟨hpyci (by simp), Set.insert_subset_iff.2
      ⟨hpyci (by simp), Set.insert_subset_iff.2
        ⟨hpyci (by simp), Set.singleton_subset_iff.2
          (subset_racl k _ (Set.mem_union_right _ ⟨j, hj, rfl⟩))⟩⟩⟩
  · exact ⟨(H i hi).1, (H i hi).2.1, (H i hi).2.2.2⟩

/-- One original prime equation is chosen before ALL supplied ambient-input families. Actual
relocation construction yields sequential freshness, generic colors and original-a cocycles over
ONE final coefficient field. The extra delta non-membership needed by L1a is explicit. -/
private theorem constructed_fresh_literal_colored_family [IsAlgClosed K] {a b x c p δ f : K}
    (hind : AlgebraicIndependent k ![a, b, x, c])
    (hp : p ∈ racl k ({a, b} : Set K)) (hpa : p ∉ racl k ({a} : Set K))
    (hδx : δ ∈ racl k ({a, x} : Set K)) (hδa : δ ∉ racl k ({a} : Set K))
    (hδy : δ ∈ racl k ({p, a * x + b} : Set K)) (hf : f ∈ racl k ({c, δ} : Set K))
    (hfm : f ∈ racl k ({a * c, x} : Set K)) (hfu : f ∉ racl k ({a * c} : Set K)) :
    ∃ F : MvPolynomial (Fin 2) ↥(adjoin k ({f} : Set K)), Prime F ∧
      idealOf ↥(adjoin k ({f} : Set K)) ![a * c, x] = Ideal.span {F} ∧
      ∀ (n : ℕ) (t : ℕ → K),
        (∀ i < n, t i ∉ racl k ({a, b, x, c} ∪ t '' Set.Iio i)) →
        ∃ a' b' x' : ℕ → K,
          (∀ i < n, a' i ∉ racl k ({a, b, x, c} ∪ a' '' Set.Iio i)) ∧
          (∀ i < n, idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a' i, b' i, x' i]) =
            idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x])) ∧
          (∀ i < n, p ∈ racl k ({a' i, b' i} : Set K)) ∧
          (∀ i < n, δ ∈ racl k ({a' i, x' i} : Set K)) ∧
          (∀ i < n, a' i * x' i + b' i = a * x + b) ∧
          let L := racl k ({a, f} ∪ a' '' Set.Iio n)
          (∀ i < n, b - b' i ∈ L) ∧
          ∃ S : Finset (Ideal (MvPolynomial (Fin 2) ↥L)), S.card ≤ F.totalDegree ∧
            ∀ i < n, idealOf ↥L ![a' i * c, x' i] ∈ S := by
  obtain ⟨F, hF, hspan, _⟩ := exists_prime_multiplier_curve_of_joint_ideal
    (p := p) (δ := δ) (a' := a) (b' := b) (x' := x) hind rfl hfm hfu
  refine ⟨F, hF, hspan, fun n t ht ↦ ?_⟩
  obtain ⟨a', b', x', hfresh, H⟩ := constructed_fresh_literal_relocations
    hind hp hpa hδx hδy hf t n ht
  have hJ : ∀ i < n, idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a' i, b' i, x' i]) =
      idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x]) := fun i hi ↦ (H i hi).1
  refine ⟨a', b', x', hfresh, hJ, (fun i hi ↦ (H i hi).2.2.1),
    (fun i hi ↦ (H i hi).2.2.2.1), (fun i hi ↦ (H i hi).2.2.2.2), ?_,
    colors_of_fresh_literal_relocations F hF hspan a' b' x' n hind hfm hfu hfresh hJ⟩
  have h3 : AlgebraicIndependent k ![a, b, x] := by
    have heq : (fun i : Fin 3 ↦ (![a, b, x, c] : Fin 4 → K) i.castSucc) =
        ![a, b, x] := by
      funext i
      fin_cases i <;> rfl
    exact heq ▸ hind.comp (fun i : Fin 3 ↦ i.castSucc) (Fin.castSucc_injective 3)
  intro i hi
  have ha3 : a' i ∉ racl k ({a, b, x} : Set K) := by
    intro h
    exact hfresh i hi (racl_mono (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union] at hz ⊢
      tauto) h)
  have hdiff := sub_mem_racl_of_affine_value_eq h3 ha3 hp hpa hδx hδa
    (H i hi).2.2.1 (H i hi).2.2.2.1 (H i hi).2.2.2.2
  have hsub : ({a, a' i} : Set K) ⊆ ({a, f} ∪ a' '' Set.Iio n) :=
    Set.insert_subset_iff.2 ⟨Set.mem_union_left _ (by simp),
      Set.singleton_subset_iff.2 (Set.mem_union_right _ ⟨i, hi, rfl⟩)⟩
  exact racl_mono hsub hdiff

/-- Sequential freshness forces each later/earlier multiplier ratio to be transcendental over
the original base, in every characteristic. This supplies the actual infinite-order scalar. -/
private theorem ratio_transcendental_of_fresh_family (T : Set K) {a' : ℕ → K} {n i j : ℕ}
    (hfresh : ∀ r < n, a' r ∉ racl k (T ∪ a' '' Set.Iio r)) (hij : i < j) (hj : j < n) :
    Transcendental k (a' j / a' i) := by
  have hi : i < n := lt_trans hij hj
  have hai0 : a' i ≠ 0 := by
    intro h
    apply hfresh i hi
    rw [h]
    exact zero_mem _
  intro halg
  have hratio : a' j / a' i ∈ racl k (T ∪ a' '' Set.Iio j) :=
    racl_mono (Set.empty_subset _) (mem_racl_empty_of_isAlgebraic halg)
  have hai : a' i ∈ racl k (T ∪ a' '' Set.Iio j) :=
    subset_racl k _ (Set.mem_union_right _ ⟨i, hij, rfl⟩)
  have hprod := mul_mem hratio hai
  rw [div_mul_cancel₀ _ hai0] at hprod
  exact hfresh j hj hprod

/-- The common affine value and actual same-color ideal give the concrete preserving map. -/
private theorem relocation_map_preserves {L : IntermediateField k K} {ai aj bi bj xi xj c : K}
    (hai : ai ≠ 0) (haj : aj ≠ 0) (hval : aj * xj + bj = ai * xi + bi)
    (hcolor : idealOf ↥L ![aj * c, xj] = idealOf ↥L ![ai * c, xi]) :
    idealOf ↥L ![(aj / ai) * (ai * c), xi / (aj / ai) + (bi - bj) / aj] =
      idealOf ↥L ![ai * c, xi] := by
  have hcoords : ![(aj / ai) * (ai * c), xi / (aj / ai) + (bi - bj) / aj] =
      (![aj * c, xj] : Fin 2 → K) := by
    funext q
    fin_cases q
    · change (aj / ai) * (ai * c) = aj * c
      rw [← mul_assoc, div_mul_cancel₀ _ hai]
    · change xi / (aj / ai) + (bi - bj) / aj = xj
      field_simp [haj]
      linear_combination hval.symm
  rw [hcoords]
  exact hcolor

/-- Three genuine same-color presentations have the same affine intersection center.
All preserving maps and ratio transcendence are derived from the actual relocation data. -/
private theorem same_color_common_center (T : Set K) {a' b' x' : ℕ → K} {n i j r : ℕ} {b c : K}
    {L : IntermediateField k K}
    (hfresh : ∀ q < n, a' q ∉ racl k (T ∪ a' '' Set.Iio q))
    (hij : i < j) (hir : i < r) (hj : j < n) (hr : r < n)
    (ha : ∀ q < n, a' q ∈ L) (hd : ∀ q < n, b - b' q ∈ L)
    (hvj : a' j * x' j + b' j = a' i * x' i + b' i)
    (hvr : a' r * x' r + b' r = a' i * x' i + b' i)
    (hx : x' i ∈ racl ↥L ({a' i * c} : Set K))
    (hcj : idealOf ↥L ![a' j * c, x' j] = idealOf ↥L ![a' i * c, x' i])
    (hcr : idealOf ↥L ![a' r * c, x' r] = idealOf ↥L ![a' i * c, x' i]) :
    (b' i - b' j) / (a' j - a' i) = (b' i - b' r) / (a' r - a' i) := by
  have hi : i < n := lt_trans hij hj
  have h0 : ∀ q < n, a' q ≠ 0 := by
    intro q hq he
    apply hfresh q hq
    rw [he]
    exact zero_mem _
  have hdiff : ∀ q < n, b' i - b' q ∈ L := by
    intro q hq
    have h := sub_mem (hd q hq) (hd i hi)
    have he : (b - b' q) - (b - b' i) = b' i - b' q := by ring
    rwa [he] at h
  let lam : ↥L := ⟨a' j / a' i, div_mem (ha j hj) (ha i hi)⟩
  let rho : ↥L := ⟨a' r / a' i, div_mem (ha r hr) (ha i hi)⟩
  let nu : ↥L := ⟨(b' i - b' j) / a' j, div_mem (hdiff j hj) (ha j hj)⟩
  let om : ↥L := ⟨(b' i - b' r) / a' r, div_mem (hdiff r hr) (ha r hr)⟩
  have hLam : Transcendental k (lam : K) :=
    ratio_transcendental_of_fresh_family T hfresh hij hj
  have hrho : rho ≠ 0 := by
    intro h
    have he : a' r / a' i = 0 := congrArg Subtype.val h
    exact (div_ne_zero (h0 r hr) (h0 i hi)) he
  have hA : idealOf ↥L ![(lam : K) * (a' i * c), x' i / (lam : K) + (nu : K)] =
      idealOf ↥L ![a' i * c, x' i] :=
    relocation_map_preserves (h0 i hi) (h0 j hj) hvj hcj
  have hB : idealOf ↥L ![(rho : K) * (a' i * c), x' i / (rho : K) + (om : K)] =
      idealOf ↥L ![a' i * c, x' i] :=
    relocation_map_preserves (h0 i hi) (h0 r hr) hvr hcr
  have h := congrArg Subtype.val
    (affine_locus_commutation_balance hx lam nu rho om hLam hrho hA hB)
  change (a' j / a' i) * (a' r / a' i - 1) * ((b' i - b' j) / a' j) =
    (a' r / a' i) * (a' j / a' i - 1) * ((b' i - b' r) / a' r) at h
  have hne : ∀ q < n, i < q → a' q - a' i ≠ 0 := by
    intro q hq hiq he
    apply hfresh q hq
    rw [sub_eq_zero.1 he]
    exact subset_racl k _ (Set.mem_union_right _ ⟨i, hiq, rfl⟩)
  apply (div_eq_div_iff (hne j hj hij) (hne r hr hir)).2
  field_simp [h0 i hi, h0 j hj, h0 r hr] at h
  linear_combination h

/-- An actual degree bound fixed before the family gives an equal-color triple with its least
index as the common base. This is a private consumer bridge, not an ambient existence theorem. -/
private theorem same_color_triple {C : Type*} (color : ℕ → C)
    (S : Finset C) {D n : ℕ} (hD : S.card ≤ D) (hn : 2 * D < n)
    (hc : ∀ i < n, color i ∈ S) :
    ∃ i j r : ℕ, i < j ∧ i < r ∧ j ≠ r ∧ r < n ∧ j < n ∧
      color j = color i ∧ color r = color i := by
  classical
  have hcard : S.card * 2 < (Finset.range n).card := by
    rw [Finset.card_range]
    omega
  obtain ⟨y, _, hF⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.range n) (t := S) (f := color)
    (fun a ha ↦ hc a (Finset.mem_range.1 ha)) hcard
  let F := (Finset.range n).filter fun a ↦ color a = y
  have hFcard : 2 < F.card := hF
  have hne : F.Nonempty := Finset.card_pos.1 (by omega)
  let i := F.min' hne
  have hi : i ∈ F := Finset.min'_mem _ _
  have he : 1 < (F.erase i).card := by
    rw [Finset.card_erase_of_mem hi]
    omega
  obtain ⟨j, hj, r, hr, hjr⟩ := Finset.one_lt_card.1 he
  obtain ⟨hji, hjF⟩ := Finset.mem_erase.1 hj
  obtain ⟨hri, hrF⟩ := Finset.mem_erase.1 hr
  have hij : i < j := lt_of_le_of_ne (Finset.min'_le F j hjF) hji.symm
  have hir : i < r := lt_of_le_of_ne (Finset.min'_le F r hrF) hri.symm
  have hii := Finset.mem_filter.1 hi
  have hjj := Finset.mem_filter.1 hjF
  have hrr := Finset.mem_filter.1 hrF
  exact ⟨i, j, r, hij, hir, hjr, Finset.mem_range.1 hrr.1,
    Finset.mem_range.1 hjj.1, hjj.2.trans hii.2.symm, hrr.2.trans hii.2.symm⟩


/-- Pairwise cocycles and the actual concurrence give a center algebraic over the original base.
The pairwise cocycles are explicit inputs in this PRIVATE bridge until B3 supplies them. -/
private theorem common_center_mem_racl_empty {ai aj ar bi bj br : K}
    (hj : aj ∉ racl k ({ai} : Set K)) (hr : ar ∉ racl k ({ai, aj} : Set K))
    (hdij : bi - bj ∈ racl k ({ai, aj} : Set K))
    (hdir : bi - br ∈ racl k ({ai, ar} : Set K))
    (hdjr : bj - br ∈ racl k ({aj, ar} : Set K))
    (hcenter : (bi - bj) / (aj - ai) = (bi - br) / (ar - ai)) :
    (bi - bj) / (aj - ai) ∈ racl k (∅ : Set K) := by
  let t := (bi - bj) / (aj - ai)
  have h0j : aj - ai ≠ 0 := by
    intro h
    apply hj
    rw [sub_eq_zero.1 h]
    exact subset_racl k _ rfl
  have h0r : ar - ai ≠ 0 := by
    intro h
    apply hr
    rw [sub_eq_zero.1 h]
    exact subset_racl k _ (by simp)
  have h0jr : ar - aj ≠ 0 := by
    intro h
    apply hr
    rw [sub_eq_zero.1 h]
    exact subset_racl k _ (by simp)
  have hjval : t * (aj - ai) = bi - bj := div_mul_cancel₀ _ h0j
  have hrval : t * (ar - ai) = bi - br := by
    change ((bi - bj) / (aj - ai)) * (ar - ai) = bi - br
    rw [hcenter, div_mul_cancel₀ _ h0r]
  have hthird : t = (bj - br) / (ar - aj) := (eq_div_iff h0jr).2 (by
    linear_combination hrval - hjval)
  have pair_mem (u v B C : K) (h : B - C ∈ racl k ({u, v} : Set K)) :
      (B - C) / (v - u) ∈ racl k ({u, v} : Set K) :=
    div_mem h (sub_mem (subset_racl k _ (by simp)) (subset_racl k _ (by simp)))
  have htij : t ∈ racl k ({ai, aj} : Set K) := pair_mem ai aj bi bj hdij
  have htir : t ∈ racl k ({ai, ar} : Set K) := by
    change (bi - bj) / (aj - ai) ∈ racl k ({ai, ar} : Set K)
    rw [hcenter]
    exact pair_mem ai ar bi br hdir
  have htjr : t ∈ racl k ({aj, ar} : Set K) := by
    rw [hthird]
    exact pair_mem aj ar bj br hdjr
  have hti : t ∈ racl k ({ai} : Set K) :=
    mem_racl_of_mem_racl_insert (A := {ai}) (a := aj) (b := ar)
      (by simpa only [Set.pair_comm] using htij)
      (by simpa only [Set.pair_comm] using htir)
      (by simpa only [Set.pair_comm] using hr)
  have htj : t ∈ racl k ({aj} : Set K) :=
    mem_racl_of_mem_racl_insert (A := {aj}) (a := ai) (b := ar) htij
      (by simpa only [Set.pair_comm] using htjr) hr
  exact mem_racl_of_mem_racl_insert (A := ∅) (a := ai) (b := aj)
    (by simpa using hti) (by simpa using htj) (by simpa using hj)

/-- Actual relocation outputs supply all pairwise cocycles, without the original-a parameter. -/
private theorem pairwise_cocycles_of_fresh_family {a b x c p δ f : K} {n : ℕ}
    (hind : AlgebraicIndependent k ![a, b, x])
    (hp : p ∈ racl k ({a, b} : Set K)) (hpa : p ∉ racl k ({a} : Set K))
    (hδ : δ ∈ racl k ({a, x} : Set K)) (hδa : δ ∉ racl k ({a} : Set K))
    (a' b' x' : ℕ → K)
    (hfresh : ∀ q < n, a' q ∉ racl k ({a, b, x, c} ∪ a' '' Set.Iio q))
    (hJ : ∀ q < n, idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a' q, b' q, x' q]) =
      idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x]))
    (hpi : ∀ q < n, p ∈ racl k ({a' q, b' q} : Set K))
    (hδi : ∀ q < n, δ ∈ racl k ({a' q, x' q} : Set K))
    (hval : ∀ q < n, a' q * x' q + b' q = a * x + b) :
    ∀ u v : ℕ, u < v → v < n → b' u - b' v ∈ racl k ({a' u, a' v} : Set K) := by
  intro u v huv hv
  have hu : u < n := lt_trans huv hv
  have hsub : (({a, b, x} : Set K) ∪ {a' u}) ⊆ ({a, b, x, c} ∪ a' '' Set.Iio v) := by
    intro z hz
    rcases hz with hz | hz
    · exact Set.mem_union_left _ (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
        tauto)
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact Set.mem_union_right _ ⟨u, huv, rfl⟩
  have hvfresh : a' v ∉ racl k (({a, b, x} : Set K) ∪ {a' u}) :=
    fun h ↦ hfresh v hv (racl_mono hsub h)
  exact sub_mem_racl_of_two_relocations hind hp hpa hδ hδa (hJ u hu)
    (hpi u hu) (hδi u hu) (hval u hu) (hpi v hv) (hδi v hv) (hval v hv) hvfresh

/-- The actual k-polynomial image transports an already derived shifted-P closure back to
the original presentation. No original-P normal form is assumed. -/
private theorem original_p_of_shifted_joint_ideal {a b x c p δ f ai bi xi : K}
    (hJ : idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![ai, bi, xi]) =
      idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x]))
    (κ : k)
    (hP : racl k ({p} : Set K) =
      racl k ({bi + (ai - 1) * algebraMap k K κ} : Set K)) :
    racl k ({p} : Set K) =
      racl k ({b + (a - 1) * algebraMap k K κ} : Set K) := by
  let u : Fin 2 → MvPolynomial (Fin 5 ⊕ Fin 3) k :=
    ![X (Sum.inl 0), X (Sum.inr 1) + (X (Sum.inr 0) - 1) * C κ]
  have hI := idealOf_aeval_comp_eq_of_idealOf_eq hJ u
  have hi : (fun q ↦ aeval (Sum.elim ![p, a * x + b, δ, c, f] ![ai, bi, xi]) (u q)) =
      ![p, bi + (ai - 1) * algebraMap k K κ] := by
    funext q
    fin_cases q <;> simp [u]
  have ho : (fun q ↦ aeval (Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x]) (u q)) =
      ![p, b + (a - 1) * algebraMap k K κ] := by
    funext q
    fin_cases q <;> simp [u]
  rw [hi, ho] at hI
  have hpm : p ∈ racl k ({bi + (ai - 1) * algebraMap k K κ} : Set K) := by
    rw [← hP]
    exact subset_racl k _ (by simp)
  have hwm : bi + (ai - 1) * algebraMap k K κ ∈ racl k ({p} : Set K) := by
    rw [hP]
    exact subset_racl k _ (by simp)
  have hpold : p ∈ racl k ({b + (a - 1) * algebraMap k K κ} : Set K) := by
    have h : (![p, bi + (ai - 1) * algebraMap k K κ] : Fin 2 → K) 0 ∈
        racl k ((![p, bi + (ai - 1) * algebraMap k K κ] : Fin 2 → K) '' {1}) := by
      simpa using hpm
    have h' := mem_racl_image_of_idealOf_eq k hI h
    simpa using h'
  have hwold : b + (a - 1) * algebraMap k K κ ∈ racl k ({p} : Set K) := by
    have h : (![p, bi + (ai - 1) * algebraMap k K κ] : Fin 2 → K) 1 ∈
        racl k ((![p, bi + (ai - 1) * algebraMap k K κ] : Fin 2 → K) '' {0}) := by
      simpa using hwm
    have h' := mem_racl_image_of_idealOf_eq k hI h
    simpa using h'
  exact racl_singleton_congr hpold hwold

/-- **Normalizing `P` from supplied fresh inputs** (#27).  Over algebraically closed `k` and `K`,
let `a, b, x, c` be independent with the incidences of the points `P`, `D` and `F` of `Ψ`.  The
prime equation `F` of the multiplier curve of `(a c, x)` over `k(f)` is fixed first; then every
family of `2 · totalDegree F + 1` inputs, each fresh over `a, b, x, c` and the earlier inputs,
yields `κ ∈ k` with `acl(p) = acl(b + (a - 1) κ)`. -/
theorem racl_normalized_P_of_supplied_fresh_inputs [IsAlgClosed k] [IsAlgClosed K]
    {a b x c p δ f : K}
    (hind : AlgebraicIndependent k ![a, b, x, c])
    (hp : p ∈ racl k ({a, b} : Set K)) (hpa : p ∉ racl k ({a} : Set K))
    (hδx : δ ∈ racl k ({a, x} : Set K)) (hδa : δ ∉ racl k ({a} : Set K))
    (hδy : δ ∈ racl k ({p, a * x + b} : Set K)) (hf : f ∈ racl k ({c, δ} : Set K))
    (hfm : f ∈ racl k ({a * c, x} : Set K)) (hfu : f ∉ racl k ({a * c} : Set K)) :
    ∃ F : MvPolynomial (Fin 2) ↥(adjoin k ({f} : Set K)), Prime F ∧
      idealOf ↥(adjoin k ({f} : Set K)) ![a * c, x] = Ideal.span {F} ∧
      ∀ (t : ℕ → K),
        (∀ q < 2 * F.totalDegree + 1,
          t q ∉ racl k ({a, b, x, c} ∪ t '' Set.Iio q)) →
        ∃ κ : k, racl k ({p} : Set K) =
          racl k ({b + (a - 1) * algebraMap k K κ} : Set K) := by
  classical
  obtain ⟨F, hF, hspan, H⟩ := constructed_fresh_literal_colored_family
    hind hp hpa hδx hδa hδy hf hfm hfu
  refine ⟨F, hF, hspan, fun t ht ↦ ?_⟩
  let n := 2 * F.totalDegree + 1
  obtain ⟨a', b', x', hfresh, hJ, hpi, hδi, hval, hdiff, S, hD, hcolor⟩ := H n t ht
  let L := racl k ({a, f} ∪ a' '' Set.Iio n)
  let color : ℕ → Ideal (MvPolynomial (Fin 2) ↥L) :=
    fun q ↦ idealOf ↥L ![a' q * c, x' q]
  obtain ⟨i, j, r, hij, hir, hjr, hr, hj, hcj, hcr⟩ :=
    same_color_triple color S hD (by dsimp [n]; omega) hcolor
  have hi : i < n := lt_trans hij hj
  have hcenter : (b' i - b' j) / (a' j - a' i) =
      (b' i - b' r) / (a' r - a' i) := by
    have ha : ∀ q < n, a' q ∈ L :=
      fun q hq ↦ subset_racl k _ (Set.mem_union_right _ ⟨q, hq, rfl⟩)
    have hai0 : a' i ≠ 0 := by
      intro he
      apply hfresh i hi
      rw [he]
      exact zero_mem _
    have hfL : f ∈ L := subset_racl k _ (by simp)
    have hc : c ∉ L := scale_notMem_racl_of_fresh_multipliers hind hfm hfu hfresh
    obtain ⟨_, _, _, hxi⟩ := affine_multiplier_curve_of_joint_ideal (hJ i hi) hfm hfu
    obtain ⟨_, hxL⟩ := generic_multiplier_pair ({a, f} ∪ a' '' Set.Iio n)
      (ha i hi) hai0 hfL hc hxi
    exact same_color_common_center ({a, b, x, c} : Set K) hfresh hij hir hj hr ha hdiff
      ((hval j hj).trans (hval i hi).symm) ((hval r hr).trans (hval i hi).symm) hxL hcj hcr
  have h3 : AlgebraicIndependent k ![a, b, x] := by
    have heq : (fun q : Fin 3 ↦ (![a, b, x, c] : Fin 4 → K) q.castSucc) =
        ![a, b, x] := by
      funext q
      fin_cases q <;> rfl
    exact heq ▸ hind.comp (fun q : Fin 3 ↦ q.castSucc) (Fin.castSucc_injective 3)
  have hpair := pairwise_cocycles_of_fresh_family h3 hp hpa hδx hδa
    a' b' x' hfresh hJ hpi hδi hval
  have hNF2 (u v w : ℕ) (huw : u < w) (hvw : v < w) (hw : w < n) :
      a' w ∉ racl k ({a' u, a' v} : Set K) := by
    have hsub : ({a' u, a' v} : Set K) ⊆ ({a, b, x, c} ∪ a' '' Set.Iio w) :=
      Set.insert_subset_iff.2 ⟨Set.mem_union_right _ ⟨u, huw, rfl⟩,
        Set.singleton_subset_iff.2 (Set.mem_union_right _ ⟨v, hvw, rfl⟩)⟩
    exact fun h ↦ hfresh w hw (racl_mono hsub h)
  have hNF1 (u v : ℕ) (huv : u < v) (hv : v < n) :
      a' v ∉ racl k ({a' u} : Set K) := by
    simpa using hNF2 u u v huv huv hv
  have htcenter : (b' i - b' j) / (a' j - a' i) ∈ racl k (∅ : Set K) := by
    by_cases hjlt : j < r
    · exact common_center_mem_racl_empty (hNF1 i j hij hj) (hNF2 i j r hir hjlt hr)
        (hpair i j hij hj) (hpair i r hir hr) (hpair j r hjlt hr) hcenter
    · have hrlt : r < j := by omega
      rw [hcenter]
      exact common_center_mem_racl_empty (hNF1 i r hir hr) (hNF2 i r j hij hrlt hj)
        (hpair i r hir hr) (hpair i j hij hj) (hpair r j hrlt hj) hcenter.symm
  let θ := (b' i - b' j) / (a' j - a' i)
  have hpai : p ∉ racl k ({a' i} : Set K) := by
    have h : (Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x])
        (Sum.inl (0 : Fin 5)) ∉
        racl k ((Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x]) ''
          {Sum.inr (0 : Fin 3)}) := by
      simpa using hpa
    have h' := notMem_racl_image_of_idealOf_eq k (hJ i hi).symm h
    simpa using h'
  have hpS : p ∈ racl k ({a, b, x, c} ∪ a' '' Set.Iio j) :=
    racl_mono (by
      intro z hz
      apply Set.mem_union_left
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto) hp
  have hNFjaip : a' j ∉ racl k ({a' i, p} : Set K) := by
    have hsub : ({a' i, p} : Set K) ⊆
        racl k ({a, b, x, c} ∪ a' '' Set.Iio j) :=
      Set.insert_subset_iff.2 ⟨subset_racl k _ (Set.mem_union_right _ ⟨i, hij, rfl⟩),
        Set.singleton_subset_iff.2 hpS⟩
    exact fun h ↦ hfresh j hj (racl_le_of_subset_racl hsub h)
  have h0j : a' j - a' i ≠ 0 := by
    intro h
    apply hNF1 i j hij hj
    rw [sub_eq_zero.1 h]
    exact subset_racl k _ (by simp)
  have hconc : b' i + (a' i - 1) * θ = b' j + (a' j - 1) * θ := by
    have hD : θ * (a' j - a' i) = b' i - b' j := div_mul_cancel₀ _ h0j
    linear_combination -hD
  have hP := racl_singleton_eq_of_concurrent htcenter
    (hpi i hi) hpai (hpi j hj) hNFjaip hconc
  obtain ⟨κ, hκ⟩ := mem_range_algebraMap_of_isAlgebraic
    (isAlgebraic_of_mem_racl_empty htcenter)
  have hOriginal : racl k ({p} : Set K) =
      racl k ({b + (a - 1) * algebraMap k K κ} : Set K) :=
    original_p_of_shifted_joint_ideal (hJ i hi) κ (by simpa only [hκ] using hP)
  exact ⟨κ, hOriginal⟩

end

end AclGeom
