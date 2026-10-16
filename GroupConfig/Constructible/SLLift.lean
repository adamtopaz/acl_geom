/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Constructible.CanonicalPresentation
import GroupConfig.Constructible.Equivariance
import GroupConfig.Germ.MoebiusLift
import GroupConfig.Germ.RelativeRank

/-!
# The constructible determinant-one lift of the Hrushovski–Weil action

Let `f₀` be a Hrushovski–Weil datum of bijections whose group `G` acts on a curve, with canonical
base of rank at least two. In a generator `t` of the function field, every member of `G` acts by
a fractional linear transformation. Its determinant-one lifts form a subgroup `Γ` of `SL₂(K)`:
every member has a lift, two lifts differ by a sign, lifts compose in the reversed order, and
`Γ` consists of exactly these lifts. Over a small algebraically closed field `M`, chosen together
with `t`, the constructible presentation of `G` and fresh samples, the set `Γ` is constructible,
and every lift is interalgebraic over `M` with the canonical base of its member
(`GroupConfig.Germ.IsHWBij.exists_constructible_slLift`).

The proof expresses the lifts as a constructible relation on the parameters of the presentation:
the action of `γ` on `t = A / B` is evaluated at generic points of the curve through the chain
relation of the presentation word for `γ⁻¹`, and generic quantification by finite sampling makes
the relation constructible. The rank comparison uses the equivariance of the presentation and
the uniqueness of lifts up to sign.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

This auxiliary action theorem supplies a prerequisite for `lem:affine-action` in
`sources/blueprint.tex`; it does not discharge that original scheme/action statement.

**Status:** the complete constructible lift and canonical-base rank comparison are proved
(#21). The internally chosen field `M` contains the generator coefficients and sampling data;
freshness from the original Ψ witness is not a conclusion. When the ordinary canonical-base
rank is exactly two, `GroupConfig.Germ.IsHWBij.exists_affine_generator` classifies this subgroup
and constructs affine coordinates of the actual K-function field. Original scheme/action and
normal-subgroup producers, algebraization and original-field descent remain obligations.
-/

namespace GroupConfig

open AclGeom IntermediateField Set MvPolynomial LocusFunctionField
open scoped MatrixGroups

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
  [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]

attribute [local instance] isAlgClosed_racl

/-! ### Fractions over small fields -/

omit [IsAlgClosed K] [UniversalDomain k K] in
/-- An element of the function field is a fraction of polynomials over a small algebraically
closed field, with denominator nonzero at every generic point over that field. -/
private theorem exists_fraction_small {ι : Type w} [Finite ι] {v : ι → K}
    (h : LocusFunctionField k v) :
    ∃ N : IntermediateField k K, IsSmall k (N : Set K) ∧
      ∃ A B : MvPolynomial ι N, (∀ y, IsGenericOver N v y → aeval y B ≠ 0) ∧
        h = mk k v (MvPolynomial.map (algebraMap N K) A) /
          mk k v (MvPolynomial.map (algebraMap N K) B) := by
  obtain ⟨C, hC, hfrac⟩ := exists_fraction_of_subset h
  exact ⟨racl k C, (IsSmall.of_finite hC).racl, hfrac _ (subset_racl k C)⟩

/-! ### The lift test -/

section Test

variable {μ ι : Type w} [Finite μ] [Finite ι] {v : ι → K}

/-- The lift test for a parameter `x = (d, m)` at a point `y`: the chain of the word `w` at the
swapped pair of `d` ends at a point `z` with `t(z) (m₁₀ t(y) + m₁₁) = m₀₀ t(y) + m₀₁` for
`t = A / B`, all denominators being nonzero. -/
private def LiftTest (w : Word k (μ ⊕ μ) v v) {N : IntermediateField k K}
    (A B : MvPolynomial ι N) (x : ((μ ⊕ μ) ⊕ (Fin 2 × Fin 2)) → K) (y : ι → K) : Prop :=
  ∃ z : ι → K, w.Chain ((x ∘ Sum.inl) ∘ Sum.swap) y z ∧ aeval z B ≠ 0 ∧ aeval y B ≠ 0 ∧
    x (Sum.inr (1, 0)) * aeval y A + x (Sum.inr (1, 1)) * aeval y B ≠ 0 ∧
    aeval z A * (x (Sum.inr (1, 0)) * aeval y A + x (Sum.inr (1, 1)) * aeval y B) =
      aeval z B * (x (Sum.inr (0, 0)) * aeval y A + x (Sum.inr (0, 1)) * aeval y B)

omit [IsAlgClosed k] [UniversalDomain k K] in
/-- The lift test is constructible over the coefficient field of `A` and `B`. -/
private theorem isConstructibleOver_liftTest (w : Word k (μ ⊕ μ) v v)
    {N : IntermediateField k K} (A B : MvPolynomial ι N) :
    IsConstructibleOver (↥N) {u : (((μ ⊕ μ) ⊕ (Fin 2 × Fin 2)) ⊕ ι) → K |
      LiftTest w A B (u ∘ Sum.inl) (u ∘ Sum.inr)} := by
  -- Coordinates of `((x, y), z)`.
  let ey : ι → (((μ ⊕ μ) ⊕ (Fin 2 × Fin 2)) ⊕ ι) ⊕ ι := Sum.inl ∘ Sum.inr
  let ez : ι → (((μ ⊕ μ) ⊕ (Fin 2 × Fin 2)) ⊕ ι) ⊕ ι := Sum.inr
  let em : Fin 2 × Fin 2 → MvPolynomial ((((μ ⊕ μ) ⊕ (Fin 2 × Fin 2)) ⊕ ι) ⊕ ι) N :=
    fun ij ↦ X (Sum.inl (Sum.inl (Sum.inr ij)))
  let L : MvPolynomial ((((μ ⊕ μ) ⊕ (Fin 2 × Fin 2)) ⊕ ι) ⊕ ι) N :=
    em (1, 0) * rename ey A + em (1, 1) * rename ey B
  let R : MvPolynomial ((((μ ⊕ μ) ⊕ (Fin 2 × Fin 2)) ⊕ ι) ⊕ ι) N :=
    rename ez A * L - rename ez B * (em (0, 0) * rename ey A + em (0, 1) * rename ey B)
  -- The chain part, reindexed.
  let e : ((μ ⊕ μ) ⊕ ι) ⊕ ι → (((μ ⊕ μ) ⊕ (Fin 2 × Fin 2)) ⊕ ι) ⊕ ι :=
    Sum.elim (Sum.elim (fun p ↦ Sum.inl (Sum.inl (Sum.inl (Sum.swap p)))) ey) ez
  have hchain : IsConstructibleOver (↥N)
      ((fun u : ((((μ ⊕ μ) ⊕ (Fin 2 × Fin 2)) ⊕ ι) ⊕ ι) → K ↦ u ∘ e) ⁻¹'
        {v' : ((μ ⊕ μ) ⊕ ι) ⊕ ι → K |
          w.Chain ((v' ∘ Sum.inl) ∘ Sum.inl) ((v' ∘ Sum.inl) ∘ Sum.inr) (v' ∘ Sum.inr)}) :=
    ((Word.isConstructibleOver_chain w).preimage_comp e).extend_base
  refine IsConstructibleOver.exists ?_
  convert hchain.inter ((IsConstructibleOver.polynomial_ne_zero (rename ez B)).inter
    ((IsConstructibleOver.polynomial_ne_zero (rename ey B)).inter
    ((IsConstructibleOver.polynomial_ne_zero L).inter (IsConstructibleOver.polynomial_zero R))))
    using 1
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, aeval_rename, L, R, em,
    map_add, map_mul, map_sub, aeval_X, sub_eq_zero]
  have he1 : ((u ∘ e) ∘ Sum.inl) ∘ Sum.inl = (((u ∘ Sum.inl) ∘ Sum.inl) ∘ Sum.inl) ∘ Sum.swap := by
    funext p
    rfl
  have he2 : ((u ∘ e) ∘ Sum.inl) ∘ Sum.inr = (u ∘ Sum.inl) ∘ Sum.inr := rfl
  have he3 : (u ∘ e) ∘ Sum.inr = u ∘ Sum.inr := rfl
  rw [he1, he2, he3]
  rfl

end Test

/-! ### Values of the action -/

section Values

variable {ι : Type w} [Finite ι] {v : ι → K} {g₀ : Germ k v v} (hw : Germ.IsHW g₀)
  (hv : erk k ∅ (range v) = 1)

omit [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
/-- A constant of `M` has itself as value. -/
private theorem hasValue_const {M : IntermediateField k K} {y : ι → K} {c : K} (hc : c ∈ M) :
    HasValue M y (algebraMap K (LocusFunctionField k v) c) c := by
  have h := hasValue_algebraMap (k := k) (v := v) (M := M) (y := y) le_rfl ⟨c, hc⟩
  rw [IsScalarTower.algebraMap_apply (↥M) K (LocusFunctionField k v)] at h
  exact h

/-- **The lift condition at a generic point.** At a point `y` generic over the field `M` of an
exponent-zero representative `r` of `γ⁻¹`, where `M` contains the coefficients of `t = A / B`
and the entries of `m`, the lift condition is the identity of the values at `y` and `r(y)`. -/
private theorem isMoebiusLift_iff_values {N : IntermediateField k K}
    {A B : MvPolynomial ι N} {t : LocusFunctionField k v}
    (htAB : t = mk k v (MvPolynomial.map (algebraMap N K) A) /
      mk k v (MvPolynomial.map (algebraMap N K) B))
    (γ : ↥hw.prodSubgroup) {r : Representative k K v v} (hr : r.f.e = 0)
    (hrγ : (⟦r⟧ : Germ k v v) = (((γ⁻¹ : ↥hw.prodSubgroup) : (Germ k v v)ˣ) : Germ k v v))
    (hNr : N ≤ r.M) (m : SL(2, K)) (hm : ∀ i j, m i j ∈ r.M) {y : ι → K}
    (hy : IsGenericOver r.M v y) (hBy : aeval y B ≠ 0) (hBz : aeval (r.f.eval y) B ≠ 0) :
    hw.IsMoebiusLift hv t γ m ↔
      (m 1 0 * aeval y A + m 1 1 * aeval y B ≠ 0 ∧
        aeval (r.f.eval y) A * (m 1 0 * aeval y A + m 1 1 * aeval y B) =
          aeval (r.f.eval y) B * (m 0 0 * aeval y A + m 0 1 * aeval y B)) := by
  let A' := MvPolynomial.map (IntermediateField.inclusion hNr).toRingHom A
  let B' := MvPolynomial.map (IntermediateField.inclusion hNr).toRingHom B
  have hmap : ∀ P : MvPolynomial ι N, MvPolynomial.map (algebraMap N K) P =
      MvPolynomial.map (algebraMap r.M K)
        (MvPolynomial.map (IntermediateField.inclusion hNr).toRingHom P) := fun P ↦ by
    rw [MvPolynomial.map_map]
    rfl
  have htAB' : t = mk k v (MvPolynomial.map (algebraMap r.M K) A') /
      mk k v (MvPolynomial.map (algebraMap r.M K) B') := by
    rw [htAB, hmap A, hmap B]
  have hA'y : ∀ u, aeval u A' = aeval u A := fun u ↦ aeval_map_inclusion hNr u A
  have hB'y : ∀ u, aeval u B' = aeval u B := fun u ↦ aeval_map_inclusion hNr u B
  -- Values of the ingredients at `y`.
  have hvt : HasValue r.M y t (aeval y A / aeval y B) :=
    ⟨A', B', by rw [hB'y]; exact hBy, htAB', by rw [hA'y, hB'y]⟩
  have hvγ : HasValue r.M y (hw.functionFieldAction hv γ t)
      (aeval (r.f.eval y) A / aeval (r.f.eval y) B) :=
    hw.hasValue_functionFieldAction hv γ hr hrγ le_rfl hy
      ⟨A', B', by rw [hB'y]; exact hBz, htAB', by rw [hA'y, hB'y]⟩
  have hvD : HasValue r.M y (algebraMap K _ (m 1 0) * t + algebraMap K _ (m 1 1))
      (m 1 0 * (aeval y A / aeval y B) + m 1 1) :=
    ((hasValue_const (hm 1 0)).mul hvt).add hy (hasValue_const (hm 1 1))
  have hvN : HasValue r.M y (algebraMap K _ (m 0 0) * t + algebraMap K _ (m 0 1))
      (m 0 0 * (aeval y A / aeval y B) + m 0 1) :=
    ((hasValue_const (hm 0 0)).mul hvt).add hy (hasValue_const (hm 0 1))
  have hv0 : HasValue r.M y (0 : LocusFunctionField k v) 0 := by
    simpa using hasValue_mk (k := k) (v := v) (M := r.M) (y := y) 0
  have hD : algebraMap K (LocusFunctionField k v) (m 1 0) * t +
      algebraMap K (LocusFunctionField k v) (m 1 1) ≠ 0 ↔
      m 1 0 * aeval y A + m 1 1 * aeval y B ≠ 0 := by
    have hval : m 1 0 * (aeval y A / aeval y B) + m 1 1 =
        (m 1 0 * aeval y A + m 1 1 * aeval y B) / aeval y B := by
      field_simp
    constructor
    · intro hne h0
      refine hne (hvD.eq hy ?_)
      rw [hval, h0, zero_div]
      exact hv0
    · intro hne h0
      rw [h0] at hvD
      have := hv0.eq_value hy hvD
      rw [hval] at this
      exact hne ((div_eq_zero_iff.1 this.symm).resolve_right hBy)
  have hE : hw.functionFieldAction hv γ t *
      (algebraMap K (LocusFunctionField k v) (m 1 0) * t +
        algebraMap K (LocusFunctionField k v) (m 1 1)) =
      algebraMap K _ (m 0 0) * t + algebraMap K _ (m 0 1) ↔
      aeval (r.f.eval y) A * (m 1 0 * aeval y A + m 1 1 * aeval y B) =
        aeval (r.f.eval y) B * (m 0 0 * aeval y A + m 0 1 * aeval y B) := by
    have hvL := hvγ.mul hvD
    constructor
    · intro h
      rw [h] at hvL
      have := hvN.eq_value hy hvL
      field_simp at this
      linear_combination -this
    · intro h
      refine hvL.eq hy ?_
      convert hvN using 1
      field_simp
      linear_combination h
  exact and_congr hD hE

/-- **The generic lift test.** Let the word `w` represent `γ⁻¹` at the swapped pair of `d`.
Then `m` lifts `γ` iff the lift test of `(d, m)` holds at every point generic over the closure
of `M₁` and the parameter. -/
private theorem forall_liftTest_iff {μ : Type w} [Finite μ] (wd : Word k (μ ⊕ μ) v v)
    {N : IntermediateField k K} {A B : MvPolynomial ι N} {t : LocusFunctionField k v}
    (htAB : t = mk k v (MvPolynomial.map (algebraMap N K) A) /
      mk k v (MvPolynomial.map (algebraMap N K) B))
    (hBgen : ∀ y, IsGenericOver N v y → aeval y B ≠ 0)
    {M₁ : IntermediateField k K} (hM₁ : IsSmall k (M₁ : Set K)) (hNM₁ : N ≤ M₁)
    (γ : ↥hw.prodSubgroup) {d : (μ ⊕ μ) → K} (hdγ : wd.IsGerm (d ∘ Sum.swap) (hw.val γ⁻¹))
    (m : SL(2, K)) :
    (∀ y, IsGenericOver ((racl (↥M₁)
          (range (Sum.elim d fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2))).restrictScalars k) v y →
        LiftTest wd A B (Sum.elim d fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) y) ↔
      hw.IsMoebiusLift hv t γ m := by
  -- The parameter and its closure.
  obtain ⟨x, hx⟩ : ∃ x : ((μ ⊕ μ) ⊕ (Fin 2 × Fin 2)) → K,
      x = Sum.elim d fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2 := ⟨_, rfl⟩
  rw [← hx]
  obtain ⟨Mx, hMx⟩ : ∃ Mx : IntermediateField k K,
      Mx = (racl (↥M₁) (range x)).restrictScalars k := ⟨_, rfl⟩
  rw [← hMx]
  have hMxs : IsSmall k (Mx : Set K) := by
    rw [hMx]
    change IsSmall k ((racl (↥M₁) (range x) : IntermediateField (↥M₁) K) : Set K)
    rw [racl_base_coe]
    exact (hM₁.union (IsSmall.of_finite (finite_range x))).racl
  have hxMx : range x ⊆ (Mx : Set K) := by
    rw [hMx]
    exact subset_racl (↥M₁) _
  have hM₁Mx : M₁ ≤ Mx := by
    rw [hMx]
    intro c hc
    change c ∈ ((racl (↥M₁) (range x) : IntermediateField (↥M₁) K) : Set K)
    rw [racl_base_coe]
    exact subset_racl k _ (Or.inl hc)
  -- An exponent-zero representative of `γ⁻¹` over a field containing everything.
  obtain ⟨r₀, hr₀γ, hr₀⟩ := hw.exists_rational_representative hv (hw.val_mem γ⁻¹)
  have hMs : IsSmall k ((racl k ((Mx : Set K) ∪ r₀.M) : IntermediateField k K) : Set K) :=
    (hMxs.union r₀.isSmall).racl
  have hr₀M : r₀.M ≤ racl k ((Mx : Set K) ∪ r₀.M) := fun c hc ↦ subset_racl k _ (Or.inr hc)
  obtain ⟨r, hr⟩ : ∃ r : Representative k K v v,
      r = r₀.extend (isAlgClosed_racl _) hMs hr₀M := ⟨_, rfl⟩
  have hre : r.f.e = 0 := by
    rw [hr]
    exact hr₀
  have hrγ : (⟦r⟧ : Germ k v v) = (((γ⁻¹ : ↥hw.prodSubgroup) : (Germ k v v)ˣ) : Germ k v v) := by
    rw [hr, Quotient.sound (r₀.extend_equivalent _ hMs hr₀M)]
    exact hr₀γ
  have hrM : r.M = racl k ((Mx : Set K) ∪ r₀.M) := by
    rw [hr]
    rfl
  have hMxr : Mx ≤ r.M := by
    rw [hrM]
    exact fun c hc ↦ subset_racl k _ (Or.inl hc)
  have hNr : N ≤ r.M := hNM₁.trans (hM₁Mx.trans hMxr)
  have hm : ∀ i j, m i j ∈ r.M := fun i j ↦ hMxr (hxMx ⟨Sum.inr (i, j), by rw [hx]; rfl⟩)
  have hxl : (x ∘ Sum.inl) ∘ Sum.swap = d ∘ Sum.swap := by
    rw [hx]
    rfl
  have hxr : ∀ i j, x (Sum.inr (i, j)) = m i j := fun i j ↦ by
    rw [hx]
    rfl
  -- The chain of the word at a point generic over `M_r` ends at `r(y)`.
  have hchain : ∀ y, IsGenericOver r.M v y → ∀ z,
      wd.Chain ((x ∘ Sum.inl) ∘ Sum.swap) y z ↔ z = r.f.eval y := by
    intro y hy z
    have _ := r.isAlgClosed
    have hds : racl k (range (d ∘ Sum.swap)) ≤ r.M := by
      refine racl_le_of_isAlgClosed (k := k) (fun c hc ↦ ?_)
      obtain ⟨p, rfl⟩ := hc
      refine hMxr (hxMx ⟨Sum.inl (Sum.swap p), ?_⟩)
      rw [hx]
      rfl
    have hyd : IsGenericOver (racl k (range (d ∘ Sum.swap))) v y := hy.of_le hds
    rw [hxl, hdγ.chain_iff hyd z]
    have hcb : (hw.val γ⁻¹).cb ≤ racl k (range (d ∘ Sum.swap)) := hdγ.cb_le
    rw [(hw.val γ⁻¹).eval_eq_of_le (IsSmall.of_finite (finite_range _)).racl r.isSmall hcb hds hy]
    change z = Germ.eval (((γ⁻¹ : ↥hw.prodSubgroup) : (Germ k v v)ˣ) : Germ k v v) r.M y ↔ _
    rw [← hrγ, Germ.eval_eq_rep r r.isSmall (by rw [hrγ]; exact hcb.trans hds) le_rfl hy]
  -- The test at one point generic over `M_r` is the lift condition.
  have htest : ∀ y, IsGenericOver r.M v y →
      (LiftTest wd A B x y ↔ hw.IsMoebiusLift hv t γ m) := by
    intro y hy
    have hBy : aeval y B ≠ 0 := hBgen y (hy.of_le hNr)
    have hz : IsGenericOver r.M v (r.f.eval y) := r.isGenericOver y hy
    have hBz : aeval (r.f.eval y) B ≠ 0 := hBgen _ (hz.of_le hNr)
    rw [isMoebiusLift_iff_values hw hv htAB γ hre hrγ hNr m hm hy hBy hBz]
    constructor
    · rintro ⟨z, hz, -, -, hL, hE⟩
      rw [hchain y hy z] at hz
      subst hz
      simp only [hxr] at hL hE
      exact ⟨hL, hE⟩
    · rintro ⟨hL, hE⟩
      refine ⟨r.f.eval y, (hchain y hy _).2 rfl, hBz, hBy, ?_, ?_⟩ <;> simp only [hxr]
      · exact hL
      · exact hE
  obtain ⟨y₀, hy₀⟩ := exists_isGenericOver r.isSmall v
  constructor
  · intro h
    exact (htest y₀ hy₀).1 (h y₀ (hy₀.of_le hMxr))
  · intro hlift y hy
    have hs := (isConstructibleOver_liftTest wd A B).of_le_intermediateField (hNM₁.trans hM₁Mx)
    have hinv : ∀ σ : K ≃ₐ[↥Mx] K, ∀ y' : ι → K,
        (⇑σ ∘ y') ∈ {y | LiftTest wd A B x y} ↔ y' ∈ {y | LiftTest wd A B x y} := by
      intro σ y'
      have hσx : ⇑σ ∘ x = x := funext fun i ↦ σ.commutes ⟨x i, hxMx ⟨i, rfl⟩⟩
      have h := hs.mem_comp_algEquiv_iff σ (Sum.elim x y')
      simp only [Set.mem_ofPred_eq] at h ⊢
      rwa [Sum.comp_elim, hσx, Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_comp_inl,
        Sum.elim_comp_inr] at h
    exact ((hy₀.of_le hMxr).mem_iff_of_invariant hy hinv).1 ((htest y₀ hy₀).2 hlift)

/-- **Lifts are interalgebraic with canonical bases.** Let `ρ` be an equivariant surjection
from a parameter domain onto the group, and let `G` be a constructible set over `M` whose
members over a parameter `d` are exactly the entries of the lifts of `ρ d`. Then each lift of
`γ` is interalgebraic over `M` with the canonical base of `γ`. -/
private theorem racl_entries_eq {t : LocusFunctionField k v} (ht : Transcendental K t)
    (htop : IntermediateField.adjoin K ({t} : Set (LocusFunctionField k v)) = ⊤)
    {P : Type w} {D : Set (P → K)} (ρ : D → ↥hw.prodSubgroup) (hρ : Function.Surjective ρ)
    (hρσ : ∀ (σ : K ≃ₐ[k] K) (d : D), ∃ hσd : ⇑σ ∘ d.1 ∈ D,
      hw.val (ρ ⟨_, hσd⟩) = (hw.val (ρ d)).map σ)
    {M : IntermediateField k K} [IsAlgClosed ↥M] (hM : IsSmall k (M : Set K))
    {G : Set ((P ⊕ (Fin 2 × Fin 2)) → K)} (hG : IsConstructibleOver (↥M) G)
    (hKE : ∀ (d : D) (m : SL(2, K)),
      Sum.elim d.1 (fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) ∈ G ↔ hw.IsMoebiusLift hv t (ρ d) m)
    (γ : ↥hw.prodSubgroup) (m : SL(2, K)) (hγm : hw.IsMoebiusLift hv t γ m) :
    racl (↥M) (range fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) =
      racl (↥M) ((hw.val γ).cb : Set K) := by
  obtain ⟨d, rfl⟩ := hρ γ
  have hmem := (hKE d m).2 hγm
  -- An automorphism over a field containing `M` moves the parameter inside `G`.
  have hmove : ∀ {E : IntermediateField k K}, M ≤ E → ∀ σ : K ≃ₐ[↥E] K,
      Sum.elim (⇑(σ.restrictScalars k) ∘ d.1)
        (⇑(σ.restrictScalars k) ∘ fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) ∈ G := by
    intro E hME σ
    have h := ((hG.of_le_intermediateField hME).mem_comp_algEquiv_iff σ _).2 hmem
    rwa [Sum.comp_elim] at h
  have hentries : ∀ σ : K ≃ₐ[k] K, (⇑σ ∘ fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) =
      fun ij : Fin 2 × Fin 2 ↦ Matrix.SpecialLinearGroup.map (σ : K →+* K) m ij.1 ij.2 := by
    intro σ
    funext ij
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  -- The entries are algebraic over `M` and the canonical base.
  have hA : range (fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) ⊆
      racl (↥M) ((hw.val (ρ d)).cb : Set K) := by
    rintro _ ⟨⟨i, j⟩, rfl⟩
    rw [racl_base_coe]
    have hE : IsSmall k ((racl k ((M : Set K) ∪ (hw.val (ρ d)).cb) : IntermediateField k K) :
        Set K) := (hM.union (hw.val (ρ d)).isSmall_cb).racl
    have hME : M ≤ racl k ((M : Set K) ∪ (hw.val (ρ d)).cb) :=
      fun c hc ↦ subset_racl k _ (Or.inl hc)
    refine (isRAC_racl _).mem_of_pow_mem two_ne_zero (mem_of_forall_algEquiv_fixed hE fun σ ↦ ?_)
    obtain ⟨hσd, hval⟩ := hρσ (σ.restrictScalars k) d
    have hfix : (hw.val (ρ d)).map (σ.restrictScalars k) = hw.val (ρ d) :=
      (Germ.map_eq_self_iff _ _).2 fun c hc ↦ σ.commutes ⟨c, subset_racl k _ (Or.inr hc)⟩
    have hρeq : ρ ⟨_, hσd⟩ = ρ d := hw.val_injective (hval.trans hfix)
    have h2 := (hKE ⟨_, hσd⟩ (Matrix.SpecialLinearGroup.map ((σ.restrictScalars k : K ≃ₐ[k] K) :
      K →+* K) m)).1 (by rw [← hentries]; exact hmove hME σ)
    rw [hρeq] at h2
    have hσm : σ (m i j) = m i j ∨ σ (m i j) = -m i j := by
      rcases hγm.eq_or_eq_neg ht h2 with h | h
      · left
        have := congrArg (fun g : SL(2, K) ↦ g i j) h
        simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this
      · right
        have := congrArg (fun g : SL(2, K) ↦ g i j) h
        simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this
    rcases hσm with h | h
    · rw [map_pow, h]
    · rw [map_pow, h, neg_sq]
  -- The canonical base is algebraic over `M` and the entries.
  have hB : ((hw.val (ρ d)).cb : Set K) ⊆
      racl (↥M) (range fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) := by
    intro c hc
    rw [racl_base_coe]
    have hE : IsSmall k ((racl k ((M : Set K) ∪ range fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) :
        IntermediateField k K) : Set K) :=
      (hM.union (IsSmall.of_finite (finite_range _))).racl
    have hME : M ≤ racl k ((M : Set K) ∪ range fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) :=
      fun c hc ↦ subset_racl k _ (Or.inl hc)
    refine mem_of_forall_algEquiv_fixed hE fun σ ↦ ?_
    obtain ⟨hσd, hval⟩ := hρσ (σ.restrictScalars k) d
    have hfixm : (⇑(σ.restrictScalars k) ∘ fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) =
        fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2 :=
      funext fun ij ↦ σ.commutes ⟨m ij.1 ij.2, subset_racl k _ (Or.inr ⟨ij, rfl⟩)⟩
    have hmv := hmove hME σ
    rw [hfixm] at hmv
    have h2 := (hKE ⟨_, hσd⟩ m).1 hmv
    have hρeq : ρ ⟨_, hσd⟩ = ρ d := h2.injective htop hγm
    have hfix : (hw.val (ρ d)).map (σ.restrictScalars k) = hw.val (ρ d) := by
      rw [← hval, hρeq]
    exact (Germ.map_eq_self_iff _ _).1 hfix c hc
  exact le_antisymm (racl_le_of_subset_racl hA) (racl_le_of_subset_racl hB)

end Values

/-! ### The lift of the actual action -/

namespace Germ.IsHWBij

/-- **The constructible determinant-one lift of the Hrushovski–Weil action.** Let `f₀` be a
Hrushovski–Weil datum of bijections, `δ₀` a member of its difference set, `v` of rank one and the
canonical base of `δ₀` of rank at least two. There are a generator `t` of the function field of
the curve, a small algebraically closed field `M` and a subgroup `Γ ≤ SL₂(K)` such that:
every member `γ` of the group has a lift in `t`; `Γ` consists of exactly these lifts; two lifts
of a member differ by a sign; lifts compose in the reversed order; `Γ` is constructible over
`M`; every lift is interalgebraic over `M` with the canonical base of its member; and the
canonical bases have rank at most that of `δ₀` over `M`, with equality for some member. -/
theorem exists_constructible_slLift {ι κ : Type w} [Finite ι] [Finite κ]
    {v : ι → K} {v' : κ → K} {f₀ : Germ k v v'} (hb : f₀.IsHWBij) {δ₀ : Germ k v v}
    (hδ₀ : δ₀ ∈ f₀.diffSet) (hv : erk k ∅ (range v) = 1)
    (hr : 2 ≤ erk k ∅ (δ₀.cb : Set K)) :
    ∃ (t : LocusFunctionField k v) (M : IntermediateField k K) (_ : IsAlgClosed ↥M)
      (Γ : Subgroup SL(2, K)),
      Transcendental K t ∧ IntermediateField.adjoin K ({t} : Set (LocusFunctionField k v)) = ⊤ ∧
      IsSmall k (M : Set K) ∧
      (∀ γ, ∃ m, (hb.isHW hδ₀).IsMoebiusLift hv t γ m) ∧
      (∀ m, m ∈ Γ ↔ ∃ γ, (hb.isHW hδ₀).IsMoebiusLift hv t γ m) ∧
      (∀ γ m m', (hb.isHW hδ₀).IsMoebiusLift hv t γ m →
        (hb.isHW hδ₀).IsMoebiusLift hv t γ m' → m' = m ∨ m' = -m) ∧
      (∀ γ δ m n, (hb.isHW hδ₀).IsMoebiusLift hv t γ m →
        (hb.isHW hδ₀).IsMoebiusLift hv t δ n →
          (hb.isHW hδ₀).IsMoebiusLift hv t (γ * δ) (n * m)) ∧
      IsConstructibleOver (↥M) {x : Fin 2 × Fin 2 → K | ∃ m ∈ Γ, ∀ i j, m i j = x (i, j)} ∧
      (∀ γ m, (hb.isHW hδ₀).IsMoebiusLift hv t γ m →
        racl (↥M) (range fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) =
          racl (↥M) (((hb.isHW hδ₀).val γ).cb : Set K)) ∧
      (∀ γ, erk (↥M) ∅ (((hb.isHW hδ₀).val γ).cb : Set K) ≤ erk k ∅ (δ₀.cb : Set K)) ∧
      ∃ γ, erk (↥M) ∅ (((hb.isHW hδ₀).val γ).cb : Set K) = erk k ∅ (δ₀.cb : Set K) := by
  -- The generator, its lifts and its fraction over a small field.
  obtain ⟨t, ht, htop, hlift⟩ := (hb.isHW hδ₀).exists_generator_isMoebiusLift hv hr
  obtain ⟨N, hN, A, B, hBgen, htAB⟩ := exists_fraction_small t
  -- The actual constructible presentation.
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype (CodeIndex (ι ⊕ κ) (genDeg f₀.graphIdeal)) := Fintype.ofFinite _
  obtain ⟨F, hF, hdim, S₀, t₁, -, -, -, -, -, -, -, -, -, -, hL, hpres, -⟩ :=
    hb.exists_fresh_canonicalGroupSpacePresentation hδ₀ N hN
  generalize adjoin k (S₀ ∪ ⋃ i, range (t₁ i)) = L at hL hpres
  -- The coefficient field `M₁` and the generic quantifier over it.
  obtain ⟨M₁, hM₁def⟩ : ∃ M₁ : IntermediateField k K, M₁ = racl k ((N : Set K) ∪ L) :=
    ⟨_, rfl⟩
  have iM₁ : IsAlgClosed ↥M₁ := hM₁def ▸ isAlgClosed_racl _
  have hM₁ : IsSmall k (M₁ : Set K) := hM₁def ▸ (hN.union hL).racl
  have hNM₁ : N ≤ M₁ := hM₁def ▸ fun c hc ↦ subset_racl k _ (Or.inl hc)
  have hLM₁ : L ≤ M₁ := hM₁def ▸ fun c hc ↦ subset_racl k _ (Or.inr hc)
  have hs := (isConstructibleOver_liftTest (F.pairWord hdim) A B).of_le_intermediateField hNM₁
  obtain ⟨ts, hts, hrk, -⟩ := exists_genericSamples M₁ hM₁ v
    (2 * Fintype.card (((CodeIndex (ι ⊕ κ) (genDeg f₀.graphIdeal)) ⊕
      (CodeIndex (ι ⊕ κ) (genDeg f₀.graphIdeal))) ⊕ (Fin 2 × Fin 2)) + 1)
  have hind : erk k (M₁ : Set K) (⋃ i, range (ts i)) =
      ∑ i, erk k (M₁ : Set K) (range (ts i)) := by
    rw [hrk]
    exact Finset.sum_congr rfl fun i _ ↦ ((hts i).erk_coe_eq.trans (hts i).erk_empty_eq).symm
  have hG := constructible_generic_quantifier M₁ hM₁ v ts hts hind (by simp) hs
  -- The final field `M`.
  obtain ⟨M, hMdef⟩ : ∃ M : IntermediateField k K,
      M = racl k ((M₁ : Set K) ∪ ⋃ i, range (ts i)) := ⟨_, rfl⟩
  have iM : IsAlgClosed ↥M := hMdef ▸ isAlgClosed_racl _
  have hMs : IsSmall k (M : Set K) :=
    hMdef ▸ (hM₁.union (IsSmall.of_finite (finite_iUnion fun i ↦ finite_range (ts i)))).racl
  have hM₁M : M₁ ≤ M := hMdef ▸ fun c hc ↦ subset_racl k _ (Or.inl hc)
  have hEM : (adjoin (↥M₁) (⋃ i, range (ts i))).restrictScalars k ≤ M := by
    rw [restrictScalars_adjoin, hMdef]
    exact adjoin_le_racl k _
  have hGM := (hG.of_restrictScalars_eq rfl).of_le_intermediateField hEM
  -- The key equivalence: membership in the quantified set is the lift condition.
  have hKE : ∀ (d : F.pairDomain L f₀.code v v') (m : SL(2, K)),
      Sum.elim d.1 (fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) ∈
        {x | ∀ y, IsGenericOver ((racl (↥M₁) (range x)).restrictScalars k) v y →
          Sum.elim x y ∈ {u | LiftTest (F.pairWord hdim) A B (u ∘ Sum.inl) (u ∘ Sum.inr)}} ↔
      (hb.isHW hδ₀).IsMoebiusLift hv t
        (F.pairDomainMap L hL hb hδ₀ f₀.adjoin_range_code hF hdim d) m := by
    intro d m
    have hdγ : (F.pairWord hdim).IsGerm (d.1 ∘ Sum.swap)
        ((hb.isHW hδ₀).val (F.pairDomainMap L hL hb hδ₀ f₀.adjoin_range_code hF hdim d)⁻¹) := by
      rw [F.val_pairDomainMap_inv L hL hb hδ₀ f₀.adjoin_range_code hF hdim d]
      exact F.isGerm_pairGerm hdim _
    rw [← forall_liftTest_iff (hb.isHW hδ₀) hv (F.pairWord hdim) htAB hBgen hM₁ hNM₁ _ hdγ m]
    simp only [Set.mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_comp_inr]
  -- The subgroup of lifts.
  let Γ : Subgroup SL(2, K) :=
    { carrier := {m | ∃ γ, (hb.isHW hδ₀).IsMoebiusLift hv t γ m}
      one_mem' := ⟨1, Germ.IsHW.isMoebiusLift_one (hw := hb.isHW hδ₀) (hv := hv) ht⟩
      mul_mem' := by
        rintro a b ⟨γ, hγ⟩ ⟨δ, hδ⟩
        exact ⟨δ * γ, hδ.mul ht hγ⟩
      inv_mem' := by
        rintro a ⟨γ, hγ⟩
        obtain ⟨m', hm'⟩ := hlift γ⁻¹
        have h1 := hγ.mul ht hm'
        rw [mul_inv_cancel] at h1
        refine ⟨γ⁻¹, ?_⟩
        have h0 := Germ.IsHW.isMoebiusLift_one (hw := hb.isHW hδ₀) (hv := hv) ht
        rcases h0.eq_or_eq_neg ht h1 with h | h
        · rw [← eq_inv_of_mul_eq_one_left h]
          exact hm'
        · have h' : -m' * a = 1 := by rw [neg_mul, h, neg_neg]
          rw [← eq_inv_of_mul_eq_one_left h']
          exact hm'.neg }
  have hΓ : ∀ m, m ∈ Γ ↔ ∃ γ, (hb.isHW hδ₀).IsMoebiusLift hv t γ m := fun _ ↦ Iff.rfl
  -- Constructibility of the lifts.
  have hdet : IsConstructibleOver (↥M) {x : ((CodeIndex (ι ⊕ κ) (genDeg f₀.graphIdeal) ⊕
      CodeIndex (ι ⊕ κ) (genDeg f₀.graphIdeal)) ⊕ (Fin 2 × Fin 2)) → K |
      x (Sum.inr (0, 0)) * x (Sum.inr (1, 1)) - x (Sum.inr (0, 1)) * x (Sum.inr (1, 0)) = 1} := by
    convert IsConstructibleOver.polynomial_zero (k := ↥M) (K := K)
      (X (Sum.inr (0, 0)) * X (Sum.inr (1, 1)) - X (Sum.inr (0, 1)) * X (Sum.inr (1, 0)) - 1 :
        MvPolynomial ((CodeIndex (ι ⊕ κ) (genDeg f₀.graphIdeal) ⊕
          CodeIndex (ι ⊕ κ) (genDeg f₀.graphIdeal)) ⊕ (Fin 2 × Fin 2)) ↥M) using 1
    ext x
    simp [sub_eq_zero]
  have hD := (hpres.domain.of_le_intermediateField (hLM₁.trans hM₁M)).preimage_comp
    (Sum.inl : (CodeIndex (ι ⊕ κ) (genDeg f₀.graphIdeal) ⊕
      CodeIndex (ι ⊕ κ) (genDeg f₀.graphIdeal)) → _ ⊕ (Fin 2 × Fin 2))
  obtain ⟨S, hSdef⟩ : ∃ S : Set (((CodeIndex (ι ⊕ κ) (genDeg f₀.graphIdeal) ⊕
      CodeIndex (ι ⊕ κ) (genDeg f₀.graphIdeal)) ⊕ (Fin 2 × Fin 2)) → K),
      S = ((fun x ↦ x ∘ Sum.inl) ⁻¹' F.pairDomain L f₀.code v v') ∩
        ({x | ∀ y, IsGenericOver ((racl (↥M₁) (range x)).restrictScalars k) v y →
          Sum.elim x y ∈ {u | LiftTest (F.pairWord hdim) A B (u ∘ Sum.inl) (u ∘ Sum.inr)}} ∩
        {x | x (Sum.inr (0, 0)) * x (Sum.inr (1, 1)) -
          x (Sum.inr (0, 1)) * x (Sum.inr (1, 0)) = 1}) := ⟨_, rfl⟩
  have hS : IsConstructibleOver (↥M) S := hSdef ▸ hD.inter (hGM.inter hdet)
  have hR : IsConstructibleOver (↥M) {y : Fin 2 × Fin 2 → K | ∃ d, Sum.elim d y ∈ S} := by
    refine IsConstructibleOver.exists (φ := fun y d ↦ Sum.elim d y ∈ S) ?_
    convert hS.preimage_comp Sum.swap using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [show Sum.elim (z ∘ Sum.inr) (z ∘ Sum.inl) = z ∘ Sum.swap from by
      funext i
      cases i <;> rfl]
  have hset : {x : Fin 2 × Fin 2 → K | ∃ m ∈ Γ, ∀ i j, m i j = x (i, j)} =
      {x | ∃ d, Sum.elim d x ∈ S} := by
    rw [hSdef]
    ext x
    constructor
    · rintro ⟨m, ⟨γ, hγ⟩, hmx⟩
      obtain ⟨d, rfl⟩ := hpres.surjective γ
      have hx : x = fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2 := funext fun ij ↦ (hmx ij.1 ij.2).symm
      subst hx
      refine ⟨d.1, ?_, (hKE d m).2 hγ, ?_⟩
      · simpa only [Set.mem_preimage, Sum.elim_comp_inl] using d.2
      · have := m.det_coe
        rw [Matrix.det_fin_two] at this
        simpa only [Set.mem_ofPred_eq, Sum.elim_inr] using this
    · rintro ⟨d, hdD, hdG, hdet⟩
      simp only [Set.mem_preimage, Sum.elim_comp_inl] at hdD
      simp only [Set.mem_ofPred_eq, Sum.elim_inr] at hdet
      let m : SL(2, K) :=
        ⟨Matrix.of fun i j ↦ x (i, j), by rw [Matrix.det_fin_two]; simpa using hdet⟩
      have hm : (fun ij : Fin 2 × Fin 2 ↦ m ij.1 ij.2) = x := rfl
      refine ⟨m, ⟨_, (hKE ⟨d, hdD⟩ m).1 (by rw [hm]; exact hdG)⟩, fun i j ↦ rfl⟩
  have hΓc : IsConstructibleOver (↥M)
      {x : Fin 2 × Fin 2 → K | ∃ m ∈ Γ, ∀ i j, m i j = x (i, j)} := by
    rw [hset]
    exact hR
  -- The rank comparison.
  have hρσ : ∀ (σ : K ≃ₐ[k] K) (d : F.pairDomain L f₀.code v v'), ∃ hσd : ⇑σ ∘ d.1 ∈ _,
      (hb.isHW hδ₀).val (F.pairDomainMap L hL hb hδ₀ f₀.adjoin_range_code hF hdim ⟨_, hσd⟩) =
        ((hb.isHW hδ₀).val (F.pairDomainMap L hL hb hδ₀ f₀.adjoin_range_code hF hdim d)).map σ :=
    fun σ d ↦ ⟨_, F.val_pairDomainMap_comp_algEquiv L hL hb hδ₀ f₀.adjoin_range_code hF hdim σ d⟩
  have hracl := racl_entries_eq (hb.isHW hδ₀) hv ht htop _ hpres.surjective hρσ hMs hGM hKE
  -- The ranks of the canonical bases.
  refine ⟨t, M, iM, Γ, ht, htop, hMs, hlift, hΓ, fun γ m m' h h' ↦ h.eq_or_eq_neg ht h',
    fun γ δ m n h h' ↦ h.mul ht h', hΓc, hracl, fun γ ↦ ?_, ?_⟩
  · rw [erk_base_empty]
    exact (hb.isHW hδ₀).erk_base_cb_le _ ((hb.isHW hδ₀).val_mem γ)
  · obtain ⟨g, hg, hgM⟩ := Germ.exists_mem_orbit_indepOver δ₀ hMs
    refine ⟨(hb.isHW hδ₀).ofMem ((hb.isHW hδ₀).mem_prodSet_of_mem hg), ?_⟩
    rw [erk_base_empty, (hb.isHW hδ₀).val_ofMem]
    exact ((hb.isHW hδ₀).erk_base_cb_eq_iff ((hb.isHW hδ₀).mem_prodSet_of_mem hg)).2 ⟨hg, hgM⟩

end Germ.IsHWBij

end

end GroupConfig
