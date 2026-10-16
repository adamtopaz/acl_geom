/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import GroupConfig.Germ.FunctionFieldAction
import GroupConfig.Germ.HomogeneousSpace

/-!
# Affine coordinates of the function-field action at generic points

Let `u` be a transcendental element of the function field of a curve, written as a fraction
`P / Q` of polynomials over a small algebraically closed field `M`. Suppose a member `γ` of a
Hrushovski–Weil group acts on `u` by `γ⁻¹ · u = a u + b`, with `a, b` algebraic over `M` and the
canonical base of `γ`. `affine_coordinate_evalGen` evaluates this identity at a point `y`
generic over `M` and the canonical base. The values `x = u(y)` and `z = u(γ y)` satisfy
`z = a x + b`, and each value generates over `M` the same closure as its point.

An exponent-zero representative of `γ` is chosen internally. It is moved by an automorphism over
the closure of the canonical base so that `y` stays generic over its coefficient field
(`exists_fresh_rational_representative`); no bound on that coefficient field is assumed.

The consumer is the initial affine chart `GroupConfig.exists_initial_chart_generic` (#27).

**Status:** proved; the supporting lemmas are private.
-/

namespace GroupConfig

open AclGeom MvPolynomial Set LocusFunctionField

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K] {ι : Type*} [Finite ι] {v : ι → K}

namespace Germ.IsHW

variable {g₀ : Germ k v v} (hw : IsHW g₀) (hv : erk k ∅ (range v) = 1)
include hw hv

/-- **Fresh rational representatives.** Let `γ` be a member of the group, `M` a small field and
`y` a generic point over `acl(M, cb γ)`. Then `γ` has an exponent-zero representative `r`, and
there is a small algebraically closed field `N ⊇ M, M_r` over which `y` is still generic. An
arbitrary rational representative is moved by an automorphism over `acl(cb γ)`; no bound on its
coefficient field is assumed. -/
private theorem exists_fresh_rational_representative {γ : Germ k v v} (hγ : γ ∈ prodSet g₀)
    {M : IntermediateField k K} (hM : IsSmall k (M : Set K)) {y : ι → K}
    (hy : IsGenericOver (racl k ((M : Set K) ∪ (γ.cb : Set K))) v y) :
    ∃ (r : Representative k K v v) (N : IntermediateField k K), (⟦r⟧ : Germ k v v) = γ ∧
      r.f.e = 0 ∧ IsAlgClosed ↥N ∧ IsSmall k (N : Set K) ∧ M ≤ N ∧ r.M ≤ N ∧
      IsGenericOver N v y := by
  obtain ⟨r₀, hr₀, he⟩ := hw.exists_rational_representative hv hγ
  -- The field of definition of `γ`, and finite generators of the coefficient field of `r₀`.
  obtain ⟨F, hFdef⟩ : ∃ F : IntermediateField k K, F = racl k (γ.cb : Set K) := ⟨_, rfl⟩
  have hF : IsSmall k (F : Set K) := hFdef ▸ γ.isSmall_cb.racl
  have : IsAlgClosed ↥F := hFdef ▸ isAlgClosed_racl _
  have hcbF : γ.cb ≤ F := hFdef ▸ fun x hx ↦ subset_racl k _ hx
  have : IsAlgClosed ↥r₀.M := r₀.isAlgClosed
  obtain ⟨B, -, hBfin, hBr⟩ := r₀.isSmall.exists_finite_racl_eq
  have hr₀B : racl k B = r₀.M :=
    hBr.trans (le_antisymm (racl_le_of_isAlgClosed fun _ hx ↦ hx) fun _ hx ↦ subset_racl k _ hx)
  have : Finite ↥B := hBfin.to_subtype
  -- Move the generators independently of `M` and `y` over `F`.
  obtain ⟨τ, hτ⟩ := exists_algEquiv_indepOver (M := F) hF (fun b : ↥B ↦ (b : K))
    (w := (M : Set K) ∪ range y) (hM.union (IsSmall.of_finite (finite_range y)))
  obtain ⟨σ, hσ⟩ : ∃ σ : K ≃ₐ[k] K, σ = τ.restrictScalars k := ⟨_, rfl⟩
  have hστ : ∀ x, σ x = τ x := fun x ↦ by rw [hσ]; rfl
  have hτ' : IndepOver k (F : Set K) (σ '' B) ((M : Set K) ∪ range y) := by
    convert hτ using 2
    rw [image_eq_range]
    exact congrArg range (funext fun b ↦ hστ b)
  -- The moved representative still represents `γ`.
  have hrγ : (⟦r₀.map σ⟧ : Germ k v v) = γ := by
    change Germ.map σ (⟦r₀⟧ : Germ k v v) = γ
    rw [hr₀, Germ.map_eq_self_iff]
    intro x hx
    rw [hστ]
    exact τ.commutes ⟨x, hcbF hx⟩
  have hrM : (((r₀.map σ).M : IntermediateField k K) : Set K) = racl k (σ '' B) := by
    rw [Representative.map_M, ← hr₀B, racl_map]
  have hcbr : (γ.cb : Set K) ⊆ racl k (σ '' B) := by
    rw [← hrM, ← hrγ]
    exact Germ.cb_mk_le _
  refine ⟨r₀.map σ, racl k ((M : Set K) ∪ ((r₀.map σ).M : Set K)), hrγ, he,
    isAlgClosed_racl _, (hM.union (r₀.map σ).isSmall).racl,
    fun x hx ↦ subset_racl k _ (Or.inl hx), fun x hx ↦ subset_racl k _ (Or.inr hx), ?_⟩
  -- Genericity over `N`, by the independence over `F`.
  have hG : IsSmall k ((racl k ((M : Set K) ∪ (γ.cb : Set K)) : IntermediateField k K) :
      Set K) := (hM.union γ.isSmall_cb).racl
  have hN : IsSmall k ((racl k ((M : Set K) ∪ ((r₀.map σ).M : Set K)) :
      IntermediateField k K) : Set K) := (hM.union (r₀.map σ).isSmall).racl
  have hyG := (isGenericOver_iff_erk_eq hG hy.inLocus).1 hy
  refine (isGenericOver_iff_erk_eq hN hy.inLocus).2 ?_
  have hind : IndepOver k ((F : Set K) ∪ M) (range y) (σ '' B) :=
    ((indepOver_union_right_iff.1 hτ').2).symm
  have hFM : racl k ((F : Set K) ∪ M) = racl k ((M : Set K) ∪ (γ.cb : Set K)) := by
    rw [hFdef, racl_union_left, union_comm]
  have hbase : racl k ((M : Set K) ∪ ((r₀.map σ).M : Set K)) =
      racl k (((F : Set K) ∪ M) ∪ σ '' B) := by
    rw [hrM, racl_union_right]
    refine le_antisymm (racl_mono (union_subset (fun x hx ↦ Or.inl (Or.inr hx))
      fun x hx ↦ Or.inr hx)) (racl_le_of_subset_racl (union_subset (union_subset ?_
      fun x hx ↦ subset_racl k _ (Or.inl hx)) fun x hx ↦ subset_racl k _ (Or.inr hx)))
    intro x hx
    exact racl_mono subset_union_right (racl_le_of_subset_racl hcbr (hFdef ▸ hx))
  calc erk k ((racl k ((M : Set K) ∪ ((r₀.map σ).M : Set K)) : IntermediateField k K) :
        Set K) (range y)
      = erk k ((racl k (((F : Set K) ∪ M) ∪ σ '' B) : IntermediateField k K) : Set K)
          (range y) := by rw [hbase]
    _ = erk k (((F : Set K) ∪ M) ∪ σ '' B) (range y) := erk_racl_base k _ _
    _ = erk k ((F : Set K) ∪ M) (range y) := hind.erk_eq (subset_refl _) (finite_range y)
    _ = erk k ((racl k ((M : Set K) ∪ (γ.cb : Set K)) : IntermediateField k K) : Set K)
          (range y) := (erk_racl_base k _ _).symm.trans (by rw [hFM])
    _ = erk k ∅ (range v) := hyG

end Germ.IsHW

/-! ### Values at generic points -/

omit [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
/-- Fraction values persist under enlarging their coefficient field. -/
private theorem hasValue_mono {M N : IntermediateField k K} (hMN : M ≤ N) {y : ι → K}
    {u : LocusFunctionField k v} {x : K} (hx : HasValue M y u x) : HasValue N y u x := by
  obtain ⟨A, B, hB, hu, hx⟩ := hx
  have he (P : MvPolynomial ι M) :
      aeval y (MvPolynomial.map (IntermediateField.inclusion hMN).toRingHom P) = aeval y P := by
    change eval₂ _ _ (MvPolynomial.map _ P) = eval₂ _ _ P
    rw [eval₂_map]
    rfl
  refine ⟨MvPolynomial.map (IntermediateField.inclusion hMN).toRingHom A,
    MvPolynomial.map (IntermediateField.inclusion hMN).toRingHom B, ?_, ?_, ?_⟩
  · rwa [he]
  · rwa [map_map_inclusion, map_map_inclusion]
  · rwa [he, he]

omit [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
/-- A fraction value is algebraic over its coefficient field and input point. -/
private theorem hasValue_mem_racl {M : IntermediateField k K} {y : ι → K}
    {u : LocusFunctionField k v} {x : K} (hx : HasValue M y u x) :
    x ∈ racl (↥M) (range y) := by
  obtain ⟨A, B, -, -, rfl⟩ := hx
  have hp (P : MvPolynomial ι M) : aeval y P ∈ racl (↥M) (range y) := by
    exact MvPolynomial.eval₂_mem (fun i _ ↦ (racl (↥M) (range y)).algebraMap_mem (P.coeff i))
      (fun i ↦ subset_racl (↥M) _ ⟨i, rfl⟩)
  exact div_mem (hp A) (hp B)

omit [UniversalDomain k K] [Finite ι] in
/-- A transcendental function evaluated at a generic point remains transcendental over its
algebraically closed coefficient field. -/
private theorem hasValue_transcendental {M : IntermediateField k K} [IsAlgClosed ↥M]
    {y : ι → K} (hy : IsGenericOver M v y) {u : LocusFunctionField k v}
    (hu : Transcendental K u) {x : K} (hx : HasValue M y u x) : Transcendental (↥M) x := by
  intro halg
  let c : M := ⟨x, isRAC_of_isAlgClosed M x halg⟩
  have hc : algebraMap M K c = x := rfl
  have hconst := hasValue_algebraMap (k := k) (v := v) (M := M) (y := y) le_rfl c
  have he : u = algebraMap K (LocusFunctionField k v) x := by
    have he := HasValue.eq hy hx (by simpa only [hc] using hconst)
    rw [he, ← hc]
    exact (IsScalarTower.algebraMap_apply (↥M) K _ c).symm
  exact hu (he.symm ▸ isAlgebraic_algebraMap x)

omit [UniversalDomain k K] [Finite ι] in
/-- On a curve, the value of a transcendental function and the point generate the same
relative algebraic closure. Inverse-coordinate coefficients are unnecessary. -/
private theorem hasValue_racl_eq_of_curve {M : IntermediateField k K} [IsAlgClosed ↥M]
    {y : ι → K} (hy : IsGenericOver M v y) (hv : erk k ∅ (range v) = 1)
    {u : LocusFunctionField k v} (hu : Transcendental K u) {x : K} (hx : HasValue M y u x) :
    racl (↥M) ({x} : Set K) = racl (↥M) (range y) := by
  have hxm := hasValue_mem_racl hx
  have hxtr := hasValue_transcendental hy hu hx
  have hry : erk (↥M) ∅ (range y) = 1 :=
    by
      rw [erk_empty_eq (↥M), ← erk_coe_eq k M]
      exact hy.erk_coe_eq.trans (hy.erk_empty_eq.trans hv)
  have hrx : erk (↥M) ∅ ({x} : Set K) = 1 := by
    apply le_antisymm ((erk_le_encard _ _ _).trans (by simp))
    exact Order.one_le_iff_ne_zero.2 fun h0 ↦ hxtr
      (isAlgebraic_of_mem_racl_empty ((erk_singleton_eq_zero_iff _).1 h0))
  have htotal : erk (↥M) ∅ ({x} ∪ range y) = 1 := by
    rw [union_comm]
    exact (erk_union_eq_of_subset_racl _ (by simpa using singleton_subset_iff.2 hxm)).trans hry
  have hzero : erk (↥M) {x} (range y) = 0 := by
    have he := erk_union_eq (↥M) ∅ ({x} : Set K) (range y)
    rw [empty_union, htotal, hrx] at he
    exact ENat.add_right_injective_of_ne_top (n := 1) (by norm_num)
      (he.symm.trans (by norm_num : (1 : ℕ∞) = 1 + 0))
  exact le_antisymm (racl_le_of_subset_racl (singleton_subset_iff.2 hxm))
    (racl_le_of_subset_racl ((erk_eq_zero_iff _).1 hzero))

omit [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
/-- Constants from the coefficient field have their literal ambient values. -/
private theorem hasValue_constant {M : IntermediateField k K} {y : ι → K} {a : K}
    (ha : a ∈ M) : HasValue M y (algebraMap K (LocusFunctionField k v) a) a := by
  have h := hasValue_algebraMap (k := k) (v := v) (M := M) (y := y) le_rfl (⟨a, ha⟩ : M)
  convert h using 1
  · exact IsScalarTower.algebraMap_apply (↥M) K _ ⟨a, ha⟩
  · rfl

/-- The actual germ action has its affine expression on coordinate values at every point
generic over the coefficients and canonical base. The exponent-zero representative and its
fresh field are chosen internally; the same fixed coordinate is used at both points. -/
theorem affine_coordinate_evalGen {g₀ : Germ k v v} (hw : g₀.IsHW)
    (hv : erk k ∅ (range v) = 1) {M : IntermediateField k K} [IsAlgClosed ↥M]
    (hM : IsSmall k (M : Set K)) {u : LocusFunctionField k v} (hu : Transcendental K u)
    (P Q : MvPolynomial ι M)
    (hQ : ∀ y, IsGenericOver M v y → aeval y Q ≠ 0)
    (huPQ : u = mk k v (MvPolynomial.map (algebraMap M K) P) /
      mk k v (MvPolynomial.map (algebraMap M K) Q))
    (γ : ↥hw.prodSubgroup) (a b : K)
    (ha : a ∈ racl k ((M : Set K) ∪ ((hw.val γ).cb : Set K)))
    (hb : b ∈ racl k ((M : Set K) ∪ ((hw.val γ).cb : Set K)))
    (hact : hw.functionFieldAction hv γ⁻¹ u = algebraMap K _ a * u + algebraMap K _ b)
    {y : ι → K} (hy : IsGenericOver (racl k ((M : Set K) ∪ ((hw.val γ).cb : Set K))) v y) :
    ∃ x z : K, HasValue M y u x ∧ HasValue M ((hw.val γ).evalGen y) u z ∧
      z = a * x + b ∧ racl (↥M) ({x} : Set K) = racl (↥M) (range y) ∧
      racl (↥M) ({z} : Set K) = racl (↥M) (range ((hw.val γ).evalGen y)) := by
  obtain ⟨r, N, hr, he, iN, hNs, hMN, hrN, hyN⟩ :=
    hw.exists_fresh_rational_representative hv (hw.val_mem γ) hM hy
  let : IsAlgClosed ↥N := iN
  let : IsAlgClosed ↥r.M := r.isAlgClosed
  have hcbN : (hw.val γ).cb ≤ N := by
    rw [← hr]
    exact (Germ.cb_mk_le r).trans hrN
  have hFN : racl k ((M : Set K) ∪ ((hw.val γ).cb : Set K)) ≤ N :=
    racl_le_of_isAlgClosed (union_subset hMN hcbN)
  have hyM : IsGenericOver M v y := hyN.of_le hMN
  have hzN : IsGenericOver N v ((hw.val γ).evalGen y) := by
    rw [(hw.val γ).evalGen_eq hNs hcbN hyN]
    exact (hw.val γ).isGenericOver_eval hNs hcbN hyN
  have hreval : (hw.val γ).evalGen y = r.f.eval y := by
    rw [← hr, Germ.evalGen_eq _ r.isSmall (Germ.cb_mk_le r) (hyN.of_le hrN)]
    exact Germ.eval_eq_rep r r.isSmall (Germ.cb_mk_le r) le_rfl (hyN.of_le hrN)
  have hvalue (z : ι → K) (hz : IsGenericOver M v z) :
      HasValue M z u (aeval z P / aeval z Q) := ⟨P, Q, hQ z hz, huPQ, rfl⟩
  let x := aeval y P / aeval y Q
  let z := aeval ((hw.val γ).evalGen y) P / aeval ((hw.val γ).evalGen y) Q
  have hx : HasValue M y u x := hvalue y hyM
  have hz : HasValue M ((hw.val γ).evalGen y) u z := hvalue _ (hzN.of_le hMN)
  have hsub : HasValue N y (hw.functionFieldAction hv γ⁻¹ u) z := by
    apply hw.hasValue_functionFieldAction hv γ⁻¹ he (by simpa [Germ.IsHW.val] using hr) hrN hyN
    rw [← hreval]
    exact hasValue_mono hMN hz
  have hlinear : HasValue N y (algebraMap K _ a * u + algebraMap K _ b) (a * x + b) :=
    ((hasValue_constant (hFN ha)).mul (hasValue_mono hMN hx)).add hyN
      (hasValue_constant (hFN hb))
  refine ⟨x, z, hx, hz, ?_, hasValue_racl_eq_of_curve hyM hv hu hx,
    hasValue_racl_eq_of_curve (hzN.of_le hMN) hv hu hz⟩
  rw [hact] at hsub
  exact hsub.eq_value hyN hlinear

end

end GroupConfig
