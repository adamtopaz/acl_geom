/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.Canonical
import AclGeom.Tate.FinitePotent

/-!
# The valuation filtration and Tate's commensurability

The valuation ring of a place as a `k`-subspace of the function field,
its filtration by uniformizer powers, and the finiteness that drives
Tate's residue: each filtration step is spanned over the previous one
by a single monomial (the residue gauge), so `π^{−m}O_P ≺ O_P` in
Tate's almost-containment order, and multiplication operators respect
the commensurability class of `O_P`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P6 via Tate residues).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- The valuation ring of a place, as a `k`-submodule of the function
field. -/
noncomputable def Place.toSubmodule (P : Place k F) : Submodule k F where
  carrier := {x | P.val.valuation x ≤ 1}
  add_mem' := by
    intro a b ha hb
    change P.val.valuation (a + b) ≤ 1
    exact le_trans (P.val.valuation.map_add a b) (max_le ha hb)
  zero_mem' := by
    change P.val.valuation 0 ≤ 1
    rw [Valuation.map_zero]
    exact zero_le
  smul_mem' := by
    intro c x hx
    change P.val.valuation (c • x) ≤ 1
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [zero_smul, Valuation.map_zero]
      exact zero_le
    · rw [Algebra.smul_def, Valuation.map_mul,
        valuation_algebraMap_eq_one P.algebraMap_mem hc0, one_mul]
      exact hx

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
theorem Place.mem_toSubmodule_iff {P : Place k F} {x : F} :
    x ∈ P.toSubmodule ↔ P.val.valuation x ≤ 1 :=
  ⟨fun h ↦ h, fun h ↦ h⟩

/-- The filtration `A_m = π^{−m} O_P`, as `k`-submodules of the
function field. -/
noncomputable def Place.filtration (P : Place k F) (m : ℕ) :
    Submodule k F where
  carrier := {x | P.val.valuation (P.pi ^ m * x) ≤ 1}
  add_mem' := by
    intro a b ha hb
    change P.val.valuation (_ * (a + b)) ≤ 1
    rw [mul_add]
    exact le_trans (P.val.valuation.map_add _ _) (max_le ha hb)
  zero_mem' := by
    change P.val.valuation (_ * (0 : F)) ≤ 1
    rw [mul_zero, Valuation.map_zero]
    exact zero_le
  smul_mem' := by
    intro c x hx
    change P.val.valuation (_ * (c • x)) ≤ 1
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [zero_smul, mul_zero, Valuation.map_zero]
      exact zero_le
    · rw [mul_smul_comm, Algebra.smul_def, Valuation.map_mul,
        valuation_algebraMap_eq_one P.algebraMap_mem hc0, one_mul]
      exact hx

theorem Place.mem_filtration_iff {P : Place k F} {m : ℕ} {x : F} :
    x ∈ P.filtration m ↔ P.val.valuation (P.pi ^ m * x) ≤ 1 :=
  ⟨fun h ↦ h, fun h ↦ h⟩

theorem Place.filtration_zero (P : Place k F) :
    P.filtration 0 = P.toSubmodule := by
  ext x
  rw [Place.mem_filtration_iff, Place.mem_toSubmodule_iff, pow_zero,
    one_mul]

/-- The filtration is increasing. -/
theorem Place.filtration_mono (P : Place k F) {m n : ℕ} (h : m ≤ n) :
    P.filtration m ≤ P.filtration n := by
  intro x hx
  rw [Place.mem_filtration_iff] at hx ⊢
  have h1 : P.pi ^ n * x = P.pi ^ (n - m) * (P.pi ^ m * x) := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  rw [h1, Valuation.map_mul, Valuation.map_pow]
  calc P.val.valuation P.pi ^ (n - m) * P.val.valuation (P.pi ^ m * x)
      ≤ 1 * 1 := by
        refine mul_le_mul' ?_ hx
        exact pow_le_one' P.pi_valuation_lt_one.le _
    _ = 1 := one_mul 1

/-- **The one-step gauge**: each filtration step is spanned over the
previous one by a single negative monomial — the residue at the top
order. -/
theorem Place.filtration_succ_le (P : Place k F) (m : ℕ) :
    P.filtration (m + 1) ≤ P.filtration m ⊔
      Submodule.span k {P.pi ^ (-(m + 1 : ℕ) : ℤ)} := by
  intro x hx
  have hy : P.val.valuation (P.pi ^ (m + 1) * x) ≤ 1 :=
    Place.mem_filtration_iff.1 hx
  obtain ⟨c, hc⟩ := P.exists_residue hy
  have hpine : (P.pi ^ (-(m + 1 : ℕ) : ℤ) : F) ≠ 0 :=
    zpow_ne_zero _ P.pi_ne_zero
  rcases eq_or_ne (P.pi ^ (m + 1) * x - algebraMap k F c) 0 with h0 | h0
  · have hxc : x = c • (P.pi ^ (-(m + 1 : ℕ) : ℤ) : F) := by
      have h1 : P.pi ^ (m + 1) * x = algebraMap k F c := by
        rwa [sub_eq_zero] at h0
      have h2 : (P.pi ^ (m + 1) : F) ≠ 0 := pow_ne_zero _ P.pi_ne_zero
      rw [Algebra.smul_def, ← h1, zpow_neg, zpow_natCast]
      field_simp
    rw [hxc]
    exact Submodule.mem_sup_right
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · have hord : 1 ≤ P.ord (P.pi ^ (m + 1) * x - algebraMap k F c) := by
      have h1 := (P.ord_pos_iff h0).2 hc
      omega
    have hmem : x - c • (P.pi ^ (-(m + 1 : ℕ) : ℤ) : F) ∈
        P.filtration m := by
      rw [Place.mem_filtration_iff]
      have halg : P.pi ^ m * (x - c • (P.pi ^ (-(m + 1 : ℕ) : ℤ) : F)) =
          (P.pi ^ (m + 1) * x - algebraMap k F c) *
            P.pi ^ (-(1 : ℕ) : ℤ) := by
        have h2 : (P.pi : F) ≠ 0 := P.pi_ne_zero
        rw [Algebra.smul_def, zpow_neg, zpow_natCast, zpow_neg,
          zpow_natCast, pow_one]
        field_simp
        ring
      rw [halg]
      have hne : (P.pi ^ (m + 1) * x - algebraMap k F c) *
          P.pi ^ (-(1 : ℕ) : ℤ) ≠ 0 :=
        mul_ne_zero h0 (zpow_ne_zero _ P.pi_ne_zero)
      rw [← P.ord_nonneg_iff hne, P.ord_mul h0
        (zpow_ne_zero _ P.pi_ne_zero), ord_pi_zpow]
      omega
    have hdecomp : x = (x - c • (P.pi ^ (-(m + 1 : ℕ) : ℤ) : F)) +
        c • (P.pi ^ (-(m + 1 : ℕ) : ℤ) : F) := by
      ring
    rw [hdecomp]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hmem)
      (Submodule.mem_sup_right
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))

/-- Filtration membership in terms of the order. -/
theorem Place.mem_filtration_iff_ord {P : Place k F} {m : ℕ} {x : F} :
    x ∈ P.filtration m ↔ x = 0 ∨ -(m : ℤ) ≤ P.ord x := by
  rw [Place.mem_filtration_iff]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hne : P.pi ^ m * x ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ P.pi_ne_zero) hx
    rw [← P.ord_nonneg_iff hne,
      P.ord_mul (pow_ne_zero _ P.pi_ne_zero) hx,
      P.ord_pow P.pi_ne_zero, P.ord_pi, mul_one]
    constructor
    · intro h
      exact Or.inr (by omega)
    · rintro (h | h)
      · exact absurd h hx
      · omega

/-- **Commensurability of the filtration** (the analytic input to
Tate's residue): every filtration stage is almost contained in the
valuation ring. -/
theorem Place.filtration_almostLE (P : Place k F) (m : ℕ) :
    AlmostLE (P.filtration m) P.toSubmodule := by
  induction m with
  | zero =>
    rw [P.filtration_zero]
    exact AlmostLE.rfl
  | succ m ih =>
    refine AlmostLE.trans ?_ ih
    obtain ⟨W, hW, hle⟩ := AlmostLE.rfl (A := P.filtration m)
    refine ⟨Submodule.span k {(P.pi ^ (-(m + 1 : ℕ) : ℤ) : F)},
      FiniteDimensional.span_of_finite k (Set.finite_singleton _), ?_⟩
    exact P.filtration_succ_le m

/-- Multiplication by a nonzero element sends the valuation ring into
a filtration stage: the pole order. -/
theorem Place.mulLeft_toSubmodule_le_filtration (P : Place k F)
    {h : F} (hh : h ≠ 0) :
    P.toSubmodule.map (LinearMap.mulLeft k h) ≤
      P.filtration (-(P.ord h)).toNat := by
  rintro x ⟨y, hy, rfl⟩
  rw [Place.mem_filtration_iff]
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [LinearMap.mulLeft_apply, mul_zero, mul_zero,
      Valuation.map_zero]
    exact zero_le
  rw [LinearMap.mulLeft_apply, ← mul_assoc]
  rw [Valuation.map_mul]
  have h1 : P.val.valuation (P.pi ^ (-(P.ord h)).toNat * h) ≤ 1 := by
    have h2 : (P.pi ^ (-(P.ord h)).toNat * h) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ P.pi_ne_zero) hh
    rw [← P.ord_nonneg_iff h2, P.ord_mul (pow_ne_zero _ P.pi_ne_zero) hh,
      P.ord_pow P.pi_ne_zero, P.ord_pi, mul_one]
    omega
  calc P.val.valuation (P.pi ^ (-(P.ord h)).toNat * h) *
      P.val.valuation y ≤ 1 * 1 :=
        mul_le_mul' h1 (Place.mem_toSubmodule_iff.1 hy)
    _ = 1 := one_mul 1

/-- **Multiplication operators respect the commensurability class**:
`h · O_P ≺ O_P` — Tate's condition for the function field to act
through his algebra `E`. -/
theorem Place.mulLeft_almostLE (P : Place k F) {h : F} (hh : h ≠ 0) :
    AlmostLE (P.toSubmodule.map (LinearMap.mulLeft k h))
      P.toSubmodule :=
  AlmostLE.mono_left (P.mulLeft_toSubmodule_le_filtration hh)
    (P.filtration_almostLE _)

section Projection

/-- A chosen `k`-linear projection of the function field onto the
valuation ring of a place. -/
noncomputable def Place.proj (P : Place k F) : F →ₗ[k] F :=
  P.toSubmodule.projection
    (Classical.choose (Submodule.exists_isCompl P.toSubmodule))
    (Classical.choose_spec (Submodule.exists_isCompl P.toSubmodule))

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
theorem Place.proj_mem (P : Place k F) (x : F) :
    P.proj x ∈ P.toSubmodule :=
  Submodule.projection_apply_mem _ x

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
theorem Place.proj_eq_self (P : Place k F) {x : F}
    (hx : x ∈ P.toSubmodule) : P.proj x = x := by
  rw [Place.proj]
  have h1 := Submodule.projection_apply_left
    (Classical.choose_spec (Submodule.exists_isCompl P.toSubmodule))
    (⟨x, hx⟩ : ↥P.toSubmodule)
  exact h1

/-- A chosen `k`-linear projection of the function field onto a
filtration stage of a place. -/
noncomputable def Place.filtrationProj (P : Place k F) (m : ℕ) :
    F →ₗ[k] F :=
  (P.filtration m).projection
    (Classical.choose (Submodule.exists_isCompl (P.filtration m)))
    (Classical.choose_spec (Submodule.exists_isCompl (P.filtration m)))

theorem Place.filtrationProj_mem (P : Place k F) (m : ℕ) (x : F) :
    P.filtrationProj m x ∈ P.filtration m :=
  Submodule.projection_apply_mem _ x

theorem Place.filtrationProj_eq_self (P : Place k F) {m : ℕ} {x : F}
    (hx : x ∈ P.filtration m) : P.filtrationProj m x = x := by
  rw [Place.filtrationProj]
  exact Submodule.projection_apply_left
    (Classical.choose_spec (Submodule.exists_isCompl (P.filtration m)))
    (⟨x, hx⟩ : ↥(P.filtration m))

/-- **Tate's local operator**: the commutator of the projection with
multiplication, `c(h) = [ε, mult h]`. It lies in Tate's trace class
`E₀`: its range is almost inside `O_P` and its image of `O_P` is
finite-dimensional. -/
noncomputable def Place.commutatorProj (P : Place k F) (h : F) :
    Module.End k F :=
  P.proj ∘ₗ LinearMap.mulLeft k h - LinearMap.mulLeft k h ∘ₗ P.proj

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
theorem Place.commutatorProj_apply (P : Place k F) (h x : F) :
    P.commutatorProj h x = P.proj (h * x) - h * P.proj x := rfl

/-- `E₁`-membership: the range of `c(h)` is almost inside `O_P`. -/
theorem Place.commutatorProj_range_almostLE (P : Place k F) {h : F}
    (hh : h ≠ 0) :
    AlmostLE (LinearMap.range (P.commutatorProj h)) P.toSubmodule := by
  have hle : LinearMap.range (P.commutatorProj h) ≤
      P.toSubmodule ⊔ P.toSubmodule.map (LinearMap.mulLeft k h) := by
    rintro x ⟨y, rfl⟩
    rw [Place.commutatorProj_apply, sub_eq_add_neg]
    refine Submodule.add_mem _
      (Submodule.mem_sup_left (P.proj_mem _)) (Submodule.neg_mem _ ?_)
    exact Submodule.mem_sup_right ⟨P.proj y, P.proj_mem y, rfl⟩
  exact AlmostLE.mono_left hle
    (AlmostLE.sup AlmostLE.rfl (P.mulLeft_almostLE hh))

/-- `E₂`-membership: `c(h)` sends the valuation ring into a
finite-dimensional subspace, since it factors through the defect of
`h · O_P` over `O_P`. -/
theorem Place.finiteDimensional_commutatorProj_map (P : Place k F)
    {h : F} (hh : h ≠ 0) :
    FiniteDimensional k
      (P.toSubmodule.map (P.commutatorProj h)) := by
  obtain ⟨W, hW, hle⟩ := P.mulLeft_almostLE hh
  haveI := hW
  set δ : F →ₗ[k] F := P.proj - LinearMap.id with hδ
  have hmap : P.toSubmodule.map (P.commutatorProj h) ≤ W.map δ := by
    rintro x ⟨a, ha, rfl⟩
    -- `c(h) a = (ε − 1)(h a)` since `ε a = a`.
    have h1 : P.commutatorProj h a = δ (h * a) := by
      rw [hδ, Place.commutatorProj_apply, P.proj_eq_self ha]
      rfl
    rw [h1]
    -- `h a` decomposes over `O_P ⊔ W`, and `ε − 1` kills `O_P`.
    have h2 : h * a ∈ P.toSubmodule ⊔ W :=
      hle ⟨a, ha, rfl⟩
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 h2
    have h3 : δ (h * a) = δ w := by
      rw [← huw, map_add]
      have h4 : δ u = 0 := by
        rw [hδ, LinearMap.sub_apply, LinearMap.id_apply,
          P.proj_eq_self hu, sub_self]
      rw [h4, zero_add]
    rw [h3]
    exact ⟨w, hw, rfl⟩
  exact Submodule.finiteDimensional_of_le hmap

/-- Multiplication respects the commensurability class, including by
zero. -/
theorem Place.mulLeft_map_almostLE (P : Place k F) (h : F) :
    AlmostLE (P.toSubmodule.map (LinearMap.mulLeft k h))
      P.toSubmodule := by
  rcases eq_or_ne h 0 with rfl | hh
  · refine AlmostLE.of_le ?_
    rintro x ⟨y, -, rfl⟩
    rw [LinearMap.mulLeft_apply, zero_mul]
    exact Submodule.zero_mem _
  · exact P.mulLeft_almostLE hh

/-- The commutator operator is trace-class. -/
theorem Place.isTraceClass_commutatorProj (P : Place k F) (h : F) :
    IsTraceClass P.toSubmodule (P.commutatorProj h) := by
  rcases eq_or_ne h 0 with rfl | hh
  · have h1 : P.commutatorProj (0 : F) = 0 := by
      refine LinearMap.ext fun x ↦ ?_
      rw [Place.commutatorProj_apply, zero_mul, zero_mul, map_zero,
        sub_zero, LinearMap.zero_apply]
    rw [h1]
    exact IsTraceClass.zero _
  · exact ⟨P.commutatorProj_range_almostLE hh,
      P.finiteDimensional_commutatorProj_map hh⟩

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- **Tate's commutator identity**: the residue commutator decomposes
through the local operators, using commutativity of multiplication. -/
theorem Place.commutator_eq (P : Place k F) (f g : F) :
    (P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f) =
    P.commutatorProj (f * g) -
      LinearMap.mulLeft k g ∘ₗ P.commutatorProj f := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, Place.commutatorProj_apply, map_sub]
  have h1 : f * (g * x) = f * g * x := by ring
  rw [h1]
  ring

/-- **The Tate residue** of the pair `(f, g)` at a place — morally
`res_P (f dg)`: the trace of the commutator of `ε ∘ (mult f)` with
`mult g`. -/
noncomputable def Place.residue (P : Place k F) (f g : F) : k :=
  tateTrace ((P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
    LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f))

/-- The residue commutator is trace-class, hence finite-potent with a
well-defined trace. -/
theorem Place.isTraceClass_residue_commutator (P : Place k F)
    (f g : F) :
    IsTraceClass P.toSubmodule
      ((P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
        LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f)) := by
  rw [P.commutator_eq f g]
  exact (P.isTraceClass_commutatorProj (f * g)).sub
    ((P.isTraceClass_commutatorProj f).comp_left
      (P.mulLeft_map_almostLE g))

section OrdLink

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- Inverse multiplications compose to the identity. -/
theorem mulLeft_inv_comp {g : F} (hg : g ≠ 0) :
    LinearMap.mulLeft k g⁻¹ ∘ₗ LinearMap.mulLeft k g = LinearMap.id := by
  refine LinearMap.ext fun x ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.mulLeft_apply, LinearMap.id_apply, ← mul_assoc,
    inv_mul_cancel₀ hg, one_mul]

/-- The projection conjugated by multiplication: a projection onto
`g · O_P`. -/
noncomputable def Place.conjProj (P : Place k F) (g : F) :
    Module.End k F :=
  LinearMap.mulLeft k g ∘ₗ P.proj ∘ₗ LinearMap.mulLeft k g⁻¹

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
theorem Place.conjProj_apply (P : Place k F) (g x : F) :
    P.conjProj g x = g * P.proj (g⁻¹ * x) := rfl

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The conjugated projection is idempotent. -/
theorem Place.isIdempotentElem_conjProj (P : Place k F) {g : F}
    (hg : g ≠ 0) : IsIdempotentElem (P.conjProj g) := by
  refine LinearMap.ext fun x ↦ ?_
  change P.conjProj g (P.conjProj g x) = P.conjProj g x
  rw [Place.conjProj_apply, Place.conjProj_apply]
  congr 1
  rw [← mul_assoc, inv_mul_cancel₀ hg, one_mul]
  exact P.proj_eq_self (P.proj_mem _)

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The residue commutator at `(g⁻¹, g)` is the difference of the two
projections. -/
theorem Place.residue_commutator_inv_self (P : Place k F) {g : F}
    (hg : g ≠ 0) :
    (P.proj ∘ₗ LinearMap.mulLeft k g⁻¹) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k g⁻¹) =
    P.proj - P.conjProj g := by
  rw [LinearMap.comp_assoc, mulLeft_inv_comp hg, LinearMap.comp_id,
    Place.conjProj]

/-- If `g` is integral at `P`, the projection absorbs its conjugate:
`ε ∘ ε' = ε'`, since the range `g · O_P` sits inside `O_P`. -/
theorem Place.proj_comp_conjProj (P : Place k F) {g : F} (hg : g ≠ 0)
    (hord : 0 ≤ P.ord g) :
    P.proj ∘ₗ P.conjProj g = P.conjProj g := by
  refine LinearMap.ext fun x ↦ ?_
  rw [LinearMap.comp_apply, Place.conjProj_apply]
  refine P.proj_eq_self ?_
  rw [Place.mem_toSubmodule_iff]
  rcases eq_or_ne (P.proj (g⁻¹ * x)) 0 with h0 | h0
  · rw [h0, mul_zero, Valuation.map_zero]
    exact zero_le
  have h1 : P.val.valuation (P.proj (g⁻¹ * x)) ≤ 1 :=
    Place.mem_toSubmodule_iff.1 (P.proj_mem _)
  have h2 : P.val.valuation g ≤ 1 := (P.ord_nonneg_iff hg).1 hord
  calc P.val.valuation (g * P.proj (g⁻¹ * x)) =
      P.val.valuation g * P.val.valuation (P.proj (g⁻¹ * x)) :=
        Valuation.map_mul _ _ _
    _ ≤ 1 * 1 := mul_le_mul' h2 h1
    _ = 1 := one_mul 1

/-- The difference of the projections factors as
`ε ∘ (1 − ε')` when `g` is integral. -/
theorem Place.proj_sub_conjProj_eq (P : Place k F) {g : F} (hg : g ≠ 0)
    (hord : 0 ≤ P.ord g) :
    P.proj - P.conjProj g =
      P.proj ∘ₗ (LinearMap.id - P.conjProj g) := by
  rw [LinearMap.comp_sub, LinearMap.comp_id,
    P.proj_comp_conjProj hg hord]

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The projection is idempotent. -/
theorem Place.proj_comp_proj (P : Place k F) :
    P.proj ∘ₗ P.proj = P.proj := by
  refine LinearMap.ext fun x ↦ ?_
  exact P.proj_eq_self (P.proj_mem x)

/-- **Finite Taylor expansion in the valuation ring**: every integral
element agrees with a polynomial in the uniformizer up to `π^n O_P`,
by iterating the residue. -/
theorem Place.exists_taylor (P : Place k F) {a : F}
    (ha : a ∈ P.toSubmodule) (n : ℕ) :
    ∃ (c : Fin n → k) (b : F), b ∈ P.toSubmodule ∧
      a = (∑ i, c i • P.pi ^ (i : ℕ)) + P.pi ^ n * b := by
  induction n generalizing a with
  | zero =>
    refine ⟨![], a, ha, ?_⟩
    simp
  | succ n ih =>
    obtain ⟨c₀, hc₀⟩ := P.exists_residue ha
    have hmem : a - algebraMap k F c₀ ∈ P.toSubmodule := by
      rw [Place.mem_toSubmodule_iff]
      exact le_of_lt hc₀
    -- the once-shifted remainder is integral
    have hdiv : (a - algebraMap k F c₀) * P.pi⁻¹ ∈ P.toSubmodule := by
      rw [Place.mem_toSubmodule_iff]
      rcases eq_or_ne (a - algebraMap k F c₀) 0 with h0 | h0
      · rw [h0, zero_mul, Valuation.map_zero]
        exact zero_le
      have h1 : 1 ≤ P.ord (a - algebraMap k F c₀) := by
        have h2 := (P.ord_pos_iff h0).2 hc₀
        omega
      have h3 : (a - algebraMap k F c₀) * P.pi⁻¹ ≠ 0 :=
        mul_ne_zero h0 (inv_ne_zero P.pi_ne_zero)
      rw [← P.ord_nonneg_iff h3, P.ord_mul h0 (inv_ne_zero P.pi_ne_zero),
        P.ord_inv P.pi_ne_zero, P.ord_pi]
      omega
    obtain ⟨c, b, hb, hexp⟩ := ih hdiv
    refine ⟨Fin.cons c₀ c, b, hb, ?_⟩
    have hpi0 : (P.pi : F) ≠ 0 := P.pi_ne_zero
    have h4 : a = algebraMap k F c₀ +
        ((a - algebraMap k F c₀) * P.pi⁻¹) * P.pi := by
      field_simp
      ring
    rw [h4, hexp, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_succ, Fin.val_zero,
      pow_zero, Algebra.smul_def, mul_one]
    rw [add_mul, Finset.sum_mul]
    have hsum : ∑ i : Fin n,
        algebraMap k F (c i) * (P.pi : F) ^ (i : ℕ) * P.pi =
        ∑ i : Fin n, algebraMap k F (c i) * P.pi ^ ((i : ℕ) + 1) :=
      Finset.sum_congr rfl fun i _ ↦ by rw [mul_assoc, ← pow_succ]
    rw [hsum, pow_succ]
    ring

/-- Uniformizer powers land in `g · O_P` from the order of `g` on:
`π^n O_P ⊆ g O_P` for `n = ord g ≥ 0`. -/
theorem Place.pi_pow_mul_mem_map (P : Place k F) {g : F} (hg : g ≠ 0)
    (hord : 0 ≤ P.ord g) {b : F} (hb : b ∈ P.toSubmodule) :
    P.pi ^ (P.ord g).toNat * b ∈
      P.toSubmodule.map (LinearMap.mulLeft k g) := by
  refine ⟨g⁻¹ * P.pi ^ (P.ord g).toNat * b, ?_, ?_⟩
  · change P.val.valuation (g⁻¹ * P.pi ^ (P.ord g).toNat * b) ≤ 1
    rcases eq_or_ne b 0 with rfl | hb0
    · rw [mul_zero, Valuation.map_zero]
      exact zero_le
    have h1 : g⁻¹ * P.pi ^ (P.ord g).toNat * b ≠ 0 :=
      mul_ne_zero (mul_ne_zero (inv_ne_zero hg)
        (pow_ne_zero _ P.pi_ne_zero)) hb0
    rw [← P.ord_nonneg_iff h1,
      P.ord_mul (mul_ne_zero (inv_ne_zero hg)
        (pow_ne_zero _ P.pi_ne_zero)) hb0,
      P.ord_mul (inv_ne_zero hg) (pow_ne_zero _ P.pi_ne_zero),
      P.ord_inv hg, P.ord_pow P.pi_ne_zero, P.ord_pi, mul_one]
    have h2 : 0 ≤ P.ord b := (P.ord_nonneg_iff hb0).2
      (Place.mem_toSubmodule_iff.1 hb)
    omega
  · rw [LinearMap.mulLeft_apply]
    field_simp

/-- The image of the valuation ring under `1 − ε'` is spanned by the
images of the uniformizer powers below `ord g`. -/
theorem Place.map_id_sub_conjProj_le_span (P : Place k F)
    {g : F} (hg : g ≠ 0) (hord : 0 ≤ P.ord g) :
    P.toSubmodule.map (LinearMap.id - P.conjProj g) ≤
      Submodule.span k (Set.range fun i : Fin (P.ord g).toNat ↦
        (LinearMap.id - P.conjProj g : F →ₗ[k] F) ((P.pi : F) ^ (i : ℕ))) := by
  classical
  set n : ℕ := (P.ord g).toNat with hn
  set δ : F →ₗ[k] F := LinearMap.id - P.conjProj g with hδ
  have hker : ∀ x ∈ P.toSubmodule.map (LinearMap.mulLeft k g),
      δ x = 0 := by
    rintro x ⟨b, hb, rfl⟩
    rw [hδ, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.mulLeft_apply, Place.conjProj_apply, ← mul_assoc,
      inv_mul_cancel₀ hg, one_mul, P.proj_eq_self hb, sub_self]
  rintro x ⟨a, ha, rfl⟩
  obtain ⟨c, b, hb, hexp⟩ := P.exists_taylor ha n
  have h1 : δ a = ∑ i : Fin n, c i • δ ((P.pi : F) ^ (i : ℕ)) := by
    rw [hexp, map_add, map_sum]
    have h2 : δ (P.pi ^ n * b) = 0 :=
      hker _ (P.pi_pow_mul_mem_map hg hord hb)
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul]
  rw [h1]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, rfl⟩)

/-- The image of the valuation ring under `1 − ε'` has finite rank. -/
theorem Place.finiteDimensional_map_id_sub_conjProj (P : Place k F)
    {g : F} (hg : g ≠ 0) (hord : 0 ≤ P.ord g) :
    FiniteDimensional k
      (P.toSubmodule.map (LinearMap.id - P.conjProj g)) := by
  haveI : FiniteDimensional k (Submodule.span k
      (Set.range fun i : Fin (P.ord g).toNat ↦
        (LinearMap.id - P.conjProj g : F →ₗ[k] F) ((P.pi : F) ^ (i : ℕ)))) :=
    FiniteDimensional.span_of_finite k (Set.finite_range _)
  exact Submodule.finiteDimensional_of_le
    (P.map_id_sub_conjProj_le_span hg hord)

/-- The transversal projection `ρ = (1 − ε') ∘ ε`: an idempotent
projecting onto a transversal of `g · O_P` in `O_P`. -/
noncomputable def Place.transversalProj (P : Place k F) (g : F) :
    Module.End k F :=
  (LinearMap.id - P.conjProj g) ∘ₗ P.proj

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
theorem Place.transversalProj_apply (P : Place k F) (g x : F) :
    P.transversalProj g x = P.proj x - P.conjProj g (P.proj x) := rfl

/-- The transversal projection is idempotent. -/
theorem Place.isIdempotentElem_transversalProj (P : Place k F) {g : F}
    (hg : g ≠ 0) (hord : 0 ≤ P.ord g) :
    IsIdempotentElem (P.transversalProj g) := by
  have hcc := P.proj_comp_conjProj hg hord
  have hii := P.isIdempotentElem_conjProj hg
  refine LinearMap.ext fun x ↦ ?_
  change P.transversalProj g (P.transversalProj g x) =
    P.transversalProj g x
  rw [Place.transversalProj_apply, Place.transversalProj_apply]
  set a := P.proj x with ha
  have h1 : P.proj (a - P.conjProj g a) = a - P.conjProj g a := by
    rw [map_sub]
    have h2 := LinearMap.congr_fun hcc a
    rw [LinearMap.comp_apply] at h2
    rw [h2, ha, P.proj_eq_self (P.proj_mem x)]
  rw [h1]
  have h3 : P.conjProj g (a - P.conjProj g a) = 0 := by
    rw [map_sub]
    have h4 := LinearMap.congr_fun hii a
    rw [Module.End.mul_apply] at h4
    rw [h4, sub_self]
  rw [h3, sub_zero]

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The range of the transversal projection is the image of the
valuation ring under `1 − ε'`. -/
theorem Place.range_transversalProj (P : Place k F) (g : F) :
    LinearMap.range (P.transversalProj g) =
      P.toSubmodule.map (LinearMap.id - P.conjProj g) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, rfl⟩
    exact ⟨P.proj y, P.proj_mem y, rfl⟩
  · rintro x ⟨a, ha, rfl⟩
    refine ⟨a, ?_⟩
    rw [Place.transversalProj_apply, P.proj_eq_self ha]
    rfl

theorem Place.finiteDimensional_range_transversalProj (P : Place k F)
    {g : F} (hg : g ≠ 0) (hord : 0 ≤ P.ord g) :
    FiniteDimensional k (LinearMap.range (P.transversalProj g)) := by
  rw [P.range_transversalProj g]
  exact P.finiteDimensional_map_id_sub_conjProj hg hord

/-- **The residue of `dg/g` is the transversal dimension**: for `g`
integral at `P`,
`res_P(g⁻¹ dg) = dim_k O_P / g O_P` (cast into `k`). -/
theorem Place.residue_inv_self_eq_finrank (P : Place k F) {g : F}
    (hg : g ≠ 0) (hord : 0 ≤ P.ord g) :
    P.residue g⁻¹ g = (Module.finrank k
      (P.toSubmodule.map (LinearMap.id - P.conjProj g)) : k) := by
  rw [Place.residue, P.residue_commutator_inv_self hg,
    P.proj_sub_conjProj_eq hg hord]
  haveI h1 : FiniteDimensional k (LinearMap.range
      ((P.proj ∘ₗ (LinearMap.id - P.conjProj g)) ^ 2)) := by
    have h2 : P.proj ∘ₗ (LinearMap.id - P.conjProj g) =
        P.proj - P.conjProj g := (P.proj_sub_conjProj_eq hg hord).symm
    rw [h2]
    have h3 := P.isTraceClass_residue_commutator g⁻¹ g
    rw [P.residue_commutator_inv_self hg] at h3
    have h4 : ((P.proj - P.conjProj g) ^ 2 : Module.End k F) =
        (P.proj - P.conjProj g) ∘ₗ (P.proj - P.conjProj g) := by
      rw [pow_two]
      rfl
    rw [h4]
    exact h3.finiteDimensional_range_comp h3
  haveI h5 : FiniteDimensional k (LinearMap.range
      (((LinearMap.id - P.conjProj g) ∘ₗ P.proj) ^ 2)) := by
    have h6 : (((LinearMap.id - P.conjProj g) ∘ₗ P.proj) ^ 2 :
        Module.End k F) = P.transversalProj g := by
      rw [pow_two]
      exact P.isIdempotentElem_transversalProj hg hord
    rw [h6]
    exact P.finiteDimensional_range_transversalProj hg hord
  rw [tateTrace_comp_comm_of_sq P.proj (LinearMap.id - P.conjProj g)]
  have h7 : (LinearMap.id - P.conjProj g) ∘ₗ P.proj =
      P.transversalProj g := rfl
  rw [h7]
  haveI := P.finiteDimensional_range_transversalProj hg hord
  rw [tateTrace_of_isIdempotentElem
    (P.isIdempotentElem_transversalProj hg hord),
    P.range_transversalProj g]

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- Elements killed by `1 − ε'` lie in `g · O_P`. -/
theorem Place.mem_map_mulLeft_of_id_sub_conjProj_eq_zero
    (P : Place k F) {g x : F}
    (hx : (LinearMap.id - P.conjProj g : F →ₗ[k] F) x = 0) :
    x ∈ P.toSubmodule.map (LinearMap.mulLeft k g) := by
  rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx
  refine ⟨P.proj (g⁻¹ * x), P.proj_mem _, ?_⟩
  rw [LinearMap.mulLeft_apply]
  exact (hx.trans (P.conjProj_apply g x)).symm

/-- Nonzero elements of `g · O_P` have order at least `ord g`. -/
theorem Place.ord_le_ord_of_mem_map_mulLeft (P : Place k F) {g x : F}
    (hg : g ≠ 0) (hx0 : x ≠ 0)
    (hx : x ∈ P.toSubmodule.map (LinearMap.mulLeft k g)) :
    P.ord g ≤ P.ord x := by
  obtain ⟨b, hb, rfl⟩ := hx
  rw [LinearMap.mulLeft_apply] at hx0 ⊢
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hx0
    exact hx0 rfl
  rw [P.ord_mul hg hb0]
  have h1 : 0 ≤ P.ord b :=
    (P.ord_nonneg_iff hb0).2 (Place.mem_toSubmodule_iff.1 hb)
  omega

/-- **Dominant-term order**: a combination of uniformizer powers of
exponents below `n` with some nonzero coefficient is nonzero, of order
below `n`. -/
theorem Place.ord_sum_smul_pow_pi_lt (P : Place k F) {n : ℕ}
    {c : Fin n → k} {i : Fin n} (hi : c i ≠ 0) :
    (∑ j, c j • (P.pi : F) ^ (j : ℕ)) ≠ 0 ∧
      P.ord (∑ j, c j • (P.pi : F) ^ (j : ℕ)) < (n : ℤ) := by
  classical
  set s : Finset (Fin n) :=
    Finset.filter (fun j : Fin n ↦ c j ≠ 0) Finset.univ with hs
  have his : i ∈ s := Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩
  have hne : s.Nonempty := ⟨i, his⟩
  set i₀ : Fin n := s.min' hne with hi₀
  have hi₀s : i₀ ∈ s := s.min'_mem hne
  have hc₀ : c i₀ ≠ 0 := (Finset.mem_filter.1 hi₀s).2
  have hterm : ∀ j : Fin n, c j ≠ 0 →
      P.val.valuation (c j • (P.pi : F) ^ (j : ℕ)) =
        P.val.valuation P.pi ^ ((j : ℕ) : ℤ) := by
    intro j hj
    rw [Algebra.smul_def, Valuation.map_mul,
      valuation_algebraMap_eq_one P.algebraMap_mem hj, one_mul,
      Valuation.map_pow, ← zpow_natCast]
  have hsum : ∑ j, c j • (P.pi : F) ^ (j : ℕ) =
      ∑ j ∈ s, c j • (P.pi : F) ^ (j : ℕ) := by
    rw [hs]
    refine (Finset.sum_filter_of_ne
      (p := fun j : Fin n ↦ c j ≠ 0) fun j _ hj h0 ↦ hj ?_).symm
    rw [h0, zero_smul]
  have hdom : P.val.valuation (∑ j ∈ s, c j • (P.pi : F) ^ (j : ℕ)) =
      P.val.valuation P.pi ^ ((i₀ : ℕ) : ℤ) := by
    rw [← hterm i₀ hc₀]
    refine valuation_sum_eq_of_forall_lt hi₀s fun j hj hji ↦ ?_
    have hcj : c j ≠ 0 := (Finset.mem_filter.1 hj).2
    rw [hterm j hcj, hterm i₀ hc₀,
      zpow_lt_zpow_iff_right_of_lt_one₀ P.pi_valuation_pos
        P.pi_valuation_lt_one]
    have h1 : i₀ < j := lt_of_le_of_ne (s.min'_le j hj)
      fun h ↦ hji h.symm
    have h2 : (i₀ : ℕ) < (j : ℕ) := h1
    exact_mod_cast h2
  have hval : P.val.valuation (∑ j, c j • (P.pi : F) ^ (j : ℕ)) =
      P.val.valuation P.pi ^ ((i₀ : ℕ) : ℤ) := by
    rw [hsum, hdom]
  have hz0 : (∑ j, c j • (P.pi : F) ^ (j : ℕ)) ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hval
    exact zpow_ne_zero _ P.pi_valuation_pos.ne' hval.symm
  refine ⟨hz0, ?_⟩
  rw [P.ord_eq_of_valuation_eq_zpow hz0 hval]
  exact_mod_cast i₀.isLt

/-- The images of `1, π, …, π^{ord g − 1}` under `1 − ε'` are linearly
independent: a vanishing combination would put an element of order
below `ord g` into `g · O_P`. -/
theorem Place.linearIndependent_id_sub_conjProj_pow (P : Place k F)
    {g : F} (hg : g ≠ 0) (hord : 0 ≤ P.ord g) :
    LinearIndependent k fun i : Fin (P.ord g).toNat ↦
      (LinearMap.id - P.conjProj g : F →ₗ[k] F) ((P.pi : F) ^ (i : ℕ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  have hδz : (LinearMap.id - P.conjProj g : F →ₗ[k] F)
      (∑ j, c j • (P.pi : F) ^ (j : ℕ)) = 0 := by
    rw [map_sum]
    have h1 : ∑ j : Fin (P.ord g).toNat,
        (LinearMap.id - P.conjProj g : F →ₗ[k] F) (c j • (P.pi : F) ^ (j : ℕ)) =
        ∑ j : Fin (P.ord g).toNat,
          c j • (LinearMap.id - P.conjProj g : F →ₗ[k] F) ((P.pi : F) ^ (j : ℕ)) :=
      Finset.sum_congr rfl fun j _ ↦ map_smul _ _ _
    exact h1.trans hc
  obtain ⟨hz0, hzlt⟩ := P.ord_sum_smul_pow_pi_lt hi
  have hle := P.ord_le_ord_of_mem_map_mulLeft hg hz0
    (P.mem_map_mulLeft_of_id_sub_conjProj_eq_zero hδz)
  omega

/-- **The transversal dimension is the order**: for `g` integral at
`P`, the image of `O_P` under `1 − ε'` has dimension `ord_P g`. -/
theorem Place.finrank_map_id_sub_conjProj (P : Place k F) {g : F}
    (hg : g ≠ 0) (hord : 0 ≤ P.ord g) :
    Module.finrank k
      (P.toSubmodule.map (LinearMap.id - P.conjProj g)) =
      (P.ord g).toNat := by
  haveI := P.finiteDimensional_map_id_sub_conjProj hg hord
  refine le_antisymm ?_ ?_
  · haveI : FiniteDimensional k (Submodule.span k
        (Set.range fun i : Fin (P.ord g).toNat ↦
          (LinearMap.id - P.conjProj g : F →ₗ[k] F) ((P.pi : F) ^ (i : ℕ)))) :=
      FiniteDimensional.span_of_finite k (Set.finite_range _)
    refine le_trans (Submodule.finrank_mono
      (P.map_id_sub_conjProj_le_span hg hord)) ?_
    have h1 := finrank_range_le_card (R := k)
      (b := fun i : Fin (P.ord g).toNat ↦
        (LinearMap.id - P.conjProj g : F →ₗ[k] F) ((P.pi : F) ^ (i : ℕ)))
    rw [Fintype.card_fin] at h1
    exact h1
  · have hmem : ∀ i : Fin (P.ord g).toNat,
        (LinearMap.id - P.conjProj g : F →ₗ[k] F) ((P.pi : F) ^ (i : ℕ)) ∈
          P.toSubmodule.map (LinearMap.id - P.conjProj g) := by
      intro i
      refine ⟨(P.pi : F) ^ (i : ℕ), ?_, rfl⟩
      change P.val.valuation ((P.pi : F) ^ (i : ℕ)) ≤ 1
      rw [Valuation.map_pow]
      exact pow_le_one' P.pi_valuation_lt_one.le _
    have hw : LinearIndependent k fun i : Fin (P.ord g).toNat ↦
        (⟨(LinearMap.id - P.conjProj g : F →ₗ[k] F) ((P.pi : F) ^ (i : ℕ)),
          hmem i⟩ :
          ↥(P.toSubmodule.map (LinearMap.id - P.conjProj g))) := by
      apply LinearIndependent.of_comp
        (P.toSubmodule.map (LinearMap.id - P.conjProj g)).subtype
      exact P.linearIndependent_id_sub_conjProj_pow hg hord
    have hcard := hw.fintype_card_le_finrank
    rw [Fintype.card_fin] at hcard
    exact hcard

/-- **Tate's ord-link** — the residue of `dg/g` is the order of `g`:
for `g` integral at `P`, `res_P(g⁻¹ dg) = ord_P g`, cast into `k`.
This is the anchor identity connecting the trace-theoretic residue to
the divisor theory. -/
theorem Place.residue_inv_self (P : Place k F) {g : F} (hg : g ≠ 0)
    (hord : 0 ≤ P.ord g) :
    P.residue g⁻¹ g = ((P.ord g).toNat : k) := by
  rw [P.residue_inv_self_eq_finrank hg hord,
    P.finrank_map_id_sub_conjProj hg hord]

end OrdLink

section ResidueCalculus

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The residue commutator is additive in the first slot. -/
theorem Place.residue_commutator_add_left (P : Place k F)
    (f₁ f₂ g : F) :
    (P.proj ∘ₗ LinearMap.mulLeft k (f₁ + f₂)) ∘ₗ
        LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ
        (P.proj ∘ₗ LinearMap.mulLeft k (f₁ + f₂)) =
    ((P.proj ∘ₗ LinearMap.mulLeft k f₁) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f₁)) +
    ((P.proj ∘ₗ LinearMap.mulLeft k f₂) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f₂)) := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, add_mul, map_add]
  ring

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The residue commutator is additive in the second slot. -/
theorem Place.residue_commutator_add_right (P : Place k F)
    (f g₁ g₂ : F) :
    (P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ
        LinearMap.mulLeft k (g₁ + g₂) -
      LinearMap.mulLeft k (g₁ + g₂) ∘ₗ
        (P.proj ∘ₗ LinearMap.mulLeft k f) =
    ((P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g₁ -
      LinearMap.mulLeft k g₁ ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f)) +
    ((P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g₂ -
      LinearMap.mulLeft k g₂ ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f)) := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, add_mul,
    map_add]
  ring

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The residue commutator scales in the first slot. -/
theorem Place.residue_commutator_smul_left (P : Place k F) (c : k)
    (f g : F) :
    (P.proj ∘ₗ LinearMap.mulLeft k (c • f)) ∘ₗ
        LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ
        (P.proj ∘ₗ LinearMap.mulLeft k (c • f)) =
    c • ((P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f)) := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, smul_mul_assoc,
    map_smul, smul_sub]

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The residue commutator scales in the second slot. -/
theorem Place.residue_commutator_smul_right (P : Place k F) (c : k)
    (f g : F) :
    (P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ
        LinearMap.mulLeft k (c • g) -
      LinearMap.mulLeft k (c • g) ∘ₗ
        (P.proj ∘ₗ LinearMap.mulLeft k f) =
    c • ((P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f)) := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, smul_mul_assoc,
    map_smul, smul_sub]

/-- **Additivity of the residue in the first argument.** -/
theorem Place.residue_add_left (P : Place k F) (f₁ f₂ g : F) :
    P.residue (f₁ + f₂) g = P.residue f₁ g + P.residue f₂ g := by
  have hφ := P.isTraceClass_residue_commutator f₁ g
  have hψ := P.isTraceClass_residue_commutator f₂ g
  haveI := hφ.finiteDimensional_range_comp hφ
  haveI := hφ.finiteDimensional_range_comp hψ
  haveI := hψ.finiteDimensional_range_comp hφ
  haveI := hψ.finiteDimensional_range_comp hψ
  rw [Place.residue, Place.residue, Place.residue,
    P.residue_commutator_add_left f₁ f₂ g]
  exact tateTrace_add_of_sq _ _

/-- **Additivity of the residue in the second argument.** -/
theorem Place.residue_add_right (P : Place k F) (f g₁ g₂ : F) :
    P.residue f (g₁ + g₂) = P.residue f g₁ + P.residue f g₂ := by
  have hφ := P.isTraceClass_residue_commutator f g₁
  have hψ := P.isTraceClass_residue_commutator f g₂
  haveI := hφ.finiteDimensional_range_comp hφ
  haveI := hφ.finiteDimensional_range_comp hψ
  haveI := hψ.finiteDimensional_range_comp hφ
  haveI := hψ.finiteDimensional_range_comp hψ
  rw [Place.residue, Place.residue, Place.residue,
    P.residue_commutator_add_right f g₁ g₂]
  exact tateTrace_add_of_sq _ _

/-- **The residue scales in the first argument.** -/
theorem Place.residue_smul_left (P : Place k F) (c : k) (f g : F) :
    P.residue (c • f) g = c * P.residue f g := by
  set C : Module.End k F :=
    (P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f)
    with hC
  have hφ := P.isTraceClass_residue_commutator f g
  rw [← hC] at hφ
  haveI : FiniteDimensional k (LinearMap.range ((C ^ 2 :
      Module.End k F))) := by
    have h2 : (C ^ 2 : Module.End k F) = C ∘ₗ C := by
      rw [pow_two]
      rfl
    rw [h2]
    exact hφ.finiteDimensional_range_comp hφ
  rw [Place.residue, Place.residue,
    P.residue_commutator_smul_left c f g, ← hC,
    tateTrace_smul (isTateCore_range_pow C 2)]

/-- **The residue scales in the second argument.** -/
theorem Place.residue_smul_right (P : Place k F) (c : k) (f g : F) :
    P.residue f (c • g) = c * P.residue f g := by
  set C : Module.End k F :=
    (P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f)
    with hC
  have hφ := P.isTraceClass_residue_commutator f g
  rw [← hC] at hφ
  haveI : FiniteDimensional k (LinearMap.range ((C ^ 2 :
      Module.End k F))) := by
    have h2 : (C ^ 2 : Module.End k F) = C ∘ₗ C := by
      rw [pow_two]
      rfl
    rw [h2]
    exact hφ.finiteDimensional_range_comp hφ
  rw [Place.residue, Place.residue,
    P.residue_commutator_smul_right c f g, ← hC,
    tateTrace_smul (isTateCore_range_pow C 2)]

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The valuation ring is closed under multiplication. -/
theorem Place.mul_mem_toSubmodule (P : Place k F) {a b : F}
    (ha : a ∈ P.toSubmodule) (hb : b ∈ P.toSubmodule) :
    a * b ∈ P.toSubmodule := by
  rw [Place.mem_toSubmodule_iff] at ha hb ⊢
  rw [Valuation.map_mul]
  calc P.val.valuation a * P.val.valuation b ≤ 1 * 1 :=
      mul_le_mul' ha hb
    _ = 1 := one_mul 1

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- **Vanishing for integral pairs** (Tate's property (R2)): when `f`
and `g` are both integral at `P`, the residue commutator kills the
valuation ring and lands in it, so it squares to zero. -/
theorem Place.residue_eq_zero_of_mem (P : Place k F) {f g : F}
    (hf : f ∈ P.toSubmodule) (hg : g ∈ P.toSubmodule) :
    P.residue f g = 0 := by
  set C : Module.End k F :=
    (P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (P.proj ∘ₗ LinearMap.mulLeft k f)
    with hC
  have happ : ∀ x : F,
      C x = P.proj (f * (g * x)) - g * P.proj (f * x) := by
    intro x
    rw [hC]
    rfl
  have hker : ∀ x ∈ P.toSubmodule, C x = 0 := by
    intro x hx
    rw [happ]
    have h1 : f * (g * x) ∈ P.toSubmodule :=
      P.mul_mem_toSubmodule hf (P.mul_mem_toSubmodule hg hx)
    have h2 : f * x ∈ P.toSubmodule := P.mul_mem_toSubmodule hf hx
    rw [P.proj_eq_self h1, P.proj_eq_self h2]
    ring
  have hrange : ∀ x : F, C x ∈ P.toSubmodule := by
    intro x
    rw [happ]
    exact Submodule.sub_mem _ (P.proj_mem _)
      (P.mul_mem_toSubmodule hg (P.proj_mem _))
  have hnil : IsNilpotent C := by
    refine ⟨2, ?_⟩
    have h2 : (C ^ 2 : Module.End k F) = C ∘ₗ C := by
      rw [pow_two]
      rfl
    rw [h2]
    refine LinearMap.ext fun x ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    exact hker _ (hrange x)
  rw [Place.residue, ← hC]
  exact tateTrace_of_isNilpotent hnil

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- **The square-zero pattern for integral pairs**, for any projection
onto the valuation ring: the commutator kills `O_P` and lands in it. -/
theorem Place.commutator_comp_self_eq_zero (P : Place k F)
    {ε : F →ₗ[k] F} (hεr : ∀ x : F, ε x ∈ P.toSubmodule)
    (hεf : ∀ x ∈ P.toSubmodule, ε x = x)
    {f g : F} (hf : f ∈ P.toSubmodule) (hg : g ∈ P.toSubmodule) :
    ((ε ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (ε ∘ₗ LinearMap.mulLeft k f)) ∘ₗ
    ((ε ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (ε ∘ₗ LinearMap.mulLeft k f)) = 0 := by
  set C : Module.End k F :=
    (ε ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (ε ∘ₗ LinearMap.mulLeft k f)
    with hC
  have happ : ∀ x : F,
      C x = ε (f * (g * x)) - g * ε (f * x) := fun x ↦ rfl
  have hker : ∀ x ∈ P.toSubmodule, C x = 0 := by
    intro x hx
    rw [happ]
    have h1 : f * (g * x) ∈ P.toSubmodule :=
      P.mul_mem_toSubmodule hf (P.mul_mem_toSubmodule hg hx)
    have h2 : f * x ∈ P.toSubmodule := P.mul_mem_toSubmodule hf hx
    rw [hεf _ h1, hεf _ h2]
    ring
  have hrange : ∀ x : F, C x ∈ P.toSubmodule := by
    intro x
    rw [happ]
    exact Submodule.sub_mem _ (hεr _)
      (P.mul_mem_toSubmodule hg (hεr _))
  refine LinearMap.ext fun x ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  exact hker _ (hrange x)

/-- The chosen bottom-stage filtration projection satisfies the
square-zero pattern for integral pairs. -/
theorem Place.filtrationProj_commutator_comp_self_eq_zero
    (P : Place k F) {f g : F} (hf : f ∈ P.toSubmodule)
    (hg : g ∈ P.toSubmodule) :
    ((P.filtrationProj 0 ∘ₗ LinearMap.mulLeft k f) ∘ₗ
        LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ
        (P.filtrationProj 0 ∘ₗ LinearMap.mulLeft k f)) ∘ₗ
    ((P.filtrationProj 0 ∘ₗ LinearMap.mulLeft k f) ∘ₗ
        LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ
        (P.filtrationProj 0 ∘ₗ LinearMap.mulLeft k f)) = 0 := by
  refine P.commutator_comp_self_eq_zero ?_ ?_ hf hg
  · intro x
    rw [← P.filtration_zero]
    exact P.filtrationProj_mem 0 x
  · intro x hx
    refine P.filtrationProj_eq_self ?_
    rw [P.filtration_zero]
    exact hx

/-- The residue vanishes when the first argument is zero. -/
theorem Place.residue_zero_left (P : Place k F) (g : F) :
    P.residue 0 g = 0 := by
  rw [← zero_smul k (0 : F), P.residue_smul_left, zero_mul]

/-- The residue vanishes when the second argument is zero. -/
theorem Place.residue_zero_right (P : Place k F) (f : F) :
    P.residue f 0 = 0 := by
  rw [← zero_smul k (0 : F), P.residue_smul_right, zero_mul]

/-- **Independence of the projection**: the residue may be computed
with any linear projection onto the valuation ring. The difference of
two projections kills `O_P` and lands in it, so all its composites
against multiplication operators have finite-rank products, and the
difference of the commutators is a traceless commutator. -/
theorem Place.residue_eq_of_projection (P : Place k F)
    {π : F →ₗ[k] F} (hmem : ∀ x : F, π x ∈ P.toSubmodule)
    (heq : ∀ x ∈ P.toSubmodule, π x = x) (f g : F) :
    tateTrace ((π ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (π ∘ₗ LinearMap.mulLeft k f)) =
    P.residue f g := by
  set θ : F →ₗ[k] F := π - P.proj with hθ
  have hθmem : ∀ x : F, θ x ∈ P.toSubmodule := fun x ↦ by
    rw [hθ, LinearMap.sub_apply]
    exact Submodule.sub_mem _ (hmem x) (P.proj_mem x)
  have hθker : ∀ x ∈ P.toSubmodule, θ x = 0 := fun x hx ↦ by
    rw [hθ, LinearMap.sub_apply, heq x hx, P.proj_eq_self hx, sub_self]
  -- the key finiteness: `θ (h O_P)` is finite-dimensional
  have hfin : ∀ h : F, FiniteDimensional k
      ((P.toSubmodule.map (LinearMap.mulLeft k h)).map θ) := by
    intro h
    obtain ⟨W, hW, hle⟩ := P.mulLeft_map_almostLE h
    haveI := hW
    have h1 : (P.toSubmodule.map (LinearMap.mulLeft k h)).map θ ≤
        W.map θ := by
      rintro x ⟨y, hy, rfl⟩
      obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 (hle hy)
      have h2 : θ y = θ w := by
        rw [← huw, map_add, hθker u hu, zero_add]
      rw [h2]
      exact ⟨w, hw, rfl⟩
    exact Submodule.finiteDimensional_of_le h1
  have hkey : ∀ (h x : F), x ∈ P.toSubmodule →
      θ (h * x) ∈ (P.toSubmodule.map (LinearMap.mulLeft k h)).map θ :=
    fun h x hx ↦ ⟨h * x, ⟨x, hx, rfl⟩, rfl⟩
  set S : F →ₗ[k] F := θ ∘ₗ LinearMap.mulLeft k f with hS
  have hSapp : ∀ x : F, S x = θ (f * x) := fun x ↦ rfl
  have hSmem : ∀ x : F, S x ∈ P.toSubmodule := fun x ↦ hθmem _
  -- the four squared-range instances for the commutator of `S` with
  -- multiplication by `g`
  haveI hI1 : FiniteDimensional k (LinearMap.range
      (((S ∘ₗ LinearMap.mulLeft k g) ^ 2 : Module.End k F))) := by
    refine Submodule.finiteDimensional_of_le (S₂ := (P.toSubmodule.map
      (LinearMap.mulLeft k (f * g))).map θ) ?_
    · rintro x ⟨y, rfl⟩
      have h1 : (((S ∘ₗ LinearMap.mulLeft k g) ^ 2 :
          Module.End k F)) y =
          θ (f * (g * θ (f * (g * y)))) := by
        rw [pow_two, Module.End.mul_apply]
        rfl
      rw [h1]
      have h2 : f * (g * θ (f * (g * y))) =
          f * g * θ (f * (g * y)) := by ring
      rw [h2]
      exact hkey _ _ (hθmem _)
  haveI hI2 : FiniteDimensional k (LinearMap.range
      (((LinearMap.mulLeft k g ∘ₗ S) ^ 2 : Module.End k F))) := by
    haveI := hfin (f * g)
    refine Submodule.finiteDimensional_of_le
      (S₂ := ((P.toSubmodule.map (LinearMap.mulLeft k (f * g))).map
        θ).map (LinearMap.mulLeft k g)) ?_
    · rintro x ⟨y, rfl⟩
      have h1 : (((LinearMap.mulLeft k g ∘ₗ S) ^ 2 :
          Module.End k F)) y =
          g * θ (f * (g * θ (f * y))) := by
        rw [pow_two, Module.End.mul_apply]
        rfl
      rw [h1]
      have h2 : f * (g * θ (f * y)) = f * g * θ (f * y) := by ring
      rw [h2]
      exact ⟨θ (f * g * θ (f * y)), hkey _ _ (hθmem _), rfl⟩
  haveI hI3 : FiniteDimensional k (LinearMap.range
      ((S ∘ₗ LinearMap.mulLeft k g) ∘ₗ
        (LinearMap.mulLeft k g ∘ₗ S))) := by
    refine Submodule.finiteDimensional_of_le (S₂ := (P.toSubmodule.map
      (LinearMap.mulLeft k (f * (g * g)))).map θ) ?_
    · rintro x ⟨y, rfl⟩
      have h1 : ((S ∘ₗ LinearMap.mulLeft k g) ∘ₗ
          (LinearMap.mulLeft k g ∘ₗ S)) y =
          θ (f * (g * (g * θ (f * y)))) := by
        rfl
      rw [h1]
      have h2 : f * (g * (g * θ (f * y))) =
          f * (g * g) * θ (f * y) := by ring
      rw [h2]
      exact hkey _ _ (hθmem _)
  haveI hI4 : FiniteDimensional k (LinearMap.range
      ((LinearMap.mulLeft k g ∘ₗ S) ∘ₗ
        (S ∘ₗ LinearMap.mulLeft k g))) := by
    haveI := hfin f
    refine Submodule.finiteDimensional_of_le
      (S₂ := ((P.toSubmodule.map (LinearMap.mulLeft k f)).map
        θ).map (LinearMap.mulLeft k g)) ?_
    · rintro x ⟨y, rfl⟩
      have h1 : ((LinearMap.mulLeft k g ∘ₗ S) ∘ₗ
          (S ∘ₗ LinearMap.mulLeft k g)) y =
          g * θ (f * θ (f * (g * y))) := by
        rfl
      rw [h1]
      exact ⟨θ (f * θ (f * (g * y))), hkey _ _ (hθmem _), rfl⟩
  -- the difference of the commutators is trace-class
  have hDtc : IsTraceClass P.toSubmodule
      (S ∘ₗ LinearMap.mulLeft k g -
        LinearMap.mulLeft k g ∘ₗ S) := by
    constructor
    · have hle : LinearMap.range (S ∘ₗ LinearMap.mulLeft k g -
          LinearMap.mulLeft k g ∘ₗ S) ≤
          P.toSubmodule ⊔
            P.toSubmodule.map (LinearMap.mulLeft k g) := by
        rintro x ⟨y, rfl⟩
        have h1 : (S ∘ₗ LinearMap.mulLeft k g -
            LinearMap.mulLeft k g ∘ₗ S) y =
            θ (f * (g * y)) - g * S y := by
          rfl
        rw [h1, sub_eq_add_neg]
        refine Submodule.add_mem _
          (Submodule.mem_sup_left (hθmem _))
          (Submodule.neg_mem _ (Submodule.mem_sup_right
            ⟨S y, hSmem y, rfl⟩))
      exact AlmostLE.mono_left hle
        (AlmostLE.sup AlmostLE.rfl (P.mulLeft_map_almostLE g))
    · haveI := hfin (f * g)
      haveI := hfin f
      refine Submodule.finiteDimensional_of_le
        (S₂ := (P.toSubmodule.map
            (LinearMap.mulLeft k (f * g))).map θ ⊔
          ((P.toSubmodule.map (LinearMap.mulLeft k f)).map
            θ).map (LinearMap.mulLeft k g)) ?_
      rintro x ⟨a, ha, rfl⟩
      have h1 : (S ∘ₗ LinearMap.mulLeft k g -
          LinearMap.mulLeft k g ∘ₗ S) a =
          θ (f * (g * a)) - g * θ (f * a) := by
        rfl
      rw [h1]
      have h2 : f * (g * a) = f * g * a := by ring
      rw [h2, sub_eq_add_neg]
      refine Submodule.add_mem _
        (Submodule.mem_sup_left (hkey _ _ ha))
        (Submodule.neg_mem _ (Submodule.mem_sup_right
          ⟨θ (f * a), hkey _ _ ha, rfl⟩))
  -- the trace of the difference vanishes
  have htrD : tateTrace (S ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ S) = 0 :=
    tateTrace_comp_sub_comp_comm_of_sq S (LinearMap.mulLeft k g)
  -- decompose the `π`-commutator
  have hCtc := P.isTraceClass_residue_commutator f g
  have hCid : (π ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (π ∘ₗ LinearMap.mulLeft k f) =
      ((P.proj ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
        LinearMap.mulLeft k g ∘ₗ
          (P.proj ∘ₗ LinearMap.mulLeft k f)) +
      (S ∘ₗ LinearMap.mulLeft k g - LinearMap.mulLeft k g ∘ₗ S) := by
    refine LinearMap.ext fun x ↦ ?_
    rw [hS, hθ]
    simp only [LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.mulLeft_apply]
    ring
  haveI := hCtc.finiteDimensional_range_comp hCtc
  haveI := hCtc.finiteDimensional_range_comp hDtc
  haveI := hDtc.finiteDimensional_range_comp hCtc
  haveI := hDtc.finiteDimensional_range_comp hDtc
  rw [hCid, tateTrace_add_of_sq, htrD, add_zero, Place.residue]

/-- Words in two multiplication operators almost-stabilize the
valuation ring. -/
theorem Place.almostLE_map_closure (P : Place k F) (f g : F) :
    ∀ w ∈ Submonoid.closure ({LinearMap.mulLeft k f,
      LinearMap.mulLeft k g} : Set (Module.End k F)),
      AlmostLE (P.toSubmodule.map w) P.toSubmodule := by
  intro w hw
  induction hw using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact P.mulLeft_map_almostLE f
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact P.mulLeft_map_almostLE g
  | one =>
    have h1 : (1 : Module.End k F) = LinearMap.id := rfl
    rw [h1, Submodule.map_id]
    exact AlmostLE.rfl
  | mul x y hx hy ihx ihy =>
    have h1 : P.toSubmodule.map (x * y) =
        (P.toSubmodule.map y).map x := by
      rw [← Submodule.map_comp]
      rfl
    rw [h1]
    obtain ⟨W, hW, hle⟩ := ihy
    haveI := hW
    have h2 : (P.toSubmodule.map y).map x ≤
        P.toSubmodule.map x ⊔ W.map x := by
      refine (Submodule.map_mono hle).trans ?_
      rw [Submodule.map_sup]
    exact AlmostLE.mono_left h2
      (AlmostLE.sup ihx AlmostLE.of_finiteDimensional)

/-- Words in two multiplication operators almost-stabilize every
filtration stage: decompose the stage over the valuation ring and a
finite gauge. -/
theorem Place.almostLE_map_closure_filtration (P : Place k F)
    (f g : F) (m : ℕ) :
    ∀ w ∈ Submonoid.closure ({LinearMap.mulLeft k f,
      LinearMap.mulLeft k g} : Set (Module.End k F)),
      AlmostLE ((P.filtration m).map w) (P.filtration m) := by
  intro w hw
  have h1 := P.almostLE_map_closure f g w hw
  obtain ⟨W, hW, hle⟩ := P.filtration_almostLE m
  haveI := hW
  have h2 : (P.filtration m).map w ≤
      P.toSubmodule.map w ⊔ W.map w := by
    refine (Submodule.map_mono hle).trans ?_
    rw [Submodule.map_sup]
  have h3 : AlmostLE ((P.filtration m).map w) P.toSubmodule :=
    AlmostLE.mono_left h2
      (AlmostLE.sup h1 AlmostLE.of_finiteDimensional)
  refine h3.mono_right ?_
  rw [← P.filtration_zero]
  exact P.filtration_mono (Nat.zero_le m)

/-- **The filtration-stage residue commutator is trace-class**
relative to its own stage. -/
theorem Place.isTraceClass_filtrationProj_commutator (P : Place k F)
    (f g : F) (m : ℕ) :
    IsTraceClass (P.filtration m)
      ((P.filtrationProj m ∘ₗ LinearMap.mulLeft k f) ∘ₗ
          LinearMap.mulLeft k g -
        LinearMap.mulLeft k g ∘ₗ
          (P.filtrationProj m ∘ₗ LinearMap.mulLeft k f)) := by
  have hcomm : LinearMap.mulLeft k g ∘ₗ LinearMap.mulLeft k f =
      LinearMap.mulLeft k f ∘ₗ LinearMap.mulLeft k g := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    ring
  have hf : LinearMap.mulLeft k f ∈ Submonoid.closure
      ({LinearMap.mulLeft k f, LinearMap.mulLeft k g} :
        Set (Module.End k F)) :=
    Submonoid.subset_closure (Set.mem_insert _ _)
  have hg : LinearMap.mulLeft k g ∈ Submonoid.closure
      ({LinearMap.mulLeft k f, LinearMap.mulLeft k g} :
        Set (Module.End k F)) :=
    Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact isTraceClass_commutator_of_comm hcomm
    (P.almostLE_map_closure_filtration f g m _ (mul_mem hf hg))
    (P.almostLE_map_closure_filtration f g m _ hf)
    (P.almostLE_map_closure_filtration f g m _ hg)
    (fun x ↦ P.filtrationProj_mem m x)
    (fun x hx ↦ P.filtrationProj_eq_self hx)

/-- **The residue reads off any commensurable level**: computing the
commutator trace with a projection onto a filtration stage
`π^{−m} O_P` still gives the residue at `P`. This is what identifies
the local blocks of a global adelic projection with the residues. -/
theorem Place.residue_eq_of_projection_filtration (P : Place k F)
    (m : ℕ) {π : F →ₗ[k] F}
    (hmem : ∀ x : F, π x ∈ P.filtration m)
    (heq : ∀ x ∈ P.filtration m, π x = x) (f g : F) :
    tateTrace ((π ∘ₗ LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ (π ∘ₗ LinearMap.mulLeft k f)) =
    P.residue f g := by
  have h1 : P.toSubmodule ≤ P.filtration m := by
    rw [← P.filtration_zero]
    exact P.filtration_mono (Nat.zero_le m)
  rw [Place.residue]
  exact tateTrace_commutator_eq_of_projection h1
    (P.filtration_almostLE m) (P.almostLE_map_closure f g)
    (fun x ↦ P.proj_mem x) (fun x hx ↦ P.proj_eq_self hx)
    hmem heq (P.isTraceClass_residue_commutator f g)

end ResidueCalculus

end Projection

end

end AclGeom
