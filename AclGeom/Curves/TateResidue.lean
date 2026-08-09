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

theorem Place.conjProj_apply (P : Place k F) (g x : F) :
    P.conjProj g x = g * P.proj (g⁻¹ * x) := rfl

/-- The conjugated projection is idempotent. -/
theorem Place.isIdempotentElem_conjProj (P : Place k F) {g : F}
    (hg : g ≠ 0) : IsIdempotentElem (P.conjProj g) := by
  refine LinearMap.ext fun x ↦ ?_
  show P.conjProj g (P.conjProj g x) = P.conjProj g x
  rw [Place.conjProj_apply, Place.conjProj_apply]
  congr 1
  rw [← mul_assoc, inv_mul_cancel₀ hg, one_mul]
  exact P.proj_eq_self (P.proj_mem _)

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

end OrdLink

end Projection

end

end AclGeom
