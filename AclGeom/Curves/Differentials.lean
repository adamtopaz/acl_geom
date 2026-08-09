/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.Specialty

/-!
# Weil differentials

A Weil differential of level `D` is a `k`-linear functional on the
adeles vanishing on `A(D) + F` — an element of the dual annihilator of
the bounded subspace, so of dimension `i(D)`. Multiplication by a field
element shifts the level by a principal divisor and is injective on
differentials, which bounds the degrees of the levels of a fixed
nonzero differential: `L(D − D₀)` injects into the level-`D₀`
differentials. Together with the join-splitting of adele spaces this
produces a maximal level — the divisor of the differential, whose class
is the canonical class.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P5).
-/

namespace AclGeom

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

section Multiplication

variable (k) in
/-- Pointwise multiplication by a field element on place-indexed
families. -/
noncomputable def adeleMulMap (f : F) :
    ((P : Place k F) → F) →ₗ[k] ((P : Place k F) → F) :=
  LinearMap.pi fun P ↦ (LinearMap.mulLeft k f).comp (LinearMap.proj P)

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
@[simp]
theorem adeleMulMap_apply (f : F) (α : (P : Place k F) → F)
    (P : Place k F) : adeleMulMap k f α P = f * α P := rfl

/-- Multiplication maps `A(D + div f)` into `A(D)`. -/
theorem adeleMulMap_mem_adeleSpace {f : F} (hf : f ≠ 0)
    {D : Divisor k F} {α : (P : Place k F) → F}
    (hα : α ∈ adeleSpace (D + divisorOf k f)) :
    adeleMulMap k f α ∈ adeleSpace D := by
  intro P
  rcases eq_or_ne (α P) 0 with h0 | h0
  · exact Or.inl (by rw [adeleMulMap_apply, h0, mul_zero])
  have h1 := (hα P).resolve_left h0
  rw [Finsupp.add_apply, divisorOf_apply hf] at h1
  refine Or.inr ?_
  rw [adeleMulMap_apply, P.ord_mul hf h0]
  omega

/-- Multiplication preserves the adeles: the new exceptional places are
poles of the multiplier. -/
theorem adeleMulMap_mem_adeleSubmodule (f : F)
    {α : (P : Place k F) → F} (hα : α ∈ adeleSubmodule k F) :
    adeleMulMap k f α ∈ adeleSubmodule k F := by
  rcases eq_or_ne f 0 with rfl | hf0
  · refine Set.Finite.subset Set.finite_empty fun P hP ↦ ?_
    simp only [Set.mem_setOf_eq, adeleMulMap_apply, zero_mul] at hP
    exact absurd rfl hP.1
  refine Set.Finite.subset
    (hα.union (finite_setOf_one_lt_valuation hf0)) fun P hP ↦ ?_
  simp only [Set.mem_setOf_eq, adeleMulMap_apply] at hP
  obtain ⟨hne, hlt⟩ := hP
  have hα0 : α P ≠ 0 := fun h ↦ hne (by rw [h, mul_zero])
  rw [P.ord_mul hf0 hα0] at hlt
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have h3 := h1 hα0
  have h4 : 0 ≤ P.ord f := (P.ord_nonneg_iff hf0).2 h2
  omega

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- Multiplication fixes the diagonal. -/
theorem adeleMulMap_diagonal (f g : F) :
    adeleMulMap k f (adeleDiagonal k F g) = adeleDiagonal k F (f * g) :=
  rfl

/-- Multiplication as an endomorphism of the adele module. -/
noncomputable def adeleSMul (f : F) :
    ↥(adeleSubmodule k F) →ₗ[k] ↥(adeleSubmodule k F) :=
  LinearMap.codRestrict _
    ((adeleMulMap k f).comp (adeleSubmodule k F).subtype)
    fun α ↦ adeleMulMap_mem_adeleSubmodule f α.2

@[simp]
theorem adeleSMul_coe (f : F) (α : ↥(adeleSubmodule k F)) :
    (adeleSMul f α : (P : Place k F) → F) = adeleMulMap k f ↑α := rfl

theorem adeleSMul_add (f g : F) :
    adeleSMul (k := k) (F := F) (f + g) = adeleSMul f + adeleSMul g := by
  refine LinearMap.ext fun α ↦ Subtype.ext (funext fun P ↦ ?_)
  change (f + g) * ((α : (Q : Place k F) → F) P) =
    f * ((α : (Q : Place k F) → F) P) +
      g * ((α : (Q : Place k F) → F) P)
  ring

theorem adeleSMul_sub (f g : F) :
    adeleSMul (k := k) (F := F) (f - g) = adeleSMul f - adeleSMul g := by
  refine LinearMap.ext fun α ↦ Subtype.ext (funext fun P ↦ ?_)
  change (f - g) * ((α : (Q : Place k F) → F) P) =
    f * ((α : (Q : Place k F) → F) P) -
      g * ((α : (Q : Place k F) → F) P)
  ring

theorem adeleSMul_smul (c : k) (f : F) :
    adeleSMul (k := k) (F := F) (c • f) = c • adeleSMul f := by
  refine LinearMap.ext fun α ↦ Subtype.ext (funext fun P ↦ ?_)
  change (c • f) * ((α : (Q : Place k F) → F) P) =
    c • (f * ((α : (Q : Place k F) → F) P))
  rw [Algebra.smul_def, Algebra.smul_def]
  ring

end Multiplication

section Differentials

/-- **Weil differentials of level `D`**: functionals on the adeles
vanishing on `A(D) + F` — the dual annihilator of the bounded
subspace. -/
noncomputable def weilDifferentialsAt (D : Divisor k F) :
    Submodule k (Module.Dual k ↥(adeleSubmodule k F)) :=
  (boundedSubmodule D).dualAnnihilator

theorem mem_weilDifferentialsAt_iff {D : Divisor k F}
    {ω : Module.Dual k ↥(adeleSubmodule k F)} :
    ω ∈ weilDifferentialsAt D ↔
      ∀ α ∈ boundedSubmodule D, ω α = 0 :=
  Submodule.mem_dualAnnihilator ω

/-- Levels are antitone: killing a larger space is harder. -/
theorem weilDifferentialsAt_antitone {D E : Divisor k F} (h : D ≤ E) :
    weilDifferentialsAt (E : Divisor k F) ≤ weilDifferentialsAt D := by
  intro ω hω
  rw [mem_weilDifferentialsAt_iff] at hω ⊢
  intro α hα
  exact hω α (boundedSubmodule_mono h hα)

/-- The level-`D` differentials are the dual of the specialty quotient:
their dimension is the index of specialty. -/
theorem finrank_weilDifferentialsAt (D : Divisor k F) :
    (Module.finrank k (weilDifferentialsAt D) : ℤ) = specialtyIndex D := by
  rw [weilDifferentialsAt, specialtyIndex,
    ← LinearEquiv.finrank_eq
      (Submodule.dualQuotEquivDualAnnihilator (boundedSubmodule D)),
    Subspace.dual_finrank_eq]

/-- The level-`D` differentials are finite-dimensional. -/
instance finiteDimensional_weilDifferentialsAt (D : Divisor k F) :
    FiniteDimensional k (weilDifferentialsAt D) :=
  LinearEquiv.finiteDimensional
    (Submodule.dualQuotEquivDualAnnihilator (boundedSubmodule D))

/-- Nonzero Weil differentials exist, at any negative-enough level. -/
theorem exists_ne_zero_mem_weilDifferentialsAt :
    ∃ (D : Divisor k F) (ω : Module.Dual k ↥(adeleSubmodule k F)),
      ω ∈ weilDifferentialsAt D ∧ ω ≠ 0 := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Place k F))
  set D : Divisor k F := Finsupp.single P (-2) with hD
  have hdeg : D.deg = -2 := by
    rw [hD, Divisor.deg, Finsupp.sum_single_index rfl]
  have hl : Module.finrank k (RiemannSpace D) = 0 := by
    rw [riemannSpace_eq_bot_of_deg_neg (by omega), finrank_bot]
  have hi : 0 < specialtyIndex D := by
    have h := finrank_riemannSpace_eq_add_specialtyIndex D
    have hg := genus_nonneg (k := k) (F := F)
    rw [hl] at h
    omega
  have hpos : 0 < Module.finrank k
      (weilDifferentialsAt (k := k) (F := F) D) := by
    have h := finrank_weilDifferentialsAt (k := k) (F := F) D
    omega
  obtain ⟨ω, hω, hω0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (p := weilDifferentialsAt (k := k) (F := F) D)
    (fun hbot ↦ by rw [hbot, finrank_bot] at hpos; omega)
  exact ⟨D, ω, hω, hω0⟩

/-- **The level shift**: precomposing a level-`D` differential with
multiplication by `f` yields a level-`(D + div f)` differential. -/
theorem comp_adeleSMul_mem_weilDifferentialsAt {f : F} (hf : f ≠ 0)
    {D : Divisor k F} {ω : Module.Dual k ↥(adeleSubmodule k F)}
    (hω : ω ∈ weilDifferentialsAt D) :
    ω ∘ₗ adeleSMul f ∈ weilDifferentialsAt (D + divisorOf k f) := by
  rw [mem_weilDifferentialsAt_iff] at hω ⊢
  intro α hα
  rw [LinearMap.comp_apply]
  refine hω _ ?_
  rw [mem_boundedSubmodule_iff] at hα ⊢
  obtain ⟨x, hx, y, ⟨g, rfl⟩, hxy⟩ := Submodule.mem_sup.1 hα
  have hcoe : (adeleSMul f α : (P : Place k F) → F) =
      adeleMulMap k f x + adeleDiagonal k F (f * g) := by
    rw [adeleSMul_coe, ← hxy, map_add, adeleMulMap_diagonal]
  rw [hcoe]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (adeleMulMap_mem_adeleSpace hf hx))
    (Submodule.mem_sup_right ⟨f * g, rfl⟩)

/-- Multiplication is injective on differentials. -/
theorem comp_adeleSMul_ne_zero {f : F} (hf : f ≠ 0)
    {ω : Module.Dual k ↥(adeleSubmodule k F)} (hω : ω ≠ 0) :
    ω ∘ₗ adeleSMul f ≠ 0 := by
  intro h0
  refine hω ?_
  ext α
  have h1 : adeleSMul f (adeleSMul f⁻¹ α) = α := by
    apply Subtype.ext
    funext P
    change f * (f⁻¹ * (α : (P : Place k F) → F) P) = _
    field_simp
  have h2 := LinearMap.congr_fun h0 (adeleSMul f⁻¹ α)
  rw [LinearMap.comp_apply, h1] at h2
  simpa using h2

/-- **Degree bound on levels** (toward Stichtenoth 1.5.10): if `ω ≠ 0`
has levels `D₀` and `D`, then `L(D − D₀)` injects into the level-`D₀`
differentials by multiplication, so
`deg D ≤ deg D₀ + g − 1 + i(D₀)`. -/
theorem deg_le_of_mem_weilDifferentialsAt
    {ω : Module.Dual k ↥(adeleSubmodule k F)} (hω0 : ω ≠ 0)
    {D₀ D : Divisor k F} (hD : ω ∈ weilDifferentialsAt D) :
    D.deg ≤ D₀.deg + genus k F - 1 + specialtyIndex D₀ := by
  classical
  -- The multiplication map `L(D − D₀) → Ω(D₀)`.
  have hmem : ∀ f : ↥(RiemannSpace (D - D₀)),
      ω ∘ₗ adeleSMul (f : F) ∈ weilDifferentialsAt D₀ := by
    intro f
    rcases eq_or_ne (f : F) 0 with h0 | h0
    · rw [h0]
      have hz : adeleSMul (k := k) (F := F) (0 : F) = 0 := by
        refine LinearMap.ext fun α ↦ Subtype.ext (funext fun P ↦ ?_)
        change (0 : F) * ((α : (Q : Place k F) → F) P) = 0
        rw [zero_mul]
      rw [hz, LinearMap.comp_zero]
      exact zero_mem _
    · have h1 := comp_adeleSMul_mem_weilDifferentialsAt h0 hD
      refine weilDifferentialsAt_antitone ?_ h1
      intro P
      have h2 := (mem_riemannSpace_iff.1 f.2).resolve_left h0 P
      rw [Finsupp.sub_apply] at h2
      rw [Finsupp.add_apply, divisorOf_apply h0]
      omega
  set φ : ↥(RiemannSpace (D - D₀)) →ₗ[k]
      ↥(weilDifferentialsAt (k := k) (F := F) D₀) :=
    { toFun := fun f ↦ ⟨ω ∘ₗ adeleSMul (f : F), hmem f⟩
      map_add' := fun f g ↦ by
        apply Subtype.ext
        change ω ∘ₗ adeleSMul ((f : F) + (g : F)) =
          ω ∘ₗ adeleSMul (f : F) + ω ∘ₗ adeleSMul (g : F)
        rw [adeleSMul_add, LinearMap.comp_add]
      map_smul' := fun c f ↦ by
        apply Subtype.ext
        change ω ∘ₗ adeleSMul (c • (f : F)) =
          c • (ω ∘ₗ adeleSMul (f : F))
        rw [adeleSMul_smul, LinearMap.comp_smul] }
  have hinj : Function.Injective φ := by
    intro f g hfg
    have h1 : ω ∘ₗ adeleSMul (f : F) = ω ∘ₗ adeleSMul (g : F) :=
      congrArg Subtype.val hfg
    by_contra hne
    have hsub : (f : F) - (g : F) ≠ 0 := by
      intro h0
      exact hne (Subtype.ext (sub_eq_zero.1 h0))
    have h2 : ω ∘ₗ adeleSMul ((f : F) - (g : F)) = 0 := by
      rw [adeleSMul_sub, LinearMap.comp_sub, h1, sub_self]
    exact comp_adeleSMul_ne_zero hsub hω0 h2
  have hcard := LinearMap.finrank_le_finrank_of_injective hinj
  have hRR := riemann_inequality (k := k) (F := F) (D - D₀)
  have hdeg : (D - D₀).deg = D.deg - D₀.deg := Divisor.deg_sub D D₀
  have hΩ := finrank_weilDifferentialsAt (k := k) (F := F) D₀
  omega

end Differentials

end

end AclGeom
