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

section CanonicalDivisor

/-- Composition of multiplications multiplies. -/
theorem adeleSMul_comp (f g : F) :
    adeleSMul (k := k) (F := F) f ∘ₗ adeleSMul g = adeleSMul (f * g) := by
  refine LinearMap.ext fun α ↦ Subtype.ext (funext fun P ↦ ?_)
  change f * (g * ((α : (Q : Place k F) → F) P)) =
    (f * g) * ((α : (Q : Place k F) → F) P)
  ring

theorem adeleSMul_one :
    adeleSMul (k := k) (F := F) (1 : F) = LinearMap.id := by
  refine LinearMap.ext fun α ↦ Subtype.ext (funext fun P ↦ ?_)
  change (1 : F) * ((α : (Q : Place k F) → F) P) = _
  rw [one_mul]
  rfl

/-- The level shift is an equivalence of conditions. -/
theorem comp_adeleSMul_mem_weilDifferentialsAt_iff {f : F} (hf : f ≠ 0)
    {D : Divisor k F} {ω : Module.Dual k ↥(adeleSubmodule k F)} :
    ω ∘ₗ adeleSMul f ∈ weilDifferentialsAt (D + divisorOf k f) ↔
      ω ∈ weilDifferentialsAt D := by
  constructor
  · intro h
    have h1 := comp_adeleSMul_mem_weilDifferentialsAt
      (inv_ne_zero hf) h
    rw [LinearMap.comp_assoc, adeleSMul_comp, mul_inv_cancel₀ hf,
      adeleSMul_one, LinearMap.comp_id, divisorOf_inv hf,
      show D + divisorOf k f + -divisorOf k f = D by abel] at h1
    exact h1
  · exact comp_adeleSMul_mem_weilDifferentialsAt hf

/-- The join-splitting of adele spaces: the pointwise-max space is the
sum of the two — split each adele by comparing the divisors placewise. -/
theorem adeleSpace_add_pos_le_sup (D E : Divisor k F) :
    adeleSpace (D + (E - D).pos) ≤ adeleSpace D ⊔ adeleSpace E := by
  classical
  intro α hα
  rw [Submodule.mem_sup]
  refine ⟨fun P ↦ if E P ≤ D P then α P else 0, ?_,
    fun P ↦ if E P ≤ D P then 0 else α P, ?_, ?_⟩
  · intro P
    by_cases h : E P ≤ D P
    · simp only [if_pos h]
      rcases hα P with h0 | h0
      · exact Or.inl h0
      · rw [Divisor.add_sub_pos_apply, max_eq_left h] at h0
        exact Or.inr h0
    · exact Or.inl (if_neg h)
  · intro P
    by_cases h : E P ≤ D P
    · exact Or.inl (if_pos h)
    · simp only [if_neg h]
      rcases hα P with h0 | h0
      · exact Or.inl h0
      · rw [Divisor.add_sub_pos_apply,
          max_eq_right (by omega : D P ≤ E P)] at h0
        exact Or.inr h0
  · funext P
    by_cases h : E P ≤ D P <;> simp [h]

/-- The levels of a differential are join-closed. -/
theorem mem_weilDifferentialsAt_add_pos {D E : Divisor k F}
    {ω : Module.Dual k ↥(adeleSubmodule k F)}
    (hD : ω ∈ weilDifferentialsAt D) (hE : ω ∈ weilDifferentialsAt E) :
    ω ∈ weilDifferentialsAt (D + (E - D).pos) := by
  rw [mem_weilDifferentialsAt_iff] at hD hE ⊢
  intro β hβ
  rw [mem_boundedSubmodule_iff] at hβ
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hβ
  obtain ⟨x₁, hx₁, x₂, hx₂, hxx⟩ :=
    Submodule.mem_sup.1 (adeleSpace_add_pos_le_sup D E hx)
  have hm₁ : x₁ ∈ adeleSubmodule k F :=
    adeleSpace_le_adeleSubmodule D hx₁
  have hm₂ : x₂ + y ∈ adeleSubmodule k F := by
    refine Submodule.add_mem _ (adeleSpace_le_adeleSubmodule E hx₂) ?_
    obtain ⟨g, rfl⟩ := hy
    exact adeleDiagonal_mem_adeleSubmodule g
  have hβ' : β = (⟨x₁, hm₁⟩ : ↥(adeleSubmodule k F)) + ⟨x₂ + y, hm₂⟩ := by
    apply Subtype.ext
    change (β : (P : Place k F) → F) = x₁ + (x₂ + y)
    rw [← hxy, ← hxx]
    abel
  have hmem₁ : (⟨x₁, hm₁⟩ : ↥(adeleSubmodule k F)) ∈ boundedSubmodule D :=
    mem_boundedSubmodule_iff.2 (Submodule.mem_sup_left hx₁)
  have hmem₂ : (⟨x₂ + y, hm₂⟩ : ↥(adeleSubmodule k F)) ∈
      boundedSubmodule E :=
    mem_boundedSubmodule_iff.2 (Submodule.add_mem _
      (Submodule.mem_sup_left hx₂) (Submodule.mem_sup_right hy))
  rw [hβ', map_add, hD _ hmem₁, hE _ hmem₂, add_zero]

/-- **The canonical divisor exists** (Stichtenoth 1.5.11): a nonzero
Weil differential has a maximal level — its divisor. Levels are
join-closed and degree-bounded, so a level of maximal degree absorbs
every other level. -/
theorem exists_isGreatest_level
    {ω : Module.Dual k ↥(adeleSubmodule k F)} (hω0 : ω ≠ 0)
    {D₁ : Divisor k F} (h₁ : ω ∈ weilDifferentialsAt D₁) :
    ∃ W : Divisor k F, ω ∈ weilDifferentialsAt W ∧
      ∀ D, ω ∈ weilDifferentialsAt D → D ≤ W := by
  classical
  set S : Set ℤ :=
    {n | ∃ D : Divisor k F, ω ∈ weilDifferentialsAt D ∧ D.deg = n}
    with hS
  have hne : S.Nonempty := ⟨D₁.deg, D₁, h₁, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨D₁.deg + genus k F - 1 + specialtyIndex D₁, ?_⟩
    rintro n ⟨D, hD, rfl⟩
    exact deg_le_of_mem_weilDifferentialsAt hω0 hD
  obtain ⟨W, hW, hWdeg⟩ := Int.csSup_mem hne hbdd
  refine ⟨W, hW, fun D hD ↦ ?_⟩
  have hjoin := mem_weilDifferentialsAt_add_pos hW hD
  have hWle : W ≤ W + (D - W).pos := fun P ↦ by
    rw [Divisor.add_sub_pos_apply]
    exact le_max_left _ _
  have hDle : D ≤ W + (D - W).pos := fun P ↦ by
    rw [Divisor.add_sub_pos_apply]
    exact le_max_right _ _
  have hdegle : (W + (D - W).pos).deg ≤ W.deg := by
    have h2 : (W + (D - W).pos).deg ∈ S := ⟨_, hjoin, rfl⟩
    have h3 := le_csSup hbdd h2
    omega
  have heq := Divisor.eq_of_le_of_deg_le hWle hdegle
  rw [heq]
  exact hDle

/-- **The multiplication pairing**: `f ↦ ω ∘ (mult by f)`, as a linear
map from `L(E)` into the level-`D` differentials, for `D + E ≤ W`. -/
noncomputable def differentialPairing {W D E : Divisor k F}
    {ω : Module.Dual k ↥(adeleSubmodule k F)}
    (hω : ω ∈ weilDifferentialsAt W) (hDE : D + E ≤ W) :
    ↥(RiemannSpace E) →ₗ[k] ↥(weilDifferentialsAt D) where
  toFun f := ⟨ω ∘ₗ adeleSMul (f : F), by
    rcases eq_or_ne (f : F) 0 with h0 | h0
    · rw [h0]
      have hz : adeleSMul (k := k) (F := F) (0 : F) = 0 := by
        refine LinearMap.ext fun α ↦ Subtype.ext (funext fun P ↦ ?_)
        change (0 : F) * ((α : (Q : Place k F) → F) P) = 0
        rw [zero_mul]
      rw [hz, LinearMap.comp_zero]
      exact zero_mem _
    · have h1 := comp_adeleSMul_mem_weilDifferentialsAt h0 hω
      refine weilDifferentialsAt_antitone ?_ h1
      intro P
      have h2 := (mem_riemannSpace_iff.1 f.2).resolve_left h0 P
      have h3 := hDE P
      rw [Finsupp.add_apply] at h3
      rw [Finsupp.add_apply, divisorOf_apply h0]
      omega⟩
  map_add' f g := by
    apply Subtype.ext
    change ω ∘ₗ adeleSMul ((f : F) + (g : F)) =
      ω ∘ₗ adeleSMul (f : F) + ω ∘ₗ adeleSMul (g : F)
    rw [adeleSMul_add, LinearMap.comp_add]
  map_smul' c f := by
    apply Subtype.ext
    change ω ∘ₗ adeleSMul (c • (f : F)) = c • (ω ∘ₗ adeleSMul (f : F))
    rw [adeleSMul_smul, LinearMap.comp_smul]

@[simp]
theorem differentialPairing_coe {W D E : Divisor k F}
    {ω : Module.Dual k ↥(adeleSubmodule k F)}
    (hω : ω ∈ weilDifferentialsAt W) (hDE : D + E ≤ W)
    (f : ↥(RiemannSpace E)) :
    (differentialPairing hω hDE f :
      Module.Dual k ↥(adeleSubmodule k F)) = ω ∘ₗ adeleSMul (f : F) :=
  rfl

/-- **Proportionality of Weil differentials** (Stichtenoth 1.5.9,
`dim_F Ω = 1`): two nonzero differentials with levels are proportional
by a field element — else `L(W₁+B) ⊕ L(W₂+B)` would inject into
`Ω(−B)` for every `B`, and the dimensions clash for `deg B` large. -/
theorem exists_eq_comp_adeleSMul
    {ω₁ ω₂ : Module.Dual k ↥(adeleSubmodule k F)}
    (h₁0 : ω₁ ≠ 0) (h₂0 : ω₂ ≠ 0)
    {W₁ W₂ : Divisor k F} (h₁ : ω₁ ∈ weilDifferentialsAt W₁)
    (h₂ : ω₂ ∈ weilDifferentialsAt W₂) :
    ∃ f : F, f ≠ 0 ∧ ω₂ = ω₁ ∘ₗ adeleSMul f := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨P⟩ := (inferInstance : Nonempty (Place k F))
  set N : ℕ := (3 * genus k F - 3 - W₁.deg - W₂.deg).toNat + 1 with hN
  set B : Divisor k F := Finsupp.single P (N : ℤ) with hB
  have hdegB : B.deg = (N : ℤ) := by
    rw [hB, Divisor.deg, Finsupp.sum_single_index rfl]
  have hle₁ : (-B) + (W₁ + B) ≤ W₁ := le_of_eq (by abel)
  have hle₂ : (-B) + (W₂ + B) ≤ W₂ := le_of_eq (by abel)
  set Φ := LinearMap.coprod (differentialPairing h₁ hle₁)
    (differentialPairing h₂ hle₂) with hΦ
  have hker : ∀ x, Φ x = 0 → x = 0 := by
    rintro ⟨f, g⟩ h0
    have h1 : ω₁ ∘ₗ adeleSMul (f : F) + ω₂ ∘ₗ adeleSMul (g : F) = 0 :=
      congrArg Subtype.val h0
    rcases eq_or_ne (g : F) 0 with hg0 | hg0
    · -- then the first summand vanishes, forcing `f = 0` too
      have hz : adeleSMul (k := k) (F := F) (0 : F) = 0 := by
        refine LinearMap.ext fun α ↦ Subtype.ext (funext fun Q ↦ ?_)
        change (0 : F) * ((α : (Q' : Place k F) → F) Q) = 0
        rw [zero_mul]
      rw [hg0, hz, LinearMap.comp_zero, add_zero] at h1
      have hf0 : (f : F) = 0 := by
        by_contra hf0
        exact comp_adeleSMul_ne_zero hf0 h₁0 h1
      refine Prod.ext (Subtype.ext hf0) (Subtype.ext hg0)
    · -- otherwise solve for `ω₂` and contradict non-proportionality
      have h2 : ω₂ ∘ₗ adeleSMul (g : F) = ω₁ ∘ₗ adeleSMul (-(f : F)) := by
        have h3 : adeleSMul (k := k) (F := F) (-(f : F)) =
            -adeleSMul (f : F) := by
          refine LinearMap.ext fun α ↦ Subtype.ext (funext fun Q ↦ ?_)
          change (-(f : F)) * ((α : (Q' : Place k F) → F) Q) =
            -((f : F) * ((α : (Q' : Place k F) → F) Q))
          ring
        rw [h3, LinearMap.comp_neg]
        rw [add_comm] at h1
        exact eq_neg_of_add_eq_zero_left h1
      have h4 : ω₂ = ω₁ ∘ₗ adeleSMul (-(f : F) * (g : F)⁻¹) := by
        have h5 := congrArg (· ∘ₗ adeleSMul ((g : F)⁻¹)) h2
        simp only [LinearMap.comp_assoc, adeleSMul_comp] at h5
        rw [mul_inv_cancel₀ hg0, adeleSMul_one, LinearMap.comp_id] at h5
        exact h5
      exact absurd h4 (hcon _ (mul_ne_zero (neg_ne_zero.2 (by
        intro hf0
        rw [hf0] at h2
        have hz : adeleSMul (k := k) (F := F) (-(0 : F)) = 0 := by
          refine LinearMap.ext fun α ↦ Subtype.ext (funext fun Q ↦ ?_)
          change (-(0 : F)) * ((α : (Q' : Place k F) → F) Q) = 0
          rw [neg_zero, zero_mul]
        rw [hz, LinearMap.comp_zero] at h2
        exact comp_adeleSMul_ne_zero hg0 h₂0 h2)) (inv_ne_zero hg0)))
  have hinj : Function.Injective Φ := by
    intro x y hxy
    have h6 := hker (x - y) (by rw [map_sub, hxy, sub_self])
    exact sub_eq_zero.1 h6
  have hcard := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hcard
  have hR₁ := riemann_inequality (k := k) (F := F) (W₁ + B)
  have hR₂ := riemann_inequality (k := k) (F := F) (W₂ + B)
  have hΩrk := finrank_weilDifferentialsAt (k := k) (F := F) (-B)
  have hi : specialtyIndex (-B : Divisor k F) =
      (N : ℤ) + genus k F - 1 := by
    have h := finrank_riemannSpace_eq_add_specialtyIndex
      (-B : Divisor k F)
    have hzero : Module.finrank k (RiemannSpace (-B : Divisor k F)) = 0 := by
      rw [riemannSpace_eq_bot_of_deg_neg ?_, finrank_bot]
      rw [Divisor.deg_neg, hdegB]
      omega
    rw [hzero, Divisor.deg_neg, hdegB] at h
    omega
  have hdeg₁ : (W₁ + B).deg = W₁.deg + N := by
    rw [Divisor.deg_add, hdegB]
  have hdeg₂ : (W₂ + B).deg = W₂.deg + N := by
    rw [Divisor.deg_add, hdegB]
  have hg := genus_nonneg (k := k) (F := F)
  have hNbig : 3 * genus k F - 3 - W₁.deg - W₂.deg < (N : ℤ) := by
    rw [hN]
    push_cast
    omega
  omega

/-- The maximal level shifts by the principal divisor under
multiplication. -/
theorem isGreatest_level_comp
    {ω : Module.Dual k ↥(adeleSubmodule k F)}
    {W : Divisor k F} (hW : ω ∈ weilDifferentialsAt W)
    (hmax : ∀ D, ω ∈ weilDifferentialsAt D → D ≤ W)
    {f : F} (hf : f ≠ 0) :
    ω ∘ₗ adeleSMul f ∈ weilDifferentialsAt (W + divisorOf k f) ∧
      ∀ D, ω ∘ₗ adeleSMul f ∈ weilDifferentialsAt D →
        D ≤ W + divisorOf k f := by
  refine ⟨comp_adeleSMul_mem_weilDifferentialsAt hf hW, fun D hD ↦ ?_⟩
  have h1 : ω ∈ weilDifferentialsAt (D - divisorOf k f) := by
    refine (comp_adeleSMul_mem_weilDifferentialsAt_iff hf
      (D := D - divisorOf k f)).1 ?_
    rw [show D - divisorOf k f + divisorOf k f = D by abel]
    exact hD
  have h2 := hmax _ h1
  intro P
  have h3 := h2 P
  rw [Finsupp.sub_apply] at h3
  rw [Finsupp.add_apply]
  omega

end CanonicalDivisor

end

end AclGeom
