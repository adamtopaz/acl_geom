/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import GroupConfig.Constructible.Admissible

/-!
# Actual uniform parameter families for an orbit of germs

Supplemental `rem:code-param` and the uniform family used by
`thm:constructible`. Transporting one fixed finite tuple generating a germ's
canonical base distinguishes exactly the germs in its orbit. Every generic
parameter comes from a unique orbit germ. Definability and joint conjugation
give one quasi-rational expression over the base, which is actually admissible
at every transported parameter and represents the corresponding orbit germ.

**Status:** the orbit parameterization and actual uniform admissible family
are proved. No naturality of the chosen `codeSet` carrier is assumed. The
constructible-group domain, quotient and operations are proved in
`GroupConfig.Constructible.CanonicalPresentation`.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k]
  [IsAlgClosed K] [UniversalDomain k K] {ι κ μ : Type*} [Finite ι] [Finite κ]
  [Finite μ] {a : ι → K} {a' : κ → K}

namespace Germ

omit [Finite μ] in
/-- Within one orbit, transporting a fixed generator tuple distinguishes exactly the germs. -/
theorem map_eq_map_iff_parameter_eq (g : Germ k a a') {c : μ → K}
    (hc : adjoin k (range c) = g.cb) (σ τ : K ≃ₐ[k] K) :
    g.map σ = g.map τ ↔ ⇑σ ∘ c = ⇑τ ∘ c := by
  constructor
  · intro hg
    have hfix : g.map (σ.trans τ.symm) = g := by
      rw [← map_map, hg, map_map]
      have hr : τ.trans τ.symm = AlgEquiv.refl :=
        AlgEquiv.ext fun x ↦ τ.symm_apply_apply x
      rw [hr, map_refl]
    funext i
    have hmem : c i ∈ g.cb := hc ▸ subset_adjoin k _ (mem_range_self i)
    have hi : τ.symm (σ (c i)) = c i := (map_eq_self_iff _ _).1 hfix _ hmem
    exact (τ.apply_symm_apply _).symm.trans (congrArg τ hi)
  · intro heq
    have hle : adjoin k (range c) ≤ fixedBy (σ.trans τ.symm) := by
      refine adjoin_le_iff.2 ?_
      rintro _ ⟨i, rfl⟩
      change τ.symm (σ (c i)) = c i
      have hi : σ (c i) = τ (c i) := congrFun heq i
      rw [hi]
      exact τ.symm_apply_apply _
    have hfix : g.map (σ.trans τ.symm) = g :=
      (map_eq_self_iff _ _).2 fun x hx ↦ hle (hc.symm ▸ hx)
    calc g.map σ = g.map ((σ.trans τ.symm).trans τ) := by
          congr 1
          exact AlgEquiv.ext fun x ↦ (τ.apply_symm_apply (σ x)).symm
      _ = (g.map (σ.trans τ.symm)).map τ := (map_map _ _ _).symm
      _ = g.map τ := congrArg (Germ.map τ) hfix

/-- A generic parameter for the fixed tuple determines a unique germ in its orbit. -/
theorem existsUnique_orbit_parameter (g : Germ k a a') {c p : μ → K}
    (hc : adjoin k (range c) = g.cb) (hp : IsGen k c p) :
    ∃! h : ↥(orbit g), ∃ σ : K ≃ₐ[k] K, ⇑σ ∘ c = p ∧ g.map σ = h.1 := by
  obtain ⟨σ, -, hσ⟩ := exists_ambientAutomorphism_of_idealOf_eq (k := k) hp.symm
  have hσc : ⇑σ ∘ c = p := funext hσ
  refine ⟨⟨g.map σ, ⟨σ, rfl⟩⟩, ⟨σ, hσc, rfl⟩, ?_⟩
  rintro h ⟨τ, hτc, hτg⟩
  apply Subtype.ext
  exact hτg.symm.trans ((g.map_eq_map_iff_parameter_eq hc τ σ).2 (hτc.trans hσc.symm))

omit [Finite μ] in
private theorem evalGen_mem_dcl_parameterPair (g : Germ k a a') {c : μ → K}
    (hc : adjoin k (range c) = g.cb) {y : ι → K} (hy : IsGen k a y)
    (hind : IndepOver k ∅ (range y) (g.cb : Set K)) (j : κ) :
    g.evalGen y j ∈ dclAdjoin (⊥ : IntermediateField k K) (Sum.elim c y) := by
  unfold dclAdjoin
  refine mem_dcl_iff_forall_fixed.2 fun σ ↦ ?_
  let τ : K ≃ₐ[k] K := σ.restrictScalars k
  have hfixc : ⇑τ ∘ c = c := funext fun i ↦ by
    change σ (c i) = c i
    exact σ.commutes ⟨c i, (mem_restrictScalars k).2
      (subset_adjoin (↥(⊥ : IntermediateField k K)) _
        (mem_range_self (f := Sum.elim c y) (Sum.inl i)))⟩
  have hfixy : ⇑τ ∘ y = y := funext fun i ↦ by
    change σ (y i) = y i
    exact σ.commutes ⟨y i, (mem_restrictScalars k).2
      (subset_adjoin (↥(⊥ : IntermediateField k K)) _
        (mem_range_self (f := Sum.elim c y) (Sum.inr i)))⟩
  have hfixg : g.map τ = g := by
    have he : g.map τ = g.map AlgEquiv.refl :=
      (g.map_eq_map_iff_parameter_eq hc τ AlgEquiv.refl).2 hfixc
    exact he.trans (map_refl g)
  have he := evalGen_map τ g hy hind
  rw [hfixg, hfixy] at he
  exact (congrFun he j).symm

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite μ] in
private theorem aeval_map_botEquiv (u : μ → K)
    (P : MvPolynomial μ (↥(⊥ : IntermediateField k K))) :
    aeval u (MvPolynomial.map (botEquiv k K).toRingHom P) = aeval u P := by
  rw [aeval_def, aeval_def, eval₂_map]
  congr 1
  exact (IsScalarTower.algebraMap_eq (↥(⊥ : IntermediateField k K)) k K).symm

/-- One expression over the base evaluates every germ in an orbit, using transported
copies of a single generator tuple. The source point is generic over that parameter. -/
theorem exists_orbit_uniformExpression (g : Germ k a a') {c : μ → K}
    (hc : adjoin k (range c) = g.cb) :
    ∃ F : QuasiRational k (μ ⊕ ι) κ, ∀ (σ : K ≃ₐ[k] K) (u : ι → K),
      IsGenericOver (racl k (range (⇑σ ∘ c))) a u →
      F.IsDefinedAt (Sum.elim (⇑σ ∘ c) u) ∧
      F.eval (Sum.elim (⇑σ ∘ c) u) = (g.map σ).evalGen u := by
  have hM : IsSmall k ((racl k (range c) : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite (finite_range c)).racl
  obtain ⟨y, hy⟩ := exists_isGenericOver hM a
  have hind : IndepOver k ∅ (range y) (g.cb : Set K) :=
    hy.indepOver.mono_right (hc ▸ adjoin_le_racl k (range c))
  obtain ⟨F₀, hF₀, he₀⟩ := exists_quasiRational_of_mem_dclAdjoin
    (g.evalGen_mem_dcl_parameterPair hc hy.isGen hind)
  let F : QuasiRational k (μ ⊕ ι) κ := F₀.map (botEquiv k K).toRingHom
  have heval (v : (μ ⊕ ι) → K) : F.eval v = F₀.eval v := by
    funext j
    simp only [F, QuasiRational.eval, QuasiRational.map, aeval_map_botEquiv]
  have hF : F.IsDefinedAt (Sum.elim c y) := by
    intro j
    simpa only [F, QuasiRational.map, aeval_map_botEquiv] using hF₀ j
  have he : F.eval (Sum.elim c y) = g.evalGen y := (heval _).trans he₀
  refine ⟨F, ?_⟩
  intro σ u hu
  have hyσ : IsGenericOver (racl k (range (⇑σ ∘ c))) a (⇑σ ∘ y) := by
    have h := (isGenericOver_map_iff σ (racl k (range c)) a y).2 hy
    rw [racl_map, ← range_comp] at h
    exact h
  obtain ⟨ρ, hρ⟩ := hyσ.exists_algEquiv hu
  let θ : K ≃ₐ[k] K := σ.trans (ρ.restrictScalars k)
  have hθc : ⇑θ ∘ c = ⇑σ ∘ c := funext fun i ↦ by
    change ρ (σ (c i)) = σ (c i)
    exact ρ.commutes ⟨σ (c i), subset_racl k _
      (mem_range_self (f := ⇑σ ∘ c) i)⟩
  have hθy : ⇑θ ∘ y = u := funext fun i ↦ hρ i
  have hθg : g.map θ = g.map σ :=
    (g.map_eq_map_iff_parameter_eq hc θ σ).2 hθc
  have hsum : ⇑θ ∘ Sum.elim c y = Sum.elim (⇑σ ∘ c) u := by
    funext i
    cases i with
    | inl i => exact congrFun hθc i
    | inr i => exact congrFun hθy i
  constructor
  · rw [← hsum]
    exact (F.isDefinedAt_comp_iff θ _).2 hF
  · rw [← hsum, F.eval_comp θ, he, ← evalGen_map θ g hy.isGen hind, hθg, hθy]

/-- The uniform expression actually supplies admissible parameters and their
orbit germs, rather than only agreeing with values at chosen points.
Named consumer: the parameter presentation of the constructible group. -/
theorem exists_orbit_admissibleFamily (g : Germ k a a') {c : μ → K}
    (hc : adjoin k (range c) = g.cb) :
    ∃ F : QuasiRational k (μ ⊕ ι) κ, ∀ σ : K ≃ₐ[k] K,
      ∃ hu : F.IsAdmissible a a' (⇑σ ∘ c), F.parameterGerm hu = g.map σ := by
  obtain ⟨F, hF⟩ := g.exists_orbit_uniformExpression hc
  refine ⟨F, fun σ ↦ ?_⟩
  have hcσ : adjoin k (range (⇑σ ∘ c)) = (g.map σ).cb := by
    rw [cb_map, ← hc, adjoin_map, AlgEquiv.coe_toAlgHom, range_comp]
  have hcb : (g.map σ).cb ≤ racl k (range (⇑σ ∘ c)) := by
    rw [← hcσ]
    exact adjoin_le_racl k _
  have hM : IsSmall k ((racl k (range (⇑σ ∘ c)) : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite (finite_range _)).racl
  have _ : IsAlgClosed ↥(racl k (range (⇑σ ∘ c))) := isAlgClosed_racl _
  have hu : F.IsAdmissible a a' (⇑σ ∘ c) := by
    intro y hy
    refine ⟨(hF σ y hy).1, ?_⟩
    rw [(hF σ y hy).2, (g.map σ).evalGen_eq hM hcb hy]
    exact (g.map σ).isGenericOver_eval hM hcb hy
  obtain ⟨y, hy⟩ := exists_isGenericOver hM a
  refine ⟨hu, eq_of_eval_eq hM (F.cb_parameterGerm_le hu) hcb hy ?_⟩
  exact (F.eval_parameterGerm hu hy).trans
    ((hF σ y hy).2.trans ((g.map σ).evalGen_eq hM hcb hy))

end Germ

end

end GroupConfig
