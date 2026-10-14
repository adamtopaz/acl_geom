/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.Code

/-!
# Automorphisms act on germs

Blueprint `sources/group_configuration/04-germs.tex`, `lem:germ-aut`.

An automorphism `σ` of `K` over `k` sends a representative `(M, f)` to the representative
`(σ M, σ f)` (`Representative.map`), compatibly with equivalence, hence acts on germs
(`Germ.map`).  The graph ideal, the canonical base and the fixed-point criterion are
equivariant: `Γ(σ g) = σ Γ(g)` (`Germ.graphIdeal_map`), `Cb(σ g) = σ Cb(g)`
(`Germ.cb_map`), and `σ g = g` iff `σ` fixes `Cb(g)` pointwise (`Germ.map_eq_self_iff`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the automorphism action, graph-ideal and canonical-base transport,
and pointwise canonical-base stabilizer criterion are proved. No naturality of
the arbitrarily chosen `codeSet` carrier is claimed. Canonical indexed codes,
evaluation, composition and group extraction are separate layers.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {ι κ : Type*}

/-! ### Automorphisms over `k` and genericity -/

/-- The locus over `k` of a tuple is invariant under automorphisms over `k`. -/
theorem locusIdeal_base_comp (σ : K ≃ₐ[k] K) (a : ι → K) :
    locusIdeal k (⇑σ ∘ a) = locusIdeal k a := by
  have h : ⇑σ ∘ a = ⇑σ.toAlgHom ∘ a := rfl
  unfold locusIdeal
  rw [h, idealOf_comp_algHom k]

/-- The extension of an ideal over `k` is invariant under the action of an automorphism
over `k` on polynomials. -/
theorem map_locusIdeal_base (σ : K ≃ₐ[k] K) (a : ι → K) :
    (locusIdeal k a).map (MvPolynomial.map σ.toRingEquiv.toRingHom) = locusIdeal k a := by
  have hcomp : σ.toRingEquiv.toRingHom.comp (algebraMap k K) = algebraMap k K :=
    RingHom.ext fun c ↦ σ.commutes c
  have hmap : (MvPolynomial.map σ.toRingEquiv.toRingHom).comp
      (MvPolynomial.map (algebraMap k K) : MvPolynomial ι k →+* MvPolynomial ι K) =
      MvPolynomial.map (algebraMap k K) :=
    RingHom.ext fun p ↦ by rw [RingHom.comp_apply, MvPolynomial.map_map, hcomp]
  unfold locusIdeal
  rw [Ideal.map_map, hmap]

/-- The action of an automorphism on polynomials is bijective. -/
theorem map_toRingHom_bijective (σ : K ≃ₐ[k] K) :
    Function.Bijective (MvPolynomial.map (σ := ι) σ.toRingEquiv.toRingHom) :=
  ⟨MvPolynomial.map_injective _ σ.injective, MvPolynomial.map_surjective _ σ.surjective⟩

/-- Genericity is equivariant: `σ y` is generic over `σ M` iff `y` is generic over `M`. -/
theorem isGenericOver_map_iff (σ : K ≃ₐ[k] K) (M : IntermediateField k K) (a y : ι → K) :
    IsGenericOver (M.map σ.toAlgHom) a (⇑σ ∘ y) ↔ IsGenericOver M a y := by
  rw [isGenericOver_iff_locusIdeal_eq, isGenericOver_iff_locusIdeal_eq, ← locusIdeal_map]
  conv_lhs => rw [← map_locusIdeal_base σ a]
  exact (Function.LeftInverse.injective (g := Ideal.comap (MvPolynomial.map (σ := ι)
    σ.toRingEquiv.toRingHom)) fun I ↦ Ideal.comap_map_of_bijective _
    (map_toRingHom_bijective σ)).eq_iff

/-! ### The action on expressions -/

/-- Evaluating a transported expression at a transported point. -/
theorem aeval_map_intermediateFieldMap (σ : K ≃ₐ[k] K) (M : IntermediateField k K)
    (y : ι → K) (P : MvPolynomial ι (↥M)) :
    aeval (⇑σ ∘ y) (MvPolynomial.map (intermediateFieldMap σ M).toRingHom P) =
      σ (aeval y P) := by
  rw [aeval_def, aeval_def, eval₂_map]
  change _ = σ.toRingEquiv.toRingHom (eval₂ (algebraMap (↥M) K) y P)
  rw [eval₂_comp_left]
  congr 1

variable [IsAlgClosed K]

omit [IsAlgClosed K] in
theorem QuasiRational.isDefinedAt_mapAlgEquiv_iff (σ : K ≃ₐ[k] K) {M : IntermediateField k K}
    (f : QuasiRational (↥M) ι κ) (y : ι → K) :
    (f.map (intermediateFieldMap σ M).toRingHom).IsDefinedAt (⇑σ ∘ y) ↔ f.IsDefinedAt y := by
  unfold QuasiRational.IsDefinedAt
  simp only [QuasiRational.map, aeval_map_intermediateFieldMap, ne_eq,
    map_eq_zero_iff _ σ.injective]

theorem QuasiRational.eval_mapAlgEquiv (σ : K ≃ₐ[k] K) {M : IntermediateField k K}
    (f : QuasiRational (↥M) ι κ) (y : ι → K) :
    (f.map (intermediateFieldMap σ M).toRingHom).eval (⇑σ ∘ y) = ⇑σ ∘ f.eval y := by
  funext j
  simp only [QuasiRational.eval, QuasiRational.map, Function.comp_apply,
    aeval_map_intermediateFieldMap, ← map_div₀, map_pRoot]

/-! ### The action on representatives and germs -/

variable {a : ι → K} {a' : κ → K}

namespace Representative

/-- `lem:germ-aut`: the image `(σ M, σ f)` of a representative under an automorphism over
`k`. -/
def map (σ : K ≃ₐ[k] K) (r : Representative k K a a') : Representative k K a a' where
  M := r.M.map σ.toAlgHom
  isAlgClosed := by
    have := r.isAlgClosed
    exact IsAlgClosed.of_ringEquiv (↥r.M) _ (intermediateFieldMap σ r.M).toRingEquiv
  isSmall := by
    have hsmall := r.isSmall
    unfold IsSmall at hsmall ⊢
    rwa [coe_map, AlgEquiv.coe_toAlgHom, ← image_empty ⇑σ, erk_image]
  f := r.f.map (intermediateFieldMap σ r.M).toRingHom
  isDefinedAt y hy := by
    have hy₀ : IsGenericOver r.M a (⇑σ.symm ∘ y) := by
      rw [← isGenericOver_map_iff σ]
      convert hy using 1
      funext i
      simp
    have hyy : y = ⇑σ ∘ (⇑σ.symm ∘ y) := by
      funext i
      simp
    rw [hyy, QuasiRational.isDefinedAt_mapAlgEquiv_iff]
    exact r.isDefinedAt _ hy₀
  isGenericOver y hy := by
    have hy₀ : IsGenericOver r.M a (⇑σ.symm ∘ y) := by
      rw [← isGenericOver_map_iff σ]
      convert hy using 1
      funext i
      simp
    have hyy : y = ⇑σ ∘ (⇑σ.symm ∘ y) := by
      funext i
      simp
    rw [hyy, QuasiRational.eval_mapAlgEquiv, isGenericOver_map_iff]
    exact r.isGenericOver _ hy₀

@[simp]
theorem map_M (σ : K ≃ₐ[k] K) (r : Representative k K a a') : (r.map σ).M = r.M.map σ.toAlgHom :=
  rfl

theorem map_eval (σ : K ≃ₐ[k] K) (r : Representative k K a a') (y : ι → K) :
    (r.map σ).f.eval (⇑σ ∘ y) = ⇑σ ∘ r.f.eval y :=
  QuasiRational.eval_mapAlgEquiv σ r.f y

omit [IsAlgClosed K] in
/-- The closure of the join of the images is the image of the closure of the join. -/
theorem racl_union_map (σ : K ≃ₐ[k] K) (M M' : IntermediateField k K) :
    racl k (((M.map σ.toAlgHom : IntermediateField k K) : Set K) ∪ (M'.map σ.toAlgHom)) =
      (racl k ((M : Set K) ∪ M')).map σ.toAlgHom := by
  rw [racl_map, image_union, coe_map, coe_map, AlgEquiv.coe_toAlgHom]

/-- `lem:germ-aut`: the action on representatives respects equivalence. -/
theorem Equivalent.map {r r' : Representative k K a a'} (σ : K ≃ₐ[k] K)
    (h : r.Equivalent r') : (r.map σ).Equivalent (r'.map σ) := by
  intro y hy
  have hyy : y = ⇑σ ∘ (⇑σ.symm ∘ y) := by
    funext i
    simp
  have hy₀ : IsGenericOver (racl k ((r.M : Set K) ∪ r'.M)) a (⇑σ.symm ∘ y) := by
    rw [← isGenericOver_map_iff σ, ← hyy, ← racl_union_map]
    exact hy
  rw [hyy, map_eval, map_eval, h _ hy₀]

end Representative

namespace Germ

variable [IsAlgClosed k] [UniversalDomain k K] [Finite ι] [Finite κ]

/-- `lem:germ-aut`: the action of an automorphism over `k` on germs. -/
def map (σ : K ≃ₐ[k] K) (g : Germ k a a') : Germ k a a' :=
  Quotient.map (Representative.map σ) (fun _ _ h ↦ Representative.Equivalent.map σ h) g

omit [Finite κ] in
theorem map_mk (σ : K ≃ₐ[k] K) (r : Representative k K a a') :
    Germ.map σ (⟦r⟧ : Germ k a a') = ⟦r.map σ⟧ := rfl

/-- `lem:germ-aut`: the graph ideal of a representative is equivariant. -/
theorem _root_.GroupConfig.Representative.graphIdeal_map (σ : K ≃ₐ[k] K)
    (r : Representative k K a a') :
    (r.map σ).graphIdeal = r.graphIdeal.map (MvPolynomial.map σ.toRingEquiv.toRingHom) := by
  obtain ⟨y, hy⟩ := exists_isGenericOver r.isSmall a
  have hy' : IsGenericOver (r.map σ).M a (⇑σ ∘ y) := (isGenericOver_map_iff σ r.M a y).2 hy
  rw [(r.map σ).graphIdeal_eq hy', r.graphIdeal_eq hy, Representative.map_M, locusIdeal_map]
  congr 1
  funext i
  cases i with
  | inl i => rfl
  | inr j => exact congrFun (r.map_eval σ y) j

/-- `lem:germ-aut`: the graph ideal of a germ is equivariant. -/
theorem graphIdeal_map (σ : K ≃ₐ[k] K) (g : Germ k a a') :
    (g.map σ).graphIdeal = g.graphIdeal.map (MvPolynomial.map σ.toRingEquiv.toRingHom) := by
  induction g using Quotient.inductionOn with
  | h r => exact r.graphIdeal_map σ

/-- `lem:germ-aut`: the canonical base of a germ is equivariant. -/
theorem cb_map (σ : K ≃ₐ[k] K) (g : Germ k a a') : (g.map σ).cb = g.cb.map σ.toAlgHom := by
  unfold cb
  rw [graphIdeal_map, idealFod_map, adjoin_map, Subfield.coe_map]
  rfl

/-- `lem:germ-aut`: an automorphism fixes a germ iff it fixes its canonical base pointwise. -/
theorem map_eq_self_iff (σ : K ≃ₐ[k] K) (g : Germ k a a') :
    g.map σ = g ↔ ∀ x ∈ g.cb, σ x = x := by
  rw [← graphIdeal_injective.eq_iff, graphIdeal_map, ideal_map_eq_self_iff]
  constructor
  · intro h x hx
    have hle : g.cb ≤ fixedBy σ := adjoin_le_iff.2 fun x hx ↦ h x hx
    exact hle hx
  · intro h x hx
    exact h x (subset_adjoin k _ hx)

end Germ

end

end GroupConfig
