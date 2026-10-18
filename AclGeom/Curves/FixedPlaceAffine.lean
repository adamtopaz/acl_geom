/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Curves.RationalAutomorphisms
import AclGeom.Curves.PlaceTransport
import AclGeom.Correspondence.AffineAction

/-!
# Affine coordinates from a fixed place

A rational generator with a simple pole at a fixed place has an affine transform under
 every automorphism fixing that place. The order formula eliminates the denominator's
 nonconstant coefficient in the existing fractional-linear expression. Transcendence
 makes the affine coefficients unique.

**Status:** proved. The faithful representation criterion takes its faithful opposite
 field action, fixed place and genus zero explicitly. Its named consumer
 `SchemeAffinePointAction.exists_faithful_affine_coordinates` derives every input from the
 actual connected-group action on an affine curve. This constructs a group homomorphism
 on k-points; rational coefficient functions and scheme-group classification remain open.
-/

namespace AclGeom.FixedPlaceAffine

noncomputable section

open IntermediateField

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
  [IsAlgClosed k] [IsFunctionFieldOneVar k F]

private theorem ord_affine (P : Place k F) {t : F} (ht0 : t ≠ 0)
    (ht : P.ord t = -1) {a : k} (ha : a ≠ 0) (b : k) :
    P.ord (algebraMap k F a * t + algebraMap k F b) = -1 := by
  have ha0 : algebraMap k F a ≠ 0 := (map_ne_zero _).2 ha
  have hat0 := mul_ne_zero ha0 ht0
  have hat : P.ord (algebraMap k F a * t) = -1 := by
    rw [P.ord_mul ha0 ht0, P.ord_algebraMap ha, ht, zero_add]
  by_cases hb : b = 0
  · rw [hb, map_zero, add_zero]
    exact hat
  · rw [P.ord_add_eq_left hat0 ((map_ne_zero _).2 hb) (by
      rw [hat, P.ord_algebraMap hb]
      omega), hat]

/-- An automorphism fixing the pole of a rational generator acts affinely in that generator.
Named consumer: the faithful affine representation of an actual regular affine curve action. -/
theorem exists_affine_of_fixed_pole {t : F} (ht : Transcendental k t)
    (htop : adjoin k ({t} : Set F) = ⊤) (P : Place k F) (hord : P.ord t = -1)
    (σ : F ≃ₐ[k] F) (hfix : P.comap σ = P) :
    ∃ a b : k, a ≠ 0 ∧ σ t = algebraMap k F a * t + algebraMap k F b := by
  have ht0 : t ≠ 0 := fun h ↦ ht (h ▸ isAlgebraic_zero)
  have hσ0 : σ t ≠ 0 := (map_ne_zero σ).2 ht0
  have hσord : P.ord (σ t) = -1 := by
    have h := Place.ord_comap σ P t
    rw [hfix, hord] at h
    exact h.symm
  obtain ⟨a, b, c, d, hdet, hden, hrel⟩ :=
    exists_moebius_of_generator_algEquiv ht htop σ
  have hc : c = 0 := by
    by_contra hc
    have hdenord := ord_affine P ht0 hord hc d
    have hnum0 : algebraMap k F a * t + algebraMap k F b ≠ 0 := by
      rw [← hrel]
      exact mul_ne_zero hσ0 hden
    have hm := P.ord_mul hσ0 hden
    rw [hrel, hσord, hdenord] at hm
    by_cases ha : a = 0
    · have hb : b ≠ 0 := by
        intro hb
        apply hnum0
        rw [ha, hb, map_zero, zero_mul, add_zero]
      rw [ha, map_zero, zero_mul, zero_add, P.ord_algebraMap hb] at hm
      omega
    · rw [ord_affine P ht0 hord ha b] at hm
      omega
  have hd : d ≠ 0 := by
    intro hd
    apply hden
    rw [hc, hd, map_zero, zero_mul, add_zero]
  have ha : a ≠ 0 := by
    intro ha
    apply hdet
    rw [ha, hc, zero_mul, mul_zero, sub_zero]
  rw [hc, map_zero, zero_mul, zero_add] at hrel
  refine ⟨a / d, b / d, div_ne_zero ha hd, ?_⟩
  have hdF : algebraMap k F d ≠ 0 := (map_ne_zero _).2 hd
  rw [map_div₀, map_div₀, div_mul_eq_mul_div, ← add_div]
  exact (eq_div_iff hdF).2 hrel

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
private theorem affine_eval_injective {t : F} (ht : Transcendental k t) :
    Function.Injective (fun A : AffineTransformation k ↦
      algebraMap k F (A.multiplier : k) * t + algebraMap k F A.shift) := by
  intro A B h
  change algebraMap k F (A.multiplier : k) * t + algebraMap k F A.shift =
    algebraMap k F (B.multiplier : k) * t + algebraMap k F B.shift at h
  by_cases ha : (A.multiplier : k) = (B.multiplier : k)
  · have hb : A.shift = B.shift := by
      apply (algebraMap k F).injective
      rw [ha] at h
      exact add_left_cancel h
    exact AffineTransformation.ext (Units.ext ha) hb
  · have hd : algebraMap k F ((A.multiplier : k) - (B.multiplier : k)) ≠ 0 :=
      (map_ne_zero _).2 (sub_ne_zero.mpr ha)
    have he : t = algebraMap k F
        ((B.shift - A.shift) / ((A.multiplier : k) - (B.multiplier : k))) := by
      rw [map_div₀]
      apply (eq_div_iff hd).2
      rw [map_sub, map_sub]
      linear_combination h
    exfalso
    apply ht
    rw [he]
    exact isAlgebraic_algebraMap _

/-- A faithful opposite function-field action fixing a place in genus zero has faithful
 affine coordinates. The actual scheme consumer derives the fixed place, genus and faithful
 field action from its genuine curve/action hypotheses. -/
theorem exists_faithful_affine_representation {Γ : Type*} [Group Γ]
    (ρ : Γ →* (F ≃ₐ[k] F)ᵐᵒᵖ) (hρ : Function.Injective ρ)
    (P : Place k F) (hP : ∀ g, P.comap (ρ g).unop = P)
    (hg : genus k F = 0) :
    ∃ t : F, Transcendental k t ∧ adjoin k ({t} : Set F) = ⊤ ∧
      ∃ Φ : Γ →* AffineTransformation k, Function.Injective Φ ∧
        ∀ g, (ρ g).unop t = algebraMap k F ((Φ g).multiplier : k) * t +
          algebraMap k F (Φ g).shift := by
  classical
  obtain ⟨t, ht, hpd, htop⟩ := exists_generator_of_genus_eq_zero hg P
  have hord : P.ord t = -1 := ord_eq_neg_one_of_poleDivisor ht hpd
  have hcoeff (g : Γ) : ∃ a b : k, a ≠ 0 ∧
      (ρ g).unop t = algebraMap k F a * t + algebraMap k F b :=
    exists_affine_of_fixed_pole ht htop P hord (ρ g).unop (hP g)
  choose a b ha hab using hcoeff
  let A (g : Γ) : AffineTransformation k := ⟨Units.mk0 (a g) (ha g), b g⟩
  let ε (T : AffineTransformation k) : F :=
    algebraMap k F (T.multiplier : k) * t + algebraMap k F T.shift
  have hε : Function.Injective ε := affine_eval_injective ht
  have hA (g : Γ) : ε (A g) = (ρ g).unop t := (hab g).symm
  let Φ : Γ →* AffineTransformation k := {
    toFun := A
    map_one' := by
      apply hε
      change ε (A 1) = ε 1
      rw [hA, ρ.map_one]
      simp [ε]
    map_mul' := by
      intro g h
      apply hε
      change ε (A (g * h)) = ε (A g * A h)
      calc
        ε (A (g * h)) = (ρ (g * h)).unop t := hA (g * h)
        _ = (ρ h).unop ((ρ g).unop t) := by
          rw [ρ.map_mul, MulOpposite.unop_mul]
          rfl
        _ = algebraMap k F (a g) *
              (algebraMap k F (a h) * t + algebraMap k F (b h)) +
                algebraMap k F (b g) := by
          rw [hab g, map_add (ρ h).unop, map_mul (ρ h).unop,
            (ρ h).unop.commutes, (ρ h).unop.commutes, hab h]
        _ = ε (A g * A h) := by
          change _ = algebraMap k F (a g * a h) * t +
            algebraMap k F (a g * b h + b g)
          rw [map_mul, map_add, map_mul]
          ring }
  refine ⟨t, ht, htop, Φ, ?_, ?_⟩
  · intro g h hgh
    apply hρ
    apply MulOpposite.unop_injective
    have htgh : (ρ g).unop t = (ρ h).unop t := by
      rw [← hA g, ← hA h]
      exact congrArg ε hgh
    let S := adjoin k ({t} : Set F)
    let incl : S →ₐ[k] F := IsScalarTower.toAlgHom k S F
    have heq : (ρ g).unop.toAlgHom.comp incl = (ρ h).unop.toAlgHom.comp incl := by
      apply IntermediateField.adjoin_algHom_ext k
      intro z hz
      have hzt : z = t := Set.mem_singleton_iff.1 hz
      subst z
      exact htgh
    apply AlgEquiv.ext
    intro x
    have hx : x ∈ S := by
      change x ∈ adjoin k ({t} : Set F)
      rw [htop]
      trivial
    exact congrArg (fun f : S →ₐ[k] F ↦ f ⟨x, hx⟩) heq
  · intro g
    exact hab g

end

end AclGeom.FixedPlaceAffine
