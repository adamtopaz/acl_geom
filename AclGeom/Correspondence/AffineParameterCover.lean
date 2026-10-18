/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AffineCoordinatePullback
import AclGeom.Correspondence.GenericFiniteCover
import AclGeom.Correspondence.AffineGroupGeometry

/-!
# A finite cover from the actual affine parameter chart

**Status:** proved criterion (#21). The same global group morphism, faithful affine point
homomorphism and independent rational chart coefficients give a finite surjective scheme
map between nonempty opens, with the actual commuting square. The criterion exposes its
chart, independence and point formulas. Named consumer: `SchemeAffineParameterCover`
derives every premise from the genuine regular action on an integral affine curve.
Inseparability is allowed; no global finiteness or scheme monomorphism is asserted.
-/

namespace AclGeom.AffineGroupScheme
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The same regular affine-group morphism and independent rational chart coefficients
 give an actual finite cover on nonempty opens. Named consumer: the genuine curve action. -/
theorem exists_finite_chart (G : AlgebraicGroup k)
    (f : G.Hom (algebraicGroup k))
    (Φ : (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) →* AffineTransformation k)
    (hΦinj : Function.Injective Φ)
    (hpoint : ∀ q, pointsMulEquiv k (q ≫ f.hom.hom) = Φ q)
    {A : Type u} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G.toGroupScheme.X)
    [IsOpenImmersion g.left] (d a b : A) (hd : d ≠ 0)
    (hab : AlgebraicIndependent k
      (![algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) d,
        algebraMap A (FractionRing A) b / algebraMap A (FractionRing A) d] :
          Fin 2 → FractionRing A))
    (hraw : ∀ (φ : A →ₐ[k] k), φ d ≠ 0 →
      ((Φ ((unitIsoSpecAsOver k).hom ≫
        (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).multiplier : k) =
          φ a / φ d ∧
      (Φ ((unitIsoSpecAsOver k).hom ≫
        (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).shift = φ b / φ d) :
    ∃ (U T : Over (Spec (.of k))) (jU : U ⟶ G.toGroupScheme.X)
      (jT : T ⟶ (algebraicGroup k).toGroupScheme.X) (π : U ⟶ T),
      IsOpenImmersion jU.left ∧ IsOpenImmersion jT.left ∧
      Nonempty U.left ∧ Nonempty T.left ∧ IsFinite π.left ∧ Surjective π.left ∧
      jU ≫ f.hom.hom = π ≫ jT := by
  have : Mono g := Over.mono_of_mono_left g
  obtain ⟨ψ, hm, hvalues⟩ := exists_chart_coordinates G f Φ hpoint g
  let C := FractionRing A
  let evC : A →ₐ[k] C := IsScalarTower.toAlgHom k A C
  have hevCinj : Function.Injective evC := IsFractionRing.injective A C
  have hdC : evC d ≠ 0 := by
    intro h
    apply hd
    apply hevCinj
    simpa only [map_zero] using h
  have hclear (s c : A) (hc : ∀ (φ : A →ₐ[k] k), φ d ≠ 0 → φ s = φ c / φ d) :
      d * s = c := by
    apply sub_eq_zero.mp
    have hz : d * (d * s - c) = 0 := IsNilpotent.eq_zero
      (isNilpotent_of_forall_algHom_eq_zero (k := k) (fun φ ↦ by
        by_cases hφ : φ d = 0
        · rw [map_mul, hφ, zero_mul]
        · have he : φ d * φ s = φ c := by
            rw [mul_comm, hc φ hφ]
            exact div_mul_cancel₀ _ hφ
          simp only [map_mul, map_sub, he, sub_self, mul_zero]))
    exact (mul_eq_zero.mp hz).resolve_left hd
  have haA : d * ψ (dilationUnit k) = a :=
    hclear _ _ (fun φ hφ ↦ (hvalues φ).1.trans (hraw φ hφ).1)
  have hbA : d * ψ (translation k) = b :=
    hclear _ _ (fun φ hφ ↦ (hvalues φ).2.trans (hraw φ hφ).2)
  have haC : evC (ψ (dilationUnit k)) = evC a / evC d := by
    apply (eq_div_iff hdC).mpr
    exact (mul_comm _ _).trans ((map_mul evC _ _).symm.trans (congrArg evC haA))
  have hbC : evC (ψ (translation k)) = evC b / evC d := by
    apply (eq_div_iff hdC).mpr
    exact (mul_comm _ _).trans ((map_mul evC _ _).symm.trans (congrArg evC hbA))
  let ρ : CoordinateRing k →ₐ[k] C := evC.comp ψ
  let au : Cˣ := Units.map ρ.toMonoidHom (dilationUnit k)
  let bz : C := ρ (translation k)
  have hρ : eval k au bz = ρ := (homCoordinates k C).left_inv ρ
  have hAI : AlgebraicIndependent k (![(au : C), bz] : Fin 2 → C) := by
    change AlgebraicIndependent k
      (![evC (ψ (dilationUnit k)), evC (ψ (translation k))] : Fin 2 → C)
    rw [haC, hbC]
    exact hab
  have hρinj : Function.Injective ρ := by
    rw [← hρ]
    exact eval_injective_of_algebraicIndependent au bz hAI
  have hψinj : Function.Injective ψ := fun _ _ h ↦ hρinj (congrArg evC h)
  have hpoints : Function.Injective (fun φ : A →ₐ[k] k ↦ φ.comp ψ) := by
    intro φ χ heq
    let sp (θ : A →ₐ[k] k) : (Spec (.of k)).asOver (Spec (.of k)) ⟶
        (Spec (.of A)).asOver (Spec (.of k)) :=
      (algSpec (.of k)).map (CommAlgCat.ofHom θ).op
    let q (θ : A →ₐ[k] k) := (unitIsoSpecAsOver k).hom ≫ sp θ ≫ g
    have ha : ((Φ (q φ)).multiplier : k) = ((Φ (q χ)).multiplier : k) :=
      (hvalues φ).1.symm.trans
        ((AlgHom.congr_fun heq (dilationUnit k)).trans (hvalues χ).1)
    have hb : (Φ (q φ)).shift = (Φ (q χ)).shift :=
      (hvalues φ).2.symm.trans
        ((AlgHom.congr_fun heq (translation k)).trans (hvalues χ).2)
    have hq : q φ = q χ := hΦinj (AffineTransformation.ext (Units.ext ha) hb)
    have hmap : sp φ = sp χ := by
      apply (cancel_epi (unitIsoSpecAsOver k).hom).mp
      apply (cancel_mono g).mp
      exact (Category.assoc (unitIsoSpecAsOver k).hom (sp φ) g).trans
        (hq.trans (Category.assoc (unitIsoSpecAsOver k).hom (sp χ) g).symm)
    have hleft := congrArg
      (fun z : (Spec (.of k)).asOver (Spec (.of k)) ⟶
        (Spec (.of A)).asOver (Spec (.of k)) ↦ z.left) hmap
    change Spec.map (CommRingCat.ofHom φ.toRingHom) =
      Spec.map (CommRingCat.ofHom χ.toRingHom) at hleft
    ext z
    exact congrArg (fun h : CommRingCat.of A ⟶ CommRingCat.of k ↦ h.hom z)
      (Spec.map_injective hleft)
  exact GenericFiniteCover.exists_finite_open_square ψ hψinj hpoints
    G.toGroupScheme.X g f.hom.hom hm

end
end AclGeom.AffineGroupScheme
