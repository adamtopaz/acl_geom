/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AffineGroupScheme
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
# The coordinate pullback of the actual affine-group morphism

**Status:** proved (#21). Evaluation at two independent affine coefficients is injective;
its field universe is independent of the base universe. The existing algebraic Spec functor
constructs the regular coordinate pullback of an actual group morphism on any affine chart,
with its literal point evaluations. The chart/morphism/point agreement are explicit generic
premises. Named consumer: `AffineParameterCover` derives dominance and actual finite opens;
`SchemeAffineParameterCover` supplies all premises internally from the genuine action.
-/

namespace AclGeom.AffineGroupScheme
noncomputable section

/-- Independent affine coordinates give an injective coordinate-algebra evaluation.
 Named consumer: dominance of the actual finite-cover parameter morphism. -/
theorem eval_injective_of_algebraicIndependent {k C : Type*} [Field k] [Field C]
    [Algebra k C] (a : Cˣ) (b : C)
    (hab : AlgebraicIndependent k (![(a : C), b] : Fin 2 → C)) :
    Function.Injective (eval k a b) := by
  let P := MvPolynomial (Fin 2) k
  let x : P := MvPolynomial.X 0
  let y : P := MvPolynomial.X 1
  let Q := Localization.Away x
  let γ : P →ₐ[k] CoordinateRing k :=
    MvPolynomial.aeval (![(dilationUnit k : CoordinateRing k), translation k])
  have hxQ : IsUnit (algebraMap P Q x) := IsLocalization.Away.algebraMap_isUnit x
  let xu : Qˣ := hxQ.unit
  let δ : CoordinateRing k →ₐ[k] Q := eval k xu (algebraMap P Q y)
  have hxγ : IsUnit (γ x) := by
    simpa only [γ, x, P, MvPolynomial.aeval_X, Matrix.cons_val_zero] using (dilationUnit k).isUnit
  let η : Q →ₐ[k] CoordinateRing k := IsLocalization.Away.liftAlgHom x (f := γ) hxγ
  have hη (z : P) : η (algebraMap P Q z) = γ z :=
    IsLocalization.Away.lift_eq x (g := γ.toRingHom) hxγ z
  have hleft : η.comp δ = AlgHom.id k (CoordinateRing k) := by
    apply hom_ext
    · simp only [AlgHom.comp_apply, δ, eval_dilation, xu, hxQ.unit_spec,
        hη, γ, x, P, MvPolynomial.aeval_X, Matrix.cons_val_zero, AlgHom.id_apply]
    · simp only [AlgHom.comp_apply, δ, eval_translation, hη, γ, y, P,
        MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero, AlgHom.id_apply]
  let ψ : P →ₐ[k] C := MvPolynomial.aeval (![(a : C), b])
  have hψ : Function.Injective ψ := algebraicIndependent_iff_injective_aeval.mp hab
  have hxψ : IsUnit (ψ x) := by
    simpa only [ψ, x, P, MvPolynomial.aeval_X, Matrix.cons_val_zero] using a.isUnit
  let μ : Q →ₐ[k] C := IsLocalization.Away.liftAlgHom x (f := ψ) hxψ
  have hμ (z : P) : μ (algebraMap P Q z) = ψ z :=
    IsLocalization.Away.lift_eq x (g := ψ.toRingHom) hxψ z
  have hμinj : Function.Injective μ := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers x) μ.toRingHom).mpr
    intro z w
    constructor
    · intro h
      exact congrArg μ h
    · intro h
      exact congrArg (algebraMap P Q) (hψ ((hμ z).symm.trans (h.trans (hμ w))))
  have hμδ : μ.comp δ = eval k a b := by
    apply hom_ext
    · simp only [AlgHom.comp_apply, δ, eval_dilation, xu, hxQ.unit_spec,
        hμ, ψ, x, P, MvPolynomial.aeval_X, Matrix.cons_val_zero]
    · simp only [AlgHom.comp_apply, δ, eval_translation, hμ, ψ, y, P,
        MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero]
  intro v w hvw
  have hd : δ v = δ w := hμinj (by
    change (μ.comp δ) v = (μ.comp δ) w
    rw [hμδ]
    exact hvw)
  have hv := AlgHom.congr_fun hleft v
  have hw := AlgHom.congr_fun hleft w
  exact hv.symm.trans ((congrArg η hd).trans hw)

end
end AclGeom.AffineGroupScheme

namespace AclGeom.AffineGroupScheme
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
universe u
variable {k : Type u} [Field k]

/-- Pullback along the actual group morphism gives regular affine coordinates on every
 actual affine chart, with their literal point evaluations. Named consumer: finite covers. -/
theorem exists_chart_coordinates (G : AlgebraicGroup k)
    (f : G.Hom (algebraicGroup k))
    (Φ : (𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) →* AffineTransformation k)
    (hpoint : ∀ q, pointsMulEquiv k (q ≫ f.hom.hom) = Φ q)
    {A : Type u} [CommRing A] [Algebra k A]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G.toGroupScheme.X) :
    ∃ ψ : CoordinateRing k →ₐ[k] A,
      (algSpec (.of k)).map (CommAlgCat.ofHom ψ).op = g ≫ f.hom.hom ∧
      ∀ φ : A →ₐ[k] k,
        φ (ψ (dilationUnit k)) =
          ((Φ ((unitIsoSpecAsOver k).hom ≫
            (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).multiplier : k) ∧
        φ (ψ (translation k)) =
          (Φ ((unitIsoSpecAsOver k).hom ≫
            (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).shift := by
  have : (algSpec (.of k)).Full := algSpec.instFull
  let m : (algSpec (.of k)).obj (.op (CommAlgCat.of k A)) ⟶
      (algSpec (.of k)).obj (.op (CommAlgCat.of k (CoordinateRing k))) := g ≫ f.hom.hom
  let ψ : CoordinateRing k →ₐ[k] A := ((algSpec (.of k)).preimage m).unop.hom
  have hm : (algSpec (.of k)).map (CommAlgCat.ofHom ψ).op = m :=
    (algSpec (.of k)).map_preimage m
  refine ⟨ψ, hm, ?_⟩
  intro φ
  let p := (unitIsoSpecAsOver k).hom ≫
    (algSpec (.of k)).map (CommAlgCat.ofHom φ).op
  let q := p ≫ g
  have hp : p ≫ m = (pointsMulEquiv k).symm (Φ q) := by
    apply (pointsMulEquiv k).injective
    have hpa : q ≫ f.hom.hom = p ≫ m := Category.assoc p g f.hom.hom
    exact (congrArg (pointsMulEquiv k) hpa.symm).trans
      ((hpoint q).trans ((pointsMulEquiv k).apply_symm_apply (Φ q)).symm)
  have hleft : (p ≫ m).left =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
    rw [← hm]
    change (𝟙 _ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫ _ = _
    rw [Category.id_comp]
    rfl
  have hs : Spec.map (CommRingCat.ofHom (φ.comp ψ).toRingHom) =
      Spec.map (CommRingCat.ofHom (eval k (Φ q).multiplier (Φ q).shift).toRingHom) := by
    have hcomp : Spec.map (CommRingCat.ofHom (φ.comp ψ).toRingHom) =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
          Spec.map (CommRingCat.ofHom ψ.toRingHom) :=
      Spec.map_comp (CommRingCat.ofHom ψ.toRingHom) (CommRingCat.ofHom φ.toRingHom)
    have he := congrArg
      (fun r : 𝟙_ (Over (Spec (.of k))) ⟶ (algebraicGroup k).toGroupScheme.X ↦ r.left) hp
    exact hcomp.trans (hleft.symm.trans (he.trans (pointsMulEquiv_symm_apply_left k (Φ q))))
  have he : φ.comp ψ = eval k (Φ q).multiplier (Φ q).shift := by
    apply AlgHom.coe_ringHom_injective
    exact congrArg (fun r : CommRingCat.of (CoordinateRing k) ⟶ CommRingCat.of k ↦ r.hom)
      (Spec.map_injective hs)
  constructor
  · change (φ.comp ψ) (dilationUnit k) = _
    rw [he, eval_dilation]
    exact congrArg (fun z ↦ ((Φ z).multiplier : k))
      (Category.assoc (unitIsoSpecAsOver k).hom
        ((algSpec (.of k)).map (CommAlgCat.ofHom φ).op) g)
  · change (φ.comp ψ) (translation k) = _
    rw [he, eval_translation]
    exact congrArg (fun z ↦ (Φ z).shift)
      (Category.assoc (unitIsoSpecAsOver k).hom
        ((algSpec (.of k)).map (CommAlgCat.ofHom φ).op) g)

end
end AclGeom.AffineGroupScheme
