/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AdditiveScaling
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Actual automorphisms of the additive group over a field

**Status:** every actual Ga group-scheme automorphism over a field is multiplication by a
nonzero scalar, in every characteristic (#21). Hopf-Spec full faithfulness gives an actual
coordinate-algebra automorphism. Polynomial inverse degrees force degree one, and the Hopf
counit removes the constant. Named consumer: `AdditiveRigidity.normal_additiveGroup_conj`.
This classifies automorphisms over fields; it asserts no such classification over arbitrary
nonreduced coefficient rings. The parameter group in the consumer is reduced.
-/

namespace AclGeom.AdditiveRigidity
noncomputable section

/-- Named consumer: actual additive group-scheme automorphisms are nonzero scalars. -/
theorem polynomialAlgEquiv_fix_zero {k : Type*} [Field k]
    (e : Polynomial k ≃ₐ[k] Polynomial k)
    (hzero : Polynomial.eval 0 (e Polynomial.X) = 0) :
    ∃ a : kˣ, e Polynomial.X = Polynomial.C (a : k) * Polynomial.X := by
  have hcomp : (e Polynomial.X).comp (e.symm Polynomial.X) = Polynomial.X := by
    rw [Polynomial.comp_eq_aeval, Polynomial.aeval_algHom_apply,
      Polynomial.aeval_X_left_apply, AlgEquiv.symm_apply_apply]
  have hdeg := congrArg Polynomial.natDegree hcomp
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_X] at hdeg
  have hdeg₁ : (e Polynomial.X).natDegree = 1 :=
    Nat.eq_one_of_dvd_one ⟨(e.symm Polynomial.X).natDegree, hdeg.symm⟩
  obtain ⟨a, ha, b, hab⟩ := Polynomial.natDegree_eq_one.mp hdeg₁
  have hb : b = 0 := by
    rw [← hab] at hzero
    simpa using hzero
  exact ⟨Units.mk0 a ha, by simpa only [hb, Polynomial.C_0, add_zero, Units.val_mk0] using hab.symm⟩
end
end AclGeom.AdditiveRigidity

namespace AclGeom.AdditiveRigidity
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u

/-- Named consumer: the actual normal additive-subgroup conjugation character. -/
theorem groupIso_eq_scale (k : Type u) [Field k]
    (e : (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme ≅
      (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme) :
    ∃ a : kˣ, e.hom.hom.hom = scale k (a : k) := by
  let R := AdditiveGroupScheme.CoordinateRing k 1
  let A : CommHopfAlgCat.{u} k := .of k R
  let F : (CommHopfAlgCat.{u} k)ᵒᵖ ⥤ Grp (Over (Spec (.of k))) := hopfSpec (.of k)
  have : F.Full := hopfSpec.instFull
  have : F.Faithful := hopfSpec.instFaithful
  let E : A ≅ A := (F.preimageIso (X := .op A) (Y := .op A) e).unop
  have he : F.map E.hom.op = e.hom := F.map_preimage (X := .op A) (Y := .op A) e.hom
  let B : R ≃ₐ[k] R := AlgEquiv.ofAlgHom E.hom.hom.toAlgHom E.inv.hom.toAlgHom
    (by apply AlgHom.ext; intro z; exact CommHopfAlgCat.hom_inv_apply E z)
    (by apply AlgHom.ext; intro z; exact CommHopfAlgCat.inv_hom_apply E z)
  let P : R ≃ₐ[k] Polynomial k :=
    (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun k (Fin 1))).trans
      (MvPolynomial.uniqueAlgEquiv k (Fin 1))
  have hPX : P (AffineSchemeAction.lineCoordinate k) = Polynomial.X := by
    change (MvPolynomial.uniqueAlgEquiv k (Fin 1))
      ((SymmetricAlgebra.equivMvPolynomial (Pi.basisFun k (Fin 1)))
        (SymmetricAlgebra.ι k (Fin 1 → k) (Pi.basisFun k (Fin 1) 0))) = Polynomial.X
    rw [SymmetricAlgebra.equivMvPolynomial_ι_apply]
    rw [MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_X]
  have hPX' : P.symm Polynomial.X = AffineSchemeAction.lineCoordinate k := by
    rw [← hPX, AlgEquiv.symm_apply_apply]
  have hP₀ : (Polynomial.aeval (0 : k)).comp P.toAlgHom = Bialgebra.counitAlgHom k R := by
    apply AffineSchemeAction.lineHom_ext
    rw [AlgHom.comp_apply]
    change Polynomial.aeval (0 : k) (P (AffineSchemeAction.lineCoordinate k)) = _
    rw [hPX, Polynomial.aeval_X]
    change 0 = (Bialgebra.counitAlgHom k (SymmetricAlgebra k (Fin 1 → k)))
      (SymmetricAlgebra.ι k (Fin 1 → k) (Pi.basisFun k (Fin 1) 0))
    simp only [SymmetricAlgebra.counitAlgHom_eq, SymmetricAlgebra.algebraMapInv_ι]
  have hPeval (z : R) : Polynomial.eval 0 (P z) = Bialgebra.counitAlgHom k R z :=
    AlgHom.congr_fun hP₀ z
  let BP : Polynomial k ≃ₐ[k] Polynomial k := P.symm.trans (B.trans P)
  have hzero : Polynomial.eval 0 (BP Polynomial.X) = 0 := by
    change Polynomial.eval 0 (P (B (P.symm Polynomial.X))) = 0
    rw [hPX', hPeval]
    have hc := AlgHom.congr_fun (BialgHom.counitAlgHom_comp E.hom.hom)
      (AffineSchemeAction.lineCoordinate k)
    change Bialgebra.counitAlgHom k R (B (AffineSchemeAction.lineCoordinate k)) =
      Bialgebra.counitAlgHom k R (AffineSchemeAction.lineCoordinate k) at hc
    rw [hc]
    change (Bialgebra.counitAlgHom k (SymmetricAlgebra k (Fin 1 → k)))
      (SymmetricAlgebra.ι k (Fin 1 → k) (Pi.basisFun k (Fin 1) 0)) = 0
    simp only [SymmetricAlgebra.counitAlgHom_eq, SymmetricAlgebra.algebraMapInv_ι]
  obtain ⟨a, ha⟩ := polynomialAlgEquiv_fix_zero BP hzero
  change P (B (P.symm Polynomial.X)) = Polynomial.C (a : k) * Polynomial.X at ha
  rw [hPX'] at ha
  have hφ : E.hom.hom (AffineSchemeAction.lineCoordinate k) =
      algebraMap k R (a : k) * AffineSchemeAction.lineCoordinate k := by
    apply P.injective
    change P (B (AffineSchemeAction.lineCoordinate k)) = _
    rw [map_mul, P.commutes, hPX]
    exact ha
  refine ⟨a, ?_⟩
  apply Over.OverMorphism.ext
  rw [← he]
  change Spec.map (CommRingCat.ofHom E.hom.hom.toAlgHom.toRingHom) =
    Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval
      (algebraMap k R (a : k) * AffineSchemeAction.lineCoordinate k)).toRingHom)
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply congrArg AlgHom.toRingHom
  apply AffineSchemeAction.lineHom_ext
  rw [AffineSchemeAction.lineEval_lineCoordinate]
  exact hφ
end
end AclGeom.AdditiveRigidity
