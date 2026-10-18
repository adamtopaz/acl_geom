/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.SchemeCoefficientPoints

/-!
# Rational coefficients of actual affine-action families

**Status:** proved over an ACF base for an actual regular action on an integral affine scheme
and a finite-type parameter domain (#21). The coordinate and its pointwise affine formulas
are explicit criterion premises. Cleared tensor identities construct rational coefficients,
retain every point specialization where the denominator is nonzero, and identify the actual
generic translate through its literal section/germ comparison. Both tensor-domain witnesses
are proved internally and bound in the result. Named consumer:
`SchemeAffineParameters` derives the coordinate and all pointwise premises internally.
-/

namespace AclGeom.AffineCoefficients

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct
open SchemeGenericTranslate

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

attribute [local instance] sectionsAlgebra ActionFunctionField.functionFieldAlgebra

/-- Given an actual affine coordinate on all group points, the actual parameter coaction has
 rational affine coefficients, with literal specialization wherever the denominator is nonzero.
 Named consumer: the genuine connected-group rational-parameter theorem. -/
theorem exists_cleared_action_coefficients (G : AlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [ModObj G.toGroupScheme.X V] {t : V.left.functionField} (ht : Transcendental k t)
    (hpoint : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X, ∃ a b : k,
      (ActionFunctionField.functionFieldAction G V q).unop t =
        algebraMap k V.left.functionField a * t + algebraMap k V.left.functionField b)
    {A : Type u} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G.toGroupScheme.X) :
    let f := (sectionsFunctionFieldEquiv V).toAlgHom.comp
      (IsScalarTower.toAlgHom k Γ(V.left, ⊤) (FractionRing Γ(V.left, ⊤)))
    let act (r : Γ(V.left, ⊤)) := Algebra.TensorProduct.map (AlgHom.id k A) f
      (sectionsTensorAut V g (1 ⊗ₜ[k] r))
    ∃ r s : Γ(V.left, ⊤), f s ≠ 0 ∧ t * f s = f r ∧
      ∃ d a b : A, d ≠ 0 ∧ a ≠ 0 ∧
        d • act r = a • ((1 ⊗ₜ[k] t) * act s) + b • act s ∧
        ∀ (φ : A →ₐ[k] k), φ d ≠ 0 →
          (ActionFunctionField.functionFieldAction G V ((unitIsoSpecAsOver k).hom ≫
            (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).unop t =
              algebraMap k V.left.functionField (φ a / φ d) * t +
                algebraMap k V.left.functionField (φ b / φ d) := by
  classical
  let R : Type u := Γ(V.left, ⊤)
  let F : Type u := V.left.functionField
  let e := sectionsFunctionFieldEquiv V
  let f : R →ₐ[k] F := e.toAlgHom.comp (IsScalarTower.toAlgHom k R (FractionRing R))
  let act (r : R) := Algebra.TensorProduct.map (AlgHom.id k A) f
    (sectionsTensorAut V g (1 ⊗ₜ[k] r))
  have : Nonempty (⊤ : V.left.Opens) := ⟨⟨genericPoint _, trivial⟩⟩
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective R (e.symm t)
  have hsF : f s ≠ 0 := by
    change e (algebraMap R (FractionRing R) s) ≠ 0
    exact (map_ne_zero e).2 (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)
  have hrel : t * f s = f r := by
    change t * e (algebraMap R (FractionRing R) s) = e (algebraMap R (FractionRing R) r)
    rw [← e.apply_symm_apply t, ← map_mul]
    exact congrArg e ((eq_div_iff
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)).1 hrs.symm)
  have hact (φ : A →ₐ[k] k) (r : R) : tensorPointEval φ (act r) =
      (ActionFunctionField.functionFieldAction G V ((unitIsoSpecAsOver k).hom ≫
        (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).unop (f r) := by
    have hf : f r = V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) r :=
      sectionsFunctionFieldEquiv_algebraMap V r
    rw [hf]
    exact (sectionsTensorAut_point_germ G V g φ r).symm
  have hS (φ : A →ₐ[k] k) : tensorPointEval φ (act s) ≠ 0 := by
    rw [hact]
    exact (map_ne_zero _).2 hsF
  have hU (φ : A →ₐ[k] k) : ∃ a b : k, tensorPointEval φ (act r) =
      (algebraMap k F a * t + algebraMap k F b) * tensorPointEval φ (act s) := by
    obtain ⟨a, b, hab⟩ := hpoint ((unitIsoSpecAsOver k).hom ≫
      (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)
    refine ⟨a, b, ?_⟩
    rw [hact, hact, ← hrel, map_mul, hab]
  obtain ⟨d, a, b, hd, hclear⟩ := exists_cleared_coefficients ht (act r) (act s) hS hU
  have hformula (φ : A →ₐ[k] k) (hdφ : φ d ≠ 0) :
      (ActionFunctionField.functionFieldAction G V ((unitIsoSpecAsOver k).hom ≫
        (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).unop t =
          algebraMap k F (φ a / φ d) * t + algebraMap k F (φ b / φ d) := by
    let q := (unitIsoSpecAsOver k).hom ≫ (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g
    let σ := (ActionFunctionField.functionFieldAction G V q).unop
    have hV : tensorPointEval φ ((1 ⊗ₜ[k] t) * act s) = t * tensorPointEval φ (act s) := by
      rw [map_mul]
      have h_eval : tensorPointEval φ (1 ⊗ₜ[k] t) = t := by
        change algebraMap k F (φ 1) * t = t
        rw [map_one, map_one, _root_.one_mul]
      rw [h_eval]
    have hh := congrArg (tensorPointEval φ) hclear
    rw [map_add, tensorPointEval_smul, tensorPointEval_smul, tensorPointEval_smul,
      hV, hact, hact] at hh
    change algebraMap k F (φ d) * σ (f r) =
      algebraMap k F (φ a) * (t * σ (f s)) + algebraMap k F (φ b) * σ (f s) at hh
    rw [← hrel, map_mul] at hh
    have hσs : σ (f s) ≠ 0 := (map_ne_zero σ).2 hsF
    have hlin : σ t * algebraMap k F (φ d) =
        algebraMap k F (φ a) * t + algebraMap k F (φ b) := by
      apply mul_right_cancel₀ hσs
      calc
        _ = algebraMap k F (φ d) * (σ t * σ (f s)) := by ring
        _ = _ := hh
        _ = _ := by ring
    change σ t = _
    rw [map_div₀, map_div₀, div_mul_eq_mul_div, ← add_div]
    exact (eq_div_iff ((map_ne_zero _).2 hdφ)).2 hlin
  have ha : a ≠ 0 := by
    intro ha
    have hex : ∃ φ : A →ₐ[k] k, φ d ≠ 0 := by
      by_contra! hh
      exact hd (IsNilpotent.eq_zero (isNilpotent_of_forall_algHom_eq_zero hh))
    obtain ⟨φ, hφ⟩ := hex
    let q := (unitIsoSpecAsOver k).hom ≫ (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g
    let σ := (ActionFunctionField.functionFieldAction G V q).unop
    have hh := hformula φ hφ
    rw [ha, map_zero, zero_div, map_zero, zero_mul, zero_add] at hh
    have he := congrArg σ.symm hh
    change σ.symm (σ t) = σ.symm (algebraMap k F (φ b / φ d)) at he
    rw [σ.symm_apply_apply, σ.symm.commutes] at he
    exact ht (he ▸ isAlgebraic_algebraMap _)
  exact ⟨r, s, hsF, hrel, d, a, b, hd, ha, hclear, hformula⟩

end

end AclGeom.AffineCoefficients

namespace AclGeom.AffineCoefficients

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct
open SchemeGenericTranslate

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

attribute [local instance] sectionsAlgebra ActionFunctionField.functionFieldAlgebra
  isDomain_tensorProduct_of_isAlgClosed

set_option maxHeartbeats 400000 in
-- A finite budget supports the dependent tensor/fraction structures and their actual
-- scheme-action comparison. Kernel, strict synthesis-depth and lint checking stay enabled.
/-- The actual generic translate and its literal point specializations share the same
 rational affine coefficients. The genuine group consumer supplies its coordinate internally.
 The tensor-domain witnesses are derived internally and bound in the result. -/
theorem exists_generic_family_coefficients (G : AlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [IsAffine V.left]
    [ModObj G.toGroupScheme.X V] {t : V.left.functionField} (ht : Transcendental k t)
    (hpoint : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X, ∃ a b : k,
      (ActionFunctionField.functionFieldAction G V q).unop t =
        algebraMap k V.left.functionField a * t + algebraMap k V.left.functionField b)
    {A : Type u} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G.toGroupScheme.X) :
    let C := FractionRing A
    let F := V.left.functionField
    let E := FractionRing (C ⊗[k] F)
    let evC : A →ₐ[k] C := IsScalarTower.toAlgHom k A C
    let τ := sectionsTensorAut V ((algSpec (.of k)).map (CommAlgCat.ofHom evC).op ≫ g)
    let T := algebraMap (C ⊗[k] F) E (1 ⊗ₜ[k] t)
    ∃ d a b : A, d ≠ 0 ∧ a ≠ 0 ∧
      (∀ (φ : A →ₐ[k] k), φ d ≠ 0 →
        (ActionFunctionField.functionFieldAction G V ((unitIsoSpecAsOver k).hom ≫
          (algSpec (.of k)).map (CommAlgCat.ofHom φ).op ≫ g)).unop t =
            algebraMap k F (φ a / φ d) * t + algebraMap k F (φ b / φ d)) ∧
      ∃ hCF : IsDomain (C ⊗[k] F),
        letI := hCF
        ∃ hCR : IsDomain (C ⊗[k] Γ(V.left, ⊤)),
          letI := hCR
          ∃ (σ : E ≃ₐ[C] E) (e : E ≃ₐ[C] FractionRing (C ⊗[k] Γ(V.left, ⊤))),
            (∀ (c : C) (r : Γ(V.left, ⊤)),
              e (algebraMap (C ⊗[k] F) E
                (c ⊗ₜ[k] V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) r)) =
                  algebraMap (C ⊗[k] Γ(V.left, ⊤)) _ (c ⊗ₜ[k] r)) ∧
            (∀ x, e (σ x) = IsFractionRing.algEquivOfAlgEquiv τ (e x)) ∧
            σ T = algebraMap C E (evC a / evC d) * T + algebraMap C E (evC b / evC d) := by
  classical
  let R : Type u := Γ(V.left, ⊤)
  let F : Type u := V.left.functionField
  let C := FractionRing A
  let T0 := C ⊗[k] F
  let E := FractionRing T0
  let evC : A →ₐ[k] C := IsScalarTower.toAlgHom k A C
  let gGeneric := (algSpec (.of k)).map (CommAlgCat.ofHom evC).op ≫ g
  let τ := sectionsTensorAut V gGeneric
  let f : R →ₐ[k] F := (sectionsFunctionFieldEquiv V).toAlgHom.comp
    (IsScalarTower.toAlgHom k R (FractionRing R))
  let act (r : R) := Algebra.TensorProduct.map (AlgHom.id k A) f
    (sectionsTensorAut V g (1 ⊗ₜ[k] r))
  obtain ⟨r, s, hs, hrs, d, a, b, hd, ha, hclear, hformula⟩ :=
    exists_cleared_action_coefficients G V ht hpoint g
  obtain ⟨e, he⟩ := exists_tensorSections_functionFieldEquiv C V
  let σ : E ≃ₐ[C] E := e.trans ((IsFractionRing.algEquivOfAlgEquiv τ).trans e.symm)
  let jF : F →ₐ[k] E := (IsScalarTower.toAlgHom k T0 E).comp
    (Algebra.TensorProduct.includeRight : F →ₐ[k] T0)
  let m : A ⊗[k] F →ₐ[k] E := (IsScalarTower.toAlgHom k T0 E).comp
    (Algebra.TensorProduct.map evC (AlgHom.id k F))
  have hf (r : R) : f r =
      V.left.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩) r :=
    sectionsFunctionFieldEquiv_algebraMap V r
  have he' (c : C) (r : R) : e (algebraMap T0 E (c ⊗ₜ[k] f r)) =
      algebraMap (C ⊗[k] R) (FractionRing (C ⊗[k] R)) (c ⊗ₜ[k] r) := by
    rw [hf]
    exact he c r
  have hσ (x : E) : e (σ x) = IsFractionRing.algEquivOfAlgEquiv τ (e x) := by
    change e (e.symm (IsFractionRing.algEquivOfAlgEquiv τ (e x))) = _
    exact e.apply_symm_apply _
  have hcomp (z : A ⊗[k] R) :
      e (m (Algebra.TensorProduct.map (AlgHom.id k A) f z)) =
        algebraMap (C ⊗[k] R) (FractionRing (C ⊗[k] R))
          (Algebra.TensorProduct.map evC (AlgHom.id k R) z) := by
    induction z using TensorProduct.inductionOn with
    | tmul a r =>
      change e (algebraMap T0 E (Algebra.TensorProduct.map evC (AlgHom.id k F)
        (Algebra.TensorProduct.map (AlgHom.id k A) f (a ⊗ₜ[k] r)))) = _
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact he' (evC a) r
    | add x y hx hy => simp only [map_add, hx, hy]
  have hbase (r : R) : Algebra.TensorProduct.map evC (AlgHom.id k R)
      (sectionsTensorAut V g (1 ⊗ₜ[k] r)) = τ (1 ⊗ₜ[k] r) := by
    have hb := sectionsTensorAut_baseChange V evC g (1 ⊗ₜ[k] r)
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one] at hb
    change Algebra.TensorProduct.map evC (AlgHom.id k R)
      (sectionsTensorAut V g (1 ⊗ₜ[k] r)) = τ (1 ⊗ₜ[k] r) at hb
    exact hb
  have hσf (r : R) : σ (jF (f r)) = m (act r) := by
    apply e.injective
    change e (σ (algebraMap T0 E (1 ⊗ₜ[k] f r))) =
      e (m (Algebra.TensorProduct.map (AlgHom.id k A) f
        (sectionsTensorAut V g (1 ⊗ₜ[k] r))))
    rw [hσ, he', IsFractionRing.algEquivOfAlgEquiv_algebraMap, hcomp, hbase]
  have hscalar (c : A) (z : A ⊗[k] F) :
      m (c • z) = algebraMap C E (evC c) * m z := by
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    change m ((c ⊗ₜ[k] (1 : F)) * z) = _
    rw [map_mul]
    have hm : m (c ⊗ₜ[k] (1 : F)) = algebraMap C E (evC c) := by
      change algebraMap T0 E (evC c ⊗ₜ[k] (1 : F)) = _
      exact IsScalarTower.algebraMap_apply C T0 E (evC c)
    rw [hm]
  have hmt : m (1 ⊗ₜ[k] t) = jF t := by
    change algebraMap T0 E (evC 1 ⊗ₜ[k] t) = _
    rw [map_one]
    rfl
  have hh := congrArg m hclear
  rw [map_add, hscalar, hscalar, hscalar, map_mul, hmt, ← hσf, ← hσf] at hh
  change algebraMap C E (evC d) * σ (jF (f r)) =
    algebraMap C E (evC a) * (jF t * σ (jF (f s))) +
      algebraMap C E (evC b) * σ (jF (f s)) at hh
  have hrel : σ (jF (f r)) = σ (jF t) * σ (jF (f s)) := by
    rw [← hrs, map_mul, map_mul]
  rw [hrel] at hh
  have hsn : σ (jF (f s)) ≠ 0 := (map_ne_zero σ).2 ((map_ne_zero jF).2 hs)
  have hlin : σ (jF t) * algebraMap C E (evC d) =
      algebraMap C E (evC a) * jF t + algebraMap C E (evC b) := by
    apply mul_right_cancel₀ hsn
    calc
      _ = algebraMap C E (evC d) * (σ (jF t) * σ (jF (f s))) := by ring
      _ = _ := hh
      _ = _ := by ring
  have hevC : Function.Injective evC := IsFractionRing.injective A C
  have hdC : evC d ≠ 0 := by
    intro h
    apply hd
    apply hevC
    simpa only [map_zero] using h
  refine ⟨d, a, b, hd, ha, hformula, inferInstance,
    isDomain_tensor_sections C V, σ, e, he, hσ, ?_⟩
  change σ (jF t) = _
  rw [map_div₀, map_div₀, div_mul_eq_mul_div, ← add_div]
  exact (eq_div_iff ((map_ne_zero _).2 hdC)).2 hlin

end

end AclGeom.AffineCoefficients
