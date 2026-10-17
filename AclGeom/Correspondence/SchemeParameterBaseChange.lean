/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import AclGeom.Correspondence.ParameterActionNaturality
import AclGeom.Correspondence.SchemeParameterAction

/-!
# Base change of an actual tensor-coordinate action

The coordinate action commutes with evaluating the parameter algebra. The parameter map is
Mathlib's `algSpec` map, so the comparison retains the actual scheme action.
Named consumer: the finite coefficient-field producer and its actual point-map faithfulness.

**Status:** proved; the actual finite-coefficient consumer is `ParameterCoefficients`.
-/

namespace AclGeom.SchemeParameterAction

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct

universe u

variable {k : Type u} [Field k]
  {A B R : Type u} [CommRing A] [CommRing B] [CommRing R]
  [Algebra k A] [Algebra k B] [Algebra k R]

private theorem spec_map_tensorMap (φ : A →ₐ[k] B) :
    Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ (AlgHom.id k R)).toRingHom) ≫
      (pullbackSpecIso k A R).inv =
    (pullbackSpecIso k B R).inv ≫
      (((algSpec (.of k)).map (CommAlgCat.ofHom φ).op) ⊗ₘ
        𝟙 ((Spec (.of R)).asOver (Spec (.of k)))).left := by
  have h := prodComparison_natural (algSpec (.of k)) (CommAlgCat.ofHom φ).op
    (𝟙 (op (CommAlgCat.of k R)))
  rw [(algSpec (.of k)).map_id] at h
  have h' := congrArg (fun f :
      (algSpec (.of k)).obj (op (CommAlgCat.of k (B ⊗[k] R))) ⟶
        (Spec (.of A)).asOver (Spec (.of k)) ⊗
          (Spec (.of R)).asOver (Spec (.of k)) ↦ f.left) h
  exact h'

variable {G : Over (Spec (.of k))} [GrpObj G]
  [ModObj G ((Spec (.of R)).asOver (Spec (.of k)))]

/-- Evaluation of the parameter algebra commutes with its actual coordinate action.
Named consumer: finite coaction coefficients and their point-map faithfulness. -/
theorem tensorAut_baseChange (φ : A →ₐ[k] B)
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G) (x : A ⊗[k] R) :
    let f : (Spec (.of B)).asOver (Spec (.of k)) ⟶
        (Spec (.of A)).asOver (Spec (.of k)) :=
      (algSpec (.of k)).map (CommAlgCat.ofHom φ).op
    Algebra.TensorProduct.map φ (AlgHom.id k R) (tensorAut g x) =
      tensorAut (f ≫ g) (Algebra.TensorProduct.map φ (AlgHom.id k R) x) := by
  let f : (Spec (.of B)).asOver (Spec (.of k)) ⟶
      (Spec (.of A)).asOver (Spec (.of k)) :=
    (algSpec (.of k)).map (CommAlgCat.ofHom φ).op
  let t := Algebra.TensorProduct.map φ (AlgHom.id k R)
  let q := Spec.map (CommRingCat.ofHom t.toRingHom)
  let iA := pullbackSpecIso k A R
  let iB := pullbackSpecIso k B R
  let a : Limits.pullback (Spec.algebraMap k B) (Spec.algebraMap k R) ⟶
      Limits.pullback (Spec.algebraMap k A) (Spec.algebraMap k R) :=
    (f ⊗ₘ 𝟙 ((Spec (.of R)).asOver (Spec (.of k)))).left
  let pA : Limits.pullback (Spec.algebraMap k A) (Spec.algebraMap k R) ⟶
      Limits.pullback (Spec.algebraMap k A) (Spec.algebraMap k R) :=
    (ModObj.parameterAct ((Spec (.of R)).asOver (Spec (.of k))) g).left
  let pB : Limits.pullback (Spec.algebraMap k B) (Spec.algebraMap k R) ⟶
      Limits.pullback (Spec.algebraMap k B) (Spec.algebraMap k R) :=
    (ModObj.parameterAct ((Spec (.of R)).asOver (Spec (.of k))) (f ≫ g)).left
  have hn := congrArg (fun m :
      (Spec (.of B)).asOver (Spec (.of k)) ⊗ (Spec (.of R)).asOver (Spec (.of k)) ⟶
        (Spec (.of A)).asOver (Spec (.of k)) ⊗ (Spec (.of R)).asOver (Spec (.of k)) ↦
      m.left) (ModObj.parameterAct_natural ((Spec (.of R)).asOver (Spec (.of k))) f g)
  change a ≫ pA = pB ≫ a at hn
  have hq := spec_map_tensorMap (R := R) φ
  change q ≫ iA.inv = iB.inv ≫ a at hq
  have hq' : q = iB.inv ≫ a ≫ iA.hom := by
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun m ↦ m ≫ iA.hom) hq
  have hs : CommRingCat.ofHom (tensorAut (R := R) g).toRingHom ≫
        CommRingCat.ofHom t.toRingHom =
      CommRingCat.ofHom t.toRingHom ≫
        CommRingCat.ofHom (tensorAut (R := R) (f ≫ g)).toRingHom := by
    apply Spec.map_injective
    simp only [Spec.map_comp]
    change q ≫ Spec.map (CommRingCat.ofHom (tensorAut (R := R) g).toRingHom) =
      Spec.map (CommRingCat.ofHom (tensorAut (R := R) (f ≫ g)).toRingHom) ≫ q
    rw [spec_map_tensorAut, spec_map_tensorAut]
    change q ≫ iA.inv ≫ pA ≫ iA.hom = iB.inv ≫ pB ≫ iB.hom ≫ q
    rw [hq']
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    simpa only [Category.assoc] using congrArg (fun m ↦ iB.inv ≫ m ≫ iA.hom) hn
  exact congrArg (fun m : CommRingCat.of (A ⊗[k] R) ⟶ CommRingCat.of (B ⊗[k] R) ↦
    m.hom x) hs

end

end AclGeom.SchemeParameterAction
