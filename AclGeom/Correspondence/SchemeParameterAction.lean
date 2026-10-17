/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import AclGeom.Correspondence.ParameterAction
import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# The coordinate automorphism of a parameter-dependent scheme action

An actual `Spec A`-point of a group scheme acting on `Spec R` gives an `A`-algebra automorphism
of `A ⊗[k] R`, by pullback along the parameter-preserving action automorphism.
Named consumer: the generic translate in the source curve-action genus argument.

**Status:** proved; the actual generic-action consumer is in `SchemeGenericTranslate`.
The source classification remains open.
-/

namespace AclGeom.SchemeParameterAction

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]
  {A R : Type u} [CommRing A] [CommRing R] [Algebra k A] [Algebra k R]
  [ModObj G ((Spec (.of R)).asOver (Spec (.of k)))]

private def tensorSchemeAut
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G) :
    Aut (Spec (.of (A ⊗[k] R))) :=
  (pullbackSpecIso k A R).symm ≪≫
    (Over.forget (Spec (.of k))).mapIso
      (ModObj.parameterAut ((Spec (.of R)).asOver (Spec (.of k))) g) ≪≫
    pullbackSpecIso k A R

private theorem tensorSchemeAut_hom_base
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G) :
    (tensorSchemeAut (R := R) g).hom ≫ Spec.algebraMap A (A ⊗[k] R) =
      Spec.algebraMap A (A ⊗[k] R) := by
  let a : Limits.pullback (Spec.algebraMap k A) (Spec.algebraMap k R) ⟶
      Limits.pullback (Spec.algebraMap k A) (Spec.algebraMap k R) :=
    (ModObj.parameterAct ((Spec (.of R)).asOver (Spec (.of k))) g).left
  have hfst : a ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ :=
    congrArg (fun f :
      (Spec (.of A)).asOver (Spec (.of k)) ⊗ (Spec (.of R)).asOver (Spec (.of k)) ⟶
        (Spec (.of A)).asOver (Spec (.of k)) ↦ f.left)
          (ModObj.parameterAct_fst ((Spec (.of R)).asOver (Spec (.of k))) g)
  change (pullbackSpecIso k A R).inv ≫ a ≫
    (pullbackSpecIso k A R).hom ≫ Spec.algebraMap A (A ⊗[k] R) = _
  rw [pullbackSpecIso_hom_fst', hfst, pullbackSpecIso_inv_fst']

/-- Pullback of the actual parameter action on the tensor coordinate ring.
Named consumer: the actual generic-translate automorphism in the curve-action genus proof. -/
def tensorAut (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G) :
    (A ⊗[k] R) ≃ₐ[A] (A ⊗[k] R) := by
  let e := tensorSchemeAut (R := R) g
  let r : CommRingCat.of (A ⊗[k] R) ≅ CommRingCat.of (A ⊗[k] R) :=
    { hom := Spec.preimage e.hom
      inv := Spec.preimage e.inv
      hom_inv_id := by rw [← Spec.preimage_comp, e.inv_hom_id, Spec.preimage_id]
      inv_hom_id := by rw [← Spec.preimage_comp, e.hom_inv_id, Spec.preimage_id] }
  apply AlgEquiv.ofRingEquiv (f := r.commRingCatIsoToRingEquiv)
  intro a
  have h : CommRingCat.ofHom (algebraMap A (A ⊗[k] R)) ≫ r.hom =
      CommRingCat.ofHom (algebraMap A (A ⊗[k] R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change Spec.map (Spec.preimage e.hom) ≫ Spec.algebraMap A (A ⊗[k] R) = _
    rw [Spec.map_preimage]
    exact tensorSchemeAut_hom_base g
  exact congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of (A ⊗[k] R) ↦ f.hom a) h

/-- The coordinate automorphism is the literal pullback of the parameter-preserving scheme
map. Named consumer: comparison with the actual generic action and its coefficients. -/
theorem spec_map_tensorAut (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G) :
    Spec.map (CommRingCat.ofHom (tensorAut (R := R) g).toRingHom) =
      (pullbackSpecIso k A R).inv ≫
        (ModObj.parameterAct ((Spec (.of R)).asOver (Spec (.of k))) g).left ≫
          (pullbackSpecIso k A R).hom := by
  change Spec.map (Spec.preimage (tensorSchemeAut (R := R) g).hom) = _
  exact Spec.map_preimage _

/-- Inverting the parameter inverts the coordinate automorphism. Named consumer: descent of
both generic action directions to their common coefficient field. -/
theorem tensorAut_inv (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G) :
    tensorAut (R := R) g⁻¹ = (tensorAut (R := R) g).symm := by
  ext x
  rfl

end

end AclGeom.SchemeParameterAction
