/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.MultiplicativeGroupScheme

/-!
# Actual automorphisms of the multiplicative group

**Status:** proved over every field, in every characteristic (#21). An actual group-scheme
isomorphism of the multiplicative group with itself is identity or inversion. Mathlib's
classification of group-algebra bialgebra maps gives the exponent internally; invertibility
forces that exponent to be one or minus one. Hopf-Spec full faithfulness transfers this
classification to the actual scheme morphism. Named consumer:
`MultiplicativeRigidity.normal_multiplicativeGroup_conj`, the torus alternative in the proof
of blueprint Lemma 8.4. No exponent or coordinate-map certificate is a caller premise.
-/

namespace AclGeom.MultiplicativeRigidity
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u

/-- An actual Hopf-algebra automorphism of the multiplicative coordinate algebra is the
 identity or exponent negation. Mathlib classifies group-algebra bialgebra maps internally;
 the inverse forces the exponent to be a unit of the integers. Named consumer:
 `groupIso_eq_id_or_inv`. -/
theorem hopfIso_eq_id_or_neg (k : Type u) [Field k]
    (e : CommHopfAlgCat.of k (AddMonoidAlgebra k ℤ) ≅
      CommHopfAlgCat.of k (AddMonoidAlgebra k ℤ)) :
    e.hom.hom = BialgHom.id k (AddMonoidAlgebra k ℤ) ∨
      e.hom.hom = AddMonoidAlgebra.mapDomainBialgHom k (-AddMonoidHom.id ℤ) := by
  let f := AddMonoidAlgebra.mapDomainOfBialgHom e.hom.hom
  let g := AddMonoidAlgebra.mapDomainOfBialgHom e.inv.hom
  have hf (z : ℤ) : f z = z * f 1 := by
    simpa only [zsmul_eq_mul, mul_one, Int.cast_id] using (map_zsmul f z (1 : ℤ))
  have hg (z : ℤ) : g z = z * g 1 := by
    simpa only [zsmul_eq_mul, mul_one, Int.cast_id] using (map_zsmul g z (1 : ℤ))
  have hcomp : g.comp f = AddMonoidHom.id ℤ := by
    dsimp only [f, g]
    rw [← AddMonoidAlgebra.mapDomainOfBialgHom_comp]
    have h : e.inv.hom.comp e.hom.hom = BialgHom.id k (AddMonoidAlgebra k ℤ) :=
      congrArg CommHopfAlgCat.Hom.hom e.hom_inv_id
    rw [h, AddMonoidAlgebra.mapDomainOfBialgHom_id]
  have hmul : f 1 * g 1 = 1 := by
    rw [← hg]
    exact congrArg (fun h : ℤ →+ ℤ ↦ h 1) hcomp
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hmul with h | h
  · left
    apply (AddMonoidAlgebra.mapDomainBialgHomEquiv (R := k) (G := ℤ) (H := ℤ)).symm.injective
    change f = AddMonoidAlgebra.mapDomainOfBialgHom (BialgHom.id k _)
    rw [AddMonoidAlgebra.mapDomainOfBialgHom_id]
    apply AddMonoidHom.ext
    intro z
    rw [hf, h.1, mul_one]
    rfl
  · right
    apply (AddMonoidAlgebra.mapDomainBialgHomEquiv (R := k) (G := ℤ) (H := ℤ)).symm.injective
    change f = AddMonoidAlgebra.mapDomainOfBialgHom
      (AddMonoidAlgebra.mapDomainBialgHom k (-AddMonoidHom.id ℤ))
    rw [AddMonoidAlgebra.mapDomainOfBialgHom_mapDomainBialgHom]
    apply AddMonoidHom.ext
    intro z
    rw [hf, h.1, mul_neg_one]
    rfl
end
end AclGeom.MultiplicativeRigidity

namespace AclGeom.MultiplicativeRigidity
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.GrpObj CategoryTheory.MonObj
universe u

/-- Every actual group-scheme automorphism of the multiplicative group over a field is
 identity or inversion, in every characteristic. Hopf-Spec full faithfulness supplies the
 coordinate automorphism internally. Named consumer: `normal_multiplicativeGroup_conj`. -/
theorem groupIso_eq_id_or_inv (k : Type u) [Field k]
    (e : (multiplicativeGroup k).toGroupScheme ≅ (multiplicativeGroup k).toGroupScheme) :
    e.hom.hom.hom = 𝟙 _ ∨ e.hom.hom.hom = ι[(multiplicativeGroup k).toGroupScheme.X] := by
  let A : CommHopfAlgCat.{u} k := .of k (AddMonoidAlgebra k ℤ)
  let F : (CommHopfAlgCat.{u} k)ᵒᵖ ⥤ Grp (Over (Spec (.of k))) := hopfSpec (.of k)
  have : F.Full := hopfSpec.instFull
  have : F.Faithful := hopfSpec.instFaithful
  let E : A ≅ A := (F.preimageIso (X := .op A) (Y := .op A) e).unop
  have he : F.map E.hom.op = e.hom := F.map_preimage (X := .op A) (Y := .op A) e.hom
  rcases hopfIso_eq_id_or_neg k E with h | h
  · left
    have hE : E.hom = 𝟙 A := CommHopfAlgCat.hom_ext h
    rw [hE, op_id, F.map_id] at he
    exact congrArg (fun f ↦ f.hom.hom) he.symm
  · right
    apply Over.OverMorphism.ext
    rw [← he]
    change Spec.map (CommRingCat.ofHom E.hom.hom.toAlgHom.toRingHom) =
      Spec.map (CommRingCat.ofHom
        (HopfAlgebra.antipodeAlgHom k (AddMonoidAlgebra k ℤ)).toRingHom)
    rw [h]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply congrArg AlgHom.toRingHom
    ext n : 1
    · change (AddMonoidAlgebra.mapDomainBialgHom k (-AddMonoidHom.id ℤ))
        (AddMonoidAlgebra.single n (1 : k)) =
          HopfAlgebra.antipode k (AddMonoidAlgebra.single n (1 : k))
      rw [AddMonoidAlgebra.mapDomainBialgHom_single]
      simp only [AddMonoidHom.neg_apply, AddMonoidHom.id_apply,
        AddMonoidAlgebra.antipode_single, HopfAlgebra.antipode_one]
    · ext
end
end AclGeom.MultiplicativeRigidity
