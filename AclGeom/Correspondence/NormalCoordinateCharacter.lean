/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AffineConjugation

/-!
# The regular conjugation character in a finite normal coordinate

**Status:** a surjective affine-group morphism and an actual factorization of a genuine
normal subgroup through translations give a surjective regular character to Gm. The
actual conjugation lift is chosen internally from Mathlib normality. Its joint diagram
and scalar formula over every coefficient algebra hold after the supplied beta:N to Ga.
Beta is never inverted or cancelled as a monomorphism. Named consumer:
`RegularAffineModel.exists_model` constructs f and beta internally from the source action.
-/

namespace AclGeom.NormalCoordinateConjugation
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The actual normal conjugation lift has a regular, surjective multiplier character
in the finite Ga coordinate. No inverse or monomorphism of β is used.
Named consumer: the coupled regular-affine curve model. -/
theorem exists_character
    (G N : AlgebraicGroup k) (i : N.Hom G) [IsMonHom.Normal i.hom.hom]
    (f : G.Hom (AffineGroupScheme.algebraicGroup k)) [Surjective f.hom.hom.left]
    (β : N.Hom (AdditiveGroupScheme.algebraicGroup k 1))
    (hfactor : β.hom.hom ≫ AdditiveTranslation.inclusion k = i.hom.hom ≫ f.hom.hom) :
    ∃ χ : G.Hom (multiplicativeGroup k), Surjective χ.hom.hom.left ∧
      χ.hom.hom = f.hom.hom ≫ AffineDilation.projection k ∧
      ∃ ψ : G.toGroupScheme.X ⊗ N.toGroupScheme.X ⟶ N.toGroupScheme.X,
        ψ ≫ i.hom.hom = G.toGroupScheme.X ◁ i.hom.hom ≫ conj G.toGroupScheme.X ∧
        ψ ≫ β.hom.hom = lift
          (fst G.toGroupScheme.X N.toGroupScheme.X ≫ χ.hom.hom)
          (snd G.toGroupScheme.X N.toGroupScheme.X ≫ β.hom.hom) ≫
            AdditiveRigidity.scalarMul k ∧
        ∀ (C : Type u) [CommRing C] [Algebra k C]
          (q : (Spec (.of C)).asOver (Spec (.of k)) ⟶ G.toGroupScheme.X)
          (n : (Spec (.of C)).asOver (Spec (.of k)) ⟶ N.toGroupScheme.X)
          (a : Cˣ) (b : C),
          q ≫ χ.hom.hom = AdditiveRigidity.unitPoint k a →
          n ≫ β.hom.hom = AffineSchemeAction.linePoint k b →
          (lift q n ≫ ψ) ≫ β.hom.hom =
            AffineSchemeAction.linePoint k ((a : C) * b) := by
  let χ : G.Hom (multiplicativeGroup k) := f ≫ AffineDilation.character k
  have hχ : χ.hom.hom = f.hom.hom ≫ AffineDilation.projection k := rfl
  have hχsurj : Surjective χ.hom.hom.left := by
    rw [hχ]
    have : Surjective (AffineDilation.projection k).left :=
      AffineDilation.projection_surjective k
    change Surjective (f.hom.hom.left ≫ (AffineDilation.projection k).left)
    infer_instance
  obtain ⟨ψ, hψ⟩ := IsMonHom.Normal.exists_comp_eq_conj (φ := i.hom.hom)
  have hψ' : ψ ≫ i.hom.hom = G.toGroupScheme.X ◁ i.hom.hom ≫
      conj G.toGroupScheme.X := hψ
  have hdiagram : ψ ≫ β.hom.hom = lift
      (fst G.toGroupScheme.X N.toGroupScheme.X ≫ χ.hom.hom)
      (snd G.toGroupScheme.X N.toGroupScheme.X ≫ β.hom.hom) ≫
        AdditiveRigidity.scalarMul k := by
    apply (cancel_mono (AdditiveTranslation.inclusion k)).mp
    calc
      _ = (f.hom.hom ⊗ₘ β.hom.hom) ≫
          (AffineGroupScheme.algebraicGroup k).toGroupScheme.X ◁
            AdditiveTranslation.inclusion k ≫
            conj (AffineGroupScheme.algebraicGroup k).toGroupScheme.X :=
        factor_conjugation i.hom.hom (AdditiveTranslation.inclusion k)
          f.hom.hom β.hom.hom ψ hfactor hψ'
      _ = _ := by
        rw [AffineDilation.standard_conjugation]
        simp only [Category.assoc, comp_lift_assoc, tensorHom_fst_assoc,
          tensorHom_snd, hχ]
  refine ⟨χ, hχsurj, hχ, ψ, hψ', hdiagram, ?_⟩
  intro C _ _ q n a b hqa hnb
  rw [Category.assoc, hdiagram, comp_lift_assoc, lift_fst_assoc, lift_snd_assoc,
    hqa, hnb, AdditiveRigidity.unitPoint_linePoint_scalarMul]

end
end AclGeom.NormalCoordinateConjugation
