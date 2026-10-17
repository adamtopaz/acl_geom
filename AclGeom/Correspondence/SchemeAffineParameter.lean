/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AffineChartDimension
import AclGeom.Correspondence.SchemeFiniteTypeSections

/-!
# An actual affine parameter chart with the required rank

Named consumer: the actual regular-affine curve genus theorem
`AclGeom.SchemeGenericTranslate.exists_constantExtension_genus_eq_zero`.

**Status:** proved for integral locally finite-type schemes over a field. The open chart,
finite-type section algebra and fraction-field rank bound are constructed internally.
-/

namespace AclGeom.SchemeGenericTranslate

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

variable {k : Type u} [Field k]

attribute [local instance] sectionsAlgebra

/-- Choose an actual affine parameter chart retaining the prescribed rank bound.
Named consumer: the actual group's effective coefficient-field genus argument. -/
theorem exists_affine_parameter (G : Over (Spec (.of k))) [IsIntegral G.left]
    [LocallyOfFiniteType G.hom] (n : ℕ)
    (hdim : (n : WithBot ℕ∞) ≤ topologicalKrullDim G.left) :
    ∃ (W : Over (Spec (.of k))) (hI : IsIntegral W.left) (hA : IsAffine W.left)
      (j : W ⟶ G) (_ : IsOpenImmersion j.left),
      letI := hI
      letI := hA
      letI := sectionsAlgebra W
      Algebra.FiniteType k Γ(W.left, ⊤) ∧
        (n : Cardinal) ≤ Algebra.trdeg k (FractionRing Γ(W.left, ⊤)) := by
  obtain ⟨U, hU, hne, hd⟩ := exists_isAffineOpen_dimension_ge G.left n hdim
  let W : Over (Spec (.of k)) := Over.mk (U.ι ≫ G.hom)
  have : Nonempty W.left := hne
  have : IsAffine W.left := hU
  have : IsIntegral W.left := isIntegral_of_isOpenImmersion U.ι
  have : LocallyOfFiniteType W.hom := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ G.hom))
  let j : W ⟶ G := Over.homMk U.ι rfl
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hft := finiteType_sections W
  refine ⟨W, inferInstance, inferInstance, j, inferInstance, hft, ?_⟩
  have := hft
  let A := Γ(W.left, ⊤)
  have he := IsHomeomorph.topologicalKrullDim_eq _ W.left.isoSpec.hom.homeomorph.isHomeomorph
  change topologicalKrullDim W.left = topologicalKrullDim (PrimeSpectrum A) at he
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at he
  obtain ⟨m, hm, ht⟩ := exists_ringKrullDim_trdeg_eq_of_finiteType k A (FractionRing A)
  have hnm : n ≤ m := by
    have h : (n : WithBot ℕ∞) ≤ m := hd.trans_eq (he.trans hm)
    exact_mod_cast h
  rw [ht]
  exact_mod_cast hnm

end

end AclGeom.SchemeGenericTranslate
