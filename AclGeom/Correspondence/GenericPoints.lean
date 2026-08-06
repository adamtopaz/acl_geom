/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.FunctionField
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin

/-!
# Relocation of generic points

The embedding form of blueprint Lemma `generic-extension` (8.1(b)): inside an
algebraically closed ambient field, a finitely generated subextension can be
re-embedded over `k` with prescribed images for a transcendence basis. This
provides *independent generic points of a locus* — the engine of the
stabilizer argument in the curve-coset lemma — without any tensor-product
regularity.

* `adjoinTranscendentalAlgHom`: a purely transcendental subextension `k(t)`
  maps over `k` into the ambient field with prescribed algebraically
  independent images for `t`;
* `exists_extension_of_isAlgebraic`: a `k`-embedding of `E` into an
  algebraically closed ambient extends along any algebraic extension
  `E ≤ E'`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M3a, checklist C2).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

section Relocate

variable {ι : Type*} {t s : ι → Ω}

/-- Relocation of a purely transcendental subextension: the `k`-embedding of
`adjoin k (range t)` into `Ω` sending each `t i` to `s i`, for any two
algebraically independent families (blueprint Lemma 8.1(b), transcendental
part). -/
def adjoinTranscendentalAlgHom (ht : AlgebraicIndependent k t)
    (hs : AlgebraicIndependent k s) :
    ↥(adjoin k (Set.range t)) →ₐ[k] Ω :=
  ((adjoin k (Set.range s)).val.comp hs.aevalEquivField.toAlgHom).comp
    ht.aevalEquivField.symm.toAlgHom

theorem adjoinTranscendentalAlgHom_apply (ht : AlgebraicIndependent k t)
    (hs : AlgebraicIndependent k s) (i : ι) :
    adjoinTranscendentalAlgHom ht hs ⟨t i, subset_adjoin k _ ⟨i, rfl⟩⟩ = s i := by
  have h1 : ht.aevalEquivField (algebraMap (MvPolynomial ι k)
      (FractionRing (MvPolynomial ι k)) (MvPolynomial.X i)) =
      ⟨t i, subset_adjoin k _ ⟨i, rfl⟩⟩ := by
    refine Subtype.ext ?_
    rw [ht.aevalEquivField_algebraMap_apply_coe]
    simp
  have h2 : ht.aevalEquivField.symm ⟨t i, subset_adjoin k _ ⟨i, rfl⟩⟩ =
      algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k))
        (MvPolynomial.X i) := by
    rw [← h1, AlgEquiv.symm_apply_apply]
  have h3 : hs.aevalEquivField (algebraMap (MvPolynomial ι k)
      (FractionRing (MvPolynomial ι k)) (MvPolynomial.X i)) =
      ⟨s i, subset_adjoin k _ ⟨i, rfl⟩⟩ := by
    refine Subtype.ext ?_
    rw [hs.aevalEquivField_algebraMap_apply_coe]
    simp
  change (adjoin k (Set.range s)).val
    (hs.aevalEquivField (ht.aevalEquivField.symm
      ⟨t i, subset_adjoin k _ ⟨i, rfl⟩⟩)) = s i
  rw [h2, h3]
  rfl

end Relocate

section Extend

/-- A `k`-embedding of an intermediate field into an algebraically closed
ambient field extends along any algebraic extension of intermediate fields
(blueprint Lemma 8.1(b), algebraic part). -/
theorem exists_extension_of_isAlgebraic [IsAlgClosed Ω]
    {E E' : IntermediateField k Ω} (hEE' : E ≤ E')
    [halg : Algebra.IsAlgebraic ↥E ↥(extendScalars hEE')]
    (φ : ↥E →ₐ[k] Ω) :
    ∃ ψ : ↥E' →ₐ[k] Ω, ∀ x : ↥E, ψ ⟨x.1, hEE' x.2⟩ = φ x := by
  -- View `Ω` as an `E`-algebra through `φ` and lift; repackage by hand to
  -- avoid an `SMul` diamond with the canonical action.
  letI : Algebra ↥E Ω := φ.toAlgebra
  let ψE : ↥(extendScalars hEE') →ₐ[↥E] Ω := IsAlgClosed.lift
  have hcomm : ∀ y : ↥E, ψE (algebraMap ↥E ↥(extendScalars hEE') y) = φ y :=
    fun y ↦ ψE.commutes y
  refine ⟨{ toRingHom := ψE.toRingHom, commutes' := fun c ↦ ?_ }, fun x ↦ ?_⟩
  · have h1 : (algebraMap k ↥E' c : ↥E') =
        algebraMap ↥E ↥(extendScalars hEE') (algebraMap k ↥E c) := rfl
    change ψE (algebraMap k ↥E' c) = algebraMap k Ω c
    rw [h1, hcomm, φ.commutes]
  · have hx : (⟨x.1, hEE' x.2⟩ : ↥(extendScalars hEE')) =
        algebraMap ↥E ↥(extendScalars hEE') x := rfl
    change ψE ⟨x.1, hEE' x.2⟩ = φ x
    rw [hx, hcomm]

end Extend

end

end AclGeom
