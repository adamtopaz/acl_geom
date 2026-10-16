/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.LocusQuotient
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Algebraic incomparability for tuple loci

For a tuple `t` in a field `Ω` over `k` and a subtuple `t ∘ g`, an element of `k[t]` algebraic over
`k(t ∘ g)` satisfies a polynomial relation over the variables of the subtuple with a coefficient
outside the locus of the subtuple (`exists_poly_of_mem_racl`). Consequently, when every coordinate
of `t` is algebraic over `k(t ∘ g)`, an ideal containing the locus of `t` with the same contraction
to the subtuple variables is the locus itself (`idealOf_eq_of_le_of_comap_eq`), by algebraic
incomparability (`Ideal.comap_lt_comap_of_root_mem_sdiff`). The ideal need not be prime.

These lemmas identify the components of the threefold incidence spectrum (`ThreefoldIncidence`)
and turn the locus-membership and rank form of genericity into the exact extended ideal
(`GenericPointExtension`).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5).
-/

open MvPolynomial
open scoped IntermediateField.algebraAdjoinAdjoin

namespace AclGeom

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- An element algebraic over the field of a subtuple satisfies a polynomial relation over the
subtuple's variables with a coefficient outside its locus. -/
theorem exists_poly_of_mem_racl {ι κ : Type*} (t : ι → Ω) (g : κ → ι) (f : MvPolynomial ι k)
    (hf : aeval t f ∈ racl k (Set.range (t ∘ g))) :
    ∃ p : Polynomial (MvPolynomial κ k), (∃ j, p.coeff j ∉ idealOf k (t ∘ g)) ∧
      p.eval₂ (rename g : MvPolynomial κ k →ₐ[k] MvPolynomial ι k).toRingHom f ∈
        idealOf k t := by
  obtain ⟨p, hp0, hpz⟩ : IsAlgebraic (Algebra.adjoin k (Set.range (t ∘ g))) (aeval t f) :=
    (IsFractionRing.isAlgebraic_iff (Algebra.adjoin k (Set.range (t ∘ g)))
      (IntermediateField.adjoin k (Set.range (t ∘ g))) Ω).2 ((mem_racl_iff k).1 hf)
  let ψ : MvPolynomial κ k →+* Algebra.adjoin k (Set.range (t ∘ g)) :=
    (locusCoordinateRingEquiv (k := k) (t ∘ g)).toRingEquiv.toRingHom.comp
      (Ideal.Quotient.mk (idealOf k (t ∘ g)))
  have hψ : Function.Surjective ψ :=
    (locusCoordinateRingEquiv (k := k) (t ∘ g)).surjective.comp Ideal.Quotient.mk_surjective
  have hcomp : (aeval t).toRingHom.comp
      (rename g : MvPolynomial κ k →ₐ[k] MvPolynomial ι k).toRingHom =
      (algebraMap (Algebra.adjoin k (Set.range (t ∘ g))) Ω).comp ψ :=
    RingHom.ext fun c ↦ (aeval_rename g t c).trans
      (congrArg Subtype.val (locusCoordinateRingEquiv_mk (k := k) (t ∘ g) c)).symm
  obtain ⟨P, hP⟩ := Polynomial.map_surjective ψ hψ p
  refine ⟨P, ?_, ?_⟩
  · obtain ⟨j, hj⟩ : ∃ j, p.coeff j ≠ 0 := ⟨p.natDegree, Polynomial.leadingCoeff_ne_zero.2 hp0⟩
    refine ⟨j, fun hmem ↦ hj ?_⟩
    rw [← hP, Polynomial.coeff_map]
    exact Subtype.ext ((congrArg Subtype.val (locusCoordinateRingEquiv_mk (k := k) (t ∘ g) _)).trans
      ((mem_idealOf_iff k).1 hmem))
  · rw [mem_idealOf_iff]
    change (aeval t).toRingHom (P.eval₂ (rename g).toRingHom f) = 0
    rw [Polynomial.hom_eval₂, hcomp, ← Polynomial.eval₂_map, hP, ← Polynomial.aeval_def]
    exact hpz

/-- Algebraic incomparability for tuple loci: an ideal containing the locus of a tuple algebraic
over a subtuple, with the same contraction to the subtuple variables, is the locus itself. -/
theorem idealOf_eq_of_le_of_comap_eq {ι κ : Type*} (t : ι → Ω) (g : κ → ι)
    (halg : ∀ i, t i ∈ racl k (Set.range (t ∘ g))) {J : Ideal (MvPolynomial ι k)}
    (hle : idealOf k t ≤ J)
    (hcomap : J.comap (rename g : MvPolynomial κ k →ₐ[k] MvPolynomial ι k) = idealOf k (t ∘ g)) :
    J = idealOf k t := by
  refine le_antisymm (fun f hf ↦ ?_) hle
  by_contra hft
  have hracl : aeval t f ∈ racl k (Set.range (t ∘ g)) := by
    have hle' : IntermediateField.adjoin k (Set.range t) ≤ racl k (Set.range (t ∘ g)) :=
      IntermediateField.adjoin_le_iff.2 (Set.range_subset_iff.2 halg)
    refine hle' (IntermediateField.algebra_adjoin_le_adjoin k _ ?_)
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact AlgHom.mem_range_self _ f
  obtain ⟨p, ⟨j, hj⟩, hp⟩ := exists_poly_of_mem_racl t g f hracl
  have hI : (idealOf k t).comap (rename g : MvPolynomial κ k →ₐ[k] MvPolynomial ι k).toRingHom =
      idealOf k (t ∘ g) := (idealOf_eq_comap_rename (k := k) rfl).symm
  have hne : p.map (Ideal.Quotient.mk ((idealOf k t).comap
      (rename g : MvPolynomial κ k →ₐ[k] MvPolynomial ι k).toRingHom)) ≠ 0 := by
    intro h
    apply hj
    rw [← hI]
    exact Ideal.Quotient.eq_zero_iff_mem.1
      (by rw [← Polynomial.coeff_map, h, Polynomial.coeff_zero])
  have hlt := Ideal.comap_lt_comap_of_root_mem_sdiff
    (f := (rename g : MvPolynomial κ k →ₐ[k] MvPolynomial ι k).toRingHom) hle ⟨hf, hft⟩ hne hp
  rw [hI] at hlt
  exact lt_irrefl _ (hlt.trans_eq hcomap)

end AclGeom
