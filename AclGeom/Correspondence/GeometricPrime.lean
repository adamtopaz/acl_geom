/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import AclGeom.Correspondence.RegularACF
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Geometric primeness over an algebraically closed base

Blueprint Lemma `generic-extension` (a) uses that the coordinate ring of an irreducible
locus stays a domain after extending the coefficient field. The theorem below states this
in the affine ideal dictionary: every prime ideal in `k[X_i]` remains prime in `E[X_i]`
for any field extension `E/k` of an algebraically closed field `k`.

The quotient embeds after scalar extension into the tensor product of its fraction field
with `E`, which is a domain by `isDomain_tensorProduct_of_isAlgClosed`. Flatness preserves
that embedding. The tensor quotient and polynomial equivalences then identify the
extended prime ideal. The private domain helper is consumed by the public theorem.

The private validation consumer `GenericScalarPoint` starts from any tuple's vanishing
ideal and derives a scalar-extension point with the exact ideals over both fields. It
also derives independence over `E` when the original tuple is independent over `k`.
The general locus-relative transcendence-basis and ambient-automorphism formulations
remain separate obligations; the absolute cardinal equality in the original proof does
not by itself establish independence when the extension has infinite transcendence degree.
The original proof wording is retained, and the inference gap is reported on issue #5.

**Status:** prime polynomial ideals remain prime after arbitrary field scalar extension
of an algebraically closed base (#5, the coordinate-ring brick of `generic-extension` (a)).
-/

namespace AclGeom

open TensorProduct

noncomputable section

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

/-- Over an algebraically closed `k`, `E ⊗[k] A` is a domain for every domain `A`:
it embeds into `E ⊗[k] Frac A`. Consumed by the prime-ideal scalar-extension theorem. -/
private theorem domain_baseChange [IsAlgClosed k] (A : Type*) [CommRing A]
    [IsDomain A] [Algebra k A] : IsDomain (E ⊗[k] A) := by
  let F := FractionRing A
  have : IsDomain (E ⊗[k] F) := AclGeom.isDomain_tensorProduct_of_isAlgClosed
  let f : A →ₐ[k] F := IsScalarTower.toAlgHom k A F
  let g : E ⊗[k] A →ₐ[k] E ⊗[k] F :=
    Algebra.TensorProduct.map (AlgHom.id k E) f
  have hg : Function.Injective g :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := E) f.toLinearMap
      (IsFractionRing.injective A F)
  exact Function.Injective.isDomain g hg

/-- **Prime ideals remain prime after scalar extension over an algebraically closed base.**
This is the coordinate-ring scalar-extension brick of blueprint Lemma `generic-extension` (a).
The extension field and the variable type are arbitrary. -/
theorem isPrime_map_of_isAlgClosed [IsAlgClosed k] {ι : Type*}
    (I : Ideal (MvPolynomial ι k)) [I.IsPrime] :
    (I.map (MvPolynomial.map (algebraMap k E))).IsPrime := by
  have : IsDomain (E ⊗[k] (MvPolynomial ι k ⧸ I)) :=
    domain_baseChange (MvPolynomial ι k ⧸ I)
  let e := MvPolynomial.algebraTensorAlgEquiv k E (σ := ι)
  let J := I.map (Algebra.TensorProduct.includeRight (A := E) (R := k)).toRingHom
  have : IsDomain ((E ⊗[k] MvPolynomial ι k) ⧸ J) :=
    MulEquiv.isDomain _
      (Algebra.TensorProduct.tensorQuotientEquiv
        (R := k) E (MvPolynomial ι k) E I).symm.toMulEquiv
  have : J.IsPrime := (Ideal.Quotient.isDomain_iff_prime J).mp inferInstance
  have h : (J.map e.toRingHom).IsPrime := Ideal.map_isPrime_of_equiv e
  have he : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight (A := E) (R := k)).toRingHom =
      MvPolynomial.map (algebraMap k E) := by
    ext i <;> simp [e]
  change (I.map (Algebra.TensorProduct.includeRight (A := E) (R := k)).toRingHom
    |>.map e.toRingHom).IsPrime at h
  rw [Ideal.map_map, he] at h
  exact h

end

end AclGeom
