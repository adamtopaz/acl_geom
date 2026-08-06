/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.GenericPoints
import AclGeom.Correspondence.CurveIdeal

/-!
# Descent of translation invariance along the locus

Step 4d of the fused curve-coset chain: the exact translation identity
`F(X + δ₁, Y + δ₂) = F` at the *generic* point `δ` of the translation locus
descends to every point of the locus. The identity is equivalent to the
vanishing at `δ` of the finitely many universal coefficient polynomials of
`F(X + U, Y + V) − F(X, Y)`; genericity places them in the vanishing ideal
of `δ`, so they vanish at any point whose ideal contains it.

* `aevalSnd`: evaluation of the second variable block at constants;
* `coeffUV`: the universal coefficient polynomials, via `toUVPoly`;
* `translate_eq_of_idealOf_le`: the descent theorem.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M3a, checklist C6/C7).
-/

namespace AclGeom

open MvPolynomial

noncomputable section

variable {k : Type*} [Field k]

section BlockEval

variable {K : Type*} [Field K] [Algebra k K]

/-- Evaluation of the second variable block at constants: `X (inl j) ↦ X j`,
`X (inr j) ↦ C (c j)`. -/
def aevalSnd (c : Fin 2 → K) :
    MvPolynomial (Fin 2 ⊕ Fin 2) k →ₐ[k] MvPolynomial (Fin 2) K :=
  aeval (Sum.elim (fun j ↦ X j) fun j ↦ C (c j))

/-- The universal coefficient view: the second block becomes the coefficient
ring. -/
def toUVPoly :
    MvPolynomial (Fin 2 ⊕ Fin 2) k →ₐ[k]
      MvPolynomial (Fin 2) (MvPolynomial (Fin 2) k) :=
  aeval (Sum.elim (fun j ↦ X j) fun j ↦ C (X j))

/-- `aevalSnd` factors through the universal coefficient view. -/
theorem aevalSnd_eq_map_toUVPoly (c : Fin 2 → K)
    (g : MvPolynomial (Fin 2 ⊕ Fin 2) k) :
    aevalSnd (k := k) c g =
      MvPolynomial.map ((aeval c : MvPolynomial (Fin 2) k →ₐ[k] K) :
        MvPolynomial (Fin 2) k →+* K) (toUVPoly (k := k) g) := by
  have hcomp : (aevalSnd (k := k) c).toRingHom =
      ((MvPolynomial.map ((aeval c : MvPolynomial (Fin 2) k →ₐ[k] K) :
        MvPolynomial (Fin 2) k →+* K)).comp (toUVPoly (k := k)).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · simp [aevalSnd, toUVPoly, MvPolynomial.algebraMap_eq]
    · rcases i with j | j
      · simp [aevalSnd, toUVPoly]
      · simp [aevalSnd, toUVPoly]
  exact congrArg (fun (f : MvPolynomial (Fin 2 ⊕ Fin 2) k →+* _) ↦ f g) hcomp

/-- The coefficient bridge: coefficients of a block evaluation are the
evaluations of the universal coefficient polynomials. -/
theorem coeff_aevalSnd (c : Fin 2 → K) (g : MvPolynomial (Fin 2 ⊕ Fin 2) k)
    (m : Fin 2 →₀ ℕ) :
    coeff m (aevalSnd (k := k) c g) =
      aeval c (coeff m (toUVPoly (k := k) g)) := by
  rw [aevalSnd_eq_map_toUVPoly, MvPolynomial.coeff_map]
  rfl

/-- Block evaluation of the sum substitution is the translation of the
extended polynomial. -/
theorem aevalSnd_addSubst (c : Fin 2 → K) (F : MvPolynomial (Fin 2) k) :
    aevalSnd (k := k) c (addSubst (k := k) F) =
      translate c (MvPolynomial.map (algebraMap k K) F) := by
  have hcomp : ((aevalSnd (k := k) c).toRingHom.comp
      (addSubst (k := k)).toRingHom) =
      ((translate c).toRingHom.comp
        (MvPolynomial.map (algebraMap k K) :
          MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) K)) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_)
    · simp [aevalSnd, addSubst, translate, MvPolynomial.algebraMap_eq]
    · simp [aevalSnd, addSubst, translate]
  exact congrArg (fun (f : MvPolynomial (Fin 2) k →+* _) ↦ f F) hcomp

/-- Block evaluation of the first-block inclusion is coefficient
extension. -/
theorem aevalSnd_rename_inl (c : Fin 2 → K) (F : MvPolynomial (Fin 2) k) :
    aevalSnd (k := k) c (rename Sum.inl F) =
      MvPolynomial.map (algebraMap k K) F := by
  have hcomp : ((aevalSnd (k := k) c).toRingHom.comp
      (rename (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2)).toRingHom) =
      (MvPolynomial.map (algebraMap k K) :
        MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) K) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_)
    · simp [aevalSnd, MvPolynomial.algebraMap_eq]
    · simp [aevalSnd]
  exact congrArg (fun (f : MvPolynomial (Fin 2) k →+* _) ↦ f F) hcomp

end BlockEval

/-- **Descent of translation invariance** (step 4d): if translation by `c`
fixes the extended generator and the vanishing ideal of `c` is contained in
that of `w`, then translation by `w` fixes the extended generator as well.
Applied with `c` the generic point of the translation locus, this transports
the exact translation identity to every point of the locus. -/
theorem translate_eq_of_idealOf_le
    {K L : Type*} [Field K] [Field L] [Algebra k K] [Algebra k L]
    {c : Fin 2 → K} {F : MvPolynomial (Fin 2) k}
    (hid : translate c (MvPolynomial.map (algebraMap k K) F) =
      MvPolynomial.map (algebraMap k K) F)
    {w : Fin 2 → L} (hle : idealOf k c ≤ idealOf k w) :
    translate w (MvPolynomial.map (algebraMap k L) F) =
      MvPolynomial.map (algebraMap k L) F := by
  classical
  set D := addSubst (k := k) F - rename Sum.inl F with hD
  have hDc : aevalSnd (k := k) c D = 0 := by
    rw [hD, map_sub, aevalSnd_addSubst, aevalSnd_rename_inl, hid, sub_self]
  have hQ : ∀ m : Fin 2 →₀ ℕ,
      coeff m (toUVPoly (k := k) D) ∈ idealOf k c := by
    intro m
    rw [mem_idealOf_iff]
    have h := congrArg (fun g ↦ coeff m g) hDc
    simp only [coeff_zero] at h
    rw [coeff_aevalSnd] at h
    exact h
  have hDw : aevalSnd (k := k) w D = 0 := by
    ext m
    rw [coeff_aevalSnd, coeff_zero]
    exact (mem_idealOf_iff k).1 (hle (hQ m))
  rw [hD, map_sub, aevalSnd_addSubst, aevalSnd_rename_inl, sub_eq_zero] at hDw
  exact hDw

end

end AclGeom
