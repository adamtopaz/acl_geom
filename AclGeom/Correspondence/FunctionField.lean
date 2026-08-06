/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Closure.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Loci of tuples and generic points

The ideal-theoretic dictionary underlying the hard kernel (blueprint §8):
for a tuple `a` of elements of an extension `Ω/k`,

* `idealOf k a`: the vanishing ideal `I(a/k)` — the kernel of evaluation at
  `a` on the polynomial ring, a prime ideal since evaluation lands in a
  field (blueprint §8, first paragraph);
* `mem_idealOf_iff`: the membership dictionary;
* `idealOf_eq_bot_iff`: `I(a/k) = ⊥` iff `a` is algebraically independent —
  "generic of the affine space";
* equivariance of `idealOf` under `k`-embeddings of the ambient field, the
  seed of blueprint Lemma `generic-extension` (b).

The locus `Loc_k(a)` of the blueprint is this prime ideal; its "dimension"
is `trdeg k k(a)`, and all statements about generic points of loci are
statements about the tuples themselves. Finite correspondences and their
composition build on this in later slices of checklist C2.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M3a, checklist C2).
-/

namespace AclGeom

open MvPolynomial

noncomputable section

variable (k : Type*) {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

variable {n : ℕ}

/-- The vanishing ideal `I(a/k)` of a tuple (blueprint §8): polynomials over
`k` vanishing at `a`. Prime, because evaluation maps into a field. -/
def idealOf (a : Fin n → Ω) : Ideal (MvPolynomial (Fin n) k) :=
  RingHom.ker (aeval a).toRingHom

theorem mem_idealOf_iff {a : Fin n → Ω} {f : MvPolynomial (Fin n) k} :
    f ∈ idealOf k a ↔ aeval a f = 0 :=
  RingHom.mem_ker

instance idealOf_isPrime (a : Fin n → Ω) : (idealOf k a).IsPrime :=
  RingHom.ker_isPrime _

/-- The locus of `a` is all of affine space exactly when `a` is
algebraically independent over `k`. -/
theorem idealOf_eq_bot_iff {a : Fin n → Ω} :
    idealOf k a = ⊥ ↔ AlgebraicIndependent k a := by
  rw [AlgebraicIndependent, idealOf, ← RingHom.injective_iff_ker_eq_bot]
  exact Iff.rfl

/-- Equivariance: a `k`-algebra embedding of ambient fields preserves
vanishing ideals (the seed of blueprint Lemma `generic-extension`). -/
theorem idealOf_comp_algHom {Ω' : Type*} [Field Ω'] [Algebra k Ω']
    (σ : Ω →ₐ[k] Ω') (a : Fin n → Ω) :
    idealOf k (⇑σ ∘ a) = idealOf k a := by
  ext f
  rw [mem_idealOf_iff, mem_idealOf_iff]
  have hcomp : aeval (⇑σ ∘ a) f = σ (aeval a f) := by
    rw [Function.comp_def, ← comp_aeval_apply]
  rw [hcomp]
  exact ⟨fun h ↦ σ.injective (by rwa [map_zero]), fun h ↦ by rw [h, map_zero]⟩

/-- Two tuples with the same vanishing ideal have the same algebraic
relations; in particular the vanishing ideal detects equality of evaluated
polynomials. -/
theorem aeval_eq_aeval_of_idealOf_eq {a b : Fin n → Ω}
    (h : idealOf k a = idealOf k b) {f g : MvPolynomial (Fin n) k}
    (hfg : aeval a f = aeval a g) : aeval b f = aeval b g := by
  have : f - g ∈ idealOf k a := by
    rw [mem_idealOf_iff, map_sub, sub_eq_zero]
    exact hfg
  rw [h, mem_idealOf_iff, map_sub, sub_eq_zero] at this
  exact this

end

end AclGeom
