/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.FunctionField
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# The multiplier curve of the meet `F`

Raw field-theoretic inputs for the proposed linearity step of meet elimination in the corrected
blueprint Lemma `affine-grid-extraction` (#27).  In affine coordinates the meet `F` is a point
`f ∈ acl(a c, x)` outside `acl(a c)`; it is a point of the curve traced by `(a c, x)`.

* `idealOf_aeval_comp_eq_of_idealOf_eq`: equal vanishing ideals stay equal after applying the
  same polynomial map, the polynomial-image analogue of `idealOf_comp_eq_of_idealOf_eq`.
* `affine_multiplier_curve_of_joint_ideal`: a relocation with `p, y, δ, c, f` literally fixed
  and the same joint vanishing ideal (the output of `exists_affine_relocation`) keeps
  `(f, a' c, x')` on the same `k`-locus as `(f, a c, x)`.  The membership `f ∈ acl(a' c, x')`,
  the non-membership `f ∉ acl(a' c)` and the finite fibre `x' ∈ acl(a' c, f)` follow.
* `multiplier_projection_genericity`: for independent `A, B, M, X` and `f ∈ acl(M, X)` outside
  `acl(M)`, the fibre is finite, `M` is generic over `A, B, f`, and `f ∉ acl(A, B)`.

No component, curve action, stabilizer or linearity is assumed or proved.  The finite-component
and stabilizer argument, iterated fresh relocation, coordinate extraction and guarded completeness
remain open.

**Status:** polynomial-image and multiplier-curve/fibre prerequisites proved (#27, L2a).
Component/stabilizer linearity, iterated fresh relocation and guarded completeness remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open MvPolynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Polynomial images preserve equality of vanishing ideals**: if `a` and `b` have the same
vanishing ideal, so do their images under the same polynomial map `g`. -/
theorem idealOf_aeval_comp_eq_of_idealOf_eq {ι κ : Type*} {a b : ι → K}
    (h : idealOf k a = idealOf k b) (g : κ → MvPolynomial ι k) :
    idealOf k (fun j ↦ aeval a (g j)) = idealOf k (fun j ↦ aeval b (g j)) := by
  ext F
  rw [mem_idealOf_iff, mem_idealOf_iff]
  have ha : aeval (fun j ↦ aeval a (g j)) F = aeval a (bind₁ g F) := (aeval_bind₁ a g F).symm
  have hb : aeval (fun j ↦ aeval b (g j)) F = aeval b (bind₁ g F) := (aeval_bind₁ b g F).symm
  rw [ha, hb]
  constructor
  · intro hz
    have hm : bind₁ g F ∈ idealOf k a := (mem_idealOf_iff k).2 hz
    exact (mem_idealOf_iff k).1 (h ▸ hm)
  · intro hz
    have hm : bind₁ g F ∈ idealOf k b := (mem_idealOf_iff k).2 hz
    exact (mem_idealOf_iff k).1 (h.symm ▸ hm)

/-- **The multiplier curve is preserved by a literal relocation** (#27, proposed linearity
step).  If `(p, y, δ, c, f; a', b', x')` has the same vanishing ideal as `(p, y, δ, c, f; a, b, x)`
with `y = a x + b`, and `f ∈ acl(a c, x) \ acl(a c)`, then `(f, a' c, x')` has the same
vanishing ideal as `(f, a c, x)`, `f ∈ acl(a' c, x') \ acl(a' c)`, and `x' ∈ acl(a' c, f)`. -/
theorem affine_multiplier_curve_of_joint_ideal {a b x c p δ f a' b' x' : K}
    (hJ : idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a', b', x']) =
      idealOf k (Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x]))
    (hfm : f ∈ racl k ({a * c, x} : Set K)) (hfu : f ∉ racl k ({a * c} : Set K)) :
    idealOf k ![f, a' * c, x'] = idealOf k ![f, a * c, x] ∧
      f ∈ racl k ({a' * c, x'} : Set K) ∧ f ∉ racl k ({a' * c} : Set K) ∧
      x' ∈ racl k ({a' * c, f} : Set K) := by
  -- The polynomial map `(…, c, f; a, b, x) ↦ (f, a c, x)`.
  have hI := idealOf_aeval_comp_eq_of_idealOf_eq hJ
    (![X (Sum.inl 4), X (Sum.inr 0) * X (Sum.inl 3), X (Sum.inr 2)] :
      Fin 3 → MvPolynomial (Fin 5 ⊕ Fin 3) k)
  have hnew : (fun j ↦ aeval (Sum.elim ![p, a * x + b, δ, c, f] ![a', b', x'])
      ((![X (Sum.inl 4), X (Sum.inr 0) * X (Sum.inl 3), X (Sum.inr 2)] :
        Fin 3 → MvPolynomial (Fin 5 ⊕ Fin 3) k) j)) = ![f, a' * c, x'] := by
    funext j
    fin_cases j <;> simp
  have hold : (fun j ↦ aeval (Sum.elim ![p, a * x + b, δ, c, f] ![a, b, x])
      ((![X (Sum.inl 4), X (Sum.inr 0) * X (Sum.inl 3), X (Sum.inr 2)] :
        Fin 3 → MvPolynomial (Fin 5 ⊕ Fin 3) k) j)) = ![f, a * c, x] := by
    funext j
    fin_cases j <;> simp
  rw [hnew, hold] at hI
  -- Transfer along the vanishing ideal of the three-coordinate tuple.
  have hm' : f ∈ racl k ({a' * c, x'} : Set K) := by
    have h : (![f, a * c, x] : Fin 3 → K) 0 ∈
        racl k ((![f, a * c, x] : Fin 3 → K) '' {1, 2}) := by
      simpa [Set.image_insert_eq] using hfm
    have h' := mem_racl_image_of_idealOf_eq k hI.symm h
    simpa [Set.image_insert_eq] using h'
  have hu' : f ∉ racl k ({a' * c} : Set K) := by
    have h : (![f, a * c, x] : Fin 3 → K) 0 ∉ racl k ((![f, a * c, x] : Fin 3 → K) '' {1}) := by
      simpa using hfu
    have h' := notMem_racl_image_of_idealOf_eq k hI.symm h
    simpa using h'
  -- The finite fibre, by exchange.
  have hx' : x' ∈ racl k ({a' * c, f} : Set K) := by
    have h : f ∈ racl k (insert x' ({a' * c} : Set K)) := by
      rwa [Set.pair_comm] at hm'
    have h' := racl_exchange h hu'
    rwa [Set.pair_comm] at h'
  exact ⟨hI, hm', hu', hx'⟩

/-- **Multiplier-projection genericity** (#27, proposed linearity step).  Let `A, B, M, X` be
independent and `f ∈ acl(M, X) \ acl(M)`.  Then `X ∈ acl(M, f)` (the fibre over `M` is finite),
`M ∉ acl(A, B, f)` (the projection to `M` is generic over `A, B, f`), and `f ∉ acl(A, B)`. -/
theorem multiplier_projection_genericity {A B M X f : K}
    (hind : AlgebraicIndependent k ![A, B, M, X])
    (hf : f ∈ racl k ({M, X} : Set K)) (hfM : f ∉ racl k ({M} : Set K)) :
    X ∈ racl k ({M, f} : Set K) ∧ M ∉ racl k ({A, B, f} : Set K) ∧
      f ∉ racl k ({A, B} : Set K) := by
  -- Independence facts.
  have hX3 : X ∉ racl k ({A, B, M} : Set K) := by
    have h := AlgebraicIndependent.notMem_racl_image hind (S := {0, 1, 2}) (i := 3) (by decide)
    simpa [Set.image_insert_eq] using h
  have hX2 : X ∉ racl k ({A, M} : Set K) := by
    have h := AlgebraicIndependent.notMem_racl_image hind (S := {0, 2}) (i := 3) (by decide)
    simpa [Set.image_insert_eq] using h
  have hM2 : M ∉ racl k ({A, B} : Set K) := by
    have h := AlgebraicIndependent.notMem_racl_image hind (S := {0, 1}) (i := 2) (by decide)
    simpa [Set.image_insert_eq] using h
  -- `acl(A, B, M) ∩ acl(M, X) = acl(M)`, in two exchange steps.
  have key : f ∈ racl k ({A, B, M} : Set K) → f ∈ racl k ({M} : Set K) := by
    intro h
    have hsub1 : ({A, B, M} : Set K) ⊆ racl k (insert B ({A, M} : Set K)) :=
      Set.insert_subset_iff.2 ⟨subset_racl k _ (by simp), Set.insert_subset_iff.2
        ⟨subset_racl k _ (by simp), Set.singleton_subset_iff.2 (subset_racl k _ (by simp))⟩⟩
    have hsub2 : ({M, X} : Set K) ⊆ racl k (insert X ({A, M} : Set K)) :=
      Set.insert_subset_iff.2 ⟨subset_racl k _ (by simp),
        Set.singleton_subset_iff.2 (subset_racl k _ (by simp))⟩
    have hsub3 : insert B ({A, M} : Set K) ⊆ racl k ({A, B, M} : Set K) :=
      Set.insert_subset_iff.2 ⟨subset_racl k _ (by simp), Set.insert_subset_iff.2
        ⟨subset_racl k _ (by simp), Set.singleton_subset_iff.2 (subset_racl k _ (by simp))⟩⟩
    have hAM : f ∈ racl k ({A, M} : Set K) :=
      mem_racl_of_mem_racl_insert (racl_le_of_subset_racl hsub1 h)
        (racl_le_of_subset_racl hsub2 hf) fun hx ↦ hX3 (racl_le_of_subset_racl hsub3 hx)
    have hsub4 : ({M, X} : Set K) ⊆ racl k (insert X ({M} : Set K)) :=
      Set.insert_subset_iff.2 ⟨subset_racl k _ (by simp),
        Set.singleton_subset_iff.2 (subset_racl k _ (by simp))⟩
    exact mem_racl_of_mem_racl_insert hAM (racl_le_of_subset_racl hsub4 hf) hX2
  -- The finite fibre, by exchange.
  have hXf : X ∈ racl k ({M, f} : Set K) := by
    have h : f ∈ racl k (insert X ({M} : Set K)) := by
      rwa [Set.pair_comm] at hf
    have h' := racl_exchange h hfM
    rwa [Set.pair_comm] at h'
  refine ⟨hXf, fun hM ↦ ?_, fun hfAB ↦ hfM (key (racl_mono ?_ hfAB))⟩
  · -- `M ∈ acl(A, B, f)` and `M ∉ acl(A, B)` would put `f` in `acl(A, B, M)`.
    have hsub5 : ({A, B, f} : Set K) ⊆ racl k (insert f ({A, B} : Set K)) :=
      Set.insert_subset_iff.2 ⟨subset_racl k _ (by simp), Set.insert_subset_iff.2
        ⟨subset_racl k _ (by simp), Set.singleton_subset_iff.2 (subset_racl k _ (by simp))⟩⟩
    have hfABM := racl_exchange (racl_le_of_subset_racl hsub5 hM) hM2
    have hsub6 : insert M ({A, B} : Set K) ⊆ racl k ({A, B, M} : Set K) :=
      Set.insert_subset_iff.2 ⟨subset_racl k _ (by simp), Set.insert_subset_iff.2
        ⟨subset_racl k _ (by simp), Set.singleton_subset_iff.2 (subset_racl k _ (by simp))⟩⟩
    exact hfM (key (racl_le_of_subset_racl hsub6 hfABM))
  · exact Set.insert_subset_insert (Set.singleton_subset_iff.2 (by simp))

end

end AclGeom
