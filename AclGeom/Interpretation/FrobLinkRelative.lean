/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Interpretation.FrobLinkRigidity
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-!
# The direct Frobenius link over a relative base

`frobenius_of_concurrent_lines` needs an algebraically closed base inside an algebraically closed
ambient field. This module removes both hypotheses by lifting the algebraic endpoint rather than the
geometry.

* Concurrency, rank and the parameter equality are proved over `K/k` itself, without any closure
  assumption (`FrobLinkIncidence`, `FrobLinkSemantic`).
* So only element-level closure facts have to move. They go along an embedding `ι : K →ₐ[k] Ω`
  into an algebraically closed `Ω`, over the base `K₀ = algebraicClosure k Ω`. The transfer
  composes `algHom_mem_racl_image_iff` (ambient invariance) with `mem_racl_base_iff_of_algebraic`
  (base insensitivity), as in blueprint §9.1, opening line.
* Independence moves by `AlgebraicIndependent.map'` and `extendScalars`.
* The Frobenius conclusion comes back by injectivity of `ι`.

No geometric lift (`liftPoint`, `Q'Geom.lift`), atom clause or extraction hypothesis is used.

**Status:** the relative-field incidence-rigidity lift is proved (#23).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open ClosedIF IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Incidence rigidity along an embedding.** The hypotheses of `frobenius_of_concurrent_lines`
over an arbitrary base `k` inside `K` transfer along `ι : K →ₐ[k] Ω` to the algebraically closed
base `algebraicClosure k Ω` of an algebraically closed `Ω`; the conclusion comes back along `ι`. -/
theorem frobenius_of_concurrent_lines_of_algHom {Ω : Type*} [Field Ω] [Algebra k Ω]
    [IsAlgClosed Ω] (ι : K →ₐ[k] Ω) (q : ℕ) [ExpChar k q] {x y a a' p : K}
    (hind : AlgebraicIndependent k ![x, y, a])
    (ha'a : a' ∈ racl k ({a} : Set K)) (haa' : a ∈ racl k ({a'} : Set K))
    (hp0 : p ∉ racl k (∅ : Set K))
    (hL1 : p ∈ racl k ({x, y} : Set K)) (hL2 : p ∈ racl k ({a * x, a' * y} : Set K))
    (hL3 : p ∈ racl k ({(1 + a) * x, (1 + a') * y} : Set K)) :
    ∃ s : ℕ, a' = a ^ q ^ s ∨ a = a' ^ q ^ s := by
  set K₀ := algebraicClosure k Ω
  have : IsAlgClosed ↥K₀ := IsAlgClosure.isAlgClosed k
  have : ExpChar (↥K₀) q := expChar_of_injective_algebraMap (algebraMap k K₀).injective q
  have halg : ∀ z ∈ K₀, IsAlgebraic k z := fun z hz ↦ mem_algebraicClosure_iff.1 hz
  have key : ∀ {S : Set K} {z : K}, ι z ∈ racl (↥K₀) (⇑ι '' S) ↔ z ∈ racl k S :=
    (mem_racl_base_iff_of_algebraic halg).trans (algHom_mem_racl_image_iff ι)
  have hinj : Function.Injective ι := ι.toRingHom.injective
  have hind' : AlgebraicIndependent (↥K₀) ![ι x, ι y, ι a] := by
    have h := AlgebraicIndependent.extendScalars (↥K₀) (hind.map' hinj)
    convert h using 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨s, hs⟩ := frobenius_of_concurrent_lines q hind'
    (by simpa using key.2 ha'a) (by simpa using key.2 haa')
    (by simpa using (not_congr key).2 hp0)
    (by simpa [Set.image_pair] using key.2 hL1) (by simpa [Set.image_pair] using key.2 hL2)
    (by simpa [Set.image_pair] using key.2 hL3)
  refine ⟨s, hs.imp (fun h ↦ hinj ?_) (fun h ↦ hinj ?_)⟩ <;> simpa using h

/-- **Incidence rigidity over any base** (`frobenius_of_concurrent_lines` without the closure
hypotheses), through the algebraic closure of `K`. -/
theorem frobenius_of_concurrent_lines_rel (q : ℕ) [ExpChar k q] {x y a a' p : K}
    (hind : AlgebraicIndependent k ![x, y, a])
    (ha'a : a' ∈ racl k ({a} : Set K)) (haa' : a ∈ racl k ({a'} : Set K))
    (hp0 : p ∉ racl k (∅ : Set K))
    (hL1 : p ∈ racl k ({x, y} : Set K)) (hL2 : p ∈ racl k ({a * x, a' * y} : Set K))
    (hL3 : p ∈ racl k ({(1 + a) * x, (1 + a') * y} : Set K)) :
    ∃ s : ℕ, a' = a ^ q ^ s ∨ a = a' ^ q ^ s :=
  frobenius_of_concurrent_lines_of_algHom (IsScalarTower.toAlgHom k K (AlgebraicClosure K)) q
    hind ha'a haa' hp0 hL1 hL2 hL3

end AclGeom
