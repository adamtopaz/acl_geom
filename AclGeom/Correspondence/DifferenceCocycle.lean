/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Closure.Basic

/-!
# The difference cocycle of two affine presentations

The first algebraic step of meet elimination in the corrected blueprint Lemma
`affine-grid-extraction` (#27).  Let `a, b, x` be independent.  Let `p ∈ acl(a, b)` and
`δ ∈ acl(a, x)` lie outside `acl(a)`; in the configuration these are the incidences
`P ≤ A`, `P ≠ S`, `D ≤ S ∨ X` and `D ≠ S`.  Suppose a second presentation
`a' x' + b' = a x + b` of the same value, with `a'` fresh over `a, b, x`, keeps
`p ∈ acl(a', b')` and `δ ∈ acl(a', x')`.  Then the translation difference `b - b'` is
algebraic over `a, a'` alone (`sub_mem_racl_of_affine_value_eq`).

The proof is exchange in each presentation followed by the independent-variable
intersection `acl(a, a', p) ∩ acl(a, a', δ) = acl(a, a')` (blueprint eq. 8.9a).  The
hypotheses are explicit data.  In the intended consumer the second presentation is a
relocation of the first that fixes `p`, the common value and `δ`; that relocation and the
linearity argument that uses this cocycle are not part of this module.

**Status:** difference-cocycle data lemma proved (#27, L1a). Fixed-five relocation with a
supplied fresh parameter is proved separately in `AffineRelocation` (#27, L1b). Linearity
and guarded extraction/completeness remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Exchange in a pair: if `w ∈ acl(a, b)` but `w ∉ acl(a)`, then `b ∈ acl(a, w)`. -/
private theorem mem_racl_pair_of_mem_racl_pair {a b w : K} (hw : w ∈ racl k ({a, b} : Set K))
    (hwa : w ∉ racl k ({a} : Set K)) : b ∈ racl k ({a, w} : Set K) := by
  have h : w ∈ racl k (insert b ({a} : Set K)) := by
    rwa [Set.pair_comm] at hw
  have h' := racl_exchange h hwa
  rwa [Set.pair_comm] at h'

/-- A transcendental element of `acl(S)` is not algebraic over an element `a'` that is
transcendental over `S`. -/
private theorem notMem_racl_singleton_of_notMem {S : Set K} {w a' : K}
    (hwS : w ∈ racl k S) (hw0 : w ∉ racl k (∅ : Set K)) (ha' : a' ∉ racl k S) :
    w ∉ racl k ({a'} : Set K) := by
  intro h
  have h' : a' ∈ racl k (insert w (∅ : Set K)) :=
    racl_exchange (by simpa using h) hw0
  have hsub : (insert w (∅ : Set K)) ⊆ racl k S :=
    Set.insert_subset_iff.2 ⟨hwS, Set.empty_subset _⟩
  exact ha' (racl_le_of_subset_racl hsub h')

/-- **The difference cocycle** (corrected blueprint Lemma `affine-grid-extraction`, first
meet elimination, #27).  Two presentations `a' x' + b' = a x + b` of one value share the
points `p ∈ acl(a, b) \ acl(a)` and `δ ∈ acl(a, x) \ acl(a)`, and `a'` is fresh over
`a, b, x`.  Then the translation difference `b - b'` is algebraic over `a, a'`. -/
theorem sub_mem_racl_of_affine_value_eq {a b x a' b' x' p δ : K}
    (hind : AlgebraicIndependent k ![a, b, x]) (ha' : a' ∉ racl k ({a, b, x} : Set K))
    (hp : p ∈ racl k ({a, b} : Set K)) (hpa : p ∉ racl k ({a} : Set K))
    (hδ : δ ∈ racl k ({a, x} : Set K)) (hδa : δ ∉ racl k ({a} : Set K))
    (hp' : p ∈ racl k ({a', b'} : Set K)) (hδ' : δ ∈ racl k ({a', x'} : Set K))
    (hy : a' * x' + b' = a * x + b) :
    b - b' ∈ racl k ({a, a'} : Set K) := by
  -- The shared points lie in `acl(a, b, x)` and are transcendental.
  have hpabx : p ∈ racl k ({a, b, x} : Set K) :=
    racl_mono (Set.insert_subset_insert (Set.singleton_subset_iff.2 (by simp))) hp
  have hδabx : δ ∈ racl k ({a, b, x} : Set K) :=
    racl_mono (Set.insert_subset_insert (Set.singleton_subset_iff.2 (by simp))) hδ
  have hp0 : p ∉ racl k (∅ : Set K) := fun h ↦ hpa (racl_mono (Set.empty_subset _) h)
  have hδ0 : δ ∉ racl k (∅ : Set K) := fun h ↦ hδa (racl_mono (Set.empty_subset _) h)
  -- Exchange in both presentations.
  have hb : b ∈ racl k ({a, p} : Set K) := mem_racl_pair_of_mem_racl_pair hp hpa
  have hx : x ∈ racl k ({a, δ} : Set K) := mem_racl_pair_of_mem_racl_pair hδ hδa
  have hb' : b' ∈ racl k ({a', p} : Set K) :=
    mem_racl_pair_of_mem_racl_pair hp' (notMem_racl_singleton_of_notMem hpabx hp0 ha')
  have hx' : x' ∈ racl k ({a', δ} : Set K) :=
    mem_racl_pair_of_mem_racl_pair hδ' (notMem_racl_singleton_of_notMem hδabx hδ0 ha')
  -- The difference is algebraic over `a, a', p`.
  have hP : b - b' ∈ racl k (insert p ({a, a'} : Set K)) := by
    have h1 : ({a, p} : Set K) ⊆ insert p ({a, a'} : Set K) :=
      Set.insert_subset_iff.2 ⟨by simp, Set.singleton_subset_iff.2 (by simp)⟩
    have h2 : ({a', p} : Set K) ⊆ insert p ({a, a'} : Set K) :=
      Set.insert_subset_iff.2 ⟨by simp, Set.singleton_subset_iff.2 (by simp)⟩
    exact sub_mem (racl_mono h1 hb) (racl_mono h2 hb')
  -- The difference is algebraic over `a, a', δ`, since `b - b' = a' x' - a x`.
  have hD : b - b' ∈ racl k (insert δ ({a, a'} : Set K)) := by
    have hw : b - b' = a' * x' - a * x :=
      sub_eq_sub_iff_add_eq_add.2 (by rw [hy, add_comm])
    have h1 : ({a, δ} : Set K) ⊆ insert δ ({a, a'} : Set K) :=
      Set.insert_subset_iff.2 ⟨by simp, Set.singleton_subset_iff.2 (by simp)⟩
    have h2 : ({a', δ} : Set K) ⊆ insert δ ({a, a'} : Set K) :=
      Set.insert_subset_iff.2 ⟨by simp, Set.singleton_subset_iff.2 (by simp)⟩
    have ha : a ∈ racl k (insert δ ({a, a'} : Set K)) := subset_racl k _ (by simp)
    have ha₂ : a' ∈ racl k (insert δ ({a, a'} : Set K)) := subset_racl k _ (by simp)
    rw [hw]
    exact sub_mem (mul_mem ha₂ (racl_mono h2 hx')) (mul_mem ha (racl_mono h1 hx))
  -- `δ` is not algebraic over `p, a, a'`: otherwise `x ∈ acl(a, b, a')`, and exchange puts
  -- `a'` in `acl(a, b, x)`.
  have hδP : δ ∉ racl k (insert p ({a, a'} : Set K)) := by
    intro h
    have hle : racl k (insert p ({a, a'} : Set K)) ≤ racl k (insert a' ({a, b} : Set K)) := by
      have hsub : insert p ({a, a'} : Set K) ⊆ racl k (insert a' ({a, b} : Set K)) :=
        Set.insert_subset_iff.2 ⟨racl_mono (Set.subset_insert _ _) hp,
          Set.insert_subset_iff.2 ⟨subset_racl k _ (by simp),
            Set.singleton_subset_iff.2 (subset_racl k _ (by simp))⟩⟩
      exact racl_le_of_subset_racl hsub
    have hsub : ({a, δ} : Set K) ⊆ racl k (insert a' ({a, b} : Set K)) :=
      Set.insert_subset_iff.2 ⟨subset_racl k _ (by simp), Set.singleton_subset_iff.2 (hle h)⟩
    have hxab' : x ∈ racl k (insert a' ({a, b} : Set K)) := racl_le_of_subset_racl hsub hx
    have hxab : x ∉ racl k ({a, b} : Set K) := by
      have h' := AlgebraicIndependent.notMem_racl_image hind (S := {0, 1}) (i := 2) (by decide)
      simpa [Set.image_insert_eq] using h'
    have ha'x := racl_exchange hxab' hxab
    apply ha'
    rwa [Set.insert_comm x a, Set.pair_comm x b] at ha'x
  exact mem_racl_of_mem_racl_insert hP hD hδP

end

end AclGeom
