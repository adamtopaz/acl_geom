/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.Moebius
import AclGeom.Curves.Rational

/-!
# Automorphisms of genus-zero function fields

Once `F = k(t)`, every `k`-automorphism sends `t` to another generator.
The two generators have degree one over one another, so the existing
bidegree-`(1,1)` correspondence theorem makes the new generator a
fractional-linear expression in `t`.  Transcendence forces the
coefficient determinant to be nonzero.

This is the genus-zero Möbius checkpoint in blueprint Lemma 8.4.

**Status:** in progress (M4b, issue #13, P7).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- A fractional-linear relation with transcendental output has
nonzero determinant. -/
theorem moebius_det_ne_zero_of_transcendental {z w : F}
    (hw : Transcendental k w) {a b c d : k}
    (hden : algebraMap k F c * z + algebraMap k F d ≠ 0)
    (hrel : w * (algebraMap k F c * z + algebraMap k F d) =
      algebraMap k F a * z + algebraMap k F b) :
    a * d - b * c ≠ 0 := by
  intro hdet
  rcases eq_or_ne c 0 with hc | hc
  · have hd : d ≠ 0 := by
      intro hd
      apply hden
      rw [hc, hd, map_zero, zero_mul, add_zero]
    have ha : a = 0 := by
      rw [hc, mul_zero, sub_zero] at hdet
      exact (mul_eq_zero.1 hdet).resolve_right hd
    have hmapd : algebraMap k F d ≠ 0 := (map_ne_zero _).2 hd
    have hwconst : w = algebraMap k F (b / d) := by
      apply mul_right_cancel₀ hmapd
      calc
        w * algebraMap k F d = algebraMap k F b := by
          simpa [hc, ha] using hrel
        _ = algebraMap k F (b / d) * algebraMap k F d := by
          rw [← map_mul, div_mul_cancel₀ b hd]
    apply hw
    rw [hwconst]
    exact isAlgebraic_algebraMap _
  · have hb : b = a * d / c := by
      apply (eq_div_iff hc).2
      linear_combination -hdet
    have hmapc : algebraMap k F c ≠ 0 := (map_ne_zero _).2 hc
    have hnum : algebraMap k F a * z + algebraMap k F b =
        algebraMap k F (a / c) *
          (algebraMap k F c * z + algebraMap k F d) := by
      rw [hb, map_div₀, map_div₀, map_mul]
      field_simp
    have hwconst : w = algebraMap k F (a / c) := by
      apply mul_right_cancel₀ hden
      calc
        w * (algebraMap k F c * z + algebraMap k F d) =
            algebraMap k F a * z + algebraMap k F b := hrel
        _ = algebraMap k F (a / c) *
            (algebraMap k F c * z + algebraMap k F d) := hnum
    apply hw
    rw [hwconst]
    exact isAlgebraic_algebraMap _

/-- An algebra automorphism carries a field generator to another
field generator. -/
theorem adjoin_image_eq_top_of_adjoin_eq_top {t : F}
    (htop : adjoin k ({t} : Set F) = ⊤) (σ : F ≃ₐ[k] F) :
    adjoin k ({σ t} : Set F) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := σ.surjective x
  have hy : y ∈ adjoin k ({t} : Set F) := by
    rw [htop]
    trivial
  have hmap : σ y ∈ (adjoin k ({t} : Set F)).map σ.toAlgHom :=
    (IntermediateField.mem_map _).2 ⟨y, hy, rfl⟩
  rw [IntermediateField.adjoin_map, Set.image_singleton] at hmap
  exact hmap

/-- Algebra automorphisms preserve transcendence over the base. -/
theorem transcendental_map_algEquiv {t : F} (ht : Transcendental k t)
    (σ : F ≃ₐ[k] F) : Transcendental k (σ t) := by
  intro halg
  apply ht
  obtain ⟨p, hp0, hp⟩ := halg
  refine ⟨p, hp0, ?_⟩
  apply σ.injective
  rw [map_zero]
  have hcomp : σ.toRingEquiv.toRingHom.comp (algebraMap k F) =
      algebraMap k F := by
    ext c
    exact σ.commutes c
  calc
    σ (Polynomial.aeval t p) = Polynomial.aeval (σ t) p := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def]
      calc
        σ (Polynomial.eval₂ (algebraMap k F) t p) =
            Polynomial.eval₂
              (σ.toRingEquiv.toRingHom.comp (algebraMap k F))
              (σ t) p :=
          Polynomial.hom_eval₂ p (algebraMap k F)
            σ.toRingEquiv.toRingHom t
        _ = Polynomial.eval₂ (algebraMap k F) (σ t) p := by
          rw [hcomp]
    _ = 0 := hp

/-- **Automorphisms of a rational function field are Möbius**: relative
to a generator `t`, the image of `t` under every `k`-automorphism is a
fractional-linear expression with nonzero determinant. -/
theorem exists_moebius_of_generator_algEquiv {t : F}
    (htr : Transcendental k t)
    (htop : adjoin k ({t} : Set F) = ⊤) (σ : F ≃ₐ[k] F) :
    ∃ a b c d : k,
      a * d - b * c ≠ 0 ∧
      algebraMap k F c * t + algebraMap k F d ≠ 0 ∧
      σ t * (algebraMap k F c * t + algebraMap k F d) =
        algebraMap k F a * t + algebraMap k F b := by
  have hσtr := transcendental_map_algEquiv htr σ
  have hσtop := adjoin_image_eq_top_of_adjoin_eq_top htop σ
  have hσt_z : σ t ∈ racl k ({t} : Set F) := by
    rw [mem_racl_iff]
    have : σ t ∈ adjoin k ({t} : Set F) := by
      rw [htop]
      trivial
    have heq : algebraMap ↥(adjoin k ({t} : Set F)) F
        (⟨σ t, this⟩ : ↥(adjoin k ({t} : Set F))) = σ t :=
      IntermediateField.algebraMap_apply (adjoin k ({t} : Set F))
        (⟨σ t, this⟩ : ↥(adjoin k ({t} : Set F)))
    rw [← heq]
    exact isAlgebraic_algebraMap _
  have ht_σz : t ∈ racl k ({σ t} : Set F) := by
    rw [mem_racl_iff]
    have : t ∈ adjoin k ({σ t} : Set F) := by
      rw [hσtop]
      trivial
    have heq : algebraMap ↥(adjoin k ({σ t} : Set F)) F
        (⟨t, this⟩ : ↥(adjoin k ({σ t} : Set F))) = t :=
      IntermediateField.algebraMap_apply (adjoin k ({σ t} : Set F))
        (⟨t, this⟩ : ↥(adjoin k ({σ t} : Set F)))
    rw [← heq]
    exact isAlgebraic_algebraMap _
  have hdeg1 :
      (minpoly ↥(adjoin k ({t} : Set F)) (σ t)).natDegree = 1 := by
    rw [minpoly.natDegree_eq_one_iff]
    exact ⟨⟨σ t, by rw [htop]; trivial⟩, rfl⟩
  have hdeg2 :
      (minpoly ↥(adjoin k ({σ t} : Set F)) t).natDegree = 1 := by
    rw [minpoly.natDegree_eq_one_iff]
    exact ⟨⟨t, by rw [hσtop]; trivial⟩, rfl⟩
  obtain ⟨a, b, c, d, hden, hrel⟩ :=
    exists_moebius_of_minpoly_natDegree_one
      (notMem_racl_empty_of_transcendental htr)
      (notMem_racl_empty_of_transcendental hσtr)
      hσt_z ht_σz hdeg1 hdeg2
  exact ⟨a, b, c, d,
    moebius_det_ne_zero_of_transcendental hσtr hden hrel,
    hden, hrel⟩

/-- **Genus-zero Möbius classification**: a genus-zero one-variable
function field admits a generator in which every base-field
automorphism is fractional linear. -/
theorem exists_generator_moebius_of_genus_eq_zero
    [IsAlgClosed k] [IsFunctionFieldOneVar k F]
    (hgenus : genus k F = 0) :
    ∃ t : F, Transcendental k t ∧
      adjoin k ({t} : Set F) = ⊤ ∧
      ∀ σ : F ≃ₐ[k] F, ∃ a b c d : k,
        a * d - b * c ≠ 0 ∧
        algebraMap k F c * t + algebraMap k F d ≠ 0 ∧
        σ t * (algebraMap k F c * t + algebraMap k F d) =
          algebraMap k F a * t + algebraMap k F b := by
  obtain ⟨t, htr, htop⟩ :=
    genus_eq_zero_iff_exists_generator.1 hgenus
  exact ⟨t, htr, htop, fun σ ↦
    exists_moebius_of_generator_algEquiv htr htop σ⟩

end

end AclGeom
