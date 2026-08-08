/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.Quadrangle
import AclGeom.Correspondence.CurveIdeal
import AclGeom.Correspondence.Binomial

/-!
# The atom clause: no rank-one parameter captures a generic line

Clause (iv) of Ψ at the soundness witness: for every atom `A' ≤ A`, the
generic point `X` is not below `A' ∨ Y` — concretely, for `t ∈ racl{u, v}`
transcendental, the generic direction `w` is not algebraic over
`{t, uw + v}`.

The blueprint proves this by the minimal-parameter derivation calculation;
this file follows the elementary *specialization route* instead (design
note on the project tracker): exchange converts the hypothesis into
`uw + v ∈ racl_{K₀}{w}` over the closed base `K₀ = racl{t}`; a nonzero
two-variable relation `G` over `K₀` then vanishes identically under the
substitution `X₁ ↦ uT + v` because `w` is transcendental over
`racl{u, v}`; specializing `T` at two base points `ξ₁ ≠ ξ₂` of `k` where
the `Y`-collapse of `G` stays nonzero puts `uξᵢ + v` into `racl{t}`, and
differencing recovers `u` and `v` there — contradicting the independence
of the coefficients, since `t` is interalgebraic with a rank-one closure.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4, checklist G3 soundness, clause (iv)).
-/

namespace AclGeom

noncomputable section

open IntermediateField

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

section LineClause

/-- Elements outside a relative algebraic closure are transcendental over
it as a base field. -/
theorem transcendental_racl_of_notMem {S : Set K} {z : K}
    (h : z ∉ racl k S) : Transcendental ↥(racl k S) z := by
  intro halg
  exact h (IsRAC.mem_of_isAlgebraic (isRAC_racl S) halg)

variable {u v w t : K}

/-- Exchange reduction for the atom clause: if the generic direction `w`
were algebraic over the atom parameter and the line value, the line value
would be algebraic over `{w, t}`. -/
theorem line_mem_of_mem (hw : w ∉ racl k ({u, v} : Set K))
    (ht : t ∈ racl k ({u, v} : Set K))
    (hmem : w ∈ racl k ({t, u * w + v} : Set K)) :
    u * w + v ∈ racl k ({w, t} : Set K) := by
  have hwt : w ∉ racl k ({t} : Set K) := fun h ↦
    hw (racl_le_of_subset_racl (Set.singleton_subset_iff.2 ht) h)
  have hmem' : w ∈ racl k (insert (u * w + v) ({t} : Set K)) := by
    rwa [Set.pair_comm t (u * w + v)] at hmem
  exact racl_exchange hmem' hwt

/-- The line value is algebraic over the direction alone, once the atom
closure is promoted to the base field. -/
theorem line_mem_over_base (h : u * w + v ∈ racl k ({w, t} : Set K)) :
    u * w + v ∈ racl ↥(racl k ({t} : Set K)) ({w} : Set K) := by
  have h1 : u * w + v ∈ racl ↥(racl k ({t} : Set K)) ({w, t} : Set K) :=
    racl_subset_racl_base (racl k ({t} : Set K)) ({w, t} : Set K) h
  have ht' : t ∈ racl ↥(racl k ({t} : Set K)) ({w} : Set K) := by
    have hmem : algebraMap ↥(racl k ({t} : Set K)) K
        ⟨t, subset_racl k _ rfl⟩ ∈
        racl ↥(racl k ({t} : Set K)) ({w} : Set K) :=
      IntermediateField.algebraMap_mem _ _
    simpa using hmem
  have h2 : ({w, t} : Set K) = insert t ({w} : Set K) :=
    Set.pair_comm w t
  rw [h2, racl_insert_of_mem ht'] at h1
  exact h1

/-- A nonzero two-variable relation over the atom base: the vanishing
ideal of `(w, uw+v)` over `racl{t}` contains a nonzero polynomial. -/
theorem exists_line_relation (h : u * w + v ∈ racl k ({w, t} : Set K)) :
    ∃ G : MvPolynomial (Fin 2) ↥(racl k ({t} : Set K)), G ≠ 0 ∧
      MvPolynomial.aeval ![w, u * w + v] G = 0 := by
  have hbot : idealOf ↥(racl k ({t} : Set K)) ![w, u * w + v] ≠ ⊥ :=
    idealOf_ne_bot_of_mem_racl _ (line_mem_over_base h)
  obtain ⟨G, hGmem, hG0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  exact ⟨G, hG0, (mem_idealOf_iff _).1 hGmem⟩

section Collapse

/-- The one-variable collapse of a line configuration, generically:
substitute `X₀ ↦ T`, `X₁ ↦ u'T + v'`, mapping coefficients along `f`.
Stated over plain commutative rings to keep the kernel work trivial. -/
private noncomputable def lineCollapse {R S : Type*} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (u' v' : S) :
    MvPolynomial (Fin 2) R →+* Polynomial S :=
  MvPolynomial.eval₂Hom ((Polynomial.C : S →+* Polynomial S).comp f)
    ![Polynomial.X, Polynomial.C u' * Polynomial.X + Polynomial.C v']

/-- Evaluating the collapse at a point recovers the direct two-variable
evaluation. -/
private theorem lineCollapse_square {R S A : Type*} [CommSemiring R]
    [CommSemiring S] [CommSemiring A] (f : R →+* S) (g : S →+* A)
    (u' v' : S) (z : A) :
    (Polynomial.eval₂RingHom g z).comp (lineCollapse f u' v') =
      MvPolynomial.eval₂Hom (g.comp f) ![z, g u' * z + g v'] := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · simp [lineCollapse]
  · fin_cases i
    · simp [lineCollapse]
    · simp [lineCollapse]

variable {u v w t : K}

/-- **The substitution collapse**: a relation over `racl{t}` that vanishes
at `(w, uw+v)` with `w` transcendental over `racl{u, v}` vanishes at every
base-field specialization `(ξ, uξ+v)` — because the one-variable
substitution sends it to the zero polynomial. -/
theorem line_relation_specialize
    (hw : w ∉ racl k ({u, v} : Set K))
    (ht : t ∈ racl k ({u, v} : Set K))
    {G : MvPolynomial (Fin 2) ↥(racl k ({t} : Set K))}
    (hG : MvPolynomial.aeval ![w, u * w + v] G = 0) (ξ : k) :
    MvPolynomial.aeval
      ![algebraMap k K ξ, u * algebraMap k K ξ + v] G = 0 := by
  classical
  have hle : racl k ({t} : Set K) ≤ racl k ({u, v} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 ht)
  have hu : u ∈ racl k ({u, v} : Set K) := subset_racl k _ (by simp)
  have hv : v ∈ racl k ({u, v} : Set K) := subset_racl k _ (by simp)
  set f : ↥(racl k ({t} : Set K)) →+* ↥(racl k ({u, v} : Set K)) :=
    (IntermediateField.inclusion hle).toRingHom with hf
  set g : ↥(racl k ({u, v} : Set K)) →+* K :=
    algebraMap ↥(racl k ({u, v} : Set K)) K with hg
  -- The composite coefficient map is the canonical embedding.
  have hgf : g.comp f = algebraMap ↥(racl k ({t} : Set K)) K := by
    refine RingHom.ext fun r ↦ ?_
    simp only [hf, hg, RingHom.comp_apply]
    exact IntermediateField.coe_inclusion hle r
  have hgu : g ⟨u, hu⟩ = u := rfl
  have hgv : g ⟨v, hv⟩ = v := rfl
  -- The square, instantiated and rewritten to `aeval` form.
  have hsq : ∀ z : K,
      Polynomial.eval₂RingHom g z (lineCollapse f ⟨u, hu⟩ ⟨v, hv⟩ G) =
      MvPolynomial.aeval ![z, u * z + v] G := by
    intro z
    have h1 := DFunLike.congr_fun
      (lineCollapse_square f g ⟨u, hu⟩ ⟨v, hv⟩ z) G
    simp only [RingHom.comp_apply] at h1
    rw [h1, hgf, hgu, hgv]
    rfl
  -- The collapsed polynomial vanishes at the transcendental `w`.
  have hPw : Polynomial.aeval w (lineCollapse f ⟨u, hu⟩ ⟨v, hv⟩ G) = 0 := by
    have h2 : Polynomial.aeval w (lineCollapse f ⟨u, hu⟩ ⟨v, hv⟩ G) =
        Polynomial.eval₂RingHom g w
          (lineCollapse f ⟨u, hu⟩ ⟨v, hv⟩ G) := rfl
    rw [h2, hsq w, hG]
  have htr : Transcendental ↥(racl k ({u, v} : Set K)) w :=
    transcendental_racl_of_notMem hw
  have hzero : lineCollapse f ⟨u, hu⟩ ⟨v, hv⟩ G = 0 :=
    transcendental_iff.1 htr _ hPw
  -- Specialize the identity at `ξ`.
  rw [← hsq (algebraMap k K ξ), hzero, map_zero]

end Collapse

section Specialize

/-- Evaluating the nested presentation at a constant outer value and then
a point recovers the direct two-variable evaluation. Generic, to keep the
kernel work trivial. -/
private theorem nestEval_square {R A : Type*} [Field R] [CommRing A]
    (g : R →+* A) (c : R) (y : A) :
    (Polynomial.eval₂RingHom g y).comp
      ((Polynomial.evalRingHom (Polynomial.C c)).comp
        (nestEquiv R).toAlgHom.toRingHom) =
    MvPolynomial.eval₂Hom g ![g c, y] := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · have hC : (nestEquiv R).toAlgHom.toRingHom (MvPolynomial.C r) =
        Polynomial.C (Polynomial.C r) := nestEquiv_C r
    simp only [RingHom.comp_apply, hC, Polynomial.coe_evalRingHom,
      Polynomial.eval_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      MvPolynomial.eval₂Hom_C]
  · fin_cases i
    · have hX : (nestEquiv R).toAlgHom.toRingHom
          (MvPolynomial.X ⟨0, by omega⟩) = Polynomial.X :=
        nestEquiv_X_zero (K := R)
      simp only [RingHom.comp_apply, hX, Polynomial.coe_evalRingHom,
        Polynomial.eval_X, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, MvPolynomial.eval₂Hom_X']
      rfl
    · have hX : (nestEquiv R).toAlgHom.toRingHom
          (MvPolynomial.X ⟨1, by omega⟩) = Polynomial.C Polynomial.X :=
        nestEquiv_X_one (K := R)
      simp only [RingHom.comp_apply, hX, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X, MvPolynomial.eval₂Hom_X']
      rfl

/-- A nonzero nested polynomial vanishes at only finitely many constant
outer values. -/
private theorem finite_bad_eval {R : Type*} [Field R]
    {P : Polynomial (Polynomial R)} (hP : P ≠ 0) :
    {c : R | Polynomial.eval (Polynomial.C c) P = 0}.Finite := by
  have hroots : {q : Polynomial R | Polynomial.IsRoot P q}.Finite :=
    Polynomial.finite_setOf_isRoot hP
  have hsub : {c : R | Polynomial.eval (Polynomial.C c) P = 0} ⊆
      Polynomial.C ⁻¹' {q : Polynomial R | Polynomial.IsRoot P q} :=
    fun c hc ↦ hc
  exact (hroots.preimage (Set.injOn_of_injective Polynomial.C_injective)).subset
    hsub

variable {u v w t : K}

/-- At a specialization point where the `Y`-collapse stays nonzero, the
line value is algebraic over the atom closure. -/
theorem line_value_mem
    (hw : w ∉ racl k ({u, v} : Set K))
    (ht : t ∈ racl k ({u, v} : Set K))
    {G : MvPolynomial (Fin 2) ↥(racl k ({t} : Set K))}
    (hG : MvPolynomial.aeval ![w, u * w + v] G = 0) {ξ : k}
    (hQ : Polynomial.eval
        (Polynomial.C (algebraMap k ↥(racl k ({t} : Set K)) ξ))
        (nestEquiv ↥(racl k ({t} : Set K)) G) ≠ 0) :
    u * algebraMap k K ξ + v ∈ racl k ({t} : Set K) := by
  have hspec := line_relation_specialize hw ht hG ξ
  have hsq := DFunLike.congr_fun (nestEval_square
    (algebraMap ↥(racl k ({t} : Set K)) K)
    (algebraMap k ↥(racl k ({t} : Set K)) ξ)
    (u * algebraMap k K ξ + v)) G
  simp only [RingHom.comp_apply] at hsq
  have htow : algebraMap ↥(racl k ({t} : Set K)) K
      (algebraMap k ↥(racl k ({t} : Set K)) ξ) = algebraMap k K ξ :=
    (IsScalarTower.algebraMap_apply k ↥(racl k ({t} : Set K)) K ξ).symm
  rw [htow] at hsq
  have hzero : Polynomial.eval₂RingHom
      (algebraMap ↥(racl k ({t} : Set K)) K)
      (u * algebraMap k K ξ + v)
      (Polynomial.eval
        (Polynomial.C (algebraMap k ↥(racl k ({t} : Set K)) ξ))
        (nestEquiv ↥(racl k ({t} : Set K)) G)) = 0 := by
    have h1 : Polynomial.eval₂RingHom
        (algebraMap ↥(racl k ({t} : Set K)) K)
        (u * algebraMap k K ξ + v)
        (Polynomial.eval
          (Polynomial.C (algebraMap k ↥(racl k ({t} : Set K)) ξ))
          (nestEquiv ↥(racl k ({t} : Set K)) G)) =
        MvPolynomial.eval₂Hom
          (algebraMap ↥(racl k ({t} : Set K)) K)
          ![algebraMap k K ξ, u * algebraMap k K ξ + v] G := hsq
    have h3 : MvPolynomial.eval₂Hom
        (algebraMap ↥(racl k ({t} : Set K)) K)
        ![algebraMap k K ξ, u * algebraMap k K ξ + v] G =
        MvPolynomial.aeval
          ![algebraMap k K ξ, u * algebraMap k K ξ + v] G := rfl
    rw [h1, h3, hspec]
  have halg : IsAlgebraic ↥(racl k ({t} : Set K))
      (u * algebraMap k K ξ + v) := ⟨_, hQ, hzero⟩
  exact IsRAC.mem_of_isAlgebraic (isRAC_racl _) halg

/-- Two distinct specializations with algebraic line values exist: the
collapse is nonzero at all but finitely many base points, and the base
field is infinite. -/
theorem exists_two_specializations [Infinite k]
    (hw : w ∉ racl k ({u, v} : Set K))
    (ht : t ∈ racl k ({u, v} : Set K))
    {G : MvPolynomial (Fin 2) ↥(racl k ({t} : Set K))} (hG0 : G ≠ 0)
    (hG : MvPolynomial.aeval ![w, u * w + v] G = 0) :
    ∃ ξ₁ ξ₂ : k, ξ₁ ≠ ξ₂ ∧
      u * algebraMap k K ξ₁ + v ∈ racl k ({t} : Set K) ∧
      u * algebraMap k K ξ₂ + v ∈ racl k ({t} : Set K) := by
  classical
  have hĜ0 : nestEquiv ↥(racl k ({t} : Set K)) G ≠ 0 := by
    intro h0
    exact hG0 ((nestEquiv _).injective (by rw [h0, map_zero]))
  have hfin := finite_bad_eval hĜ0
  have hbadk : {ξ : k | Polynomial.eval
      (Polynomial.C (algebraMap k ↥(racl k ({t} : Set K)) ξ))
      (nestEquiv ↥(racl k ({t} : Set K)) G) = 0}.Finite := by
    refine (hfin.preimage (Set.injOn_of_injective ?_)).subset fun ξ hξ ↦ hξ
    exact (algebraMap k ↥(racl k ({t} : Set K))).injective
  have hgood : {ξ : k | Polynomial.eval
      (Polynomial.C (algebraMap k ↥(racl k ({t} : Set K)) ξ))
      (nestEquiv ↥(racl k ({t} : Set K)) G) = 0}ᶜ.Infinite :=
    Set.Finite.infinite_compl hbadk
  obtain ⟨ξ₁, hξ₁, ξ₂, hξ₂, hne⟩ := hgood.nontrivial
  exact ⟨ξ₁, ξ₂, hne, line_value_mem hw ht hG hξ₁,
    line_value_mem hw ht hG hξ₂⟩

/-- **The atom clause, elementwise** (blueprint clause (iv), by the
specialization route): no transcendental parameter `t` algebraic over the
independent line coefficients `u, v` can make the generic direction `w`
algebraic over `{t, uw + v}`. -/
theorem notMem_racl_line [Infinite k]
    (hu0 : u ∉ racl k (∅ : Set K))
    (hvu : v ∉ racl k ({u} : Set K))
    (hw : w ∉ racl k ({u, v} : Set K))
    (ht : t ∈ racl k ({u, v} : Set K))
    (ht0 : t ∉ racl k (∅ : Set K)) :
    w ∉ racl k ({t, u * w + v} : Set K) := by
  intro hmem
  obtain ⟨G, hG0, hG⟩ := exists_line_relation (line_mem_of_mem hw ht hmem)
  obtain ⟨ξ₁, ξ₂, hne, h1, h2⟩ := exists_two_specializations hw ht hG0 hG
  -- Differencing the two values recovers `u`.
  have hu : u ∈ racl k ({t} : Set K) := by
    have hsub := sub_mem h1 h2
    have harith : (u * algebraMap k K ξ₁ + v) -
        (u * algebraMap k K ξ₂ + v) = u * algebraMap k K (ξ₁ - ξ₂) := by
      rw [map_sub]
      ring
    rw [harith] at hsub
    have hinv : algebraMap k K (ξ₁ - ξ₂)⁻¹ ∈ racl k ({t} : Set K) :=
      IntermediateField.algebraMap_mem _ _
    have h := MulMemClass.mul_mem hsub hinv
    rwa [mul_assoc, ← map_mul, mul_inv_cancel₀ (sub_ne_zero.2 hne),
      map_one, mul_one] at h
  -- Then the constant term recovers `v`.
  have hv : v ∈ racl k ({t} : Set K) := by
    have hux : u * algebraMap k K ξ₁ ∈ racl k ({t} : Set K) :=
      MulMemClass.mul_mem hu (IntermediateField.algebraMap_mem _ _)
    have h := sub_mem h1 hux
    rwa [add_sub_cancel_left] at h
  -- Exchange the transcendental `u` against `t`.
  have hu' : u ∈ racl k (insert t (∅ : Set K)) := by
    simpa using hu
  have ht' := racl_exchange hu' hu0
  have ht'' : t ∈ racl k ({u} : Set K) := by
    simpa using ht'
  exact hvu (racl_le_of_subset_racl (Set.singleton_subset_iff.2 ht'') hv)

end Specialize

end LineClause

end

end AclGeom
