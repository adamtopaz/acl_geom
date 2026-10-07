/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.MulDiagramCheck
import AclGeom.Config.Quadrangle
import AclGeom.Geometry.Representatives
import AclGeom.Transfer.LiftConfig
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-!
# The geometric half of the #25 counterexamples

Let `s, t, e₁, e₂, e₃ ∈ K` be algebraically independent over `k`, and let `r` be a square root of
`s` in an algebraically closed `Ω ⊇ K`.  Then geometric `Q` and `Q′` hold over `K/k` for

* `([s], [s t²], [s (1 + t)²], [t])` (`qGeom_rat`), and
* `([s], [s t²], [s (1 + t)²], [s t])` (`qPrimeGeom_rat`),

although, for `K = k(s, t, e₁, e₂, e₃)` with `k = ℚ`, the corresponding semantic relations fail
(issue #25; the semantic half is separate).

The proofs descend explicit witnesses over the algebraically closed pair `k̄ ⊆ Ω`.
* For `Q`, the table-7.1 witness `qWitness` at `(a, b, c, d, x) = (e₁, r, e₂, r e₃, r t / e₁)`
  satisfies `Ψ` by `qWitness_psi`.
* For `Q′`, the multiplication diagram `mulDiagram_of_indep` holds at `(r, r t, e₁)`.

Every point of these witnesses is the lift of a point of `K/k`. An entry `v` is either `ι w`,
`(ι w)⁻¹`, or a square root of `ι w`, with `w` given by the issue-#25 table, and an element and its
square generate the same closure.  The reflections of `AclGeom.Transfer.LiftConfig`
(`QWitness.Psi.of_lift` with the table-7.2 quadrangle supplied as lifts, and `MulDiagram.of_lift`)
then give the configurations over `K/k`.  No general descent of witnesses is used, and no
completeness hypothesis enters.

**Status:** the displayed explicit-witness descents are proved. The characteristic-zero
semantic obstruction and concrete refutations are in QSemantic and QRefutation.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open ClosedIF IntermediateField

noncomputable section

section Identification

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω]
  {K₀ : IntermediateField k Ω} (halg : ∀ y ∈ K₀, IsAlgebraic k y) (ι : K →ₐ[k] Ω)

include halg

/-- An image point is the lift of the point. -/
theorem point_eq_liftClosed_of_eq {v : Ω} {w : K} (h : v = ι w) :
    point (↥K₀) v = liftClosed K₀ ι (point k w) := by
  rw [liftClosed_point halg ι, h]

/-- A square root of an image generates the lift of the point. -/
theorem point_eq_liftClosed_of_sq {v : Ω} {w : K} (h : v ^ 2 = ι w) :
    point (↥K₀) v = liftClosed K₀ ι (point k w) := by
  rw [liftClosed_point halg ι, ← h, point_pow v two_ne_zero]

/-- An inverse image generates the lift of the point. -/
theorem point_eq_liftClosed_of_inv {v : Ω} {w : K} (h : v = (ι w)⁻¹) :
    point (↥K₀) v = liftClosed K₀ ι (point k w) := by
  rw [liftClosed_point halg ι, h, point_inv]

/-- A representative of a lifted point that is transcendental over `K₀` is transcendental. -/
theorem notMem_bot_of_point_eq_liftClosed {v : Ω} {w : K} (hv : v ∉ (⊥ : ClosedIF (↥K₀) Ω))
    (h : point (↥K₀) v = liftClosed K₀ ι (point k w)) : w ∉ (⊥ : ClosedIF k K) := fun hw ↦
  hv (point_eq_bot_iff.1 (by rw [h, point_eq_bot_iff.2 hw, liftClosed_bot halg ι]))

/-- A point of `K/k` with representative `w` lifts to the principal point of `v` whenever the two
generate corresponding closures. -/
theorem liftPoint_eq_mk' {v : Ω} {hv : v ∉ (⊥ : ClosedIF (↥K₀) Ω)} {P : Point k K} {w : K}
    (hP : P.1 = point k w) (h : point (↥K₀) v = liftClosed K₀ ι (point k w)) :
    liftPoint halg ι P = Point.mk' (↥K₀) v hv :=
  Subtype.ext (by rw [liftPoint_val, hP]; exact h.symm)

end Identification

section Rational

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω]
  [IsAlgClosed Ω] (ι : K →ₐ[k] Ω) {s t e₁ e₂ e₃ : K}
  (hind : AlgebraicIndependent k ![s, t, e₁, e₂, e₃]) {r : Ω} (hr : r ^ 2 = ι s)

include hind

omit [IsAlgClosed Ω] in
/-- The five generators, transported to `Ω` over `k̄ = algebraicClosure k Ω`. -/
theorem qDescent_indep_image :
    AlgebraicIndependent (↥(algebraicClosure k Ω)) ![ι s, ι t, ι e₁, ι e₂, ι e₃] := by
  have hinj : Function.Injective ι := ι.toRingHom.injective
  have h := AlgebraicIndependent.extendScalars (↥(algebraicClosure k Ω)) (hind.map' hinj)
  convert h using 1
  funext i
  fin_cases i <;> rfl

include hr

omit [IsAlgClosed Ω] in
/-- `r` and `e₁` are nonzero. -/
theorem qDescent_ne_zero : r ≠ 0 ∧ ι e₁ ≠ 0 := by
  have hs0 : s ≠ 0 := AlgebraicIndependent.ne_zero hind 0
  have he₁0 : e₁ ≠ 0 := AlgebraicIndependent.ne_zero hind 2
  refine ⟨fun h0 ↦ (map_ne_zero ι).2 hs0 ?_, (map_ne_zero ι).2 he₁0⟩
  rw [← hr, h0, zero_pow two_ne_zero]

omit [IsAlgClosed Ω] in
/-- **The table-7.1 generators are independent over `k̄`**:
`(a, b, c, d, x) = (e₁, r, e₂, r e₃, r t / e₁)`. -/
theorem qDescent_indep :
    AlgebraicIndependent (↥(algebraicClosure k Ω))
      ![ι e₁, r, ι e₂, r * ι e₃, r * ι t / ι e₁] := by
  obtain ⟨hr0, he₁⟩ := qDescent_ne_zero ι hind hr
  set K₀ := algebraicClosure k Ω
  have h5 := qDescent_indep_image ι hind
  set S := Set.range ![ι s, ι t, ι e₁, ι e₂, ι e₃]
  set T := Set.range ![ι e₁, r, ι e₂, r * ι e₃, r * ι t / ι e₁]
  -- The generators on each side, as named memberships.
  have hsS : ι s ∈ racl (↥K₀) S := subset_racl _ _ ⟨0, rfl⟩
  -- `r` lies over `s`.
  have hrS : r ∈ racl (↥K₀) S := by
    have hsq : r ^ 2 ∈ racl (↥K₀) S := by
      rw [hr]
      exact hsS
    exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 hsq)
      (mem_racl_singleton_pow two_ne_zero)
  have htS : ι t ∈ racl (↥K₀) S := subset_racl _ _ ⟨1, rfl⟩
  have he₁S : ι e₁ ∈ racl (↥K₀) S := subset_racl _ _ ⟨2, rfl⟩
  have he₂S : ι e₂ ∈ racl (↥K₀) S := subset_racl _ _ ⟨3, rfl⟩
  have he₃S : ι e₃ ∈ racl (↥K₀) S := subset_racl _ _ ⟨4, rfl⟩
  have haT : ι e₁ ∈ racl (↥K₀) T := subset_racl _ _ ⟨0, rfl⟩
  have hbT : r ∈ racl (↥K₀) T := subset_racl _ _ ⟨1, rfl⟩
  have hcT : ι e₂ ∈ racl (↥K₀) T := subset_racl _ _ ⟨2, rfl⟩
  have hdT : r * ι e₃ ∈ racl (↥K₀) T := subset_racl _ _ ⟨3, rfl⟩
  have hxT : r * ι t / ι e₁ ∈ racl (↥K₀) T := subset_racl _ _ ⟨4, rfl⟩
  refine AlgebraicIndependent.of_racl_range_eq h5 (racl_range_eq_of_mem (fun j ↦ ?_) (fun i ↦ ?_))
  · fin_cases j
    · exact he₁S
    · exact hrS
    · exact he₂S
    · exact mul_mem hrS he₃S
    · exact div_mem (mul_mem hrS htS) he₁S
  · fin_cases i
    · -- `s = b ^ 2`
      have h2 : r ^ 2 ∈ racl (↥K₀) T := pow_mem hbT 2
      rw [hr] at h2
      exact h2
    · -- `t = x a / b`
      change ι t ∈ racl (↥K₀) T
      simpa only [div_mul_cancel₀ _ he₁, mul_div_cancel_left₀ _ hr0] using
        (div_mem (mul_mem hxT haT) hbT)
    · exact haT
    · exact hcT
    · -- `e₃ = d / b`
      change ι e₃ ∈ racl (↥K₀) T
      simpa only [mul_div_cancel_left₀ _ hr0] using (div_mem hdT hbT)

/-- **Geometric `Q` over `K/k` for the #25 tuple** `([s], [s t²], [s (1 + t)²], [t])`: the
table-7.1 witness at `(e₁, r, e₂, r e₃, r t / e₁)` over `k̄ ⊆ Ω` is the lift of a witness over
`K/k`, and the table-7.2 quadrangle is the lift of `([e₁], [e₂], [e₁ e₂], [s], [s e₁² e₂²],
[s e₂²])`. -/
theorem qGeom_rat {P D Y I : Point k K} (hP : P.1 = point k s) (hD : D.1 = point k (s * t ^ 2))
    (hY : Y.1 = point k (s * (1 + t) ^ 2)) (hI : I.1 = point k t) :
    QGeom P D Y I := by
  obtain ⟨hr0, he₁⟩ := qDescent_ne_zero ι hind hr
  set K₀ := algebraicClosure k Ω
  have halg : ∀ z ∈ K₀, IsAlgebraic k z := fun _ hz ↦ (mem_algebraicClosure_iff (F := k)).1 hz
  have hq := qDescent_indep ι hind hr
  -- The table entries `a x = r t` and `a c x = e₂ (r t)` after cancelling `e₁`.
  have hax : ι e₁ * (r * ι t / ι e₁) = r * ι t := by field_simp
  have hacx : ι e₁ * ι e₂ * (r * ι t / ι e₁) = ι e₂ * (r * ι t) := by
    rw [mul_comm (ι e₁) (ι e₂), mul_assoc, hax]
  -- Identification of every table point with the lift of a point of `K/k`.
  have iA₁ := point_eq_liftClosed_of_eq halg ι (v := ι e₁) (w := e₁) rfl
  have iA₂ := point_eq_liftClosed_of_sq halg ι (v := r) (w := s) hr
  have iB₁ := point_eq_liftClosed_of_eq halg ι (v := ι e₂) (w := e₂) rfl
  have iB₂ := point_eq_liftClosed_of_sq halg ι (v := r * ι e₃) (w := s * e₃ ^ 2) (by
    rw [mul_pow, hr, map_mul, map_pow])
  have iC₁ := point_eq_liftClosed_of_eq halg ι (v := ι e₁ * ι e₂) (w := e₁ * e₂)
    (map_mul ι e₁ e₂).symm
  have iC₂ := point_eq_liftClosed_of_sq halg ι (v := r * ι e₂ + r * ι e₃)
      (w := s * (e₂ + e₃) ^ 2) (by
    simp only [map_mul, map_pow, map_add]
    linear_combination (ι e₂ + ι e₃) ^ 2 * hr)
  have iD := point_eq_liftClosed_of_sq halg ι (v := ι e₁ * (r * ι t / ι e₁)) (w := s * t ^ 2)
    (by rw [hax]; simp only [map_mul, map_pow]; linear_combination ι t ^ 2 * hr)
  have iE := point_eq_liftClosed_of_sq halg ι (v := ι e₂ * (ι e₁ * (r * ι t / ι e₁) + r))
      (w := s * e₂ ^ 2 * (1 + t) ^ 2) (by
    rw [hax]
    simp only [map_mul, map_pow, map_add, map_one]
    linear_combination ι e₂ ^ 2 * (1 + ι t) ^ 2 * hr)
  have iF := point_eq_liftClosed_of_sq halg ι (v := ι e₁ * ι e₂ * (r * ι t / ι e₁))
      (w := s * e₂ ^ 2 * t ^ 2) (by
    rw [hacx]
    simp only [map_mul, map_pow]
    linear_combination ι e₂ ^ 2 * ι t ^ 2 * hr)
  have iG := point_eq_liftClosed_of_sq halg ι (v := r * ι e₂) (w := s * e₂ ^ 2) (by
    rw [mul_pow, hr, map_mul, map_pow])
  have iH := point_eq_liftClosed_of_sq halg ι (v := ι e₁ / r) (w := e₁ ^ 2 / s) (by
    rw [div_pow, hr, map_div₀, map_pow])
  have iI := point_eq_liftClosed_of_eq halg ι (v := ι e₁ * (r * ι t / ι e₁) / r) (w := t) (by
    rw [hax, mul_div_cancel_left₀ _ hr0])
  have iX := point_eq_liftClosed_of_sq halg ι (v := r * ι t / ι e₁) (w := s * t ^ 2 / e₁ ^ 2)
    (by rw [div_pow, mul_pow, hr, map_div₀, map_mul, map_pow, map_pow])
  have iY := point_eq_liftClosed_of_sq halg ι (v := ι e₁ * (r * ι t / ι e₁) + r)
      (w := s * (1 + t) ^ 2) (by
    rw [hax]
    simp only [map_mul, map_pow, map_add, map_one]
    linear_combination (1 + ι t) ^ 2 * hr)
  have iZ := point_eq_liftClosed_of_sq halg ι
      (v := ι e₂ * (ι e₁ * (r * ι t / ι e₁) + r) + r * ι e₃)
      (w := s * (e₂ * (1 + t) + e₃) ^ 2) (by
    rw [hax]
    simp only [map_mul, map_pow, map_add, map_one]
    linear_combination (ι e₂ * (1 + ι t) + ι e₃) ^ 2 * hr)
  have iT' := point_eq_liftClosed_of_sq halg ι (v := ι e₁ * ι e₂ * r)
      (w := s * e₁ ^ 2 * e₂ ^ 2) (by
    simp only [map_mul, map_pow]
    linear_combination ι e₁ ^ 2 * ι e₂ ^ 2 * hr)
  have iU' := point_eq_liftClosed_of_sq halg ι (v := ι e₂ * r) (w := s * e₂ ^ 2) (by
    simp only [map_mul, map_pow]
    linear_combination ι e₂ ^ 2 * hr)
  -- The witness over `K/k`, with the table-7.1 field order.
  let pt := fun (w : K) (v : Ω) (hv : v ∉ (⊥ : ClosedIF (↥K₀) Ω))
      (h : point (↥K₀) v = liftClosed K₀ ι (point k w)) ↦
    Point.mk' k w (notMem_bot_of_point_eq_liftClosed halg ι hv h)
  let wK : QWitness k K :=
    { A₁ := pt _ _ (qtable_a_notMem_bot hq) iA₁
      A₂ := pt _ _ (qtable_b_notMem_bot hq) iA₂
      B₁ := pt _ _ (qtable_c_notMem_bot hq) iB₁
      B₂ := pt _ _ (qtable_d_notMem_bot hq) iB₂
      C₁ := pt _ _ (qtable_mul_ac_notMem_bot hq) iC₁
      C₂ := pt _ _ (qtable_bcd_notMem_bot hq) iC₂
      D := pt _ _ (qtable_mul_ax_notMem_bot hq) iD
      E := pt _ _ (qtable_E_notMem_bot hq) iE
      F := pt _ _ (qtable_acx_notMem_bot hq) iF
      G := pt _ _ (qtable_mul_bc_notMem_bot hq) iG
      H := pt _ _ (qtable_div_ab_notMem_bot hq) iH
      I := pt _ _ (qtable_axb_notMem_bot hq) iI
      P := pt _ _ (qtable_b_notMem_bot hq) iA₂
      Q := pt _ _ (qtable_d_notMem_bot hq) iB₂
      R := pt _ _ (qtable_bcd_notMem_bot hq) iC₂
      S := pt _ _ (qtable_a_notMem_bot hq) iA₁
      T := pt _ _ (qtable_c_notMem_bot hq) iB₁
      U := pt _ _ (qtable_mul_ac_notMem_bot hq) iC₁
      X := pt _ _ (qtable_x_notMem_bot hq) iX
      Y := pt _ _ (qtable_Y_notMem_bot hq) iY
      Z := pt _ _ (qtable_Z_notMem_bot hq) iZ }
  -- Its lift is the table-7.1 witness over `k̄ ⊆ Ω`.
  have hlift : wK.lift halg ι = qWitness hq := by
    unfold QWitness.lift qWitness
    congr 1 <;> exact liftPoint_eq_mk' halg ι rfl (by assumption)
  -- The table-7.2 quadrangle, supplied as lifts.
  let S' := pt _ _ (qtable_b_notMem_bot hq) iA₂
  let T' := pt _ _ (qtable_acb_notMem_bot hq) iT'
  let U' := pt _ _ (qtable_mul_cb_notMem_bot hq) iU'
  have hquad : IsPartialQuadrangle (liftPoint halg ι ∘ ![wK.S, wK.T, wK.U, S', T', U']) := by
    have hvec : liftPoint halg ι ∘ ![wK.S, wK.T, wK.U, S', T', U'] = qQuad hq := by
      funext i
      fin_cases i
      · exact liftPoint_eq_mk' halg ι (hv := qtable_a_notMem_bot hq) rfl iA₁
      · exact liftPoint_eq_mk' halg ι (hv := qtable_c_notMem_bot hq) rfl iB₁
      · exact liftPoint_eq_mk' halg ι (hv := qtable_mul_ac_notMem_bot hq) rfl iC₁
      · exact liftPoint_eq_mk' halg ι (hv := qtable_b_notMem_bot hq) rfl iA₂
      · exact liftPoint_eq_mk' halg ι (hv := qtable_acb_notMem_bot hq) rfl iT'
      · exact liftPoint_eq_mk' halg ι (hv := qtable_mul_cb_notMem_bot hq) rfl iU'
    rw [hvec]
    exact qQuad_isPartialQuadrangle hq
  have hPsi : (wK.lift halg ι).Psi := by
    rw [hlift]
    exact qWitness_psi hq
  have hQ := QGeom.of_lift_witness halg ι wK hPsi hquad
  obtain rfl : P = wK.P := Subtype.ext hP
  obtain rfl : D = wK.D := Subtype.ext hD
  obtain rfl : Y = wK.Y := Subtype.ext hY
  obtain rfl : I = wK.I := Subtype.ext hI
  exact hQ

omit [IsAlgClosed Ω] in
/-- The multiplication-diagram generators `(r, r t, e₁)` are independent over `k̄`. -/
theorem qDescent_indep_mul :
    AlgebraicIndependent (↥(algebraicClosure k Ω)) ![r, r * ι t, ι e₁] := by
  obtain ⟨hr0, -⟩ := qDescent_ne_zero ι hind hr
  have h5 := qDescent_indep_image ι hind
  have h3 : AlgebraicIndependent (↥(algebraicClosure k Ω)) ![ι s, ι t, ι e₁] := by
    have h := h5.comp ![0, 1, 2] (by decide)
    convert h using 1
    funext i
    fin_cases i <;> rfl
  set K₀ := algebraicClosure k Ω
  set S := Set.range ![ι s, ι t, ι e₁]
  set T := Set.range ![r, r * ι t, ι e₁]
  have hsS : ι s ∈ racl (↥K₀) S := subset_racl _ _ ⟨0, rfl⟩
  have htS : ι t ∈ racl (↥K₀) S := subset_racl _ _ ⟨1, rfl⟩
  have he₁S : ι e₁ ∈ racl (↥K₀) S := subset_racl _ _ ⟨2, rfl⟩
  have hxT : r ∈ racl (↥K₀) T := subset_racl _ _ ⟨0, rfl⟩
  have hyT : r * ι t ∈ racl (↥K₀) T := subset_racl _ _ ⟨1, rfl⟩
  have haT : ι e₁ ∈ racl (↥K₀) T := subset_racl _ _ ⟨2, rfl⟩
  have hrS : r ∈ racl (↥K₀) S := by
    have hsq : r ^ 2 ∈ racl (↥K₀) S := by
      rw [hr]
      exact hsS
    exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 hsq)
      (mem_racl_singleton_pow two_ne_zero)
  refine AlgebraicIndependent.triple_of_mem h3 (fun j ↦ ?_) (fun i ↦ ?_)
  · fin_cases j
    · exact hrS
    · exact mul_mem hrS htS
    · exact he₁S
  · fin_cases i
    · have h2 : r ^ 2 ∈ racl (↥K₀) T := pow_mem hxT 2
      rw [hr] at h2
      exact h2
    · change ι t ∈ racl (↥K₀) T
      simpa only [mul_div_cancel_left₀ _ hr0] using (div_mem hyT hxT)
    · exact haT

/-- **Geometric `Q′` over `K/k` for the #25 tuple** `([s], [s t²], [s (1 + t)²], [s t])`.  Its `Q`
conjunct is `qGeom_rat` with `V = [t]`.  The multiplication diagram at `(r, r t, e₁)` over `k̄ ⊆ Ω`
is the lift of `([s], [s t²], [t], [s t], [e₁], [e₁² s], [e₁² s t²], [e₁ s t])`. -/
theorem qPrimeGeom_rat {X Y S E : Point k K} (hX : X.1 = point k s)
    (hY : Y.1 = point k (s * t ^ 2)) (hS : S.1 = point k (s * (1 + t) ^ 2))
    (hE : E.1 = point k (s * t)) : Q'Geom X Y S E := by
  obtain ⟨hr0, -⟩ := qDescent_ne_zero ι hind hr
  set K₀ := algebraicClosure k Ω
  have halg : ∀ z ∈ K₀, IsAlgebraic k z := fun _ hz ↦ (mem_algebraicClosure_iff (F := k)).1 hz
  have hm := qDescent_indep_mul ι hind hr
  have hM := mulDiagram_of_indep hm
  -- Identification of the eight diagram points.
  have iX := point_eq_liftClosed_of_sq halg ι (v := r) (w := s) hr
  have iY := point_eq_liftClosed_of_sq halg ι (v := r * ι t) (w := s * t ^ 2) (by
    rw [mul_pow, hr, map_mul, map_pow])
  have iV := point_eq_liftClosed_of_inv halg ι (v := r / (r * ι t)) (w := t) (by
    rw [div_mul_eq_div_div, div_self hr0, one_div])
  have iE := point_eq_liftClosed_of_eq halg ι (v := r * (r * ι t)) (w := s * t) (by
    rw [← mul_assoc, ← sq, hr, map_mul])
  have iA := point_eq_liftClosed_of_eq halg ι (v := ι e₁) (w := e₁) rfl
  have iB := point_eq_liftClosed_of_sq halg ι (v := ι e₁ * r) (w := e₁ ^ 2 * s) (by
    rw [mul_pow, hr, map_mul, map_pow])
  have iC := point_eq_liftClosed_of_sq halg ι (v := ι e₁ * (r * ι t)) (w := e₁ ^ 2 * s * t ^ 2)
    (by simp only [map_mul, map_pow]; linear_combination ι e₁ ^ 2 * ι t ^ 2 * hr)
  have iD := point_eq_liftClosed_of_eq halg ι (v := ι e₁ * r * (r * ι t)) (w := e₁ * s * t) (by
    simp only [map_mul]
    linear_combination ι e₁ * ι t * hr)
  -- The points of `K/k`.
  let pt := fun (w : K) (v : Ω) (hv : v ∉ (⊥ : ClosedIF (↥K₀) Ω))
      (h : point (↥K₀) v = liftClosed K₀ ι (point k w)) ↦
    Point.mk' k w (notMem_bot_of_point_eq_liftClosed halg ι hv h)
  let V := pt _ _ (mtable_div_notMem_bot hm) iV
  let A₀ := pt _ _ (mtable_a_notMem_bot hm) iA
  let B₀ := pt _ _ (mtable_ax_notMem_bot hm) iB
  let C₀ := pt _ _ (mtable_ay_notMem_bot hm) iC
  let D₀ := pt _ _ (mtable_axy_notMem_bot hm) iD
  refine ⟨V, A₀, B₀, C₀, D₀, qGeom_rat ι hind hr hX hY hS rfl,
    MulDiagram.of_lift halg ι ?_⟩
  convert hM using 1
  · exact liftPoint_eq_mk' halg ι hX iX
  · exact liftPoint_eq_mk' halg ι hY iY
  · exact liftPoint_eq_mk' halg ι rfl iV
  · exact liftPoint_eq_mk' halg ι hE iE
  · exact liftPoint_eq_mk' halg ι rfl iA
  · exact liftPoint_eq_mk' halg ι rfl iB
  · exact liftPoint_eq_mk' halg ι rfl iC
  · exact liftPoint_eq_mk' halg ι rfl iD

end Rational

end

end AclGeom
