/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.MeetEquations
import AclGeom.Geometry.Representatives

/-!
# The meets `D`, `F` and `R` after normalizing `P`

Let `a, b, c, d, x` be independent and let `κ ∈ k`.  Translating the common curve coordinate by
`κ` gives the starred table coordinates `b* = b + (a - 1) κ`, `d* = d + (c - 1) κ` and
`x* = x - κ`.  Then `a x* + b* = a x + b - κ` and `c (a x* + b*) + d* = c (a x + b) + d - κ`.

* `algebraicIndependent_table_shift`: the starred coordinates are again independent.
* `racl_shifted_D_F_R_of_normalized_P`: if the point `P` is normalized, `acl(p) = acl(b*)`,
  then points `δ, f, r` with the incidences of the meets `D`, `F` and `R` of `Ψ` are the table
  entries `a x*`, `a c x*` and `b c + d + a c κ`; the last one is `b* c + d*` up to `κ`.

The meets are the soundness meets `qWitness_meet_D`, `qWitness_meet_F` and `qWitness_meet_R` of
the starred table, reused verbatim.  The second theorem is conditional on the normalized `P`.
Deriving that normalization, from a supplied family of fresh relocation inputs over an
algebraically closed base, is a separate check.  The meets `E, G, H, I`, the point `Q`, the
combined generator presentation, ambient input existence and descent, the action presentation,
extraction and completeness remain open.

**Status:** conditional `D/F/R` normalization proved (#27, P2). The original five-variable
supplied-input family chain derives the shift, `P` and these rows in a private check under
explicit base/ambient ACF. `E/G/H/I/Q`, the combined generator presentation, ambient existence/
descent, actions, extraction and completeness remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Translating the table coordinates** (#27).  If `a, b, c, d, x` are independent and
`κ ∈ k`, then so are `a`, `b + (a - 1) κ`, `c`, `d + (c - 1) κ` and `x - κ`: the change of
coordinates is triangular with an inverse of the same form. -/
theorem algebraicIndependent_table_shift {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) (κ : k) :
    AlgebraicIndependent k ![a, b + (a - 1) * algebraMap k K κ,
      c, d + (c - 1) * algebraMap k K κ, x - algebraMap k K κ] := by
  obtain ⟨e, he⟩ : ∃ e, algebraMap k K κ = e := ⟨_, rfl⟩
  rw [he]
  have ht (S : Set K) : e ∈ racl k S := by
    rw [← he]
    exact (racl k S).algebraMap_mem κ
  refine AlgebraicIndependent.of_racl_range_eq hind (racl_range_eq_of_mem ?_ ?_)
  · have hm (i : Fin 5) : ![a, b, c, d, x] i ∈ racl k (Set.range ![a, b, c, d, x]) :=
      subset_racl k _ ⟨i, rfl⟩
    intro i
    fin_cases i
    · exact hm 0
    · exact add_mem (hm 1) (mul_mem (sub_mem (hm 0) (one_mem _)) (ht _))
    · exact hm 2
    · exact add_mem (hm 3) (mul_mem (sub_mem (hm 2) (one_mem _)) (ht _))
    · exact sub_mem (hm 4) (ht _)
  · have hm (i : Fin 5) : ![a, b + (a - 1) * e, c, d + (c - 1) * e, x - e] i ∈
        racl k (Set.range ![a, b + (a - 1) * e, c, d + (c - 1) * e, x - e]) :=
      subset_racl k _ ⟨i, rfl⟩
    intro i
    fin_cases i
    · exact hm 0
    · change b ∈ _
      have h := sub_mem (hm 1) (mul_mem (sub_mem (hm 0) (one_mem _)) (ht _))
      change b + (a - 1) * e - (a - 1) * e ∈ _ at h
      rwa [add_sub_cancel_right] at h
    · exact hm 2
    · change d ∈ _
      have h := sub_mem (hm 3) (mul_mem (sub_mem (hm 2) (one_mem _)) (ht _))
      change d + (c - 1) * e - (c - 1) * e ∈ _ at h
      rwa [add_sub_cancel_right] at h
    · change x ∈ _
      have h := add_mem (hm 4) (ht _)
      change x - e + e ∈ _ at h
      rwa [sub_add_cancel] at h

/-- A point in both joins of a meet that equals `point m`, and not algebraic over `k`, has the
same singleton closure as `m`. -/
private theorem racl_singleton_eq_of_mem_meet {p₁ p₂ q₁ q₂ m w : K}
    (hmeet : (ClosedIF.point k p₁ ⊔ ClosedIF.point k p₂) ⊓
      (ClosedIF.point k q₁ ⊔ ClosedIF.point k q₂) = ClosedIF.point k m)
    (hp : w ∈ racl k ({p₁, p₂} : Set K)) (hq : w ∈ racl k ({q₁, q₂} : Set K))
    (hw : w ∉ racl k (∅ : Set K)) :
    racl k ({w} : Set K) = racl k ({m} : Set K) := by
  have hwm : w ∈ racl k ({m} : Set K) := by
    have h : w ∈ (ClosedIF.point k p₁ ⊔ ClosedIF.point k p₂) ⊓
        (ClosedIF.point k q₁ ⊔ ClosedIF.point k q₂) :=
      ClosedIF.mem_inf_iff.2 ⟨ClosedIF.mem_sup_point_iff.2 hp, ClosedIF.mem_sup_point_iff.2 hq⟩
    rw [hmeet] at h
    exact ClosedIF.mem_point.1 h
  have hmw : m ∈ racl k (insert w (∅ : Set K)) := racl_exchange (by simpa using hwm) hw
  exact racl_singleton_congr hwm (by simpa using hmw)

/-- The soundness meets `D`, `F` and `R` of the table, `qWitness_meet_D`, `qWitness_meet_F` and
`qWitness_meet_R`, stated with explicit points for arbitrary independent coordinates.  Stating
them once for variables lets the starred table instantiate them by substitution. -/
private theorem table_meets_D_F_R {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) :
    (ClosedIF.point k b ⊔ ClosedIF.point k (a * x + b)) ⊓
        (ClosedIF.point k a ⊔ ClosedIF.point k x) = ClosedIF.point k (a * x) ∧
      (ClosedIF.point k (a * c) ⊔ ClosedIF.point k x) ⊓
        (ClosedIF.point k c ⊔ ClosedIF.point k (a * x)) = ClosedIF.point k (a * c * x) ∧
      (ClosedIF.point k (a * c * x) ⊔ ClosedIF.point k (c * (a * x + b) + d)) ⊓
        (ClosedIF.point k (a * c) ⊔ ClosedIF.point k (b * c + d)) =
          ClosedIF.point k (b * c + d) :=
  ⟨qWitness_meet_D hind, qWitness_meet_F hind, qWitness_meet_R hind⟩


/-- An element algebraic over two elements of `acl(S)` lies in `acl(S)`. -/
private theorem shifted_pair_mem_racl {u v w : K} {S : Set K} (hu : u ∈ racl k S)
    (hv : v ∈ racl k S) (hw : w ∈ racl k ({u, v} : Set K)) : w ∈ racl k S :=
  racl_le_of_subset_racl (Set.insert_subset_iff.2 ⟨hu, Set.singleton_subset_iff.2 hv⟩) hw

/-- The `D` transport: with `x = xs + e` and `a x + b = ys + e` for a constant `e`, a point `δ`
with the incidences of `D` lies in `P ∨ Y` and `S ∨ X` of the starred table. -/
private theorem shifted_meet_D {a b x p δ e bs xs ys : K} (he : e ∈ racl k (∅ : Set K))
    (hx : x = xs + e) (hy : a * x + b = ys + e)
    (hD : (ClosedIF.point k bs ⊔ ClosedIF.point k ys) ⊓
      (ClosedIF.point k a ⊔ ClosedIF.point k xs) = ClosedIF.point k (a * xs))
    (hpb : p ∈ racl k ({bs} : Set K))
    (hδx : δ ∈ racl k ({a, x} : Set K)) (hδy : δ ∈ racl k ({p, a * x + b} : Set K))
    (hδa : δ ∉ racl k ({a} : Set K)) :
    racl k ({δ} : Set K) = racl k ({a * xs} : Set K) := by
  have hbs : bs ∈ racl k ({bs, ys} : Set K) := subset_racl k _ (Set.mem_insert _ _)
  have hys : ys ∈ racl k ({bs, ys} : Set K) := subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hp : p ∈ racl k ({bs, ys} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 hbs) hpb
  have hY : a * x + b ∈ racl k ({bs, ys} : Set K) := by
    rw [hy]
    exact add_mem hys (racl_mono (Set.empty_subset _) he)
  have ha : a ∈ racl k ({a, xs} : Set K) := subset_racl k _ (Set.mem_insert _ _)
  have hxs : xs ∈ racl k ({a, xs} : Set K) := subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hX : x ∈ racl k ({a, xs} : Set K) := by
    rw [hx]
    exact add_mem hxs (racl_mono (Set.empty_subset _) he)
  exact racl_singleton_eq_of_mem_meet hD (shifted_pair_mem_racl hp hY hδy)
    (shifted_pair_mem_racl ha hX hδx) (fun h ↦ hδa (racl_mono (Set.empty_subset _) h))

/-- The `F` transport: with `x = xs + e` for a constant `e` and `δ ∈ acl(a xs)`, a point `f`
with the incidences of `F` lies in `U ∨ X` and `T ∨ D` of the starred table. -/
private theorem shifted_meet_F {a c x δ f e xs : K} (he : e ∈ racl k (∅ : Set K))
    (hx : x = xs + e)
    (hF : (ClosedIF.point k (a * c) ⊔ ClosedIF.point k xs) ⊓
      (ClosedIF.point k c ⊔ ClosedIF.point k (a * xs)) = ClosedIF.point k (a * c * xs))
    (hδD : δ ∈ racl k ({a * xs} : Set K))
    (hf : f ∈ racl k ({c, δ} : Set K)) (hfm : f ∈ racl k ({a * c, x} : Set K))
    (hfu : f ∉ racl k ({a * c} : Set K)) :
    racl k ({f} : Set K) = racl k ({a * c * xs} : Set K) := by
  have hac : a * c ∈ racl k ({a * c, xs} : Set K) := subset_racl k _ (Set.mem_insert _ _)
  have hxs : xs ∈ racl k ({a * c, xs} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hX : x ∈ racl k ({a * c, xs} : Set K) := by
    rw [hx]
    exact add_mem hxs (racl_mono (Set.empty_subset _) he)
  have hc : c ∈ racl k ({c, a * xs} : Set K) := subset_racl k _ (Set.mem_insert _ _)
  have hax : a * xs ∈ racl k ({c, a * xs} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hδ : δ ∈ racl k ({c, a * xs} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 hax) hδD
  exact racl_singleton_eq_of_mem_meet hF (shifted_pair_mem_racl hac hX hfm)
    (shifted_pair_mem_racl hc hδ hf) (fun h ↦ hfu (racl_mono (Set.empty_subset _) h))

/-- The `R` transport: with `Z = zs + e` and `W = ws - a c e + e` for a constant `e` and
`f ∈ acl(a c xs)`, a point `r` with the incidences of `R` lies in `F ∨ Z` and `C` of the starred
table, and `ws` differs from `W + a c e` by the constant `e`. -/
private theorem shifted_meet_R {a c f r e xs zs ws Z W : K} (he : e ∈ racl k (∅ : Set K))
    (hz : Z = zs + e) (hw : W = ws - a * c * e + e)
    (hR : (ClosedIF.point k (a * c * xs) ⊔ ClosedIF.point k zs) ⊓
      (ClosedIF.point k (a * c) ⊔ ClosedIF.point k ws) = ClosedIF.point k ws)
    (hfF : f ∈ racl k ({a * c * xs} : Set K))
    (hrFZ : r ∈ racl k ({f, Z} : Set K)) (hrC : r ∈ racl k ({a * c, W} : Set K))
    (hr0 : r ∉ racl k (∅ : Set K)) :
    racl k ({r} : Set K) = racl k ({W + a * c * e} : Set K) := by
  have ht (S : Set K) : e ∈ racl k S := racl_mono (Set.empty_subset S) he
  have hF : a * c * xs ∈ racl k ({a * c * xs, zs} : Set K) :=
    subset_racl k _ (Set.mem_insert _ _)
  have hzs : zs ∈ racl k ({a * c * xs, zs} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hf : f ∈ racl k ({a * c * xs, zs} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 hF) hfF
  have hZ : Z ∈ racl k ({a * c * xs, zs} : Set K) := by
    rw [hz]
    exact add_mem hzs (ht _)
  have hac : a * c ∈ racl k ({a * c, ws} : Set K) := subset_racl k _ (Set.mem_insert _ _)
  have hws : ws ∈ racl k ({a * c, ws} : Set K) := subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hW : W ∈ racl k ({a * c, ws} : Set K) := by
    rw [hw]
    exact add_mem (sub_mem hws (mul_mem hac (ht _))) (ht _)
  have hrw := racl_singleton_eq_of_mem_meet hR (shifted_pair_mem_racl hf hZ hrFZ)
    (shifted_pair_mem_racl hac hW hrC) hr0
  rw [hrw]
  have hW' : W + a * c * e ∈ racl k ({W + a * c * e} : Set K) := subset_racl k _ rfl
  have hws' : ws ∈ racl k ({ws} : Set K) := subset_racl k _ rfl
  refine racl_singleton_congr ?_ ?_
  · have heq : ws = W + a * c * e - e := by
      rw [hw]
      ring
    rw [heq]
    exact sub_mem hW' (ht _)
  · have heq : W + a * c * e = ws + e := by
      rw [hw]
      ring
    rw [heq]
    exact add_mem hws' (ht _)

/-- **The meets `D`, `F` and `R` after normalizing `P`** (#27).  Let `a, b, c, d, x` be
independent, `κ ∈ k`, and suppose `acl(p) = acl(b + (a - 1) κ)`.  If `δ` has the incidences of
the meet `D = (P ∨ Y) ∧ (S ∨ X)`, `f` those of `F = (U ∨ X) ∧ (T ∨ D)` and `r` those of
`R = (F ∨ Z) ∧ C`, then `δ`, `f` and `r` are interalgebraic with `a (x - κ)`, `a c (x - κ)` and
`b c + d + a c κ`.  These are the table entries for the coordinates translated by `κ`. -/
theorem racl_shifted_D_F_R_of_normalized_P {a b c d x p δ f r : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) (κ : k)
    (hP : racl k ({p} : Set K) =
      racl k ({b + (a - 1) * algebraMap k K κ} : Set K))
    (hδx : δ ∈ racl k ({a, x} : Set K))
    (hδy : δ ∈ racl k ({p, a * x + b} : Set K))
    (hδa : δ ∉ racl k ({a} : Set K))
    (hf : f ∈ racl k ({c, δ} : Set K))
    (hfm : f ∈ racl k ({a * c, x} : Set K))
    (hfu : f ∉ racl k ({a * c} : Set K))
    (hrFZ : r ∈ racl k ({f, c * (a * x + b) + d} : Set K))
    (hrC : r ∈ racl k ({a * c, b * c + d} : Set K))
    (hr0 : r ∉ racl k (∅ : Set K)) :
    racl k ({δ} : Set K) = racl k ({a * (x - algebraMap k K κ)} : Set K) ∧
      racl k ({f} : Set K) = racl k ({a * c * (x - algebraMap k K κ)} : Set K) ∧
      racl k ({r} : Set K) =
        racl k ({b * c + d + a * c * algebraMap k K κ} : Set K) := by
  have hstar := algebraicIndependent_table_shift hind κ
  obtain ⟨e, he⟩ : ∃ e, algebraMap k K κ = e := ⟨_, rfl⟩
  rw [he] at hstar hP
  rw [he]
  have he0 : e ∈ racl k (∅ : Set K) := by
    rw [← he]
    exact (racl k (∅ : Set K)).algebraMap_mem κ
  -- The starred meets: the soundness meets of the table, instantiated by substitution.
  obtain ⟨hD, hF, hR⟩ := table_meets_D_F_R hstar
  have hpb : p ∈ racl k ({b + (a - 1) * e} : Set K) := by
    rw [← hP]
    exact subset_racl k _ rfl
  have hDeq := shifted_meet_D he0 (by ring) (by ring) hD hpb hδx hδy hδa
  have hδD : δ ∈ racl k ({a * (x - e)} : Set K) := by
    rw [← hDeq]
    exact subset_racl k _ rfl
  have hFeq := shifted_meet_F he0 (by ring) hF hδD hf hfm hfu
  have hfF : f ∈ racl k ({a * c * (x - e)} : Set K) := by
    rw [← hFeq]
    exact subset_racl k _ rfl
  exact ⟨hDeq, hFeq, shifted_meet_R he0 (by ring) (by ring) hR hfF hrFZ hrC hr0⟩

end

end AclGeom
