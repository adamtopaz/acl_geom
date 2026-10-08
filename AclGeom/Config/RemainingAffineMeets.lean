/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.MeetEquations
import AclGeom.Geometry.Representatives

/-!
# The meets `G`, `H`, `I` and `E` after normalizing `P` and `Q`

Let `a, b, c, d, x` be independent and let `η ∈ k`.  Translating by `η` gives the shifted table
coordinates `b' = b - η` and `d' = d + (c - 1) η`, with `a`, `c` and `x` unchanged.  Then
`b' c + d' = b c + d - η`, `a x + b' = a x + b - η` and `c (a x + b') + d' = c (a x + b) + d - η`,
so the points `P`, `R`, `Y` and `Z` of the table keep their closures.

* `algebraicIndependent_table_Q_shift`: the shifted coordinates are again independent.
* `racl_shifted_G_H_I_E_of_normalized_P_Q`: if `acl(p) = acl(b)`, `acl(q) = acl(d')` and
  `acl(r) = acl(b c + d)`, then points `g, h, i, e`, not algebraic over `k`, with the incidences
  of the meets `G = (P ∨ T) ∧ (Q ∨ R)`, `H = (U ∨ G) ∧ A`, `I = (H ∨ X) ∧ (P ∨ Y)` and
  `E = (T ∨ Y) ∧ (Q ∨ Z)` of `Ψ` are the shifted table entries `b' c`, `a / b'`, `a x / b'` and
  `c (a x + b')`.

The meets are the soundness meets `qWitness_meet_G`, `qWitness_meet_H`, `qWitness_meet_I` and
`qWitness_meet_E` of the shifted table, reused verbatim.  The meet `H` uses the plane
`A = acl(a, b)`, which the shift does not change.  The second theorem is conditional on the
normalized `P`, `Q` and `R`; it makes no uniqueness or common-shift claim.

**Status:** conditional `G/H/I/E` normalization proved (#27, P3b), with no ACF hypothesis.
The actual PRIVATE 274-line two-family consumer derives `P`, `D/F/R` and `Q` before these
four rows and final independence, under explicit base/ambient ACF, supplied fresh INPUT families,
strong `Q`-producer non-memberships and raw `I/E` incidences/nonconstancy. Both original curves
precede all corresponding inputs; no normal-form or output-freshness oracle. An actual PRIVATE
zero-origin example uses arbitrary raw representatives with no ACF. The initial action chart,
actual guarded-`Ψ` input derivation, input existence/enlargement/descent, combined generator
presentation, actions, extraction and completeness remain open; #11 and frozen117 are independent.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Translating `b` and `d` by a constant** (#27).  If `a, b, c, d, x` are independent and
`η ∈ k`, then so are `a`, `b - η`, `c`, `d + (c - 1) η` and `x`: the change of coordinates is
triangular with an inverse of the same form. -/
theorem algebraicIndependent_table_Q_shift {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) (η : k) :
    AlgebraicIndependent k ![a, b - algebraMap k K η,
      c, d + (c - 1) * algebraMap k K η, x] := by
  obtain ⟨t, ht⟩ : ∃ t, algebraMap k K η = t := ⟨_, rfl⟩
  rw [ht]
  have htS (S : Set K) : t ∈ racl k S := by
    rw [← ht]
    exact (racl k S).algebraMap_mem η
  refine AlgebraicIndependent.of_racl_range_eq hind (racl_range_eq_of_mem ?_ ?_)
  · have hm (i : Fin 5) : ![a, b, c, d, x] i ∈ racl k (Set.range ![a, b, c, d, x]) :=
      subset_racl k _ ⟨i, rfl⟩
    intro i
    fin_cases i
    · exact hm 0
    · exact sub_mem (hm 1) (htS _)
    · exact hm 2
    · exact add_mem (hm 3) (mul_mem (sub_mem (hm 2) (one_mem _)) (htS _))
    · exact hm 4
  · have hm (i : Fin 5) : ![a, b - t, c, d + (c - 1) * t, x] i ∈
        racl k (Set.range ![a, b - t, c, d + (c - 1) * t, x]) :=
      subset_racl k _ ⟨i, rfl⟩
    intro i
    fin_cases i
    · exact hm 0
    · change b ∈ _
      have h := add_mem (hm 1) (htS _)
      change b - t + t ∈ _ at h
      rwa [sub_add_cancel] at h
    · exact hm 2
    · change d ∈ _
      have h := sub_mem (hm 3) (mul_mem (sub_mem (hm 2) (one_mem _)) (htS _))
      change d + (c - 1) * t - (c - 1) * t ∈ _ at h
      rwa [add_sub_cancel_right] at h
    · exact hm 4

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

/-- The soundness meets `G`, `H`, `I` and `E` of the table, `qWitness_meet_G`,
`qWitness_meet_H`, `qWitness_meet_I` and `qWitness_meet_E`, stated with explicit points for
arbitrary independent coordinates.  Stating them once for variables lets the shifted table
instantiate them by substitution. -/
private theorem table_meets_G_H_I_E {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) :
    (ClosedIF.point k b ⊔ ClosedIF.point k c) ⊓
        (ClosedIF.point k d ⊔ ClosedIF.point k (b * c + d)) = ClosedIF.point k (b * c) ∧
      (ClosedIF.point k (a * c) ⊔ ClosedIF.point k (b * c)) ⊓
        (ClosedIF.point k a ⊔ ClosedIF.point k b) = ClosedIF.point k (a / b) ∧
      (ClosedIF.point k (a / b) ⊔ ClosedIF.point k x) ⊓
        (ClosedIF.point k b ⊔ ClosedIF.point k (a * x + b)) = ClosedIF.point k (a * x / b) ∧
      (ClosedIF.point k c ⊔ ClosedIF.point k (a * x + b)) ⊓
        (ClosedIF.point k d ⊔ ClosedIF.point k (c * (a * x + b) + d)) =
          ClosedIF.point k (c * (a * x + b)) :=
  ⟨qWitness_meet_G hind, qWitness_meet_H hind, qWitness_meet_I hind, qWitness_meet_E hind⟩

/-- An element algebraic over two elements of `acl(S)` lies in `acl(S)`. -/
private theorem shifted_pair_mem_racl {u v w : K} {S : Set K} (hu : u ∈ racl k S)
    (hv : v ∈ racl k S) (hw : w ∈ racl k ({u, v} : Set K)) : w ∈ racl k S :=
  racl_le_of_subset_racl (Set.insert_subset_iff.2 ⟨hu, Set.singleton_subset_iff.2 hv⟩) hw

/-- The `G` transport: with `B = bs + t` and `W = ws + t` for a constant `t`, and `p`, `q`, `r`
algebraic over `B`, `ds`, `W`, a point `g` with the incidences of `G` lies in `P ∨ T` and
`Q ∨ R` of the shifted table. -/
private theorem shifted_meet_G {c p q r g t B bs ds ws W : K} (ht : t ∈ racl k (∅ : Set K))
    (hb : B = bs + t) (hw : W = ws + t)
    (hG : (ClosedIF.point k bs ⊔ ClosedIF.point k c) ⊓
      (ClosedIF.point k ds ⊔ ClosedIF.point k ws) = ClosedIF.point k (bs * c))
    (hpB : p ∈ racl k ({B} : Set K)) (hqd : q ∈ racl k ({ds} : Set K))
    (hrW : r ∈ racl k ({W} : Set K))
    (hgP : g ∈ racl k ({p, c} : Set K)) (hgQ : g ∈ racl k ({q, r} : Set K))
    (hg0 : g ∉ racl k (∅ : Set K)) :
    racl k ({g} : Set K) = racl k ({bs * c} : Set K) := by
  have htS (S : Set K) : t ∈ racl k S := racl_mono (Set.empty_subset S) ht
  have hbs : bs ∈ racl k ({bs, c} : Set K) := subset_racl k _ (Set.mem_insert _ _)
  have hc : c ∈ racl k ({bs, c} : Set K) := subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hB : B ∈ racl k ({bs, c} : Set K) := by
    rw [hb]
    exact add_mem hbs (htS _)
  have hp : p ∈ racl k ({bs, c} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 hB) hpB
  have hds : ds ∈ racl k ({ds, ws} : Set K) := subset_racl k _ (Set.mem_insert _ _)
  have hws : ws ∈ racl k ({ds, ws} : Set K) := subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hq : q ∈ racl k ({ds, ws} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 hds) hqd
  have hW : W ∈ racl k ({ds, ws} : Set K) := by
    rw [hw]
    exact add_mem hws (htS _)
  have hr : r ∈ racl k ({ds, ws} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 hW) hrW
  exact racl_singleton_eq_of_mem_meet hG (shifted_pair_mem_racl hp hc hgP)
    (shifted_pair_mem_racl hq hr hgQ) hg0

/-- The `H` transport: with `B = bs + t` for a constant `t` and `g ∈ acl(bs c)`, a point `h`
with the incidences of `H` lies in `U ∨ G` and `A` of the shifted table. -/
private theorem shifted_meet_H {a c g h t B bs : K} (ht : t ∈ racl k (∅ : Set K))
    (hb : B = bs + t)
    (hH : (ClosedIF.point k (a * c) ⊔ ClosedIF.point k (bs * c)) ⊓
      (ClosedIF.point k a ⊔ ClosedIF.point k bs) = ClosedIF.point k (a / bs))
    (hgG : g ∈ racl k ({bs * c} : Set K))
    (hhU : h ∈ racl k ({a * c, g} : Set K)) (hhA : h ∈ racl k ({a, B} : Set K))
    (hh0 : h ∉ racl k (∅ : Set K)) :
    racl k ({h} : Set K) = racl k ({a / bs} : Set K) := by
  have hac : a * c ∈ racl k ({a * c, bs * c} : Set K) := subset_racl k _ (Set.mem_insert _ _)
  have hbc : bs * c ∈ racl k ({a * c, bs * c} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hg : g ∈ racl k ({a * c, bs * c} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 hbc) hgG
  have ha : a ∈ racl k ({a, bs} : Set K) := subset_racl k _ (Set.mem_insert _ _)
  have hbs : bs ∈ racl k ({a, bs} : Set K) := subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hB : B ∈ racl k ({a, bs} : Set K) := by
    rw [hb]
    exact add_mem hbs (racl_mono (Set.empty_subset _) ht)
  exact racl_singleton_eq_of_mem_meet hH (shifted_pair_mem_racl hac hg hhU)
    (shifted_pair_mem_racl ha hB hhA) hh0

/-- The `I` transport: with `B = bs + t` and `Y = ys + t` for a constant `t`, `h ∈ acl(a / bs)`
and `p` algebraic over `B`, a point `i` with the incidences of `I` lies in `H ∨ X` and `P ∨ Y`
of the shifted table. -/
private theorem shifted_meet_I {a x p h i t B Y bs ys : K} (ht : t ∈ racl k (∅ : Set K))
    (hb : B = bs + t) (hy : Y = ys + t)
    (hI : (ClosedIF.point k (a / bs) ⊔ ClosedIF.point k x) ⊓
      (ClosedIF.point k bs ⊔ ClosedIF.point k ys) = ClosedIF.point k (a * x / bs))
    (hhH : h ∈ racl k ({a / bs} : Set K)) (hpB : p ∈ racl k ({B} : Set K))
    (hiH : i ∈ racl k ({h, x} : Set K)) (hiP : i ∈ racl k ({p, Y} : Set K))
    (hi0 : i ∉ racl k (∅ : Set K)) :
    racl k ({i} : Set K) = racl k ({a * x / bs} : Set K) := by
  have htS (S : Set K) : t ∈ racl k S := racl_mono (Set.empty_subset S) ht
  have hm : a / bs ∈ racl k ({a / bs, x} : Set K) := subset_racl k _ (Set.mem_insert _ _)
  have hx : x ∈ racl k ({a / bs, x} : Set K) := subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hh : h ∈ racl k ({a / bs, x} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 hm) hhH
  have hbs : bs ∈ racl k ({bs, ys} : Set K) := subset_racl k _ (Set.mem_insert _ _)
  have hys : ys ∈ racl k ({bs, ys} : Set K) := subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hB : B ∈ racl k ({bs, ys} : Set K) := by
    rw [hb]
    exact add_mem hbs (htS _)
  have hp : p ∈ racl k ({bs, ys} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 hB) hpB
  have hY : Y ∈ racl k ({bs, ys} : Set K) := by
    rw [hy]
    exact add_mem hys (htS _)
  exact racl_singleton_eq_of_mem_meet hI (shifted_pair_mem_racl hh hx hiH)
    (shifted_pair_mem_racl hp hY hiP) hi0

/-- The `E` transport: with `Y = ys + t` and `Z = zs + t` for a constant `t` and `q` algebraic
over `ds`, a point `e` with the incidences of `E` lies in `T ∨ Y` and `Q ∨ Z` of the shifted
table. -/
private theorem shifted_meet_E {c q e t Y Z ys ds zs : K} (ht : t ∈ racl k (∅ : Set K))
    (hy : Y = ys + t) (hz : Z = zs + t)
    (hE : (ClosedIF.point k c ⊔ ClosedIF.point k ys) ⊓
      (ClosedIF.point k ds ⊔ ClosedIF.point k zs) = ClosedIF.point k (c * ys))
    (hqd : q ∈ racl k ({ds} : Set K))
    (heT : e ∈ racl k ({c, Y} : Set K)) (heQ : e ∈ racl k ({q, Z} : Set K))
    (he0 : e ∉ racl k (∅ : Set K)) :
    racl k ({e} : Set K) = racl k ({c * ys} : Set K) := by
  have htS (S : Set K) : t ∈ racl k S := racl_mono (Set.empty_subset S) ht
  have hc : c ∈ racl k ({c, ys} : Set K) := subset_racl k _ (Set.mem_insert _ _)
  have hys : ys ∈ racl k ({c, ys} : Set K) := subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hY : Y ∈ racl k ({c, ys} : Set K) := by
    rw [hy]
    exact add_mem hys (htS _)
  have hds : ds ∈ racl k ({ds, zs} : Set K) := subset_racl k _ (Set.mem_insert _ _)
  have hzs : zs ∈ racl k ({ds, zs} : Set K) := subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hq : q ∈ racl k ({ds, zs} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 hds) hqd
  have hZ : Z ∈ racl k ({ds, zs} : Set K) := by
    rw [hz]
    exact add_mem hzs (htS _)
  exact racl_singleton_eq_of_mem_meet hE (shifted_pair_mem_racl hc hY heT)
    (shifted_pair_mem_racl hq hZ heQ) he0

/-- **The meets `G`, `H`, `I` and `E` after normalizing `P` and `Q`** (#27).  Let
`a, b, c, d, x` be independent, `η ∈ k`, and suppose `acl(p) = acl(b)`,
`acl(q) = acl(d + (c - 1) η)` and `acl(r) = acl(b c + d)`.  If `g`, `h`, `i` and `e` are not
algebraic over `k` and have the incidences of the meets `G = (P ∨ T) ∧ (Q ∨ R)`,
`H = (U ∨ G) ∧ A`, `I = (H ∨ X) ∧ (P ∨ Y)` and `E = (T ∨ Y) ∧ (Q ∨ Z)`, then they are
interalgebraic with `(b - η) c`, `a / (b - η)`, `a x / (b - η)` and `c (a x + (b - η))`.  These
are the table entries for the coordinates `b - η` and `d + (c - 1) η`. -/
theorem racl_shifted_G_H_I_E_of_normalized_P_Q {a b c d x p q r g h i e : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) (η : k)
    (hP : racl k ({p} : Set K) = racl k ({b} : Set K))
    (hQ : racl k ({q} : Set K) =
      racl k ({d + (c - 1) * algebraMap k K η} : Set K))
    (hR : racl k ({r} : Set K) = racl k ({b * c + d} : Set K))
    (hgP : g ∈ racl k ({p, c} : Set K)) (hgQ : g ∈ racl k ({q, r} : Set K))
    (hg0 : g ∉ racl k (∅ : Set K))
    (hhU : h ∈ racl k ({a * c, g} : Set K))
    (hhA : h ∈ racl k ({a, b} : Set K)) (hh0 : h ∉ racl k (∅ : Set K))
    (hiH : i ∈ racl k ({h, x} : Set K))
    (hiP : i ∈ racl k ({p, a * x + b} : Set K))
    (hi0 : i ∉ racl k (∅ : Set K))
    (heT : e ∈ racl k ({c, a * x + b} : Set K))
    (heQ : e ∈ racl k ({q, c * (a * x + b) + d} : Set K))
    (he0 : e ∉ racl k (∅ : Set K)) :
    racl k ({g} : Set K) = racl k ({(b - algebraMap k K η) * c} : Set K) ∧
      racl k ({h} : Set K) = racl k ({a / (b - algebraMap k K η)} : Set K) ∧
      racl k ({i} : Set K) = racl k ({a * x / (b - algebraMap k K η)} : Set K) ∧
      racl k ({e} : Set K) =
        racl k ({c * (a * x + (b - algebraMap k K η))} : Set K) := by
  have hstar := algebraicIndependent_table_Q_shift hind η
  obtain ⟨t, ht⟩ : ∃ t, algebraMap k K η = t := ⟨_, rfl⟩
  rw [ht] at hstar hQ
  rw [ht]
  have ht0 : t ∈ racl k (∅ : Set K) := by
    rw [← ht]
    exact (racl k (∅ : Set K)).algebraMap_mem η
  -- The shifted meets: the soundness meets of the table, instantiated by substitution.
  obtain ⟨hG, hH, hI, hE⟩ := table_meets_G_H_I_E hstar
  have hpb : p ∈ racl k ({b} : Set K) := by
    rw [← hP]
    exact subset_racl k _ rfl
  have hqd : q ∈ racl k ({d + (c - 1) * t} : Set K) := by
    rw [← hQ]
    exact subset_racl k _ rfl
  have hrw : r ∈ racl k ({b * c + d} : Set K) := by
    rw [← hR]
    exact subset_racl k _ rfl
  have hGeq := shifted_meet_G ht0 (by ring) (by ring) hG hpb hqd hrw hgP hgQ hg0
  have hgG : g ∈ racl k ({(b - t) * c} : Set K) := by
    rw [← hGeq]
    exact subset_racl k _ rfl
  have hHeq := shifted_meet_H ht0 (by ring) hH hgG hhU hhA hh0
  have hhH : h ∈ racl k ({a / (b - t)} : Set K) := by
    rw [← hHeq]
    exact subset_racl k _ rfl
  exact ⟨hGeq, hHeq, shifted_meet_I ht0 (by ring) (by ring) hI hhH hpb hiH hiP hi0,
    shifted_meet_E ht0 (by ring) (by ring) hE hqd heT heQ he0⟩

end

end AclGeom
