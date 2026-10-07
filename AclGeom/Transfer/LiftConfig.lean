/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.Multiplication
import AclGeom.Transfer.Lift

/-!
# Lifting and reflecting configurations along `ι : K →ₐ[k] Ω`

The configuration predicates `IsPartialQuadrangle`, `Ψ`, `QGeom`, `MulDiagram` and `Q′Geom` along
the lift of points `liftPoint` of `AclGeom.Transfer.Lift`, over a base `K₀` of elements algebraic
over `k`.

* **Lift** (`K/k → Ω/K₀`; preserved from the independently checked point-descent draft):
  `IsPartialQuadrangle.lift`, `QWitness.lift`, `QWitness.Psi.lift`, `QGeom.lift`,
  `MulDiagram.lift`, `Q'Geom.lift`.
* **Reflection** (`Ω/K₀ → K/k`, for configurations of lifted points): `IsPartialQuadrangle.of_lift`,
  `MulDiagram.of_lift`, `QWitness.Psi.of_lift` (with explicitly lifted clause-(vi) witnesses) and
  `QGeom.of_lift_witness`.  These provide explicit-instance reflection for the planned #25
  `Counterexamples.QDescent` consumer, with the clause-(vi) witnesses supplied over `K`.

The module needs only the lift of `AclGeom.Transfer.Lift` and the configuration language; no
completeness hypothesis (`JAssembly`) enters.

**Status:** the listed lifts and explicit-instance reflections are proved. General witness
descent and the concrete #25 refutations remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω] [Algebra k K]
  [Algebra k Ω] {K₀ : IntermediateField k Ω}
  (halg : ∀ y ∈ K₀, IsAlgebraic k y) (ι : K →ₐ[k] Ω)

/-- The join of two points is the closure of their representatives. -/
theorem coe_sup_point_val (P Q : Point k K) :
    ((P.1 ⊔ Q.1).1 : IntermediateField k K) = racl k {P.rep, Q.rep} := by
  have h := coe_sup_point₂ (k := k) P.rep Q.rep
  rwa [P.point_rep, Q.point_rep] at h

/-- Lifting a six-point vector entrywise. -/
theorem liftPoint_comp_vec₆ (a b c d e f : Point k K) :
    liftPoint halg ι ∘ ![a, b, c, d, e, f] =
      ![liftPoint halg ι a, liftPoint halg ι b, liftPoint halg ι c,
        liftPoint halg ι d, liftPoint halg ι e, liftPoint halg ι f] := by
  funext i
  fin_cases i <;> rfl

/-- Lifting an eight-point vector entrywise. -/
theorem liftPoint_comp_vec₈ (a b c d e f g h : Point k K) :
    liftPoint halg ι ∘ ![a, b, c, d, e, f, g, h] =
      ![liftPoint halg ι a, liftPoint halg ι b, liftPoint halg ι c,
        liftPoint halg ι d, liftPoint halg ι e, liftPoint halg ι f,
        liftPoint halg ι g, liftPoint halg ι h] := by
  funext i
  fin_cases i <;> rfl

include halg

/-- Partial quadrangles are absolute under the lift. -/
theorem IsPartialQuadrangle.lift {f : Fin 6 → Point k K}
    (h : IsPartialQuadrangle f) : IsPartialQuadrangle (liftPoint halg ι ∘ f) where
  injective := (liftPoint_injective halg ι).comp h.injective
  rank_dep s hs := by
    have := (rankEq_liftClosed_iff halg ι).2 (h.rank_dep s hs)
    rwa [liftClosed_finset_sup halg ι] at this
  rank_free s hs hns := by
    have := (rankEq_liftClosed_iff halg ι).2 (h.rank_free s hs hns)
    rwa [liftClosed_finset_sup halg ι] at this
  rank_total := by
    have := (rankEq_liftClosed_iff halg ι).2 h.rank_total
    rwa [liftClosed_finset_sup halg ι] at this

namespace QWitness

/-- The lift of a `Q`-witness: all twenty-one points lifted. -/
def lift (w : QWitness k K) : QWitness (↥K₀) Ω where
  A₁ := liftPoint halg ι w.A₁
  A₂ := liftPoint halg ι w.A₂
  B₁ := liftPoint halg ι w.B₁
  B₂ := liftPoint halg ι w.B₂
  C₁ := liftPoint halg ι w.C₁
  C₂ := liftPoint halg ι w.C₂
  D := liftPoint halg ι w.D
  E := liftPoint halg ι w.E
  F := liftPoint halg ι w.F
  G := liftPoint halg ι w.G
  H := liftPoint halg ι w.H
  I := liftPoint halg ι w.I
  P := liftPoint halg ι w.P
  Q := liftPoint halg ι w.Q
  R := liftPoint halg ι w.R
  S := liftPoint halg ι w.S
  T := liftPoint halg ι w.T
  U := liftPoint halg ι w.U
  X := liftPoint halg ι w.X
  Y := liftPoint halg ι w.Y
  Z := liftPoint halg ι w.Z

variable (w : QWitness k K)

/-- The `A`-join of a lifted witness is the lift of the `A`-join. -/
theorem lift_A : (w.lift halg ι).A = liftClosed K₀ ι w.A :=
  (liftClosed_sup halg ι _ _).symm

/-- The `B`-join of a lifted witness is the lift of the `B`-join. -/
theorem lift_B : (w.lift halg ι).B = liftClosed K₀ ι w.B :=
  (liftClosed_sup halg ι _ _).symm

/-- The `C`-join of a lifted witness is the lift of the `C`-join. -/
theorem lift_C : (w.lift halg ι).C = liftClosed K₀ ι w.C :=
  (liftClosed_sup halg ι _ _).symm

/-- A universal atom clause of `Ψ(iv)` for a rank-two join `P₁ ∨ P₂` lifts
to `Ω/K₀`. -/
theorem free_lift [IsAlgClosed Ω] {P₁ P₂ X Y : Point k K}
    (h : ∀ A' : Point k K, A'.1 ≤ P₁.1 ⊔ P₂.1 → ¬ X.1 ≤ A'.1 ⊔ Y.1) :
    ∀ A'' : Point (↥K₀) Ω, A''.1 ≤ liftClosed K₀ ι (P₁.1 ⊔ P₂.1) →
      ¬ (liftPoint halg ι X).1 ≤ A''.1 ⊔ (liftPoint halg ι Y).1 := by
  intro A'' hA'' hcap
  obtain ⟨A', h1, h2⟩ := exists_point_of_lift halg ι
    (Set.toFinite {P₁.rep, P₂.rep}) (coe_sup_point_val P₁ P₂)
    ⟨A'', hA'', hcap⟩
  exact h A' h1 h2

/-- **Lift of `Ψ`** (blueprint Theorem `j-descent`, `(4) ⇒ (3)` for `Q`):
rank, join, meet and incidence clauses are absolute; the atom clauses
transfer by the one-quantifier transfer. -/
theorem Psi.lift [IsAlgClosed Ω] {w : QWitness k K} (h : w.Psi) :
    (w.lift halg ι).Psi := by
  have hsup := fun E F ↦ (liftClosed_sup halg ι E F).symm
  have hinf := fun E F ↦ (liftClosed_inf halg ι E F).symm
  have hle := fun E F ↦ liftClosed_le_liftClosed_iff halg ι (E := E) (F := F)
  have hrk := fun n E ↦ rankEq_liftClosed_iff halg ι (n := n) (E := E)
  have heq := fun E F ↦ (liftClosed_injective halg ι).eq_iff (a := E) (b := F)
  have hA := w.lift_A halg ι
  have hB := w.lift_B halg ι
  have hC := w.lift_C halg ι
  refine
    { rank_ABC := ?_, rank_AB := ?_, rank_BC := ?_, rank_AC := ?_
      X_le := ?_, Z_le := ?_, X_notLe := ?_, Y_notLe := ?_, Z_notLe := ?_
      X_free := ?_, Z_freeB := ?_, Z_freeC := ?_
      S_le := ?_, T_le := ?_, U_le := ?_, rank_STU := ?_, quad := ?_
      meet_D := ?_, meet_E := ?_, meet_F := ?_, meet_G := ?_, meet_I := ?_
      meet_H := ?_, meet_R := ?_ } <;>
    (try simp only [hA, hB, hC]) <;> (try dsimp only [QWitness.lift, liftPoint_val])
  · rw [hsup, hsup, hrk]; exact h.rank_ABC
  · rw [hsup, hrk]; exact h.rank_AB
  · rw [hsup, hrk]; exact h.rank_BC
  · rw [hsup, hrk]; exact h.rank_AC
  · rw [hsup, hle]; exact h.X_le
  · rw [hsup, hsup, hinf, hle]; exact h.Z_le
  · rw [hsup, hsup, hle]; exact h.X_notLe
  · rw [hsup, hsup, hle]; exact h.Y_notLe
  · rw [hsup, hsup, hle]; exact h.Z_notLe
  · exact free_lift halg ι h.X_free
  · exact free_lift halg ι h.Z_freeB
  · exact free_lift halg ι h.Z_freeC
  · rw [hle]; exact h.S_le
  · rw [hle]; exact h.T_le
  · rw [hle]; exact h.U_le
  · rw [hsup, hsup, hrk]; exact h.rank_STU
  · obtain ⟨S', T', U', hq⟩ := h.quad
    refine ⟨liftPoint halg ι S', liftPoint halg ι T', liftPoint halg ι U', ?_⟩
    have := hq.lift halg ι
    rwa [liftPoint_comp_vec₆] at this
  · rw [hsup, hsup, hinf, heq]; exact h.meet_D
  · rw [hsup, hsup, hinf, heq]; exact h.meet_E
  · rw [hsup, hsup, hinf, heq]; exact h.meet_F
  · rw [hsup, hsup, hinf, heq]; exact h.meet_G
  · rw [hsup, hsup, hinf, heq]; exact h.meet_I
  · rw [hsup, hinf, heq]; exact h.meet_H
  · rw [hsup, hinf, heq]; exact h.meet_R

end QWitness

/-- Geometric `Q` lifts to `Ω/K₀`. -/
theorem QGeom.lift [IsAlgClosed Ω] {P D Y I : Point k K} (h : QGeom P D Y I) :
    QGeom (liftPoint halg ι P) (liftPoint halg ι D) (liftPoint halg ι Y)
      (liftPoint halg ι I) := by
  obtain ⟨w, hw, rfl, rfl, rfl, rfl⟩ := h
  exact ⟨w.lift halg ι, hw.lift halg ι, rfl, rfl, rfl, rfl⟩

/-- The multiplication diagram is absolute under the lift. -/
theorem MulDiagram.lift {X Y V E A₀ B₀ C₀ D₀ : Point k K}
    (h : MulDiagram X Y V E A₀ B₀ C₀ D₀) :
    MulDiagram (liftPoint halg ι X) (liftPoint halg ι Y) (liftPoint halg ι V)
      (liftPoint halg ι E) (liftPoint halg ι A₀) (liftPoint halg ι B₀)
      (liftPoint halg ι C₀) (liftPoint halg ι D₀) := by
  have hsup := fun E F ↦ (liftClosed_sup halg ι E F).symm
  have hrk := fun n E ↦ rankEq_liftClosed_iff halg ι (n := n) (E := E)
  refine
    { distinct := ?_, line_XAB := ?_, line_AYC := ?_, line_AED := ?_
      line_BYD := ?_, line_XCD := ?_, line_BCV := ?_, line_XYEV := ?_
      rank_XYA := ?_ } <;> (try dsimp only [liftPoint_val])
  · rw [← liftPoint_comp_vec₈]
    exact (liftPoint_injective halg ι).comp h.distinct
  · rw [hsup, hsup, hrk]; exact h.line_XAB
  · rw [hsup, hsup, hrk]; exact h.line_AYC
  · rw [hsup, hsup, hrk]; exact h.line_AED
  · rw [hsup, hsup, hrk]; exact h.line_BYD
  · rw [hsup, hsup, hrk]; exact h.line_XCD
  · rw [hsup, hsup, hrk]; exact h.line_BCV
  · rw [hsup, hsup, hsup, hrk]; exact h.line_XYEV
  · rw [hsup, hsup, hrk]; exact h.rank_XYA

/-- Geometric `Q′` lifts to `Ω/K₀`. -/
theorem Q'Geom.lift [IsAlgClosed Ω] {X Y S E : Point k K} (h : Q'Geom X Y S E) :
    Q'Geom (liftPoint halg ι X) (liftPoint halg ι Y) (liftPoint halg ι S)
      (liftPoint halg ι E) := by
  obtain ⟨V, A₀, B₀, C₀, D₀, hQ, hM⟩ := h
  exact ⟨_, _, _, _, _, hQ.lift halg ι, hM.lift halg ι⟩

/-! ### Reflection along the lift

The converses of the lifts above, for configurations whose points are all lifts of points of `K/k`.
Rank, order, join and meet clauses reflect because the lift is an order embedding that preserves
joins, meets (for algebraically closed `Ω`) and exact rank.  The universal atom clauses of `Ψ(iv)`
reflect by instantiating the `Ω`-statement at lifted atoms.  The existential clause `Ψ(vi)` is NOT
reflected in general: its partial-quadrangle witnesses must be supplied as lifts (`hq`).  No
general descent of witnesses is claimed. -/

/-- Partial quadrangles of lifted points are reflected by the lift. -/
theorem IsPartialQuadrangle.of_lift {f : Fin 6 → Point k K}
    (h : IsPartialQuadrangle (liftPoint halg ι ∘ f)) : IsPartialQuadrangle f where
  injective := h.injective.of_comp
  rank_dep s hs := (rankEq_liftClosed_iff halg ι).1 <| by
    rw [liftClosed_finset_sup halg ι]
    exact h.rank_dep s hs
  rank_free s hs hns := (rankEq_liftClosed_iff halg ι).1 <| by
    rw [liftClosed_finset_sup halg ι]
    exact h.rank_free s hs hns
  rank_total := (rankEq_liftClosed_iff halg ι).1 <| by
    rw [liftClosed_finset_sup halg ι]
    exact h.rank_total

/-- A multiplication diagram of lifted points is reflected by the lift. -/
theorem MulDiagram.of_lift {X Y V E A₀ B₀ C₀ D₀ : Point k K}
    (h : MulDiagram (liftPoint halg ι X) (liftPoint halg ι Y) (liftPoint halg ι V)
      (liftPoint halg ι E) (liftPoint halg ι A₀) (liftPoint halg ι B₀)
      (liftPoint halg ι C₀) (liftPoint halg ι D₀)) :
    MulDiagram X Y V E A₀ B₀ C₀ D₀ := by
  have hrk := fun n E ↦ rankEq_liftClosed_iff halg ι (n := n) (E := E)
  have push := liftClosed_sup halg ι
  refine
    { distinct := ?_, line_XAB := ?_, line_AYC := ?_, line_AED := ?_
      line_BYD := ?_, line_XCD := ?_, line_BCV := ?_, line_XYEV := ?_
      rank_XYA := ?_ }
  · have hd := h.distinct
    rw [← liftPoint_comp_vec₈] at hd
    exact hd.of_comp
  · rw [← hrk]; simp only [push]; exact h.line_XAB
  · rw [← hrk]; simp only [push]; exact h.line_AYC
  · rw [← hrk]; simp only [push]; exact h.line_AED
  · rw [← hrk]; simp only [push]; exact h.line_BYD
  · rw [← hrk]; simp only [push]; exact h.line_XCD
  · rw [← hrk]; simp only [push]; exact h.line_BCV
  · rw [← hrk]; simp only [push]; exact h.line_XYEV
  · rw [← hrk]; simp only [push]; exact h.rank_XYA

namespace QWitness

/-- **Reflection of `Ψ` along the lift**, with explicitly lifted partial-quadrangle witnesses.  If
the lift of a `K`-witness satisfies `Ψ` over `Ω/K₀`, and the partial quadrangle of clause (vi) is
the lift of `(S, T, U, S', T', U')`, then the `K`-witness satisfies `Ψ` over `K/k`. -/
theorem Psi.of_lift [IsAlgClosed Ω] {w : QWitness k K} (h : (w.lift halg ι).Psi)
    {S' T' U' : Point k K}
    (hq : IsPartialQuadrangle (liftPoint halg ι ∘ ![w.S, w.T, w.U, S', T', U'])) : w.Psi := by
  have hle := fun E F ↦ liftClosed_le_liftClosed_iff halg ι (E := E) (F := F)
  have hrk := fun n E ↦ rankEq_liftClosed_iff halg ι (n := n) (E := E)
  have heq := fun E F ↦ (liftClosed_injective halg ι).eq_iff (a := E) (b := F)
  have push := liftClosed_sup halg ι
  have pushInf := liftClosed_inf halg ι
  have hA := w.lift_A halg ι
  have hB := w.lift_B halg ι
  have hC := w.lift_C halg ι
  refine
    { rank_ABC := ?_, rank_AB := ?_, rank_BC := ?_, rank_AC := ?_
      X_le := ?_, Z_le := ?_, X_notLe := ?_, Y_notLe := ?_, Z_notLe := ?_
      X_free := ?_, Z_freeB := ?_, Z_freeC := ?_
      S_le := ?_, T_le := ?_, U_le := ?_, rank_STU := ?_
      quad := ⟨S', T', U', IsPartialQuadrangle.of_lift halg ι hq⟩
      meet_D := ?_, meet_E := ?_, meet_F := ?_, meet_G := ?_, meet_I := ?_
      meet_H := ?_, meet_R := ?_ }
  -- (i) ranks
  · rw [← hrk]; simp only [push, ← hA, ← hB, ← hC]; exact h.rank_ABC
  · rw [← hrk]; simp only [push, ← hA, ← hB]; exact h.rank_AB
  · rw [← hrk]; simp only [push, ← hB, ← hC]; exact h.rank_BC
  · rw [← hrk]; simp only [push, ← hA, ← hC]; exact h.rank_AC
  -- (ii) incidences
  · rw [← hle]; simp only [push, ← hA]; exact h.X_le
  · rw [← hle]; simp only [push, pushInf, ← hB, ← hC]; exact h.Z_le
  -- (iii) non-incidences
  · rw [← hle]; simp only [push, ← hA, ← hB, ← hC]; exact h.X_notLe
  · rw [← hle]; simp only [push, ← hA, ← hB, ← hC]; exact h.Y_notLe
  · rw [← hle]; simp only [push, ← hA, ← hB, ← hC]; exact h.Z_notLe
  -- (iv) universal atom clauses, instantiated at lifted atoms
  · intro A' hA' hX
    refine h.X_free (liftPoint halg ι A') ?_ ?_
    · rw [hA]; exact (hle _ _).2 hA'
    · have hl := (hle _ _).2 hX
      rw [push] at hl
      exact hl
  · intro B' hB' hZ
    refine h.Z_freeB (liftPoint halg ι B') ?_ ?_
    · rw [hB]; exact (hle _ _).2 hB'
    · have hl := (hle _ _).2 hZ
      rw [push] at hl
      exact hl
  · intro C' hC' hZ
    refine h.Z_freeC (liftPoint halg ι C') ?_ ?_
    · rw [hC]; exact (hle _ _).2 hC'
    · have hl := (hle _ _).2 hZ
      rw [push] at hl
      exact hl
  -- (v) the triple `(S, T, U)`
  · rw [← hle, ← hA]; exact h.S_le
  · rw [← hle, ← hB]; exact h.T_le
  · rw [← hle, ← hC]; exact h.U_le
  · rw [← hrk]; simp only [push]; exact h.rank_STU
  -- (vii) meets
  · rw [← heq]; simp only [push, pushInf]; exact h.meet_D
  · rw [← heq]; simp only [push, pushInf]; exact h.meet_E
  · rw [← heq]; simp only [push, pushInf]; exact h.meet_F
  · rw [← heq]; simp only [push, pushInf]; exact h.meet_G
  · rw [← heq]; simp only [push, pushInf]; exact h.meet_I
  · rw [← heq]; simp only [push, pushInf, ← hA]; exact h.meet_H
  · rw [← heq]; simp only [push, pushInf, ← hC]; exact h.meet_R

end QWitness

/-- **Geometric `Q` descends along the lift of an explicit witness** (the named consumer is the
geometric half of the #25 refutation, `qGeom_rat`): if the lift of a `K`-witness satisfies `Ψ` over
`Ω/K₀` and the clause-(vi) quadrangle is supplied as a lift, then geometric `Q` holds over `K/k`. -/
theorem QGeom.of_lift_witness [IsAlgClosed Ω] (w : QWitness k K) (h : (w.lift halg ι).Psi)
    {S' T' U' : Point k K}
    (hq : IsPartialQuadrangle (liftPoint halg ι ∘ ![w.S, w.T, w.U, S', T', U'])) :
    QGeom w.P w.D w.Y w.I :=
  ⟨w, QWitness.Psi.of_lift halg ι h hq, rfl, rfl, rfl, rfl⟩

end

end AclGeom
