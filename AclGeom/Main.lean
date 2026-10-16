/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.Completeness
import AclGeom.Reconstruct.Target
import AclGeom.Reconstruct.Uniqueness

/-!
# The public theorems

The reconstruction theorem in lattice form for chosen perfections (blueprint Thm `target`,
§Assembly).

* `Reconstructs π ρ φ Φ`: `Φ : K^perf ≃+* L^perf` reconstructs `φ : 𝒢(K/k) ≃o 𝒢(L/l)`, i.e.
  `(φ M)^perf = Φ(M^perf)` for every closed `M`.  This is the blueprint's `Reconstructs` record,
  as an alias of `Perfection.Induces`.
* `exists_reconstruction`: for relatively algebraically closed `K/k` and `L/l` with
  `trdeg(K/k) ≥ 5`, every order isomorphism `φ` has a reconstruction.
* `reconstruction_target`: the assembled statement.  It gives equal transcendence degrees, and a
  reconstruction `Φ` with `Φ(k^perf) = l^perf` and `φ(M) = Φ(M^perf) ∩ L`.  The reconstructions of
  `φ` are exactly the Frobenius twists of `Φ`: `Φ` is unique in characteristic zero, and the
  exponent is unique in positive characteristic.  Conversely, every isomorphism of perfections
  carrying `k^perf` onto `l^perf` reconstructs its transported lattice map.

The chosen perfections are arbitrary, with their own characteristic exponents.  The hypotheses
are exactly the blueprint's: relatively algebraically closed bases and `trdeg(K/k) ≥ 5`.  ACF
J-completeness of the two perfections' algebraic-closure pairs, needed by the existence proof,
is supplied by `jCompletenessACF` (`Config.Completeness`, #27).

**Status:** the public reconstruction relation, existence and the assembled lattice-form
target are proved (#9/#10) from the blueprint hypotheses alone. Reconstructs is a reducible
alias of Induces. Point-geometry reconstruction is proved in `Reconstruct.PointVariant`,
the automorphism exact sequence in `Variants`, and the literal and Frobenius-quotient
functors in `Functorial`. `Functorial.ChoiceIndependence` proves equivalence under changing
all perfection choices and agreement of the geometry functors. The full validation suite,
literal provenance items, true bypassed source statements and frozen M4a obligations
remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

universe u v

variable {k : Type*} {K : Type u} {l : Type*} {L : Type v} [Field k] [Field K] [Algebra k K]
  [Field l] [Field L] [Algebra l L]

/-- `Φ : K^perf ≃+* L^perf` **reconstructs** `φ : 𝒢(K/k) ≃o 𝒢(L/l)` (blueprint §Assembly,
record `Reconstructs`): `(φ M)^perf = Φ(M^perf)` for every closed `M`.  This is
`Perfection.Induces`. -/
abbrev Reconstructs (π : Perfection K) (ρ : Perfection L) (φ : ClosedIF k K ≃o ClosedIF l L)
    (Φ : π.carrier ≃+* ρ.carrier) : Prop :=
  π.Induces ρ φ Φ

/-- An inducing isomorphism of the chosen perfections, with both ACF J-completeness inputs of
`Perfection.exists_induces` supplied by `jCompletenessACF` at rank five. -/
private theorem exists_induces_of_five_le_trdeg (π : Perfection K) (ρ : Perfection L)
    (hk : IsRAC (⊥ : IntermediateField k K)) (hl : IsRAC (⊥ : IntermediateField l L))
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) (φ : ClosedIF k K ≃o ClosedIF l L) :
    ∃ Φ : π.carrier ≃+* ρ.carrier,
      CrossBase.Compatible (k := π.basePerf k) (l := ρ.basePerf l) Φ ∧ π.Induces ρ φ Φ := by
  have : IsAlgClosed ↥(algebraicClosure (↥(π.basePerf k)) (AlgebraicClosure π.carrier)) :=
    IsAlgClosure.isAlgClosed (↥(π.basePerf k))
  have : IsAlgClosed ↥(algebraicClosure (↥(ρ.basePerf l)) (AlgebraicClosure ρ.carrier)) :=
    IsAlgClosure.isAlgClosed (↥(ρ.basePerf l))
  exact π.exists_induces ρ hk hl htr
    (jCompletenessACF (five_le_trdeg_algebraicClosure
      (Perfection.five_le_trdeg_basePerf π (OrderIso.refl (ClosedIF k K)) htr)))
    (jCompletenessACF (five_le_trdeg_algebraicClosure
      (Perfection.five_le_trdeg_basePerf ρ φ htr))) φ

/-- **Existence of a reconstruction** (blueprint §Assembly, `exists_reconstruction`): for
relatively algebraically closed `K/k` and `L/l` with `trdeg(K/k) ≥ 5`, every order isomorphism
of closed-subfield lattices has a reconstruction between the chosen perfections. -/
theorem exists_reconstruction (π : Perfection K) (ρ : Perfection L)
    (hk : IsRAC (⊥ : IntermediateField k K)) (hl : IsRAC (⊥ : IntermediateField l L))
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) (φ : ClosedIF k K ≃o ClosedIF l L) :
    ∃ Φ : π.carrier ≃+* ρ.carrier, Reconstructs π ρ φ Φ :=
  (exists_induces_of_five_le_trdeg π ρ hk hl htr φ).imp fun _ h ↦ h.2

/-- **The reconstruction theorem in lattice form** (blueprint Thm `target`).  Let `K/k` and
`L/l` be relatively algebraically closed with `trdeg(K/k) ≥ 5`, and let
`φ : 𝒢(K/k) ≃o 𝒢(L/l)`.  Then:
* `K/k` and `L/l` have the same transcendence degree;
* some `Φ : K^perf ≃+* L^perf` carries `k^perf` onto `l^perf`, reconstructs `φ`, and satisfies
  `φ(M) = Φ(M^perf) ∩ L`;
* the reconstructions of `φ` are exactly the Frobenius twists `Frob^n ∘ Φ`.  `Φ` is the only one
  in characteristic zero, and the exponent `n` is unique in positive characteristic;
* conversely, every `Ψ : K^perf ≃+* L^perf` carrying `k^perf` onto `l^perf` reconstructs its
  transported lattice map. -/
theorem reconstruction_target (π : Perfection K) (ρ : Perfection L)
    (hk : IsRAC (⊥ : IntermediateField k K)) (hl : IsRAC (⊥ : IntermediateField l L))
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) (φ : ClosedIF k K ≃o ClosedIF l L) :
    Cardinal.lift.{v} (Algebra.trdeg k K) = Cardinal.lift.{u} (Algebra.trdeg l L) ∧
      ∃ Φ : π.carrier ≃+* ρ.carrier,
        CrossBase.Compatible (k := π.basePerf k) (l := ρ.basePerf l) Φ ∧
        Reconstructs π ρ φ Φ ∧
        (∀ (M : ClosedIF k K) (y : L),
          y ∈ φ M ↔ ρ.incl y ∈ (π.perfSubfield M.1.toSubfield).map Φ.toRingHom) ∧
        (∀ Ψ : π.carrier ≃+* ρ.carrier,
          Reconstructs π ρ φ Ψ ↔ ∃ n : ℤ, Ψ = Φ.trans (ρ.frobZPow n)) ∧
        (ρ.p = 1 → ∀ Ψ : π.carrier ≃+* ρ.carrier, Reconstructs π ρ φ Ψ → Ψ = Φ) ∧
        (ρ.p ≠ 1 → Function.Injective fun n : ℤ ↦ Φ.trans (ρ.frobZPow n)) ∧
        ∀ (Ψ : π.carrier ≃+* ρ.carrier)
          (hΨ : CrossBase.Compatible (k := π.basePerf k) (l := ρ.basePerf l) Ψ),
          Reconstructs π ρ (π.inducedIso ρ hΨ) Ψ := by
  obtain ⟨Φ, hΦ, h⟩ := exists_induces_of_five_le_trdeg π ρ hk hl htr φ
  exact ⟨lift_trdeg_eq_of_orderIso φ, Φ, hΦ, h, fun _ _ ↦ h.mem_iff,
    fun _ ↦ h.iff_exists_eq_trans_frobZPow htr,
    fun hp _ hΨ ↦ (h.eq_of_p_eq_one hΨ htr hp).symm,
    fun hp ↦ Perfection.trans_frobZPow_injective φ htr hp Φ,
    fun _ hΨ ↦ Perfection.induces_inducedIso hΨ⟩

end AclGeom
