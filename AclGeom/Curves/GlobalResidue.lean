/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.TateResidue
import AclGeom.Curves.Differentials

/-!
# Toward the residue theorem: global adelic operators

The bounded adele spaces viewed inside the adele module are pairwise
commensurable — enlarging the divisor adds one line per point — and
the adelic multiplication operators almost-stabilize each of them, so
the global residue commutator against any projection onto a bounded
adele space is trace-class. These are the global inputs to Tate's
residue theorem `Σ_P res_P (f dg) = 0`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P6 via Tate residues).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- The bounded adele space `A(D)` as a subspace of the adele
module. -/
noncomputable def adeleSpaceIn (D : Divisor k F) :
    Submodule k ↥(adeleSubmodule k F) :=
  (adeleSpace D).comap (adeleSubmodule k F).subtype

theorem mem_adeleSpaceIn_iff {D : Divisor k F}
    {α : ↥(adeleSubmodule k F)} :
    α ∈ adeleSpaceIn (k := k) (F := F) D ↔
      (α : (P : Place k F) → F) ∈ adeleSpace D :=
  Iff.rfl

theorem adeleSpaceIn_mono {D E : Divisor k F} (h : D ≤ E) :
    adeleSpaceIn (k := k) (F := F) D ≤ adeleSpaceIn E :=
  Submodule.comap_mono (adeleSpace_mono h)

/-- One-point commensurability: adding a single point to the divisor
grows the bounded adele space by at most a line. -/
theorem almostLE_adeleSpaceIn_add_single (D : Divisor k F)
    (P : Place k F) :
    AlmostLE (adeleSpaceIn (k := k) (F := F)
      (D + Finsupp.single P 1)) (adeleSpaceIn D) := by
  have hmem : adeleMonomial P (-(D P) - 1) ∈ adeleSubmodule k F :=
    adeleSpace_le_adeleSubmodule (D + Finsupp.single P 1) (by
      rw [adeleSpace_add_single]
      exact Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self _))
  refine ⟨Submodule.span k
    {(⟨adeleMonomial P (-(D P) - 1), hmem⟩ :
      ↥(adeleSubmodule k F))},
    FiniteDimensional.span_of_finite k (Set.finite_singleton _), ?_⟩
  intro α hα
  have h1 : (α : (Q : Place k F) → F) ∈ adeleSpace D ⊔
      Submodule.span k {adeleMonomial P (-(D P) - 1)} := by
    rw [← adeleSpace_add_single]
    exact hα
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 h1
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hw
  refine Submodule.mem_sup.2
    ⟨α - c • ⟨adeleMonomial P (-(D P) - 1), hmem⟩, ?_,
      c • ⟨adeleMonomial P (-(D P) - 1), hmem⟩, ?_, by abel⟩
  · rw [mem_adeleSpaceIn_iff]
    change (α : (Q : Place k F) → F) -
      c • adeleMonomial P (-(D P) - 1) ∈ adeleSpace D
    rw [← huw, ← hc, add_sub_cancel_right]
    exact hu
  · exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)

/-- Bounded adele spaces are commensurable downward: enlarging the
divisor adds finitely many dimensions. -/
theorem almostLE_adeleSpaceIn_of_le {D E : Divisor k F}
    (hDE : D ≤ E) :
    AlmostLE (adeleSpaceIn (k := k) (F := F) E) (adeleSpaceIn D) := by
  classical
  induction hmeas : ((E - D).deg).toNat using Nat.strong_induction_on
    generalizing E with
  | _ n ih =>
  rcases eq_or_ne D E with rfl | hne
  · exact AlmostLE.rfl
  · have hED : 0 ≤ E - D := by
      intro P
      have h1 := hDE P
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.sub_apply]
      omega
    obtain ⟨P, hP⟩ := Finsupp.support_nonempty_iff.2
      (sub_ne_zero.2 (Ne.symm hne))
    have hPpos : 0 < (E - D) P := by
      have h1 : (E - D) P ≠ 0 := Finsupp.mem_support_iff.1 hP
      have h2 : (0 : ℤ) ≤ (E - D) P := by simpa using hED P
      omega
    have hsub : (E - D) P = E P - D P := Finsupp.sub_apply E D P
    have hDE' : D ≤ E - Finsupp.single P 1 := by
      intro Q
      rcases eq_or_ne Q P with rfl | hQ
      · rw [Finsupp.sub_apply, Finsupp.single_eq_same]
        omega
      · rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hQ, sub_zero]
        exact hDE Q
    have hdeg1 : E - Finsupp.single P 1 - D =
        E - D - Finsupp.single P 1 := by abel
    have hdegP : (E - D) P ≤ (E - D).deg := by
      rw [Divisor.deg, Finsupp.sum]
      exact Finset.single_le_sum (fun Q _ ↦ by simpa using hED Q) hP
    have hmeas' : ((E - Finsupp.single P 1 - D).deg).toNat < n := by
      rw [hdeg1, deg_sub_single]
      omega
    have hstep :=
      almostLE_adeleSpaceIn_add_single (k := k) (F := F)
        (E - Finsupp.single P 1) P
    have hE : E - Finsupp.single P 1 + Finsupp.single P 1 = E := by
      abel
    rw [hE] at hstep
    exact hstep.trans (ih _ hmeas' hDE' rfl)

/-- **Any two bounded adele spaces are commensurable**: compare both
with the pointwise join. -/
theorem almostLE_adeleSpaceIn (E D : Divisor k F) :
    AlmostLE (adeleSpaceIn (k := k) (F := F) E) (adeleSpaceIn D) := by
  have h1 : E ≤ D + (E - D).pos := fun P ↦ by
    rw [Divisor.add_sub_pos_apply]
    exact le_max_right _ _
  have h2 : D ≤ D + (E - D).pos := fun P ↦ by
    rw [Divisor.add_sub_pos_apply]
    exact le_max_left _ _
  exact AlmostLE.mono_left (adeleSpaceIn_mono h1)
    (almostLE_adeleSpaceIn_of_le h2)

/-- Adelic multiplication shifts the divisor bound by the principal
divisor. -/
theorem map_adeleSMul_le {f : F} (hf : f ≠ 0) (D : Divisor k F) :
    (adeleSpaceIn (k := k) (F := F) D).map (adeleSMul f) ≤
      adeleSpaceIn (D - divisorOf k f) := by
  rintro α ⟨β, hβ, rfl⟩
  rw [mem_adeleSpaceIn_iff, adeleSMul_coe]
  refine adeleMulMap_mem_adeleSpace hf ?_
  have h1 : D - divisorOf k f + divisorOf k f = D := by abel
  rw [h1]
  exact hβ

/-- Adelic multiplication almost-stabilizes each bounded adele
space. -/
theorem almostLE_map_adeleSMul (f : F) (D : Divisor k F) :
    AlmostLE ((adeleSpaceIn (k := k) (F := F) D).map (adeleSMul f))
      (adeleSpaceIn D) := by
  rcases eq_or_ne f 0 with rfl | hf
  · have h0 : adeleSMul (k := k) (F := F) 0 = 0 := by
      rw [← zero_smul k (1 : F), adeleSMul_smul, zero_smul]
    refine AlmostLE.of_le ?_
    rintro α ⟨β, hβ, rfl⟩
    rw [h0, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  · exact AlmostLE.mono_left (map_adeleSMul_le hf D)
      (almostLE_adeleSpaceIn _ _)

/-- Words in two adelic multiplication operators almost-stabilize
each bounded adele space. -/
theorem almostLE_map_closure_adeleSMul (f g : F) (D : Divisor k F) :
    ∀ w ∈ Submonoid.closure ({adeleSMul f, adeleSMul g} :
      Set (Module.End k ↥(adeleSubmodule k F))),
      AlmostLE ((adeleSpaceIn D).map w) (adeleSpaceIn D) := by
  refine almostLE_map_closure_of fun w hw ↦ ?_
  rcases hw with rfl | hw
  · exact almostLE_map_adeleSMul f D
  · rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact almostLE_map_adeleSMul g D

/-- The diagonal copy of the function field inside the adele
module. -/
noncomputable def adeleDiagonalIn : Submodule k ↥(adeleSubmodule k F) :=
  (LinearMap.range (adeleDiagonal k F)).comap
    (adeleSubmodule k F).subtype

theorem mem_adeleDiagonalIn_iff {α : ↥(adeleSubmodule k F)} :
    α ∈ adeleDiagonalIn (k := k) (F := F) ↔
      ∃ f : F, adeleDiagonal k F f = (α : (P : Place k F) → F) :=
  Iff.rfl

/-- The diagonal is invariant under adelic multiplication. -/
theorem adeleSMul_mem_adeleDiagonalIn (f : F)
    {α : ↥(adeleSubmodule k F)}
    (hα : α ∈ adeleDiagonalIn (k := k) (F := F)) :
    adeleSMul f α ∈ adeleDiagonalIn (k := k) (F := F) := by
  obtain ⟨g, hg⟩ := hα
  refine ⟨f * g, ?_⟩
  change adeleDiagonal k F (f * g) = adeleMulMap k f ↑α
  rw [← adeleMulMap_diagonal, hg]
  rfl

/-- **1.5.8 inside the adele module**: when the bounded space and the
diagonal fill the adeles at the ambient level, they fill the adele
module. -/
theorem adeleSpaceIn_sup_adeleDiagonalIn {D : Divisor k F}
    (hD : adeleSubmodule k F =
      adeleSpace D ⊔ LinearMap.range (adeleDiagonal k F)) :
    adeleSpaceIn (k := k) (F := F) D ⊔ adeleDiagonalIn = ⊤ := by
  rw [eq_top_iff]
  intro α _
  have h1 : (α : (P : Place k F) → F) ∈
      adeleSpace D ⊔ LinearMap.range (adeleDiagonal k F) := by
    rw [← hD]
    exact α.2
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 h1
  have hu' : u ∈ adeleSubmodule k F := adeleSpace_le_adeleSubmodule D hu
  have hw' : w ∈ adeleSubmodule k F := by
    obtain ⟨f, rfl⟩ := hw
    exact adeleDiagonal_mem_adeleSubmodule f
  exact Submodule.mem_sup.2
    ⟨⟨u, hu'⟩, hu, ⟨w, hw'⟩, hw, Subtype.ext huw⟩

/-- The Riemann–Roch space maps to the adele module diagonally. -/
noncomputable def riemannToAdele (D : Divisor k F) :
    ↥(RiemannSpace D) →ₗ[k] ↥(adeleSubmodule k F) :=
  LinearMap.codRestrict _
    ((adeleDiagonal k F).comp (RiemannSpace D).subtype)
    fun _ ↦ adeleDiagonal_mem_adeleSubmodule _

/-- The intersection of the bounded space with the diagonal is the
diagonal copy of the Riemann–Roch space. -/
theorem range_riemannToAdele (D : Divisor k F) :
    LinearMap.range (riemannToAdele (k := k) (F := F) D) =
      adeleSpaceIn D ⊓ adeleDiagonalIn := by
  refine le_antisymm ?_ ?_
  · rintro α ⟨f, rfl⟩
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_adeleSpaceIn_iff]
      change adeleDiagonal k F (f : F) ∈ adeleSpace D
      exact adeleDiagonal_mem_adeleSpace_iff.2 f.2
    · exact ⟨(f : F), rfl⟩
  · intro α hα
    obtain ⟨hα1, hα2⟩ := Submodule.mem_inf.1 hα
    obtain ⟨f, hf⟩ := hα2
    have hfL : f ∈ RiemannSpace D := by
      rw [← adeleDiagonal_mem_adeleSpace_iff (D := D), hf]
      exact hα1
    exact ⟨⟨f, hfL⟩, Subtype.ext hf⟩

/-- The intersection is finite-dimensional for effective divisors. -/
theorem finiteDimensional_adeleSpaceIn_inf_adeleDiagonalIn
    {D : Divisor k F} (hD : 0 ≤ D) :
    FiniteDimensional k
      ↥(adeleSpaceIn (k := k) (F := F) D ⊓ adeleDiagonalIn) := by
  haveI := (finiteDimensional_riemannSpace_of_nonneg hD).1
  rw [← range_riemannToAdele]
  exact LinearMap.finiteDimensional_range _

/-- **The global residue commutator is trace-class** relative to any
bounded adele space, for any projection onto it. -/
theorem isTraceClass_adeleSMul_commutator (f g : F) (D : Divisor k F)
    {ε : Module.End k ↥(adeleSubmodule k F)}
    (hεr : ∀ α, ε α ∈ adeleSpaceIn (k := k) (F := F) D)
    (hεf : ∀ α ∈ adeleSpaceIn (k := k) (F := F) D, ε α = α) :
    IsTraceClass (adeleSpaceIn D)
      ((ε ∘ₗ adeleSMul f) ∘ₗ adeleSMul g -
        adeleSMul g ∘ₗ (ε ∘ₗ adeleSMul f)) := by
  have hcomm : adeleSMul (k := k) (F := F) g ∘ₗ adeleSMul f =
      adeleSMul f ∘ₗ adeleSMul g := by
    rw [adeleSMul_comp, adeleSMul_comp, mul_comm]
  have hμν : AlmostLE ((adeleSpaceIn (k := k) (F := F) D).map
      (adeleSMul f ∘ₗ adeleSMul g)) (adeleSpaceIn D) := by
    rw [adeleSMul_comp]
    exact almostLE_map_adeleSMul _ D
  exact isTraceClass_commutator_of_comm hcomm hμν
    (almostLE_map_adeleSMul f D) (almostLE_map_adeleSMul g D) hεr hεf

end

end AclGeom
