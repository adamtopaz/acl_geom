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

/-- The componentwise projection onto local filtration stages, at the
ambient level: each coordinate is projected onto
`π_P^{−D(P)} O_P`. -/
noncomputable def adeleProjPi (D : Divisor k F) :
    ((P : Place k F) → F) →ₗ[k] ((P : Place k F) → F) :=
  LinearMap.pi fun P ↦
    (P.filtrationProj (D P).toNat).comp (LinearMap.proj P)

theorem adeleProjPi_apply (D : Divisor k F)
    (α : (P : Place k F) → F) (P : Place k F) :
    adeleProjPi D α P = P.filtrationProj (D P).toNat (α P) := rfl

/-- The componentwise projection preserves the adeles: the image
coordinate at `P` has order at least `−D(P)`, so the exceptional set
is inside the support of `D`. -/
theorem adeleProjPi_mem_adeleSubmodule (D : Divisor k F)
    (α : (P : Place k F) → F) :
    adeleProjPi D α ∈ adeleSubmodule k F := by
  refine Set.Finite.subset D.support.finite_toSet fun P hP ↦ ?_
  simp only [Set.mem_setOf_eq, adeleProjPi_apply] at hP
  obtain ⟨hne, hlt⟩ := hP
  have h1 := P.filtrationProj_mem (D P).toNat (α P)
  rw [Place.mem_filtration_iff_ord] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 hne
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  omega

/-- The componentwise projection as an endomorphism of the adele
module. -/
noncomputable def adeleProj (D : Divisor k F) :
    Module.End k ↥(adeleSubmodule k F) :=
  LinearMap.codRestrict _
    ((adeleProjPi D).comp (adeleSubmodule k F).subtype)
    fun α ↦ adeleProjPi_mem_adeleSubmodule D ↑α

theorem adeleProj_coe (D : Divisor k F) (α : ↥(adeleSubmodule k F)) :
    ((adeleProj D α : ↥(adeleSubmodule k F)) :
      (P : Place k F) → F) = adeleProjPi D ↑α := rfl

/-- The componentwise projection lands in the bounded adele space. -/
theorem adeleProj_mem_adeleSpaceIn {D : Divisor k F} (hD : 0 ≤ D)
    (α : ↥(adeleSubmodule k F)) :
    adeleProj D α ∈ adeleSpaceIn (k := k) (F := F) D := by
  rw [mem_adeleSpaceIn_iff]
  intro P
  have h1 := P.filtrationProj_mem (D P).toNat
    ((α : (Q : Place k F) → F) P)
  rw [Place.mem_filtration_iff_ord] at h1
  have h2 : ((adeleProj D α : ↥(adeleSubmodule k F)) :
      (Q : Place k F) → F) P =
      P.filtrationProj (D P).toNat
        ((α : (Q : Place k F) → F) P) := rfl
  rcases h1 with h1 | h1
  · exact Or.inl (by rw [h2, h1])
  · refine Or.inr ?_
    rw [h2]
    have h3 : ((D P).toNat : ℤ) = D P := Int.toNat_of_nonneg (hD P)
    omega

/-- The componentwise projection fixes the bounded adele space. -/
theorem adeleProj_eq_self {D : Divisor k F} (hD : 0 ≤ D)
    {α : ↥(adeleSubmodule k F)}
    (hα : α ∈ adeleSpaceIn (k := k) (F := F) D) :
    adeleProj D α = α := by
  refine Subtype.ext (funext fun P ↦ ?_)
  have h2 : ((adeleProj D α : ↥(adeleSubmodule k F)) :
      (Q : Place k F) → F) P =
      P.filtrationProj (D P).toNat
        ((α : (Q : Place k F) → F) P) := rfl
  rw [h2]
  refine P.filtrationProj_eq_self ?_
  rw [Place.mem_filtration_iff_ord]
  rcases (mem_adeleSpaceIn_iff.1 hα) P with h1 | h1
  · exact Or.inl h1
  · refine Or.inr ?_
    have h3 : ((D P).toNat : ℤ) = D P := Int.toNat_of_nonneg (hD P)
    omega

/-- **The componentwise commutator acts blockwise**: each coordinate
sees the local residue commutator at its own filtration stage. -/
theorem adeleProj_commutator_apply (D : Divisor k F) (f g : F)
    (α : ↥(adeleSubmodule k F)) (P : Place k F) :
    ((((adeleProj D ∘ₗ adeleSMul f) ∘ₗ adeleSMul g -
      adeleSMul g ∘ₗ (adeleProj D ∘ₗ adeleSMul f)) α :
        ↥(adeleSubmodule k F)) : (Q : Place k F) → F) P =
    ((P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f) ∘ₗ
      LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ
        (P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f))
      ((α : (Q : Place k F) → F) P) := rfl

open Classical in
/-- The single-place inclusion at the ambient level: the value `x`
concentrated at the place `P`. -/
noncomputable def adeleSinglePi (P : Place k F) :
    F →ₗ[k] ((Q : Place k F) → F) where
  toFun x := fun Q ↦ if Q = P then x else 0
  map_add' x y := by
    funext Q
    by_cases h : Q = P <;> simp [h]
  map_smul' c x := by
    funext Q
    by_cases h : Q = P <;> simp [h]

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
theorem adeleSinglePi_apply_self (P : Place k F) (x : F) :
    adeleSinglePi (k := k) P x P = x := if_pos rfl

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
theorem adeleSinglePi_apply_ne (P : Place k F) {Q : Place k F}
    (hQ : Q ≠ P) (x : F) : adeleSinglePi (k := k) P x Q = 0 :=
  if_neg hQ

theorem adeleSinglePi_mem_adeleSubmodule (P : Place k F) (x : F) :
    adeleSinglePi (k := k) P x ∈ adeleSubmodule k F := by
  refine Set.Finite.subset (Set.finite_singleton P) fun Q hQ ↦ ?_
  simp only [Set.mem_setOf_eq] at hQ
  rw [Set.mem_singleton_iff]
  by_contra hne
  rw [adeleSinglePi_apply_ne P hne] at hQ
  exact hQ.1 rfl

/-- The single-place inclusion into the adele module. -/
noncomputable def adeleSingle (P : Place k F) :
    F →ₗ[k] ↥(adeleSubmodule k F) :=
  LinearMap.codRestrict _ (adeleSinglePi P)
    fun x ↦ adeleSinglePi_mem_adeleSubmodule P x

theorem adeleSingle_coe (P : Place k F) (x : F) :
    ((adeleSingle P x : ↥(adeleSubmodule k F)) :
      (Q : Place k F) → F) = adeleSinglePi (k := k) P x := rfl

theorem adeleSingle_injective (P : Place k F) :
    Function.Injective (adeleSingle (k := k) (F := F) P) := by
  intro x y hxy
  have h1 := congrArg
    (fun α : ↥(adeleSubmodule k F) ↦ (α : (Q : Place k F) → F) P) hxy
  simpa [adeleSingle_coe, adeleSinglePi_apply_self] using h1

/-- **The blockwise commutator restricted to a single place**: the
global commutator built from the componentwise projection carries the
single-place copy of `F` into itself, by the local commutator. -/
theorem adeleProj_commutator_comp_single (D : Divisor k F) (f g : F)
    (P : Place k F) (x : F) :
    ((adeleProj D ∘ₗ adeleSMul f) ∘ₗ adeleSMul g -
      adeleSMul g ∘ₗ (adeleProj D ∘ₗ adeleSMul f)) (adeleSingle P x) =
    adeleSingle P
      (((P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f) ∘ₗ
          LinearMap.mulLeft k g -
        LinearMap.mulLeft k g ∘ₗ
          (P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f))
        x) := by
  refine Subtype.ext (funext fun Q ↦ ?_)
  rw [adeleProj_commutator_apply]
  rcases eq_or_ne Q P with rfl | hQ
  · rw [adeleSingle_coe, adeleSingle_coe, adeleSinglePi_apply_self,
      adeleSinglePi_apply_self]
  · have h1 : ((adeleSingle P x : ↥(adeleSubmodule k F)) :
        (R : Place k F) → F) Q = 0 := adeleSinglePi_apply_ne P hQ x
    have h2 : ((adeleSingle P
        (((P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f) ∘ₗ
            LinearMap.mulLeft k g -
          LinearMap.mulLeft k g ∘ₗ
            (P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f))
          x) : ↥(adeleSubmodule k F)) : (R : Place k F) → F) Q = 0 :=
      adeleSinglePi_apply_ne P hQ _
    rw [h1, h2, map_zero]

/-- **The global commutator trace vanishes** (the heart of the residue
theorem): for any projection `π` onto a bounded adele space that,
together with the diagonal, fills the adele module, the trace of
`[π ∘ M_f, M_g]` is zero. The compatible projection triple decomposes
the commutator into the zero commutator of multiplications, a
finite-rank commutator, and a nilpotent commutator on the invariant
diagonal. -/
theorem tateTrace_adeleSMul_commutator_eq_zero (f g : F)
    {D₀ : Divisor k F} (hD₀ : 0 ≤ D₀)
    (hD : adeleSubmodule k F =
      adeleSpace D₀ ⊔ LinearMap.range (adeleDiagonal k F))
    {π : Module.End k ↥(adeleSubmodule k F)}
    (hπr : ∀ α, π α ∈ adeleSpaceIn (k := k) (F := F) D₀)
    (hπf : ∀ α ∈ adeleSpaceIn (k := k) (F := F) D₀, π α = α) :
    tateTrace ((π ∘ₗ adeleSMul f) ∘ₗ adeleSMul g -
      adeleSMul g ∘ₗ (π ∘ₗ adeleSMul f)) = 0 := by
  haveI hUfin := finiteDimensional_adeleSpaceIn_inf_adeleDiagonalIn
    (k := k) (F := F) hD₀
  obtain ⟨εA, εB, hAr, hAf, hBr, hBf, hU⟩ :=
    exists_projection_pair (adeleSpaceIn_sup_adeleDiagonalIn hD)
  have hMcomm : adeleSMul (k := k) (F := F) g ∘ₗ adeleSMul f =
      adeleSMul f ∘ₗ adeleSMul g := by
    rw [adeleSMul_comp, adeleSMul_comp, mul_comm]
  have hMcommPt : ∀ x, adeleSMul (k := k) (F := F) g
      (adeleSMul f x) = adeleSMul f (adeleSMul g x) := by
    intro x
    have h1 := LinearMap.congr_fun hMcomm x
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
    exact h1
  set εU : Module.End k ↥(adeleSubmodule k F) :=
    εA + εB - LinearMap.id with hεU
  have hUr : ∀ x, εU x ∈
      adeleSpaceIn (k := k) (F := F) D₀ ⊓ adeleDiagonalIn := by
    intro x
    have h1 : εU x = εA x + εB x - x := rfl
    rw [h1]
    exact hU x
  set CB : Module.End k ↥(adeleSubmodule k F) :=
    (εB ∘ₗ adeleSMul f) ∘ₗ adeleSMul g -
      adeleSMul g ∘ₗ (εB ∘ₗ adeleSMul f) with hCB
  set CU : Module.End k ↥(adeleSubmodule k F) :=
    (εU ∘ₗ adeleSMul f) ∘ₗ adeleSMul g -
      adeleSMul g ∘ₗ (εU ∘ₗ adeleSMul f) with hCU
  have hCBapp : ∀ x, CB x = εB (adeleSMul f (adeleSMul g x)) -
      adeleSMul g (εB (adeleSMul f x)) := fun x ↦ rfl
  have hCUapp : ∀ x, CU x = εU (adeleSMul f (adeleSMul g x)) -
      adeleSMul g (εU (adeleSMul f x)) := fun x ↦ rfl
  -- the diagonal commutator kills the diagonal and lands in it
  have hBker : ∀ x ∈ adeleDiagonalIn (k := k) (F := F), CB x = 0 := by
    intro x hx
    rw [hCBapp]
    have h1 : adeleSMul g x ∈ adeleDiagonalIn (k := k) (F := F) :=
      adeleSMul_mem_adeleDiagonalIn g hx
    have h2 : adeleSMul f (adeleSMul g x) ∈
        adeleDiagonalIn (k := k) (F := F) :=
      adeleSMul_mem_adeleDiagonalIn f h1
    have h3 : adeleSMul f x ∈ adeleDiagonalIn (k := k) (F := F) :=
      adeleSMul_mem_adeleDiagonalIn f hx
    rw [hBf _ h2, hBf _ h3, hMcommPt, sub_self]
  have hBrange : ∀ x, CB x ∈ adeleDiagonalIn (k := k) (F := F) := by
    intro x
    rw [hCBapp]
    exact Submodule.sub_mem _ (hBr _)
      (adeleSMul_mem_adeleDiagonalIn g (hBr _))
  have hBsq : CB ∘ₗ CB = 0 := by
    refine LinearMap.ext fun x ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    exact hBker _ (hBrange x)
  have hBnil : IsNilpotent CB := by
    refine ⟨2, ?_⟩
    have h1 : (CB ^ 2 : Module.End k ↥(adeleSubmodule k F)) =
        CB ∘ₗ CB := by
      rw [pow_two]
      rfl
    rw [h1, hBsq]
  -- the correction commutator has finite rank
  have hUrange : ∀ x, CU x ∈
      (adeleSpaceIn (k := k) (F := F) D₀ ⊓ adeleDiagonalIn) ⊔
        (adeleSpaceIn (k := k) (F := F) D₀ ⊓
          adeleDiagonalIn).map (adeleSMul g) := by
    intro x
    rw [hCUapp, sub_eq_add_neg]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hUr _))
      (Submodule.neg_mem _ (Submodule.mem_sup_right ⟨_, hUr _, rfl⟩))
  haveI hCUfin : FiniteDimensional k (LinearMap.range CU) := by
    refine Submodule.finiteDimensional_of_le
      (S₂ := (adeleSpaceIn (k := k) (F := F) D₀ ⊓ adeleDiagonalIn) ⊔
        (adeleSpaceIn (k := k) (F := F) D₀ ⊓
          adeleDiagonalIn).map (adeleSMul g)) ?_
    rintro x ⟨y, rfl⟩
    exact hUrange y
  -- trace of the correction commutator vanishes: finite-rank flip
  have htrCU : tateTrace CU = 0 := by
    haveI hI1 : FiniteDimensional k (LinearMap.range
        ((εU ∘ₗ adeleSMul f) ∘ₗ adeleSMul g)) := by
      refine Submodule.finiteDimensional_of_le
        (S₂ := adeleSpaceIn (k := k) (F := F) D₀ ⊓
          adeleDiagonalIn) ?_
      rintro x ⟨y, rfl⟩
      exact hUr _
    haveI hI2 : FiniteDimensional k (LinearMap.range
        (adeleSMul g ∘ₗ (εU ∘ₗ adeleSMul f))) := by
      refine Submodule.finiteDimensional_of_le
        (S₂ := (adeleSpaceIn (k := k) (F := F) D₀ ⊓
          adeleDiagonalIn).map (adeleSMul g)) ?_
      rintro x ⟨y, rfl⟩
      exact ⟨εU (adeleSMul f y), hUr _, rfl⟩
    rw [hCU]
    exact tateTrace_comp_sub_comp_comm (εU ∘ₗ adeleSMul f)
      (adeleSMul g)
  -- trace of the diagonal commutator vanishes: nilpotent
  have htrCB : tateTrace CB = 0 := tateTrace_of_isNilpotent hBnil
  have htrnCB : tateTrace (-CB) = 0 := by
    have hcore : IsTateCore CB (⊥ : Submodule k
        ↥(adeleSubmodule k F)) := by
      refine ⟨inferInstance, fun x hx ↦ ?_, ⟨2, fun x ↦ ?_⟩⟩
      · rw [Submodule.mem_bot] at hx
        rw [hx, map_zero]
        exact Submodule.zero_mem _
      · have h1 : (CB ^ 2 : Module.End k ↥(adeleSubmodule k F)) =
            CB ∘ₗ CB := by
          rw [pow_two]
          rfl
        rw [h1, hBsq, LinearMap.zero_apply]
        exact Submodule.zero_mem _
    have h2 : (-CB : Module.End k ↥(adeleSubmodule k F)) =
        (-1 : k) • CB := by
      rw [neg_one_smul]
    rw [h2, tateTrace_smul hcore, htrCB, mul_zero]
  -- the operator identity: the εA-commutator is CU − CB
  have hεA : εA = LinearMap.id + εU - εB := by
    rw [hεU]
    abel
  have hCid : (εA ∘ₗ adeleSMul f) ∘ₗ adeleSMul g -
      adeleSMul g ∘ₗ (εA ∘ₗ adeleSMul f) = CU - CB := by
    refine LinearMap.ext fun x ↦ ?_
    rw [hεA]
    simp only [hCU, hCB, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.id_apply, map_add, map_sub]
    have h1 := hMcommPt x
    abel_nf
    rw [h1]
    abel
  -- additivity across the two pieces
  have htrA : tateTrace ((εA ∘ₗ adeleSMul f) ∘ₗ adeleSMul g -
      adeleSMul g ∘ₗ (εA ∘ₗ adeleSMul f)) = 0 := by
    rw [hCid]
    have hsub : CU - CB = CU + (-CB) := sub_eq_add_neg CU CB
    haveI hJ1 : FiniteDimensional k (LinearMap.range
        (CU ∘ₗ CU)) := by
      refine Submodule.finiteDimensional_of_le
        (S₂ := LinearMap.range CU) ?_
      rintro x ⟨y, rfl⟩
      exact ⟨CU y, rfl⟩
    haveI hJ2 : FiniteDimensional k (LinearMap.range
        (CU ∘ₗ (-CB))) := by
      refine Submodule.finiteDimensional_of_le
        (S₂ := LinearMap.range CU) ?_
      rintro x ⟨y, rfl⟩
      exact ⟨(-CB) y, rfl⟩
    haveI hJ3 : FiniteDimensional k (LinearMap.range
        ((-CB) ∘ₗ CU)) := by
      haveI : FiniteDimensional k
          ((LinearMap.range CU).map (-CB)) := inferInstance
      refine Submodule.finiteDimensional_of_le
        (S₂ := (LinearMap.range CU).map (-CB)) ?_
      rintro x ⟨y, rfl⟩
      exact ⟨CU y, ⟨y, rfl⟩, rfl⟩
    haveI hJ4 : FiniteDimensional k (LinearMap.range
        ((-CB) ∘ₗ (-CB))) := by
      have h1 : (-CB) ∘ₗ (-CB) = CB ∘ₗ CB := by
        rw [LinearMap.neg_comp, LinearMap.comp_neg, neg_neg]
      rw [h1, hBsq, LinearMap.range_zero]
      infer_instance
    rw [hsub, tateTrace_add_of_sq, htrCU, htrnCB, add_zero]
  -- compare the given projection with the constructed one
  have hcmp := tateTrace_commutator_eq_of_projection
    (le_refl (adeleSpaceIn (k := k) (F := F) D₀)) AlmostLE.rfl
    (almostLE_map_closure_adeleSMul f g D₀) hAr hAf hπr hπf
    (isTraceClass_adeleSMul_commutator f g D₀ hAr hAf)
  rw [hcmp, htrA]

end

end AclGeom
