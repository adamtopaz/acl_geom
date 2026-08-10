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

/-- **Local behavior at the divisor of a differential**: if `W` is
a greatest level of `ω`, then at every place `P` the functional kills
all single-place adeles of order at least `-W(P)`, but does not kill
the uniformizer monomial of order `-W(P)-1`. -/
theorem local_behavior_of_isGreatest_level
    {ω : Module.Dual k ↥(adeleSubmodule k F)} {W : Divisor k F}
    (hW : ω ∈ weilDifferentialsAt W)
    (hmax : ∀ D, ω ∈ weilDifferentialsAt D → D ≤ W)
    (P : Place k F) :
    (∀ f : F, f = 0 ∨ -(W P) ≤ P.ord f →
      ω (adeleSingle P f) = 0) ∧
    ∃ f : F, ω (adeleSingle P f) ≠ 0 ∧
      P.ord f = -(W P) - 1 := by
  classical
  have hkillW : ∀ α ∈ boundedSubmodule W, ω α = 0 :=
    mem_weilDifferentialsAt_iff.1 hW
  constructor
  · intro f hf
    apply hkillW
    rw [mem_boundedSubmodule_iff]
    refine Submodule.mem_sup_left ?_
    intro Q
    change adeleSinglePi (k := k) P f Q = 0 ∨
      -(W Q) ≤ Q.ord (adeleSinglePi (k := k) P f Q)
    rcases eq_or_ne Q P with rfl | hQ
    · rw [adeleSinglePi_apply_self]
      exact hf
    · exact Or.inl (adeleSinglePi_apply_ne P hQ f)
  · have hmono :
        ω (adeleMonomialMem P (-(W P) - 1)) ≠ 0 := by
      intro hzero
      have hnext : ω ∈
          weilDifferentialsAt (W + Finsupp.single P 1) := by
        rw [mem_weilDifferentialsAt_iff]
        intro α hα
        rw [boundedSubmodule_add_single W P] at hα
        obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hα
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy
        rw [← hxy, map_add, hkillW x hx, ← hc, map_smul,
          hzero, smul_zero, add_zero]
      have hle := hmax (W + Finsupp.single P 1) hnext P
      rw [Finsupp.add_apply, Finsupp.single_eq_same] at hle
      omega
    have hsingle :
        adeleSingle P (P.pi ^ (-(W P) - 1)) =
          adeleMonomialMem P (-(W P) - 1) := by
      apply Subtype.ext
      funext Q
      change adeleSinglePi (k := k) P (P.pi ^ (-(W P) - 1)) Q =
        adeleMonomial P (-(W P) - 1) Q
      rcases eq_or_ne Q P with rfl | hQ
      · rw [adeleSinglePi_apply_self, adeleMonomial_apply_self]
      · rw [adeleSinglePi_apply_ne P hQ,
          adeleMonomial_apply_ne P hQ]
    refine ⟨P.pi ^ (-(W P) - 1), ?_, ?_⟩
    · rwa [hsingle]
    · exact ord_pi_zpow P (-(W P) - 1)

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

/-- **Finite-support decomposition**: an adele supported on a finite
set of places is the sum of its single-place pieces. -/
theorem eq_sum_adeleSingle {S : Finset (Place k F)}
    {β : ↥(adeleSubmodule k F)}
    (hβ : ∀ Q ∉ S, (β : (P : Place k F) → F) Q = 0) :
    β = ∑ Q ∈ S, adeleSingle Q ((β : (P : Place k F) → F) Q) := by
  refine Subtype.ext (funext fun R ↦ ?_)
  have h1 := map_sum (adeleSubmodule k F).subtype
    (fun Q ↦ adeleSingle Q ((β : (P : Place k F) → F) Q)) S
  have h2 : ((∑ Q ∈ S, adeleSingle Q
      ((β : (P : Place k F) → F) Q) : ↥(adeleSubmodule k F)) :
        (P : Place k F) → F) R =
      ∑ Q ∈ S, adeleSinglePi (k := k) Q
        ((β : (P : Place k F) → F) Q) R := by
    have h3 : ((∑ Q ∈ S, adeleSingle Q
        ((β : (P : Place k F) → F) Q) : ↥(adeleSubmodule k F)) :
          (P : Place k F) → F) =
        ∑ Q ∈ S, ((adeleSingle Q ((β : (P : Place k F) → F) Q) :
          ↥(adeleSubmodule k F)) : (P : Place k F) → F) := h1
    rw [h3, Finset.sum_apply]
    rfl
  rw [h2]
  rcases em (R ∈ S) with hR | hR
  · rw [Finset.sum_eq_single R
      (fun Q _ hQ ↦ adeleSinglePi_apply_ne Q (Ne.symm hQ) _)
      (fun h ↦ absurd hR h)]
    exact (adeleSinglePi_apply_self R _).symm
  · rw [Finset.sum_eq_zero
      (fun Q hQ ↦ adeleSinglePi_apply_ne Q
        (fun h ↦ hR (by rw [h]; exact hQ)) _),
      hβ R hR]

/-- Powers of the blockwise commutator act blockwise. -/
theorem adeleProj_commutator_pow_apply (D : Divisor k F) (f g : F)
    (n : ℕ) (α : ↥(adeleSubmodule k F)) (P : Place k F) :
    (((((adeleProj D ∘ₗ adeleSMul f) ∘ₗ adeleSMul g -
      adeleSMul g ∘ₗ (adeleProj D ∘ₗ adeleSMul f)) ^ n) α :
        ↥(adeleSubmodule k F)) : (Q : Place k F) → F) P =
    (((P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f) ∘ₗ
      LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ
        (P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f)) ^ n)
      ((α : (Q : Place k F) → F) P) := by
  induction n generalizing α with
  | zero =>
    rw [pow_zero, pow_zero]
    rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply,
      Module.End.mul_apply, ih]
    congr 1

/-- Evaluation of an adele at a place. -/
noncomputable def adeleEval (P : Place k F) :
    ↥(adeleSubmodule k F) →ₗ[k] F :=
  (LinearMap.proj P).comp (adeleSubmodule k F).subtype

theorem adeleEval_apply (P : Place k F) (α : ↥(adeleSubmodule k F)) :
    adeleEval P α = (α : (Q : Place k F) → F) P := rfl

/-- The single-place block of the global residue commutator: evaluate
at `P`, apply the local commutator, include back at `P`. -/
noncomputable def blockOp (D : Divisor k F) (f g : F)
    (P : Place k F) : Module.End k ↥(adeleSubmodule k F) :=
  adeleSingle P ∘ₗ
    ((P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f) ∘ₗ
        LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ
        (P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f)) ∘ₗ
    adeleEval P

theorem blockOp_apply (D : Divisor k F) (f g : F) (P : Place k F)
    (α : ↥(adeleSubmodule k F)) :
    blockOp D f g P α = adeleSingle P
      (((P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f) ∘ₗ
          LinearMap.mulLeft k g -
        LinearMap.mulLeft k g ∘ₗ
          (P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f))
        ((α : (Q : Place k F) → F) P)) := rfl

/-- Blocks at distinct places compose to zero. -/
theorem blockOp_comp_blockOp_of_ne (D : Divisor k F) (f g : F)
    {P Q : Place k F} (hPQ : P ≠ Q) :
    blockOp D f g P ∘ₗ blockOp D f g Q = 0 := by
  refine LinearMap.ext fun α ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.zero_apply, blockOp_apply,
    blockOp_apply]
  have h1 : ((adeleSingle Q
      (((Q.filtrationProj (D Q).toNat ∘ₗ LinearMap.mulLeft k f) ∘ₗ
          LinearMap.mulLeft k g -
        LinearMap.mulLeft k g ∘ₗ
          (Q.filtrationProj (D Q).toNat ∘ₗ LinearMap.mulLeft k f))
        ((α : (R : Place k F) → F) Q)) : ↥(adeleSubmodule k F)) :
        (R : Place k F) → F) P = 0 :=
    adeleSinglePi_apply_ne Q hPQ _
  rw [h1, map_zero, map_zero]

/-- Squares of blocks have finite-dimensional range. -/
theorem finiteDimensional_range_blockOp_comp_self (D : Divisor k F)
    (f g : F) (P : Place k F) :
    FiniteDimensional k (LinearMap.range
      (blockOp D f g P ∘ₗ blockOp D f g P)) := by
  have hTC := P.isTraceClass_filtrationProj_commutator f g (D P).toNat
  haveI := hTC.finiteDimensional_range_comp hTC
  refine Submodule.finiteDimensional_of_le
    (S₂ := (LinearMap.range
      (((P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f) ∘ₗ
          LinearMap.mulLeft k g -
        LinearMap.mulLeft k g ∘ₗ
          (P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f)) ∘ₗ
        ((P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f) ∘ₗ
          LinearMap.mulLeft k g -
        LinearMap.mulLeft k g ∘ₗ
          (P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f)))).map
      (adeleSingle P)) ?_
  rintro x ⟨α, rfl⟩
  rw [LinearMap.comp_apply, blockOp_apply, blockOp_apply]
  refine ⟨_, ⟨(α : (Q : Place k F) → F) P, rfl⟩, ?_⟩
  congr 1
  rw [LinearMap.comp_apply]
  congr 1
  exact (adeleSinglePi_apply_self P _).symm

/-- **The block trace is the local trace**: the single-place block has
the same Tate trace as the local commutator it conjugates, computed on
the pushed-forward core. -/
theorem tateTrace_blockOp (D : Divisor k F) (f g : F)
    (P : Place k F) :
    tateTrace (blockOp D f g P) =
      tateTrace
        ((P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f) ∘ₗ
            LinearMap.mulLeft k g -
          LinearMap.mulLeft k g ∘ₗ
            (P.filtrationProj (D P).toNat ∘ₗ
              LinearMap.mulLeft k f)) := by
  set C : Module.End k F :=
    (P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f) ∘ₗ
        LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ
        (P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f)
    with hC
  obtain ⟨W, hW⟩ := (P.isTraceClass_filtrationProj_commutator f g
    (D P).toNat).isFinitePotent.exists_isTateCore
  haveI := hW.finite
  have hstable : ∀ x ∈ W.map (adeleSingle P),
      blockOp D f g P x ∈ W.map (adeleSingle P) := by
    rintro x ⟨w, hw, rfl⟩
    rw [blockOp_apply]
    have h1 : ((adeleSingle P w : ↥(adeleSubmodule k F)) :
        (Q : Place k F) → F) P = w := adeleSinglePi_apply_self P w
    rw [h1]
    exact ⟨C w, hW.stable w hw, rfl⟩
  obtain ⟨n, hn⟩ := hW.absorbs
  have hpow : ∀ (m : ℕ), 1 ≤ m → ∀ α : ↥(adeleSubmodule k F),
      (blockOp D f g P ^ m) α =
        adeleSingle P ((C ^ m) ((α : (Q : Place k F) → F) P)) := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      intro α
      rcases Nat.lt_or_ge 0 m with h1 | h1
      · have hm1 : 1 ≤ m := h1
        rw [pow_succ, pow_succ, Module.End.mul_apply,
          Module.End.mul_apply, ih hm1]
        congr 1
        rw [blockOp_apply]
        congr 1
        exact adeleSinglePi_apply_self P _
      · have hm0 : m = 0 := by omega
        subst hm0
        rw [pow_one, pow_one]
        exact blockOp_apply D f g P α
  have hcore : IsTateCore (blockOp D f g P)
      (W.map (adeleSingle P)) := by
    refine ⟨inferInstance, hstable, ⟨max n 1, fun α ↦ ?_⟩⟩
    rw [hpow (max n 1) (le_max_right n 1) α]
    exact ⟨(C ^ max n 1) ((α : (Q : Place k F) → F) P),
      hW.pow_mem_of_le hn (le_max_left n 1) _, rfl⟩
  rw [hcore.tateTrace_eq, hW.tateTrace_eq]
  set e := Submodule.equivMapOfInjective (adeleSingle P)
    (adeleSingle_injective P) W with he
  have hconj : (blockOp D f g P).restrict hcore.stable =
      e.conj (C.restrict hW.stable) := by
    refine LinearMap.ext fun x ↦ Subtype.ext ?_
    have h2 : (x : ↥(adeleSubmodule k F)) =
        adeleSingle P ((e.symm x : ↥W) : F) := by
      conv_lhs => rw [← e.apply_symm_apply x]
      rw [he]
      exact Submodule.coe_equivMapOfInjective_apply (adeleSingle P)
        (adeleSingle_injective P) W _
    have h3 : (((blockOp D f g P).restrict hcore.stable x :
        ↥(W.map (adeleSingle P))) : ↥(adeleSubmodule k F)) =
        blockOp D f g P (x : ↥(adeleSubmodule k F)) := rfl
    have h4 : ((e.conj (C.restrict hW.stable) x :
        ↥(W.map (adeleSingle P))) : ↥(adeleSubmodule k F)) =
        adeleSingle P (C ((e.symm x : ↥W) : F)) := by
      rw [LinearEquiv.conj_apply, he]
      exact Submodule.coe_equivMapOfInjective_apply (adeleSingle P)
        (adeleSingle_injective P) W _
    rw [h3, h4, blockOp_apply]
    congr 1
    have h5 : ((x : ↥(adeleSubmodule k F)) :
        (Q : Place k F) → F) P =
        ((e.symm x : ↥W) : F) := by
      rw [h2]
      exact adeleSinglePi_apply_self P _
    rw [h5]
  rw [hconj, LinearMap.trace_conj']

/-- **Localization of the global trace**: away from the poles of `f`,
`g` and the support of `D`, the blocks square to zero, so the global
blockwise commutator is the sum of the bad blocks plus a square-zero
remainder, and its trace is the sum of the local traces. -/
theorem tateTrace_adeleProj_commutator (D : Divisor k F) (f g : F)
    (S : Finset (Place k F))
    (hS : ∀ Q : Place k F, Q ∉ S → f ∈ Q.toSubmodule ∧
      g ∈ Q.toSubmodule ∧ D Q = 0) :
    tateTrace ((adeleProj D ∘ₗ adeleSMul f) ∘ₗ adeleSMul g -
      adeleSMul g ∘ₗ (adeleProj D ∘ₗ adeleSMul f)) =
    ∑ P ∈ S, tateTrace
      ((P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f) ∘ₗ
          LinearMap.mulLeft k g -
        LinearMap.mulLeft k g ∘ₗ
          (P.filtrationProj (D P).toNat ∘ₗ
            LinearMap.mulLeft k f)) := by
  classical
  -- coordinates of the block sum
  have hsum_coord : ∀ (α : ↥(adeleSubmodule k F)) (Q : Place k F),
      (((∑ P ∈ S, blockOp D f g P) α : ↥(adeleSubmodule k F)) :
        (R : Place k F) → F) Q =
      ∑ P ∈ S, ((blockOp D f g P α : ↥(adeleSubmodule k F)) :
        (R : Place k F) → F) Q := by
    intro α Q
    have h1 : (∑ P ∈ S, blockOp D f g P) α =
        ∑ P ∈ S, blockOp D f g P α := LinearMap.sum_apply _ _ _
    rw [h1]
    have h3 : ((∑ P ∈ S, blockOp D f g P α :
        ↥(adeleSubmodule k F)) : (R : Place k F) → F) =
        ∑ P ∈ S, ((blockOp D f g P α : ↥(adeleSubmodule k F)) :
          (R : Place k F) → F) :=
      map_sum (adeleSubmodule k F).subtype
        (fun P ↦ blockOp D f g P α) S
    rw [h3, Finset.sum_apply]
  have hcoordS : ∀ (α : ↥(adeleSubmodule k F)) (Q : Place k F),
      Q ∈ S →
      (((∑ P ∈ S, blockOp D f g P) α : ↥(adeleSubmodule k F)) :
        (R : Place k F) → F) Q =
      ((Q.filtrationProj (D Q).toNat ∘ₗ LinearMap.mulLeft k f) ∘ₗ
          LinearMap.mulLeft k g -
        LinearMap.mulLeft k g ∘ₗ
          (Q.filtrationProj (D Q).toNat ∘ₗ LinearMap.mulLeft k f))
        ((α : (R : Place k F) → F) Q) := by
    intro α Q hQ
    have h4 : ∑ P ∈ S, ((blockOp D f g P α :
        ↥(adeleSubmodule k F)) : (R : Place k F) → F) Q =
        ((blockOp D f g Q α : ↥(adeleSubmodule k F)) :
          (R : Place k F) → F) Q :=
      Finset.sum_eq_single Q
        (fun P _ hne ↦ adeleSinglePi_apply_ne P (Ne.symm hne) _)
        (fun h ↦ absurd hQ h)
    rw [hsum_coord, h4, blockOp_apply]
    exact adeleSinglePi_apply_self Q _
  have hcoordN : ∀ (α : ↥(adeleSubmodule k F)) (Q : Place k F),
      Q ∉ S →
      (((∑ P ∈ S, blockOp D f g P) α : ↥(adeleSubmodule k F)) :
        (R : Place k F) → F) Q = 0 := by
    intro α Q hQ
    rw [hsum_coord]
    exact Finset.sum_eq_zero fun P hP ↦
      adeleSinglePi_apply_ne P (fun h ↦ hQ (by rw [h]; exact hP)) _
  -- the remainder and its coordinates
  set Dop : Module.End k ↥(adeleSubmodule k F) :=
    ((adeleProj D ∘ₗ adeleSMul f) ∘ₗ adeleSMul g -
      adeleSMul g ∘ₗ (adeleProj D ∘ₗ adeleSMul f)) -
      ∑ P ∈ S, blockOp D f g P with hDop
  have hDcoe : ∀ (α : ↥(adeleSubmodule k F)) (Q : Place k F),
      ((Dop α : ↥(adeleSubmodule k F)) : (R : Place k F) → F) Q =
      (((((adeleProj D ∘ₗ adeleSMul f) ∘ₗ adeleSMul g -
        adeleSMul g ∘ₗ (adeleProj D ∘ₗ adeleSMul f)) α) :
          ↥(adeleSubmodule k F)) : (R : Place k F) → F) Q -
      (((∑ P ∈ S, blockOp D f g P) α : ↥(adeleSubmodule k F)) :
        (R : Place k F) → F) Q := fun α Q ↦ rfl
  have hDmem : ∀ (α : ↥(adeleSubmodule k F)) (Q : Place k F),
      Q ∈ S →
      ((Dop α : ↥(adeleSubmodule k F)) : (R : Place k F) → F) Q =
        0 := by
    intro α Q hQ
    rw [hDcoe, adeleProj_commutator_apply, hcoordS α Q hQ, sub_self]
  have hDnot : ∀ (α : ↥(adeleSubmodule k F)) (Q : Place k F),
      Q ∉ S →
      ((Dop α : ↥(adeleSubmodule k F)) : (R : Place k F) → F) Q =
      ((Q.filtrationProj (D Q).toNat ∘ₗ LinearMap.mulLeft k f) ∘ₗ
          LinearMap.mulLeft k g -
        LinearMap.mulLeft k g ∘ₗ
          (Q.filtrationProj (D Q).toNat ∘ₗ LinearMap.mulLeft k f))
        ((α : (R : Place k F) → F) Q) := by
    intro α Q hQ
    rw [hDcoe, adeleProj_commutator_apply, hcoordN α Q hQ, sub_zero]
  -- good blocks square to zero
  have hCQsq : ∀ Q : Place k F, Q ∉ S →
      ((Q.filtrationProj (D Q).toNat ∘ₗ LinearMap.mulLeft k f) ∘ₗ
          LinearMap.mulLeft k g -
        LinearMap.mulLeft k g ∘ₗ
          (Q.filtrationProj (D Q).toNat ∘ₗ
            LinearMap.mulLeft k f)) ∘ₗ
      ((Q.filtrationProj (D Q).toNat ∘ₗ LinearMap.mulLeft k f) ∘ₗ
          LinearMap.mulLeft k g -
        LinearMap.mulLeft k g ∘ₗ
          (Q.filtrationProj (D Q).toNat ∘ₗ
            LinearMap.mulLeft k f)) = 0 := by
    intro Q hQ
    obtain ⟨hf, hg, hDQ⟩ := hS Q hQ
    have h1 : (D Q).toNat = 0 := by
      rw [hDQ]
      rfl
    rw [h1]
    exact Q.filtrationProj_commutator_comp_self_eq_zero hf hg
  -- the remainder squares to zero
  have hDsq : Dop ∘ₗ Dop = 0 := by
    refine LinearMap.ext fun α ↦ Subtype.ext (funext fun Q ↦ ?_)
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    rcases em (Q ∈ S) with hQ | hQ
    · exact hDmem (Dop α) Q hQ
    · rw [hDnot (Dop α) Q hQ, hDnot α Q hQ]
      have h1 := LinearMap.congr_fun (hCQsq Q hQ)
        ((α : (R : Place k F) → F) Q)
      rw [LinearMap.comp_apply, LinearMap.zero_apply] at h1
      exact h1
  -- vanishing compositions with the blocks
  have hDB : ∀ P ∈ S, Dop ∘ₗ blockOp D f g P = 0 := by
    intro P hP
    refine LinearMap.ext fun α ↦ Subtype.ext (funext fun Q ↦ ?_)
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    rcases em (Q ∈ S) with hQ | hQ
    · exact hDmem _ Q hQ
    · rw [hDnot _ Q hQ]
      have h1 : ((blockOp D f g P α : ↥(adeleSubmodule k F)) :
          (R : Place k F) → F) Q =
          0 :=
        adeleSinglePi_apply_ne P (fun h ↦ hQ (by rw [h]; exact hP)) _
      rw [h1, map_zero]
      rfl
  have hBD : ∀ P ∈ S, blockOp D f g P ∘ₗ Dop = 0 := by
    intro P hP
    refine LinearMap.ext fun α ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.zero_apply, blockOp_apply,
      hDmem α P hP, map_zero, map_zero]
  -- pairwise finiteness for the blocks
  have hpair : ∀ P ∈ S, ∀ Q ∈ S, FiniteDimensional k
      (LinearMap.range (blockOp D f g P ∘ₗ blockOp D f g Q)) := by
    intro P _ Q _
    rcases eq_or_ne P Q with rfl | hne
    · exact finiteDimensional_range_blockOp_comp_self D f g P
    · rw [blockOp_comp_blockOp_of_ne D f g hne, LinearMap.range_zero]
      infer_instance
  -- instances for additivity of the two pieces
  haveI J1 : FiniteDimensional k (LinearMap.range (Dop ∘ₗ Dop)) := by
    rw [hDsq, LinearMap.range_zero]
    infer_instance
  haveI J2 : FiniteDimensional k (LinearMap.range
      (Dop ∘ₗ ∑ P ∈ S, blockOp D f g P)) := by
    have h1 : Dop ∘ₗ (∑ P ∈ S, blockOp D f g P) =
        ∑ P ∈ S, (Dop ∘ₗ blockOp D f g P) :=
      Finset.mul_sum S _ Dop
    rw [h1]
    refine finiteDimensional_range_finset_sum S _ fun P hP ↦ ?_
    rw [hDB P hP, LinearMap.range_zero]
    infer_instance
  haveI J3 : FiniteDimensional k (LinearMap.range
      ((∑ P ∈ S, blockOp D f g P) ∘ₗ Dop)) := by
    have h1 : (∑ P ∈ S, blockOp D f g P) ∘ₗ Dop =
        ∑ P ∈ S, (blockOp D f g P ∘ₗ Dop) :=
      Finset.sum_mul S _ Dop
    rw [h1]
    refine finiteDimensional_range_finset_sum S _ fun P hP ↦ ?_
    rw [hBD P hP, LinearMap.range_zero]
    infer_instance
  haveI J4 : FiniteDimensional k (LinearMap.range
      ((∑ P ∈ S, blockOp D f g P) ∘ₗ ∑ P ∈ S, blockOp D f g P)) := by
    have h1 : (∑ P ∈ S, blockOp D f g P) ∘ₗ
        (∑ P ∈ S, blockOp D f g P) =
        ∑ P ∈ S, (blockOp D f g P ∘ₗ ∑ Q ∈ S, blockOp D f g Q) :=
      Finset.sum_mul S _ _
    rw [h1]
    refine finiteDimensional_range_finset_sum S _ fun P hP ↦ ?_
    have h2 : blockOp D f g P ∘ₗ (∑ Q ∈ S, blockOp D f g Q) =
        ∑ Q ∈ S, (blockOp D f g P ∘ₗ blockOp D f g Q) :=
      Finset.mul_sum S _ _
    rw [h2]
    exact finiteDimensional_range_finset_sum S _
      fun Q hQ ↦ hpair P hP Q hQ
  -- assemble
  have hCid : (adeleProj D ∘ₗ adeleSMul f) ∘ₗ adeleSMul g -
      adeleSMul g ∘ₗ (adeleProj D ∘ₗ adeleSMul f) =
      Dop + ∑ P ∈ S, blockOp D f g P := by
    rw [hDop]
    abel
  have hDnil : IsNilpotent Dop := by
    refine ⟨2, ?_⟩
    have h1 : (Dop ^ 2 : Module.End k ↥(adeleSubmodule k F)) =
        Dop ∘ₗ Dop := by
      rw [pow_two]
      rfl
    rw [h1, hDsq]
  rw [hCid, tateTrace_add_of_sq, tateTrace_of_isNilpotent hDnil,
    zero_add, tateTrace_finset_sum S _ hpair]
  exact Finset.sum_congr rfl fun P _ ↦ tateTrace_blockOp D f g P

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

/-- **The residue theorem** (Tate): the residues of `f dg` sum to
zero over any finite set of places outside which both `f` and `g` are
integral. The global commutator trace vanishes by the triple
decomposition against the diagonal, and localizes to the sum of the
local residues by the block decomposition. -/
theorem sum_residue_eq_zero (f g : F) (S : Finset (Place k F))
    (hS : ∀ Q : Place k F, Q ∉ S →
      f ∈ Q.toSubmodule ∧ g ∈ Q.toSubmodule) :
    ∑ P ∈ S, P.residue f g = 0 := by
  classical
  obtain ⟨D₀, hD₀nonneg, hdefect⟩ :=
    exists_le_defect_eq_genus (k := k) (F := F) 0
  have hsup := adeleSubmodule_eq_sup_of_defect_eq_genus hdefect
  have h0 := tateTrace_adeleSMul_commutator_eq_zero f g hD₀nonneg hsup
    (π := adeleProj D₀) (adeleProj_mem_adeleSpaceIn hD₀nonneg)
    (fun α hα ↦ adeleProj_eq_self hD₀nonneg hα)
  set S' : Finset (Place k F) := S ∪ D₀.support with hS'
  have hS'good : ∀ Q : Place k F, Q ∉ S' →
      f ∈ Q.toSubmodule ∧ g ∈ Q.toSubmodule ∧ D₀ Q = 0 := by
    intro Q hQ
    rw [hS', Finset.mem_union] at hQ
    push Not at hQ
    obtain ⟨h1, h2⟩ := hQ
    obtain ⟨hf, hg⟩ := hS Q h1
    refine ⟨hf, hg, ?_⟩
    by_contra h3
    exact h2 (Finsupp.mem_support_iff.2 h3)
  have hloc := tateTrace_adeleProj_commutator D₀ f g S' hS'good
  rw [h0] at hloc
  have hres : ∀ P ∈ S',
      tateTrace ((P.filtrationProj (D₀ P).toNat ∘ₗ
          LinearMap.mulLeft k f) ∘ₗ LinearMap.mulLeft k g -
        LinearMap.mulLeft k g ∘ₗ
          (P.filtrationProj (D₀ P).toNat ∘ₗ LinearMap.mulLeft k f)) =
      P.residue f g := fun P _ ↦
    P.residue_eq_of_projection_filtration (D₀ P).toNat
      (fun x ↦ P.filtrationProj_mem _ x)
      (fun x hx ↦ P.filtrationProj_eq_self hx) f g
  rw [Finset.sum_congr rfl hres] at hloc
  have hsub : ∑ P ∈ S, P.residue f g = ∑ P ∈ S', P.residue f g :=
    Finset.sum_subset Finset.subset_union_left fun P _ hP ↦
      P.residue_eq_zero_of_mem (hS P hP).1 (hS P hP).2
  rw [hsub, ← hloc]

/-- The residue of `α_P dg` vanishes at almost every place: outside
the exceptional set of `α` and the poles of `g`, both entries are
integral. -/
theorem residue_support_finite (g : F) (α : ↥(adeleSubmodule k F)) :
    {P : Place k F |
      P.residue ((α : (Q : Place k F) → F) P) g ≠ 0}.Finite := by
  rcases eq_or_ne g 0 with rfl | hg
  · refine Set.Finite.subset Set.finite_empty fun P hP ↦ ?_
    exact absurd (P.residue_zero_right _) hP
  refine Set.Finite.subset
    ((show Set.Finite _ from α.2).union
      (finite_setOf_one_lt_valuation hg)) fun P hP ↦ ?_
  rw [Set.mem_setOf_eq] at hP
  rw [Set.mem_union]
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Set.mem_setOf_eq] at h1 h2
  push Not at h1 h2
  refine hP (P.residue_eq_zero_of_mem ?_ ?_)
  · rw [Place.mem_toSubmodule_iff]
    rcases eq_or_ne ((α : (Q : Place k F) → F) P) 0 with h3 | h3
    · rw [h3, Valuation.map_zero]
      exact zero_le
    · have h4 := h1 h3
      rw [← P.ord_nonneg_iff h3]
      omega
  · rw [Place.mem_toSubmodule_iff]
    exact h2

/-- **The residue functional of `dg`**: the finite sum of the local
residues `res_P(α_P dg)`, as a linear functional on the adele
module. -/
noncomputable def residueFunctional (g : F) :
    Module.Dual k ↥(adeleSubmodule k F) where
  toFun α := ∑ᶠ P : Place k F,
    P.residue ((α : (Q : Place k F) → F) P) g
  map_add' α β := by
    have h1 : ∀ P : Place k F,
        P.residue (((α + β : ↥(adeleSubmodule k F)) :
          (Q : Place k F) → F) P) g =
        P.residue ((α : (Q : Place k F) → F) P) g +
          P.residue ((β : (Q : Place k F) → F) P) g := by
      intro P
      have h2 : ((α + β : ↥(adeleSubmodule k F)) :
          (Q : Place k F) → F) P =
          (α : (Q : Place k F) → F) P +
            (β : (Q : Place k F) → F) P := rfl
      rw [h2, Place.residue_add_left]
    rw [finsum_congr h1]
    exact finsum_add_distrib (residue_support_finite g α)
      (residue_support_finite g β)
  map_smul' c α := by
    have h1 : ∀ P : Place k F,
        P.residue (((c • α : ↥(adeleSubmodule k F)) :
          (Q : Place k F) → F) P) g =
        c • P.residue ((α : (Q : Place k F) → F) P) g := by
      intro P
      have h2 : ((c • α : ↥(adeleSubmodule k F)) :
          (Q : Place k F) → F) P =
          c • (α : (Q : Place k F) → F) P := rfl
      rw [h2, Place.residue_smul_left]
      rfl
    rw [finsum_congr h1, ← smul_finsum]
    rfl

theorem residueFunctional_apply (g : F) (α : ↥(adeleSubmodule k F)) :
    residueFunctional g α = ∑ᶠ P : Place k F,
      P.residue ((α : (Q : Place k F) → F) P) g := rfl

/-- The residue functional is additive in its differential
parameter. -/
theorem residueFunctional_add (g h : F) :
    residueFunctional (k := k) (F := F) (g + h) =
      residueFunctional g + residueFunctional h := by
  ext α
  rw [LinearMap.add_apply, residueFunctional_apply,
    residueFunctional_apply, residueFunctional_apply]
  have hpoint : ∀ P : Place k F,
      P.residue ((α : (Q : Place k F) → F) P) (g + h) =
        P.residue ((α : (Q : Place k F) → F) P) g +
          P.residue ((α : (Q : Place k F) → F) P) h :=
    fun P ↦ P.residue_add_right _ _ _
  rw [finsum_congr hpoint]
  exact finsum_add_distrib (residue_support_finite g α)
    (residue_support_finite h α)

/-- The residue functional scales in its differential parameter. -/
theorem residueFunctional_smul (c : k) (g : F) :
    residueFunctional (k := k) (F := F) (c • g) =
      c • residueFunctional g := by
  ext α
  rw [LinearMap.smul_apply, residueFunctional_apply,
    residueFunctional_apply]
  have hpoint : ∀ P : Place k F,
      P.residue ((α : (Q : Place k F) → F) P) (c • g) =
        c • P.residue ((α : (Q : Place k F) → F) P) g := by
    intro P
    rw [P.residue_smul_right]
    rfl
  rw [finsum_congr hpoint, ← smul_finsum]

/-- The linear map sending a function to the residue differential of
its formal differential. -/
noncomputable def residueFunctionalLinearMap :
    F →ₗ[k] Module.Dual k ↥(adeleSubmodule k F) where
  toFun := residueFunctional
  map_add' := residueFunctional_add
  map_smul' := residueFunctional_smul

@[simp]
theorem residueFunctionalLinearMap_apply (g : F) :
    residueFunctionalLinearMap (k := k) (F := F) g =
      residueFunctional g := rfl

/-- The residue functional evaluates as a finite sum over any
covering set of places. -/
theorem residueFunctional_eq_sum {g : F} {α : ↥(adeleSubmodule k F)}
    {S : Finset (Place k F)}
    (hS : ∀ P ∉ S,
      P.residue ((α : (Q : Place k F) → F) P) g = 0) :
    residueFunctional g α =
      ∑ P ∈ S, P.residue ((α : (Q : Place k F) → F) P) g := by
  refine finsum_eq_finsetSum_of_support_subset _ fun P hP ↦ ?_
  rw [Function.mem_support] at hP
  by_contra h
  exact hP (hS P h)

/-- The residue functional on an adele supported at one place is the
corresponding local residue. -/
theorem residueFunctional_adeleSingle (P : Place k F) (f g : F) :
    residueFunctional g (adeleSingle P f) = P.residue f g := by
  classical
  rw [residueFunctional_eq_sum (S := {P}) (fun Q hQ ↦ ?_),
    Finset.sum_singleton, adeleSingle_coe,
    adeleSinglePi_apply_self]
  have hQP : Q ≠ P := by
    simpa using hQ
  rw [adeleSingle_coe, adeleSinglePi_apply_ne P hQP]
  exact Q.residue_zero_left g

/-- Inverting the differential parameter shifts its residue functional
by multiplication with the square:
`ω_t = -(ω_{t⁻¹} ∘ m_{t²})`. -/
theorem residueFunctional_eq_neg_comp_inv {t : F} (ht : t ≠ 0) :
    residueFunctional (k := k) (F := F) t =
      -(residueFunctional t⁻¹ ∘ₗ adeleSMul (t ^ 2)) := by
  ext α
  simp only [LinearMap.neg_apply, LinearMap.comp_apply]
  rw [residueFunctional_apply, residueFunctional_apply]
  have hpoint : ∀ P : Place k F,
      P.residue ((α : (Q : Place k F) → F) P) t =
        -P.residue
          (((adeleSMul (t ^ 2) α : ↥(adeleSubmodule k F)) :
            (Q : Place k F) → F) P) t⁻¹ := by
    intro P
    simpa only [adeleSMul_coe, adeleMulMap_apply] using
      P.residue_eq_neg_residue_sq_inv ht
        ((α : (Q : Place k F) → F) P)
  rw [finsum_congr hpoint]
  have hfin : Function.HasFiniteSupport (fun P : Place k F ↦
      P.residue
        (((adeleSMul (t ^ 2) α : ↥(adeleSubmodule k F)) :
          (Q : Place k F) → F) P) t⁻¹) :=
    residue_support_finite t⁻¹ (adeleSMul (t ^ 2) α)
  simpa only [LinearMap.neg_apply, LinearMap.id_apply] using
    (map_finsum (-LinearMap.id : k →ₗ[k] k) hfin).symm

/-- Greatest levels of the residue differentials of `t` and `t⁻¹`
differ by the principal divisor of `t²`. -/
theorem isGreatest_level_residueFunctional_inv {t : F} (ht : t ≠ 0)
    {W Winv : Divisor k F}
    (hW : residueFunctional (k := k) (F := F) t ∈
      weilDifferentialsAt W)
    (hmax : ∀ D, residueFunctional (k := k) (F := F) t ∈
      weilDifferentialsAt D → D ≤ W)
    (hWinv : residueFunctional (k := k) (F := F) t⁻¹ ∈
      weilDifferentialsAt Winv)
    (hmaxinv : ∀ D, residueFunctional (k := k) (F := F) t⁻¹ ∈
      weilDifferentialsAt D → D ≤ Winv) :
    W = Winv + divisorOf k (t ^ 2) := by
  have hcomp := isGreatest_level_comp hWinv hmaxinv
    (pow_ne_zero 2 ht)
  have hnew : residueFunctional (k := k) (F := F) t ∈
      weilDifferentialsAt (Winv + divisorOf k (t ^ 2)) := by
    rw [residueFunctional_eq_neg_comp_inv ht]
    exact Submodule.neg_mem _ hcomp.1
  have hle : Winv + divisorOf k (t ^ 2) ≤ W := hmax _ hnew
  have hcompW :
      residueFunctional (k := k) (F := F) t⁻¹ ∘ₗ adeleSMul (t ^ 2) ∈
        weilDifferentialsAt W := by
    have hneg := Submodule.neg_mem (weilDifferentialsAt W) hW
    rw [residueFunctional_eq_neg_comp_inv ht] at hneg
    simpa only [neg_neg] using hneg
  exact le_antisymm (hcomp.2 W hcompW) hle

/-- Pointwise form of the inverse-level shift. -/
theorem isGreatest_level_residueFunctional_inv_apply {t : F}
    (ht : t ≠ 0) {W Winv : Divisor k F}
    (hW : residueFunctional (k := k) (F := F) t ∈
      weilDifferentialsAt W)
    (hmax : ∀ D, residueFunctional (k := k) (F := F) t ∈
      weilDifferentialsAt D → D ≤ W)
    (hWinv : residueFunctional (k := k) (F := F) t⁻¹ ∈
      weilDifferentialsAt Winv)
    (hmaxinv : ∀ D, residueFunctional (k := k) (F := F) t⁻¹ ∈
      weilDifferentialsAt D → D ≤ Winv)
    (P : Place k F) :
    W P = Winv P + 2 * P.ord t := by
  have h := congrArg (fun D : Divisor k F ↦ D P)
    (isGreatest_level_residueFunctional_inv ht hW hmax hWinv hmaxinv)
  rw [Finsupp.add_apply, divisorOf_apply (pow_ne_zero 2 ht),
    P.ord_pow ht] at h
  omega

/-- **The residue functional kills the diagonal**: the residue
theorem in functional form. -/
theorem residueFunctional_diagonal (g h : F) :
    residueFunctional g
      (⟨adeleDiagonal k F h, adeleDiagonal_mem_adeleSubmodule h⟩ :
        ↥(adeleSubmodule k F)) = 0 := by
  classical
  rcases eq_or_ne h 0 with rfl | hh
  · rw [residueFunctional_eq_sum (S := (∅ : Finset (Place k F)))
      (fun P _ ↦ ?_), Finset.sum_empty]
    have h2 : ((⟨adeleDiagonal k F 0,
        adeleDiagonal_mem_adeleSubmodule 0⟩ :
        ↥(adeleSubmodule k F)) : (Q : Place k F) → F) P = 0 := by
      change adeleDiagonal k F 0 P = 0
      rw [map_zero]
      rfl
    rw [h2]
    exact P.residue_zero_left g
  rcases eq_or_ne g 0 with rfl | hg
  · rw [residueFunctional_eq_sum (S := (∅ : Finset (Place k F)))
      (fun P _ ↦ P.residue_zero_right _), Finset.sum_empty]
  set S : Finset (Place k F) :=
    (finite_setOf_one_lt_valuation hh).toFinset ∪
      (finite_setOf_one_lt_valuation hg).toFinset with hSdef
  have hcoord : ∀ P : Place k F,
      ((⟨adeleDiagonal k F h, adeleDiagonal_mem_adeleSubmodule h⟩ :
        ↥(adeleSubmodule k F)) : (Q : Place k F) → F) P = h :=
    fun P ↦ rfl
  have hmem : ∀ Q : Place k F, Q ∉ S →
      h ∈ Q.toSubmodule ∧ g ∈ Q.toSubmodule := by
    intro Q hQ
    rw [hSdef, Finset.mem_union] at hQ
    push Not at hQ
    obtain ⟨h1, h2⟩ := hQ
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h1 h2
    push Not at h1 h2
    exact ⟨h1, h2⟩
  have h1 : residueFunctional g
      (⟨adeleDiagonal k F h, adeleDiagonal_mem_adeleSubmodule h⟩ :
        ↥(adeleSubmodule k F)) = ∑ P ∈ S, P.residue h g := by
    rw [residueFunctional_eq_sum (S := S) (fun P hP ↦ ?_)]
    · exact Finset.sum_congr rfl fun P _ ↦ by rw [hcoord]
    · rw [hcoord]
      obtain ⟨hh', hg'⟩ := hmem P hP
      exact P.residue_eq_zero_of_mem hh' hg'
  rw [h1]
  exact sum_residue_eq_zero h g S hmem

/-- **The residue functional is a Weil differential**: it kills the
bounded space at level `−2 · (pole divisor of g)` — integral pairs at
good places, the depth threshold at the poles. -/
theorem residueFunctional_mem_weilDifferentialsAt {g : F}
    (hg : g ≠ 0) :
    residueFunctional (k := k) (F := F) g ∈
      weilDifferentialsAt (-((2 : ℤ) • (-(divisorOf k g)).pos)) := by
  rw [mem_weilDifferentialsAt_iff]
  intro α hα
  rw [mem_boundedSubmodule_iff] at hα
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hα
  obtain ⟨h, rfl⟩ := hw
  have hu' : u ∈ adeleSubmodule k F :=
    adeleSpace_le_adeleSubmodule _ hu
  have hα' : α = (⟨u, hu'⟩ : ↥(adeleSubmodule k F)) +
      ⟨adeleDiagonal k F h, adeleDiagonal_mem_adeleSubmodule h⟩ :=
    Subtype.ext huw.symm
  rw [hα', map_add, residueFunctional_diagonal, add_zero]
  rw [residueFunctional_eq_sum (S := (∅ : Finset (Place k F)))
    (fun P _ ↦ ?_), Finset.sum_empty]
  have hcoord : ((⟨u, hu'⟩ : ↥(adeleSubmodule k F)) :
      (Q : Place k F) → F) P = u P := rfl
  rw [hcoord]
  rcases eq_or_ne (u P) 0 with h0 | h0
  · rw [h0]
    exact P.residue_zero_left g
  have h1 := (hu P).resolve_left h0
  have h2 : (-((2 : ℤ) • (-(divisorOf k g)).pos)) P =
      -(2 * max (-(P.ord g)) 0) := by
    rw [Finsupp.neg_apply, Finsupp.smul_apply, smul_eq_mul,
      Divisor.pos, Finsupp.mapRange_apply, Finsupp.neg_apply,
      divisorOf_apply hg]
  rw [h2] at h1
  rcases le_or_gt 0 (P.ord g) with hgP | hgP
  · refine P.residue_eq_zero_of_mem ?_ ?_
    · rw [Place.mem_toSubmodule_iff, ← P.ord_nonneg_iff h0]
      omega
    · rw [Place.mem_toSubmodule_iff, ← P.ord_nonneg_iff hg]
      exact hgP
  · refine P.residue_eq_zero_of_ord_ge (m := (-(P.ord g)).toNat)
      h0 hg ?_ ?_
    · omega
    · omega

/-- **The residue functional of a uniformizer is nonzero**: it takes
the value `1` on the single-place adele `π⁻¹`. -/
theorem residueFunctional_pi_ne_zero (P : Place k F) :
    residueFunctional (k := k) (F := F) P.pi ≠ 0 := by
  intro h0
  have h1 : residueFunctional (k := k) (F := F) P.pi
      (adeleSingle P (P.pi)⁻¹) = 0 := by
    rw [h0, LinearMap.zero_apply]
  rw [residueFunctional_eq_sum (S := {P}) (fun Q hQ ↦ ?_)] at h1
  · rw [Finset.sum_singleton] at h1
    have h2 : ((adeleSingle P (P.pi)⁻¹ : ↥(adeleSubmodule k F)) :
        (Q : Place k F) → F) P = (P.pi)⁻¹ :=
      adeleSinglePi_apply_self P _
    rw [h2, P.residue_inv_self P.pi_ne_zero
      (by rw [P.ord_pi]; omega), P.ord_pi] at h1
    simp at h1
  · have h3 : ((adeleSingle P (P.pi)⁻¹ : ↥(adeleSubmodule k F)) :
        (R : Place k F) → F) Q = 0 :=
      adeleSinglePi_apply_ne P (by simpa using hQ) _
    rw [h3]
    exact Q.residue_zero_left _

end

end AclGeom
