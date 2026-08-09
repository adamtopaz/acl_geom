/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.Adeles

/-!
# The index of specialty

The quotient `𝔸 / (A(D) + F)` and its dimension `i(D)`. The one-point
decomposition of adele spaces makes the quotient grow by at most a line
per point, and the dichotomy trades that line against the growth of the
Riemann–Roch space; chaining up to a genus-attaining divisor — where the
quotient vanishes by adelic surjectivity — yields Stichtenoth 1.5.4:
`i(D) = ℓ(D) − deg D − 1 + g`, i.e. the full Riemann–Roch identity with
`i(D)` as the correction term.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P5).
-/

namespace AclGeom

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- The subspace `A(D) + F` of the adele module. -/
noncomputable def boundedSubmodule (D : Divisor k F) :
    Submodule k ↥(adeleSubmodule k F) :=
  (adeleSpace D ⊔ LinearMap.range (adeleDiagonal k F)).comap
    (adeleSubmodule k F).subtype

theorem mem_boundedSubmodule_iff {D : Divisor k F}
    {α : ↥(adeleSubmodule k F)} :
    α ∈ boundedSubmodule D ↔
      (α : (Q : Place k F) → F) ∈
        adeleSpace D ⊔ LinearMap.range (adeleDiagonal k F) := Iff.rfl

theorem boundedSubmodule_mono {D E : Divisor k F} (h : D ≤ E) :
    boundedSubmodule (D : Divisor k F) ≤ boundedSubmodule E :=
  Submodule.comap_mono (sup_le_sup_right (adeleSpace_mono h) _)

/-- At genus-attaining divisors the bounded subspace is everything —
adelic surjectivity restated. -/
theorem boundedSubmodule_eq_top_of_defect_eq_genus {D : Divisor k F}
    (hD : D.defect = genus k F) : boundedSubmodule D = ⊤ := by
  rw [boundedSubmodule, Submodule.comap_subtype_eq_top]
  exact le_of_eq (adeleSubmodule_eq_sup_of_defect_eq_genus hD)

theorem adeleMonomial_mem_adeleSubmodule (P : Place k F) (n : ℤ) :
    adeleMonomial P n ∈ adeleSubmodule k F :=
  adeleSpace_le_adeleSubmodule (Finsupp.single P (-n))
    (adeleMonomial_mem_adeleSpace P
      (by rw [Finsupp.single_eq_same]; omega))

/-- The monomial adele as an element of the adele module. -/
noncomputable def adeleMonomialMem (P : Place k F) (n : ℤ) :
    ↥(adeleSubmodule k F) :=
  ⟨adeleMonomial P n, adeleMonomial_mem_adeleSubmodule P n⟩

/-- The one-point decomposition, inside the adele module: the bounded
subspace at `D + P` is spanned over the one at `D` by the monomial. -/
theorem boundedSubmodule_add_single (D : Divisor k F) (P : Place k F) :
    boundedSubmodule (D + Finsupp.single P 1) =
      boundedSubmodule D ⊔
        Submodule.span k {adeleMonomialMem P (-(D P) - 1)} := by
  refine le_antisymm ?_ (sup_le
    (boundedSubmodule_mono (Divisor.le_add_single D P)) ?_)
  · intro α hα
    have h1 : (α : (Q : Place k F) → F) ∈
        (adeleSpace D ⊔ LinearMap.range (adeleDiagonal k F)) ⊔
          Submodule.span k {adeleMonomial P (-(D P) - 1)} := by
      have h2 := mem_boundedSubmodule_iff.1 hα
      rw [adeleSpace_add_single P D, sup_right_comm] at h2
      exact h2
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy
    have hmem : α - c • adeleMonomialMem P (-(D P) - 1) ∈
        boundedSubmodule D := by
      rw [mem_boundedSubmodule_iff]
      have hcoe : ((α - c • adeleMonomialMem P (-(D P) - 1) :
          ↥(adeleSubmodule k F)) : (Q : Place k F) → F) = x := by
        rw [AddSubgroupClass.coe_sub, SetLike.val_smul]
        rw [show ((adeleMonomialMem P (-(D P) - 1) :
            ↥(adeleSubmodule k F)) : (Q : Place k F) → F) =
          adeleMonomial P (-(D P) - 1) from rfl]
        rw [← hxy, ← hc]
        abel
      rw [hcoe]
      exact hx
    have hα' : α = (α - c • adeleMonomialMem P (-(D P) - 1)) +
        c • adeleMonomialMem P (-(D P) - 1) := by abel
    rw [hα']
    exact Submodule.add_mem _ (Submodule.mem_sup_left hmem)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self _)))
  · rw [Submodule.span_singleton_le_iff_mem, mem_boundedSubmodule_iff]
    refine Submodule.mem_sup_left
      (adeleMonomial_mem_adeleSpace P ?_)
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
    omega

/-- The dichotomy, inside the adele module. -/
theorem adeleMonomialMem_mem_boundedSubmodule_iff (D : Divisor k F)
    (P : Place k F) :
    adeleMonomialMem P (-(D P) - 1) ∈ boundedSubmodule D ↔
      ∃ f, f ∈ RiemannSpace (D + Finsupp.single P 1) ∧
        f ∉ RiemannSpace D :=
  (mem_boundedSubmodule_iff).trans (adeleMonomial_mem_sup_iff P D)

/-- The **index of specialty** quotient `𝔸 / (A(D) + F)`. -/
abbrev SpecialtyQuotient (D : Divisor k F) :=
  ↥(adeleSubmodule k F) ⧸ boundedSubmodule D

/-- **Stichtenoth 1.5.4**: relative to a genus-attaining divisor `E`
above `D`, the specialty quotient is finite-dimensional of dimension
`(deg E − ℓ(E)) − (deg D − ℓ(D))` — each one-point step adds a line to
the quotient or to the Riemann–Roch space, never both. -/
theorem finiteDimensional_finrank_specialtyQuotient {D E : Divisor k F}
    (hE : E.defect = genus k F) (hDE : D ≤ E) :
    FiniteDimensional k (SpecialtyQuotient D) ∧
      (Module.finrank k (SpecialtyQuotient D) : ℤ) =
        (E.deg - Module.finrank k (RiemannSpace E)) -
          (D.deg - Module.finrank k (RiemannSpace D)) := by
  classical
  induction hmeas : ((E - D).deg).toNat using Nat.strong_induction_on
    generalizing D with
  | _ n ih =>
  rcases eq_or_ne D E with rfl | hne
  · -- At the top the quotient is trivial.
    haveI hsub : Subsingleton (SpecialtyQuotient D) := by
      refine ⟨fun a b ↦ ?_⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      rw [Submodule.Quotient.eq,
        boundedSubmodule_eq_top_of_defect_eq_genus hE]
      trivial
    refine ⟨Module.Finite.of_surjective
      (0 : (Fin 0 → k) →ₗ[k] SpecialtyQuotient D)
      (fun y ↦ ⟨0, Subsingleton.elim _ y⟩), ?_⟩
    rw [Module.finrank_zero_of_subsingleton]
    push_cast
    ring
  · -- Step up one point towards `E`.
    have hED : 0 ≤ E - D := by
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
    set D' : Divisor k F := D + Finsupp.single P 1 with hD'
    have hD'E : D' ≤ E := by
      intro Q
      rcases eq_or_ne Q P with rfl | hQ
      · rw [hD', Finsupp.add_apply, Finsupp.single_eq_same]
        omega
      · rw [hD', Finsupp.add_apply, Finsupp.single_eq_of_ne hQ,
          add_zero]
        exact hDE Q
    have hdeg1 : E - D' = E - D - Finsupp.single P 1 := by
      rw [hD']
      abel
    have hdegP : (E - D) P ≤ (E - D).deg := by
      rw [Divisor.deg, Finsupp.sum]
      exact Finset.single_le_sum (fun Q _ ↦ by simpa using hED Q) hP
    have hmeas' : ((E - D').deg).toNat < n := by
      rw [hdeg1, deg_sub_single]
      omega
    obtain ⟨ihfd, ihrk⟩ := ih _ hmeas' hD'E rfl
    haveI := ihfd
    -- The lattice step and the third isomorphism theorem.
    have hWW' : boundedSubmodule D ≤ boundedSubmodule D' :=
      boundedSubmodule_mono (Divisor.le_add_single D P)
    have hmap : (boundedSubmodule D').map (boundedSubmodule D).mkQ =
        Submodule.span k {(boundedSubmodule D).mkQ
          (adeleMonomialMem P (-(D P) - 1))} := by
      have hbot : (boundedSubmodule D).map (boundedSubmodule D).mkQ =
          ⊥ := by
        refine le_antisymm ?_ bot_le
        rintro y ⟨x, hx, rfl⟩
        rw [Submodule.mem_bot, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact hx
      rw [hD', boundedSubmodule_add_single D P, Submodule.map_sup,
        hbot, bot_sup_eq, Submodule.map_span, Set.image_singleton,
        Submodule.mkQ_apply]
    have hequiv := Submodule.quotientQuotientEquivQuotient
      (boundedSubmodule D) (boundedSubmodule D') hWW'
    haveI hfd2 : FiniteDimensional k
        ((SpecialtyQuotient D) ⧸ (boundedSubmodule D').map
          (boundedSubmodule D).mkQ) :=
      hequiv.symm.finiteDimensional
    haveI hfd3 : FiniteDimensional k
        ↥((boundedSubmodule D').map (boundedSubmodule D).mkQ) := by
      rw [hmap]
      exact FiniteDimensional.span_of_finite k (Set.finite_singleton _)
    haveI hfd1 : FiniteDimensional k (SpecialtyQuotient D) :=
      Module.Finite.of_submodule_quotient
        ((boundedSubmodule D').map (boundedSubmodule D).mkQ)
    refine ⟨hfd1, ?_⟩
    -- Dimension bookkeeping.
    have hadd := Submodule.finrank_quotient_add_finrank
      ((boundedSubmodule D').map (boundedSubmodule D).mkQ)
    have hq : Module.finrank k
        ((SpecialtyQuotient D) ⧸ (boundedSubmodule D').map
          (boundedSubmodule D).mkQ) =
        Module.finrank k (SpecialtyQuotient D') := hequiv.finrank_eq
    have hadd' : Module.finrank k
        ((SpecialtyQuotient D) ⧸ (boundedSubmodule D').map
          (boundedSubmodule D).mkQ) +
        Module.finrank k
          ↥((boundedSubmodule D').map (boundedSubmodule D).mkQ) =
        Module.finrank k (SpecialtyQuotient D) := hadd
    have hdegD' : D'.deg = D.deg + 1 := by
      have h1 : D' - Finsupp.single P 1 = D := by rw [hD']; abel
      have h2 := deg_sub_single D' P
      rw [h1] at h2
      omega
    -- The dichotomy decides the two growth patterns.
    by_cases hjump : ∃ f, f ∈ RiemannSpace D' ∧ f ∉ RiemannSpace D
    · -- Monomial absorbed; the Riemann–Roch space jumps by one.
      have hmem : adeleMonomialMem P (-(D P) - 1) ∈
          boundedSubmodule D := by
        refine (adeleMonomialMem_mem_boundedSubmodule_iff D P).2 ?_
        rwa [hD'] at hjump
      have hzero : (boundedSubmodule D).mkQ
          (adeleMonomialMem P (-(D P) - 1)) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hmem
      have hspan0 : Module.finrank k
          ↥((boundedSubmodule D').map (boundedSubmodule D).mkQ) = 0 := by
        rw [hmap, hzero, Submodule.span_zero_singleton k]
        exact finrank_bot k _
      have hlt : RiemannSpace D < RiemannSpace D' := by
        refine lt_of_le_of_ne ?_ ?_
        · rw [hD']
          exact riemannSpace_mono (Divisor.le_add_single D P)
        · intro heq
          obtain ⟨f, hf1, hf2⟩ := hjump
          rw [← heq] at hf1
          exact hf2 hf1
      have hltrk := Submodule.finrank_lt_finrank_of_lt hlt
      have hle : Module.finrank k (RiemannSpace D') ≤
          Module.finrank k (RiemannSpace D) + 1 := by
        rw [hD']
        exact finrank_riemannSpace_add_single_le D P
      omega
    · -- Monomial independent; the Riemann–Roch space is unchanged.
      have hnmem : adeleMonomialMem P (-(D P) - 1) ∉
          boundedSubmodule D := by
        intro hmem
        refine hjump ?_
        have h := (adeleMonomialMem_mem_boundedSubmodule_iff D P).1 hmem
        rwa [← hD'] at h
      have hne0 : (boundedSubmodule D).mkQ
          (adeleMonomialMem P (-(D P) - 1)) ≠ 0 := by
        intro h0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
        exact hnmem h0
      have hspan1 : Module.finrank k
          ↥((boundedSubmodule D').map (boundedSubmodule D).mkQ) = 1 := by
        rw [hmap]
        exact finrank_span_singleton hne0
      have hrk : Module.finrank k (RiemannSpace D') =
          Module.finrank k (RiemannSpace D) := by
        have hDD : D' - Finsupp.single P 1 = D := by
          rw [hD']
          abel
        have h := riemannSpace_eq_or_eq_sup D' P
        rw [hDD] at h
        rcases h with heq | ⟨f₀, hf₀, heq⟩
        · rw [heq]
        · have hf₀D : f₀ ∈ RiemannSpace D := by
            by_contra hf₀D
            exact hjump ⟨f₀, hf₀, hf₀D⟩
          have hle : Submodule.span k {f₀} ≤ RiemannSpace D := by
            rw [Submodule.span_singleton_le_iff_mem]
            exact hf₀D
          rw [heq, sup_eq_left.2 hle]
      omega

/-- The specialty quotient is finite-dimensional for every divisor. -/
instance finiteDimensional_specialtyQuotient (D : Divisor k F) :
    FiniteDimensional k (SpecialtyQuotient D) := by
  obtain ⟨E, hDE, hE⟩ := exists_le_defect_eq_genus D
  exact (finiteDimensional_finrank_specialtyQuotient hE hDE).1

/-- The **index of specialty** `i(D)`: the codimension of `A(D) + F`
in the adeles. -/
noncomputable def specialtyIndex (D : Divisor k F) : ℤ :=
  Module.finrank k (SpecialtyQuotient D)

theorem specialtyIndex_nonneg (D : Divisor k F) :
    0 ≤ specialtyIndex D :=
  Int.natCast_nonneg _

/-- The index vanishes at genus-attaining divisors. -/
theorem specialtyIndex_eq_zero_of_defect_eq_genus {D : Divisor k F}
    (hD : D.defect = genus k F) : specialtyIndex D = 0 := by
  have h := (finiteDimensional_finrank_specialtyQuotient hD le_rfl).2
  rw [specialtyIndex]
  omega

/-- **Riemann–Roch with the index of specialty** (Stichtenoth 1.5.4):
`ℓ(D) = deg D + 1 − g + i(D)` for every divisor. -/
theorem finrank_riemannSpace_eq_add_specialtyIndex (D : Divisor k F) :
    (Module.finrank k (RiemannSpace D) : ℤ) =
      D.deg + 1 - genus k F + specialtyIndex D := by
  obtain ⟨E, hDE, hE⟩ := exists_le_defect_eq_genus D
  have h := (finiteDimensional_finrank_specialtyQuotient hE hDE).2
  have hEfr := finrank_riemannSpace_eq_of_defect_eq_genus hE
  rw [specialtyIndex]
  omega

end

end AclGeom
