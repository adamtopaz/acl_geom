/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.GenericExtension
import GroupConfig.FieldOfDefinition

/-!
# Fields of definition under scalar extension

Blueprint `sources/group_configuration/02-fields-of-definition.tex`, the remark after
`thm:weil-fod`: for a field extension `L ⊆ K` and an ideal `J` of `L[X]`,
`FOD(J · K[X]) = FOD(J)`, because `rref((J · K[X])_{≤d}) = rref(J_{≤d})`.

* For a subspace `W` of `L^𝓜` and a field embedding `f : L → K`, the scalar extension
  `GroupConfig.spanMap f W` is the `K`-span of the image of `W`. Its reduced row echelon basis
  is the image of that of `W`, under an increasing bijection of the pivots
  (`GroupConfig.exists_rref_spanMap`), so its field of definition is the image of that of `W`
  (`GroupConfig.fod_spanMap`). Reduced row echelon form is preserved by injective maps preserving
  `0` and `1` (`Matrix.IsReducedRowEchelon.map`).
* The degree pieces of `J · K[X]` are the scalar extensions of those of `J`
  (`GroupConfig.degSubspace_map_algebraMap`), by `lem:ideal-filtration`(1) and
  `lem:extcontr`(1). Hence `FOD(J · K[X])` is the image of `FOD(J)`
  (`GroupConfig.idealFod_map_algebraMap`).

The construction of `FOD` itself is already stated over an arbitrary field, which is the first
sentence of the remark.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the scalar-extension remark after `thm:weil-fod` is complete.
-/

/-- Reduced row echelon form is preserved by an injective map preserving `0` and `1`. -/
theorem Matrix.IsReducedRowEchelon.map {m n R S : Type*} [LT m] [LT n] [Zero R] [One R]
    [Zero S] [One S] {A : Matrix m n R} (hA : A.IsReducedRowEchelon) {f : R → S}
    (hf : Function.Injective f) (h0 : f 0 = 0) (h1 : f 1 = 1) :
    (A.map f).IsReducedRowEchelon := by
  have hz (x : R) : f x = 0 ↔ x = 0 := ⟨fun h ↦ hf (h.trans h0.symm), fun h ↦ h ▸ h0⟩
  have hlead (i : m) (c : n) : (A.map f).IsLeadingEntry i c ↔ A.IsLeadingEntry i c := by
    simp only [Matrix.IsLeadingEntry, Matrix.map_apply, ne_eq, hz]
  refine ⟨fun i₁ i₂ hlt j₂ hj ↦ ?_, fun i c h ↦ ?_, fun i₁ i₂ c hlt h ↦ ?_⟩
  · simp only [Matrix.map_apply, hz] at hj ⊢
    exact hA.isRowEchelon hlt hj
  · rw [Matrix.map_apply, hA.eq_one ((hlead i c).1 h), h1]
  · rw [Matrix.map_apply, hA.eq_zero hlt ((hlead i₂ c).1 h), h0]

namespace GroupConfig

open Module Set MvPolynomial

noncomputable section

/-! ### Subspaces -/

section Subspace

variable {L K : Type*} [Field L] [Field K] {𝓜 : Type*} (f : L →+* K)
  (W : Submodule L (𝓜 → L))

/-- The scalar extension of a subspace `W ⊆ L^𝓜` along `f : L → K`: the `K`-span of the image
of `W` in `K^𝓜`. -/
def spanMap : Submodule K (𝓜 → K) :=
  Submodule.span K ((fun v ↦ ⇑f ∘ v) '' W)

variable [Finite 𝓜] [LinearOrder 𝓜]

/-- The scalar extension is spanned by the image of the reduced row echelon basis. -/
theorem span_range_comp_rref :
    Submodule.span K (range fun μ : Pivots W ↦ ⇑f ∘ rref W μ) = spanMap f W := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨μ, rfl⟩
    exact Submodule.subset_span ⟨_, rref_mem W μ, rfl⟩
  · let T := Submodule.span K (range fun μ : Pivots W ↦ ⇑f ∘ rref W μ)
    rintro _ ⟨v, hv, rfl⟩
    rw [← span_range_rref W] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨μ, rfl⟩ := hx
      exact Submodule.subset_span ⟨μ, rfl⟩
    | zero =>
      change ⇑f ∘ (0 : 𝓜 → L) ∈ (T : Set (𝓜 → K))
      rw [show ⇑f ∘ (0 : 𝓜 → L) = 0 from funext fun _ ↦ map_zero f]
      exact T.zero_mem
    | add x y _ _ hx hy =>
      change ⇑f ∘ (x + y) ∈ (T : Set (𝓜 → K))
      rw [show ⇑f ∘ (x + y) = ⇑f ∘ x + ⇑f ∘ y from funext fun _ ↦ map_add f _ _]
      exact T.add_mem hx hy
    | smul c x _ hx =>
      change ⇑f ∘ (c • x) ∈ (T : Set (𝓜 → K))
      rw [show ⇑f ∘ (c • x) = f c • (⇑f ∘ x) from funext fun _ ↦ map_mul f _ _]
      exact T.smul_mem (f c) hx

/-- `rref((W ⊗ K)) = rref(W)`: the reduced row echelon basis of the scalar extension is the
image of that of `W`, under an increasing bijection of the pivots. -/
theorem exists_rref_spanMap :
    ∃ e : Pivots W ≃ Pivots (spanMap f W), StrictMono e ∧
      ∀ μ, rref (spanMap f W) (e μ) = ⇑f ∘ rref W μ := by
  classical
  let v : Pivots W → 𝓜 → K := fun μ ↦ ⇑f ∘ rref W μ
  have hv : LinearIndependent K v := by
    let w : Pivots W → (⊤ : Submodule K (𝓜 → K)) := fun μ ↦ ⟨v μ, trivial⟩
    have hw : LinearIndependent K w :=
      linearIndependent_of_leading ⊤ w (fun μ ↦ (μ : 𝓜)) Subtype.val_injective
        (fun μ ↦ by simp [w, v, rref_apply_self])
        (fun μ ν hν ↦ by simp [w, v, rref_apply_of_lt W μ hν])
    exact hw.map' (⊤ : Submodule K (𝓜 → K)).subtype (Submodule.ker_subtype _)
  let B : Basis (Pivots W) K (spanMap f W) :=
    (Basis.span hv).map (LinearEquiv.ofEq _ _ (span_range_comp_rref f W))
  have hBv (μ : Pivots W) : (B μ : 𝓜 → K) = v μ := by
    simp [B, Basis.span_apply]
  have hB : Matrix.IsReducedRowEchelon (fun μ ↦ (B μ : 𝓜 → K)) := by
    have hM : (fun μ ↦ (B μ : 𝓜 → K)) = Matrix.map (rref W) f :=
      funext fun μ ↦ by rw [hBv]; rfl
    rw [hM]
    exact (rref_isReducedRowEchelon W).map f.injective f.map_zero f.map_one
  obtain ⟨e, he, hBe⟩ := eq_rref_of_basis_isReducedRowEchelon (spanMap f W) B hB
  exact ⟨e, he, fun μ ↦ (hBe μ).symm.trans (hBv μ)⟩

/-- The field of definition of the scalar extension is the image of the field of definition. -/
theorem fod_spanMap : fod (spanMap f W) = (fod W).map f := by
  obtain ⟨e, -, he⟩ := exists_rref_spanMap f W
  have hset : fodSet (spanMap f W) = f '' fodSet W := by
    ext x
    constructor
    · rintro ⟨⟨μ', ν⟩, rfl⟩
      obtain ⟨μ, rfl⟩ := e.surjective μ'
      refine ⟨rref W μ ν, ⟨(μ, ν), rfl⟩, ?_⟩
      change f (rref W μ ν) = rref (spanMap f W) (e μ) ν
      rw [he μ]
      rfl
    · rintro ⟨_, ⟨⟨μ, ν⟩, rfl⟩, rfl⟩
      refine ⟨(e μ, ν), ?_⟩
      change rref (spanMap f W) (e μ) ν = f (rref W μ ν)
      rw [he μ]
      rfl
  unfold fod
  rw [hset]
  refine le_antisymm ?_ ?_
  · refine Subfield.closure_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, Subfield.subset_closure hx, rfl⟩
  · rw [Subfield.map_le_iff_le_comap]
    refine Subfield.closure_le.2 fun x hx ↦ ?_
    change f x ∈ Subfield.closure (f '' fodSet W)
    exact Subfield.subset_closure ⟨x, hx, rfl⟩

end Subspace

/-! ### Ideals -/

section Ideal

variable {L K : Type*} [Field L] [Field K] [Algebra L K] {ι : Type*}

/-- `lem:ideal-filtration`(1) for an extended ideal: the degree pieces of `J · K[X]` are the
scalar extensions of those of `J`. -/
theorem degSubspace_map_algebraMap (J : Ideal (MvPolynomial ι L)) (d : ℕ) :
    degSubspace (J.map (MvPolynomial.map (algebraMap L K))) d =
      spanMap (algebraMap L K) (degSubspace J d) := by
  set φ : MvPolynomial ι L →+* MvPolynomial ι K := MvPolynomial.map (algebraMap L K)
  have hinj : Function.Injective (algebraMap L K) := (algebraMap L K).injective
  have hdeg (q : MvPolynomial ι L) : (φ q).totalDegree = q.totalDegree := by
    unfold totalDegree
    rw [support_map_of_injective _ hinj]
  have hvec (q : MvPolynomial ι L) :
      coeffVec d (φ q) = ⇑(algebraMap L K) ∘ coeffVec d q := by
    funext m
    simp [φ, coeffVec_apply, coeff_map]
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · -- `J · K[X]` is generated by polynomials with coefficients in the image of `L`.
    let F : Subfield K := (algebraMap L K).fieldRange
    have hdef : IdealDefinedOver F (J.map φ) := by
      refine idealDefinedOver_of_le_span F (Ideal.span_le.2 ?_)
      rintro _ ⟨q, hq, rfl⟩
      exact Ideal.subset_span ⟨Ideal.mem_map_of_mem φ hq, fun m ↦ by
        rw [coeff_map]
        exact ⟨q.coeff m, rfl⟩⟩
    calc degSubspace (J.map φ) d
        = Submodule.span K {w | w ∈ degSubspace (J.map φ) d ∧ ∀ ν, w ν ∈ F} :=
          degSubspace_definedOver F hdef d
      _ ≤ spanMap (algebraMap L K) (degSubspace J d) := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨hw, hwF⟩
          obtain ⟨g, hgI, hgd, rfl⟩ := mem_degSubspace_iff.1 hw
          -- Every coefficient of `g` lies in the image of `L`.
          have hcoeff : (g.coeffs : Set K) ⊆ (algebraMap L K).range := by
            intro c hc
            obtain ⟨m, hm, rfl⟩ := mem_coeffs_iff.1 hc
            have hmd : m.sum (fun _ e ↦ e) ≤ d :=
              (le_totalDegree hm).trans hgd
            exact hwF ⟨m, hmd⟩
          obtain ⟨q, rfl⟩ := mem_range_map_iff_coeffs_subset.2 hcoeff
          have hqJ : q ∈ J := by
            rw [← AclGeom.comap_map_mvPolynomial_eq_self (E := K) J]
            exact hgI
          refine Submodule.subset_span ⟨coeffVec d q, coeffVec_mem_degSubspace hqJ ?_, ?_⟩
          · rw [← hdeg q]
            exact hgd
          · exact (hvec q).symm
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨q, hqJ, hqd, rfl⟩ := mem_degSubspace_iff.1 hw
    have h := coeffVec_mem_degSubspace (I := J.map φ) (Ideal.mem_map_of_mem φ hqJ)
      ((hdeg q).le.trans hqd)
    rw [hvec q] at h
    exact h

/-- The remark after `thm:weil-fod`: for an ideal `J` of `L[X]`, the field of definition of
`J · K[X]` is the image of the field of definition of `J`. -/
theorem idealFod_map_algebraMap [Finite ι] (J : Ideal (MvPolynomial ι L)) :
    idealFod (J.map (MvPolynomial.map (algebraMap L K))) =
      (idealFod J).map (algebraMap L K) := by
  unfold idealFod
  rw [Subfield.map_iSup]
  exact iSup_congr fun d ↦ by rw [degSubspace_map_algebraMap, fod_spanMap]

end Ideal

end

end GroupConfig
