/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.Triple

/-!
# The canonical code tuple of a germ

Blueprint `sources/group_configuration/04-germs.tex`, the code tuple of `def:germcode` and the
equivariance and injectivity in `rem:code-param`.

* The coordinate vector of the reduced row echelon basis of a subspace (`rrefVec`) is indexed
  by pairs of indices; rows that are not pivot rows are zero. It is equivariant under field
  automorphisms (`rrefVec_map`), generates the field of definition (`closure_range_rrefVec`)
  and determines the subspace (`eq_of_rrefVec_eq`).
* The code tuple of an ideal up to degree `D` (`codeVec`) lists the coordinates of the reduced
  row echelon bases of its degree pieces of degree at most `D`. It is padded with zeros at the
  rows of non-pivot indices, so that its index type `CodeIndex` does not depend on the ideal.
  It is a canonical encoding of the source's code tuple, not the unpadded coordinate list
  itself (`rrefVec_of_isPivot`, `rrefVec_of_not_isPivot` identify the two kinds of entries).
  It is equivariant (`codeVec_map`). Once `D` is at least the least degree `genDeg I` in which
  `I` is generated, it generates the field of definition of `I` (`closure_range_codeVec`) and
  determines `I` (`eq_of_codeVec_eq`).
* The code tuple of a germ (`Germ.code`) is the code tuple of its graph ideal up to that
  degree. It generates the canonical base (`Germ.adjoin_range_code`). Conjugation acts on code
  tuples coordinatewise (`Germ.codeVec_graphIdeal_map`) and preserves the degree bound
  (`Germ.genDeg_graphIdeal_map`), and a germ is determined by its code
  (`Germ.eq_of_codeVec_graphIdeal_eq`).
* The codes of the members of a generic set are exactly the generic points of its code
  variety (`Germ.isGen_codeVec_of_mem_orbit`, `Germ.exists_mem_orbit_codeVec_eq`), and a
  member is determined by its code (`Germ.eq_of_mem_orbit_of_codeVec_eq`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the code tuple of `def:germcode`, as a canonical zero-padded RREF encoding, is
complete. So are the equivariance and injectivity of codes in `rem:code-param` and the
parametrisation of a generic set by the generic points of its code variety in `def:genset`.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

/-! ### The coordinate vector of a reduced row echelon basis -/

section Rref

variable {R : Type*} [Field R] {𝓜 : Type*} [Finite 𝓜] [LinearOrder 𝓜]
  (W : Submodule R (𝓜 → R))

open Classical in
/-- The coordinates of the reduced row echelon basis of `W`, indexed by pairs of indices: the
row of a pivot index `μ` at `(μ, ν)`, and zero when `μ` is not a pivot index. -/
def rrefVec (p : 𝓜 × 𝓜) : R := if h : IsPivot W p.1 then rref W ⟨p.1, h⟩ p.2 else 0

theorem rrefVec_of_isPivot {μ : 𝓜} (h : IsPivot W μ) (ν : 𝓜) :
    rrefVec W (μ, ν) = rref W ⟨μ, h⟩ ν := by
  unfold rrefVec
  split_ifs with h'
  · rfl
  · exact absurd h h'

theorem rrefVec_of_not_isPivot {μ : 𝓜} (h : ¬ IsPivot W μ) (ν : 𝓜) : rrefVec W (μ, ν) = 0 := by
  unfold rrefVec
  split_ifs with h'
  · exact absurd h' h
  · rfl

theorem rrefVec_mem_fod (p : 𝓜 × 𝓜) : rrefVec W p ∈ fod W := by
  rcases p with ⟨μ, ν⟩
  by_cases h : IsPivot W μ
  · rw [rrefVec_of_isPivot W h]
    exact rref_apply_mem_fod W _ _
  · rw [rrefVec_of_not_isPivot W h]
    exact zero_mem _

/-- The coordinate vector generates the field of definition. -/
theorem closure_range_rrefVec : Subfield.closure (range (rrefVec W)) = fod W := by
  refine le_antisymm (Subfield.closure_le.2 ?_) ?_
  · rintro _ ⟨p, rfl⟩
    exact rrefVec_mem_fod W p
  · change Subfield.closure (fodSet W) ≤ _
    refine Subfield.closure_le.2 ?_
    rintro _ ⟨⟨μ, ν⟩, rfl⟩
    exact Subfield.subset_closure ⟨(μ.1, ν), rrefVec_of_isPivot W μ.2 ν⟩

/-- The coordinate vector is equivariant under field automorphisms. -/
theorem rrefVec_map (σ : R ≃+* R) : rrefVec (W.map (mapVec σ)) = ⇑σ ∘ rrefVec W := by
  ext ⟨μ, ν⟩
  by_cases h : IsPivot W μ
  · rw [Function.comp_apply, rrefVec_of_isPivot _ ((isPivot_map_iff W σ μ).2 h), rref_map,
      mapVec_apply, rrefVec_of_isPivot W h]
    rfl
  · rw [Function.comp_apply, rrefVec_of_not_isPivot _ fun h' ↦ h ((isPivot_map_iff W σ μ).1 h'),
      rrefVec_of_not_isPivot W h, map_zero]

/-- The coordinate vector determines the subspace. -/
theorem eq_of_rrefVec_eq {W W' : Submodule R (𝓜 → R)} (h : rrefVec W = rrefVec W') :
    W = W' := by
  have key : ∀ V : Submodule R (𝓜 → R), V = Submodule.span R
      {v | ∃ μ, rrefVec V (μ, μ) = 1 ∧ v = fun ν ↦ rrefVec V (μ, ν)} := by
    intro V
    conv_lhs => rw [← span_range_rref V]
    congr 1
    ext v
    constructor
    · rintro ⟨μ, rfl⟩
      refine ⟨μ.1, ?_, funext fun ν ↦ (rrefVec_of_isPivot V μ.2 ν).symm⟩
      rw [rrefVec_of_isPivot V μ.2]
      exact rref_apply_self V μ
    · rintro ⟨μ, hμ, rfl⟩
      have hp : IsPivot V μ := by
        by_contra hp
        rw [rrefVec_of_not_isPivot V hp] at hμ
        exact zero_ne_one hμ
      exact ⟨⟨μ, hp⟩, funext fun ν ↦ (rrefVec_of_isPivot V hp ν).symm⟩
  rw [key W, key W', h]

end Rref

/-! ### The code tuple of an ideal -/

section Ideal

variable {K : Type*} [Field K] {ι : Type*} [Finite ι]

/-- The index type of the code tuple up to degree `D`: a degree `d ≤ D` and a pair of monomials
of degree at most `d`. -/
abbrev CodeIndex (ι : Type*) (D : ℕ) : Type _ :=
  Σ d : Fin (D + 1), Monomials ι d × Monomials ι d

/-- `def:germcode`, for ideals: the code tuple up to degree `D`, the coordinates of the reduced
row echelon bases of the degree pieces of degree at most `D`. -/
def codeVec (D : ℕ) (I : Ideal (MvPolynomial ι K)) : CodeIndex ι D → K :=
  fun p ↦ rrefVec (degSubspace I p.1) p.2

/-- The code tuple is equivariant under field automorphisms. -/
theorem codeVec_map (D : ℕ) (I : Ideal (MvPolynomial ι K)) (σ : K ≃+* K) :
    codeVec D (I.map (MvPolynomial.map σ.toRingHom)) = ⇑σ ∘ codeVec D I := by
  ext p
  simp only [codeVec, Function.comp_apply, degSubspace_map, rrefVec_map]

theorem exists_span_eq (I : Ideal (MvPolynomial ι K)) :
    ∃ d, Ideal.span {f | f ∈ I ∧ f.totalDegree ≤ d} = I :=
  (exists_forall_idealDefinedOver_iff I).imp fun _ h ↦ h.1

open Classical in
/-- The least degree `d₀` in which an ideal is generated (`def:germcode`). -/
def genDeg (I : Ideal (MvPolynomial ι K)) : ℕ := Nat.find (exists_span_eq I)

theorem span_eq_of_genDeg_le {I : Ideal (MvPolynomial ι K)} {D : ℕ} (hD : genDeg I ≤ D) :
    Ideal.span {f | f ∈ I ∧ f.totalDegree ≤ D} = I := by
  classical
  have h0 : Ideal.span {f | f ∈ I ∧ f.totalDegree ≤ genDeg I} = I :=
    Nat.find_spec (exists_span_eq I)
  refine le_antisymm (Ideal.span_le.2 fun f hf ↦ hf.1) ?_
  conv_lhs => rw [← h0]
  exact Ideal.span_mono fun f hf ↦ ⟨hf.1, hf.2.trans hD⟩

theorem genDeg_le {I : Ideal (MvPolynomial ι K)} {D : ℕ}
    (h : Ideal.span {f | f ∈ I ∧ f.totalDegree ≤ D} = I) : genDeg I ≤ D := by
  classical
  exact Nat.find_min' (exists_span_eq I) h

/-- `lem:ideal-filtration`(3): an ideal generated in degree at most `d` has the field of
definition of its degree-`d` piece. -/
theorem idealFod_eq_fod_of_span {I : Ideal (MvPolynomial ι K)} {d : ℕ}
    (hd : Ideal.span {f | f ∈ I ∧ f.totalDegree ≤ d} = I) :
    idealFod I = fod (degSubspace I d) :=
  le_antisymm (idealDefinedOver_iff.1 (idealDefinedOver_of_span _ hd (fun _ hf ↦ hf.2)
    (DefinedOver.of_fod_le le_rfl))) (fod_degSubspace_le_idealFod I d)

/-- `def:germcode`: the code tuple generates the field of definition. -/
theorem closure_range_codeVec {D : ℕ} {I : Ideal (MvPolynomial ι K)} (hD : genDeg I ≤ D) :
    Subfield.closure (range (codeVec D I)) = idealFod I := by
  refine le_antisymm (Subfield.closure_le.2 ?_) ?_
  · rintro _ ⟨p, rfl⟩
    exact fod_degSubspace_le_idealFod I p.1 (rrefVec_mem_fod _ p.2)
  · rw [idealFod_eq_fod_of_span (span_eq_of_genDeg_le hD), ← closure_range_rrefVec]
    exact Subfield.closure_mono fun _ ⟨q, hq⟩ ↦ ⟨⟨⟨D, Nat.lt_succ_self D⟩, q⟩, hq⟩

/-- The code tuple determines the ideal. -/
theorem eq_of_codeVec_eq {D : ℕ} {I J : Ideal (MvPolynomial ι K)} (hI : genDeg I ≤ D)
    (hJ : genDeg J ≤ D) (h : codeVec D I = codeVec D J) : I = J := by
  have hW : degSubspace I D = degSubspace J D :=
    eq_of_rrefVec_eq (funext fun q ↦ congrFun h ⟨⟨D, Nat.lt_succ_self D⟩, q⟩)
  have key : ∀ L : Ideal (MvPolynomial ι K), {f | f ∈ L ∧ f.totalDegree ≤ D} =
      {f | f.totalDegree ≤ D ∧ coeffVec D f ∈ degSubspace L D} := by
    intro L
    ext f
    constructor
    · rintro ⟨hfL, hfd⟩
      exact ⟨hfd, coeffVec_mem_degSubspace hfL hfd⟩
    · rintro ⟨hfd, hf⟩
      obtain ⟨f', hf'L, hf'd, hf'⟩ := mem_degSubspace_iff.1 hf
      have hmem : ∀ {p : MvPolynomial ι K}, p.totalDegree ≤ D →
          p ∈ (restrictTotalDegree ι K D : Set (MvPolynomial ι K)) := fun hp ↦ by
        rw [SetLike.mem_coe, mem_restrictTotalDegree]
        exact hp
      have hff : f' = f := coeffVec_injOn D (hmem hf'd) (hmem hfd) hf'
      exact ⟨hff ▸ hf'L, hfd⟩
  rw [← span_eq_of_genDeg_le hI, ← span_eq_of_genDeg_le hJ, key I, key J, hW]

/-- Conjugation by a field automorphism preserves the degree in which an ideal is
generated. -/
theorem genDeg_map (I : Ideal (MvPolynomial ι K)) (σ : K ≃+* K) :
    genDeg (I.map (MvPolynomial.map σ.toRingHom)) = genDeg I := by
  have hψφ : ∀ p : MvPolynomial ι K,
      MvPolynomial.map σ.symm.toRingHom (MvPolynomial.map σ.toRingHom p) = p := fun p ↦ by
    simp [MvPolynomial.map_map, MvPolynomial.map_id]
  have hφψ : ∀ p : MvPolynomial ι K,
      MvPolynomial.map σ.toRingHom (MvPolynomial.map σ.symm.toRingHom p) = p := fun p ↦ by
    simp [MvPolynomial.map_map, MvPolynomial.map_id]
  have hcomp : (MvPolynomial.map σ.symm.toRingHom).comp (MvPolynomial.map σ.toRingHom) =
      RingHom.id (MvPolynomial ι K) := RingHom.ext hψφ
  have hJ : ∀ J : Ideal (MvPolynomial ι K),
      (J.map (MvPolynomial.map σ.toRingHom)).map (MvPolynomial.map σ.symm.toRingHom) = J :=
    fun J ↦ by rw [Ideal.map_map, hcomp, Ideal.map_id]
  /- The low-degree members of the image ideal are the images of the low-degree members. -/
  have himage : ∀ d, {f | f ∈ I.map (MvPolynomial.map σ.toRingHom) ∧ f.totalDegree ≤ d} =
      MvPolynomial.map σ.toRingHom '' {f | f ∈ I ∧ f.totalDegree ≤ d} := fun d ↦ by
    ext f
    constructor
    · rintro ⟨hf, hfd⟩
      refine ⟨MvPolynomial.map σ.symm.toRingHom f, ⟨?_, ?_⟩, hφψ f⟩
      · rw [← hJ I]
        exact Ideal.mem_map_of_mem _ hf
      · rwa [totalDegree_map_ringEquiv]
    · rintro ⟨g, ⟨hg, hgd⟩, rfl⟩
      exact ⟨Ideal.mem_map_of_mem _ hg, by rwa [totalDegree_map_ringEquiv]⟩
  have hiff : ∀ d, Ideal.span {f | f ∈ I.map (MvPolynomial.map σ.toRingHom) ∧
      f.totalDegree ≤ d} = I.map (MvPolynomial.map σ.toRingHom) ↔
      Ideal.span {f | f ∈ I ∧ f.totalDegree ≤ d} = I := fun d ↦ by
    rw [himage, ← Ideal.map_span]
    refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
    have h' := congrArg (Ideal.map (MvPolynomial.map σ.symm.toRingHom)) h
    rwa [hJ, hJ] at h'
  exact le_antisymm (genDeg_le ((hiff _).2 (span_eq_of_genDeg_le le_rfl)))
    (genDeg_le ((hiff _).1 (span_eq_of_genDeg_le le_rfl)))

end Ideal

/-! ### The code tuple of a germ -/

section Germ

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] {ι κ : Type*}
  [Finite ι] [Finite κ] {a : ι → K} {a' : κ → K} [IsAlgClosed k] [UniversalDomain k K]

namespace Germ

/-- `def:germcode`: the code tuple of a germ, the coordinates of the reduced row echelon bases
of the degree pieces of its graph ideal up to the least degree in which the graph ideal is
generated. -/
def code (g : Germ k a a') : CodeIndex (ι ⊕ κ) (genDeg g.graphIdeal) → K :=
  codeVec _ g.graphIdeal

/-- `def:germcode`: the code tuple generates the canonical base. -/
theorem adjoin_range_code (g : Germ k a a') : adjoin k (range g.code) = g.cb := by
  change adjoin k (range (codeVec (genDeg g.graphIdeal) g.graphIdeal)) = g.cb
  rw [cb, ← closure_range_codeVec (le_refl (genDeg g.graphIdeal)), adjoin_coe_closure]

/-- `rem:code-param`: conjugation preserves the length of the code tuple. -/
theorem genDeg_graphIdeal_map (σ : K ≃ₐ[k] K) (g : Germ k a a') :
    genDeg (g.map σ).graphIdeal = genDeg g.graphIdeal := by
  rw [graphIdeal_map, genDeg_map]

/-- `rem:code-param`: conjugation acts coordinatewise on code tuples of a given length. With
`genDeg_graphIdeal_map`, the code tuple of `σ g` is `σ` applied to the code tuple of `g`. -/
theorem codeVec_graphIdeal_map (D : ℕ) (σ : K ≃ₐ[k] K) (g : Germ k a a') :
    codeVec D (g.map σ).graphIdeal = ⇑σ ∘ codeVec D g.graphIdeal := by
  rw [graphIdeal_map]
  exact codeVec_map D _ σ.toRingEquiv

/-- `rem:code-param`: a germ is determined by its code tuple. -/
theorem eq_of_codeVec_graphIdeal_eq {D : ℕ} {g g' : Germ k a a'}
    (hg : genDeg g.graphIdeal ≤ D) (hg' : genDeg g'.graphIdeal ≤ D)
    (h : codeVec D g.graphIdeal = codeVec D g'.graphIdeal) : g = g' :=
  graphIdeal_injective (GroupConfig.eq_of_codeVec_eq hg hg' h)

/-! ### Generic sets of germs and their codes -/

theorem genDeg_graphIdeal_of_mem_orbit {g₀ g : Germ k a a'} (hg : g ∈ orbit g₀) :
    genDeg g.graphIdeal = genDeg g₀.graphIdeal := by
  obtain ⟨σ, rfl⟩ := hg
  exact genDeg_graphIdeal_map σ g₀

/-- `def:genset`: the codes of the members of a generic set are generic points of the code
variety. -/
theorem isGen_codeVec_of_mem_orbit (D : ℕ) {g₀ g : Germ k a a'} (hg : g ∈ orbit g₀) :
    IsGen k (codeVec D g₀.graphIdeal) (codeVec D g.graphIdeal) := by
  obtain ⟨σ, rfl⟩ := hg
  dsimp only
  rw [codeVec_graphIdeal_map]
  exact IsGen.map rfl σ

/-- `def:genset`: every generic point of the code variety is the code of a member of the
generic set. -/
theorem exists_mem_orbit_codeVec_eq (D : ℕ) (g₀ : Germ k a a')
    {c : CodeIndex (ι ⊕ κ) D → K} (hc : IsGen k (codeVec D g₀.graphIdeal) c) :
    ∃ g ∈ orbit g₀, codeVec D g.graphIdeal = c := by
  obtain ⟨σ, -, hσ⟩ := exists_ambientAutomorphism_of_idealOf_eq (k := k) hc.symm
  exact ⟨g₀.map σ, ⟨σ, rfl⟩, by rw [codeVec_graphIdeal_map]; exact funext hσ⟩

/-- `def:genset`: members of a generic set with the same code are equal. With
`isGen_codeVec_of_mem_orbit` and `exists_mem_orbit_codeVec_eq`, `g ↦ code g` is a bijection
from the generic set onto the generic points of its code variety. -/
theorem eq_of_mem_orbit_of_codeVec_eq {g₀ g g' : Germ k a a'} (hg : g ∈ orbit g₀)
    (hg' : g' ∈ orbit g₀)
    (h : codeVec (genDeg g₀.graphIdeal) g.graphIdeal =
      codeVec (genDeg g₀.graphIdeal) g'.graphIdeal) : g = g' :=
  eq_of_codeVec_graphIdeal_eq (genDeg_graphIdeal_of_mem_orbit hg).le
    (genDeg_graphIdeal_of_mem_orbit hg').le h

end Germ

end Germ

end

end GroupConfig
