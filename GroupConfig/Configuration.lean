/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.CanonicalBase

/-!
# Group configurations

Blueprint `sources/group_configuration/07-configurations.tex`, `def:gc`, `lem:gc-ranks` and
`lem:gc-invariance`(1),(3).

A group configuration (`GroupConfig.GroupConfiguration`) is a six-tuple `(a, b, c, x, y, z)`
of tuples with lines `{a, b, c}`, `{a, x, y}`, `{b, y, z}`, `{c, z, x}` satisfying the
conditions (GC1)–(GC5) of the blueprint; non-collinearity of index triples is the decidable
predicate `GroupConfig.GCCollinear` on `Fin 6` (with `0 = a, 1 = b, 2 = c, 3 = x, 4 = y,
5 = z`).  The definition is invariant under relabelings permuting the space lines
(`GroupConfiguration.swapBC`, `GroupConfiguration.swapAB`), under automorphisms
(`GroupConfiguration.map`) and under replacing points by interalgebraic ones
(`GroupConfiguration.ofRaclEq`).  The rank facts of `lem:gc-ranks` are
`GroupConfiguration.indepOver_pts`, `GroupConfiguration.erk_b_eq`, …

Canonical bases are invariant under renaming the variables by a bijection
(`GroupConfig.canonicalBase_comp_equiv`), which makes (GC4) symmetric in the two space points
of a line.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the six-point predicate, pairwise independence, equality of the
three group ranks and of the three space ranks, the generating relabelings,
and invariance under automorphisms and interalgebraic replacement are proved.
The remaining rank bounds, total-rank and point/line independence clauses are
proved in `GroupConfig.ConfigurationRanks`. Independent base change is in
`GroupConfig.ConfigurationBaseChange`, and extraction of the group of germs is in
`GroupConfig.Main`. The actual constructible presentations and their general configuration
consumer are proved in `GroupConfig.Constructible.CanonicalPresentation` and
`GroupConfig.MainConstructible`. Independent descent and necessity of the configuration
hypotheses are in `GroupConfig.ConfigurationNecessity`.
The predicate depends only on the canonical-base layer; no germ import is needed.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### Renaming the variables -/

section Rename

/-- Ring homomorphisms which are mutually inverse turn `map` into `comap`. -/
theorem Ideal.map_eq_comap_of_inverse {R S : Type*} [CommRing R] [CommRing S] {ρ : R →+* S}
    {ρ' : S →+* R} (h₁ : ρ'.comp ρ = RingHom.id R) (h₂ : ρ.comp ρ' = RingHom.id S)
    (J : Ideal R) : J.map ρ = J.comap ρ' := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 ?_) ?_
  · rw [Ideal.comap_comap, h₁, Ideal.comap_id]
  · intro p hp
    have : ρ (ρ' p) = p := RingHom.congr_fun h₂ p
    rw [← this]
    exact Ideal.mem_map_of_mem _ hp

variable {ι ι' : Type*}

theorem rename_comp_rename_symm_eq_id {R : Type*} [CommRing R] (e : ι ≃ ι') :
    (rename e.symm : MvPolynomial ι' R →ₐ[R] MvPolynomial ι R).toRingHom.comp
      (rename e : MvPolynomial ι R →ₐ[R] MvPolynomial ι' R).toRingHom = RingHom.id _ :=
  RingHom.ext fun p ↦ by
    change rename e.symm (rename e p) = p
    rw [rename_rename, e.symm_comp_self, rename_id_apply]

theorem mapF_comp_rename (F : Subfield K) (e : ι → ι') :
    (mapF F (ι := ι')).comp
        (rename e : MvPolynomial ι (↥F) →ₐ[↥F] MvPolynomial ι' (↥F)).toRingHom =
      (rename e : MvPolynomial ι K →ₐ[K] MvPolynomial ι' K).toRingHom.comp (mapF F) :=
  RingHom.ext fun p ↦ map_rename _ _ p

/-- Being defined over `F` is invariant under renaming the variables by a bijection. -/
theorem idealDefinedOver_map_rename (F : Subfield K) (e : ι ≃ ι')
    (I : Ideal (MvPolynomial ι K)) :
    IdealDefinedOver F
      (I.map (rename e : MvPolynomial ι K →ₐ[K] MvPolynomial ι' K).toRingHom) ↔
      IdealDefinedOver F I := by
  have h₁ := rename_comp_rename_symm_eq_id (R := K) e
  have h₂ := rename_comp_rename_symm_eq_id (R := K) e.symm
  have hF₁ := rename_comp_rename_symm_eq_id (R := ↥F) e
  have hF₂ := rename_comp_rename_symm_eq_id (R := ↥F) e.symm
  rw [Equiv.symm_symm] at h₂ hF₂
  have key1 : ∀ J : Ideal (MvPolynomial ι K),
      (J.map (rename e : MvPolynomial ι K →ₐ[K] _).toRingHom).comap (mapF F) =
        (J.comap (mapF F)).map (rename e : MvPolynomial ι (↥F) →ₐ[↥F] _).toRingHom := by
    intro J
    rw [Ideal.map_eq_comap_of_inverse h₁ h₂, Ideal.comap_comap, ← mapF_comp_rename,
      ← Ideal.comap_comap, Ideal.map_eq_comap_of_inverse hF₁ hF₂]
  have key2 : ∀ J : Ideal (MvPolynomial ι (↥F)),
      (J.map (rename e : MvPolynomial ι (↥F) →ₐ[↥F] _).toRingHom).map (mapF F) =
        (J.map (mapF F)).map (rename e : MvPolynomial ι K →ₐ[K] _).toRingHom := by
    intro J
    rw [Ideal.map_map, Ideal.map_map, mapF_comp_rename]
  unfold IdealDefinedOver
  rw [key1, key2]
  constructor
  · intro h
    have := congrArg (Ideal.map (rename e.symm : MvPolynomial ι' K →ₐ[K] _).toRingHom) h
    rwa [Ideal.map_map, Ideal.map_map, h₁, Ideal.map_id, Ideal.map_id] at this
  · intro h
    exact congrArg (Ideal.map (rename e : MvPolynomial ι K →ₐ[K] _).toRingHom) h

/-- The field of definition is invariant under renaming the variables by a bijection. -/
theorem idealFod_map_rename [Finite ι] [Finite ι'] (e : ι ≃ ι') (I : Ideal (MvPolynomial ι K)) :
    idealFod (I.map (rename e : MvPolynomial ι K →ₐ[K] MvPolynomial ι' K).toRingHom) =
      idealFod I :=
  le_antisymm
    (idealDefinedOver_iff.1 ((idealDefinedOver_map_rename _ e I).2 (idealDefinedOver_idealFod I)))
    (idealDefinedOver_iff.1 ((idealDefinedOver_map_rename _ e I).1 (idealDefinedOver_idealFod _)))

theorem idealOf_comp_equiv (L : Type*) [Field L] [Algebra L K] (a : ι' → K) (e : ι ≃ ι') :
    idealOf L (a ∘ e) =
      (idealOf L a).comap
        (rename e : MvPolynomial ι L →ₐ[L] MvPolynomial ι' L).toRingHom := by
  ext f
  rw [Ideal.mem_comap, mem_idealOf_iff, mem_idealOf_iff]
  change aeval (a ∘ e) f = 0 ↔ aeval a (rename e f) = 0
  rw [aeval_rename]

/-- The locus ideal is equivariant under renaming the variables by a bijection. -/
theorem locusIdeal_comp_equiv (L : Type*) [Field L] [Algebra L K] (a : ι' → K) (e : ι ≃ ι') :
    locusIdeal L (a ∘ e) =
      (locusIdeal L a).map
        (rename e.symm : MvPolynomial ι' K →ₐ[K] MvPolynomial ι K).toRingHom := by
  have hL₁ := rename_comp_rename_symm_eq_id (R := L) e
  have hL₂ := rename_comp_rename_symm_eq_id (R := L) e.symm
  rw [Equiv.symm_symm] at hL₂
  unfold locusIdeal
  rw [idealOf_comp_equiv, ← Ideal.map_eq_comap_of_inverse hL₂ hL₁, Ideal.map_map, Ideal.map_map]
  congr 1
  exact RingHom.ext fun p ↦ map_rename _ _ _

/-- The canonical base is invariant under renaming the variables by a bijection. -/
theorem canonicalBase_comp_equiv [Finite ι] [Finite ι'] (L : IntermediateField k K) (a : ι' → K)
    (e : ι ≃ ι') : canonicalBase L (a ∘ e) = canonicalBase L a := by
  unfold canonicalBase
  rw [locusIdeal_comp_equiv, idealFod_map_rename]

/-- The canonical base of a pair does not depend on the order of the pair. -/
theorem canonicalBase_sum_elim_swap [Finite ι] [Finite ι'] (L : IntermediateField k K)
    (x : ι → K) (y : ι' → K) : canonicalBase L (Sum.elim y x) = canonicalBase L (Sum.elim x y) := by
  rw [← canonicalBase_comp_equiv L (Sum.elim x y) (Equiv.sumComm ι' ι)]
  congr 1
  funext s
  cases s <;> rfl

end Rename

/-! ### Independent triples -/

variable (k) in
/-- Three sets are *independent* if the rank of their union is the sum of their ranks. -/
def IndepTriple (A B C : Set K) : Prop :=
  erk k ∅ (A ∪ B ∪ C) = erk k ∅ A + erk k ∅ B + erk k ∅ C

namespace IndepTriple

variable {A B C : Set K}

theorem perm_left (h : IndepTriple k A B C) : IndepTriple k B A C := by
  unfold IndepTriple at h ⊢
  rw [union_comm B A, add_comm (erk k ∅ B)]
  exact h

theorem perm_right (h : IndepTriple k A B C) : IndepTriple k A C B := by
  unfold IndepTriple at h ⊢
  rw [union_assoc, union_comm C B, ← union_assoc, add_assoc, add_comm (erk k ∅ C), ← add_assoc]
  exact h

theorem rotate (h : IndepTriple k A B C) : IndepTriple k B C A := h.perm_left.perm_right

theorem erk_union_left (h : IndepTriple k A B C) (hC : C.Finite) :
    erk k ∅ (A ∪ B) = erk k ∅ A + erk k ∅ B := by
  refine WithTop.add_right_cancel (erk_lt_top k hC ∅).ne (le_antisymm ?_ ?_)
  · exact add_le_add_left (erk_union_le k ∅ A B) _
  · exact h.symm.le.trans (erk_union_le k ∅ (A ∪ B) C)

theorem indepOver_left (h : IndepTriple k A B C) (hA : A.Finite) (hB : B.Finite)
    (hC : C.Finite) : IndepOver k ∅ A B := by
  have h1 := h.erk_union_left hC
  rw [erk_union_eq] at h1
  refine (indepOver_of_erk_eq hB ?_).symm
  exact WithTop.add_left_cancel (erk_lt_top k hA ∅).ne h1

/-- The first set is independent from the union of the other two. -/
theorem indepOver_union (h : IndepTriple k A B C) (hA : A.Finite) (hB : B.Finite)
    (hC : C.Finite) : IndepOver k ∅ A (B ∪ C) := by
  have h1 : erk k ∅ (A ∪ (B ∪ C)) = erk k ∅ A + erk k ∅ (B ∪ C) := by
    rw [← union_assoc, h, h.rotate.erk_union_left hA, add_assoc]
  rw [erk_union_eq] at h1
  refine (indepOver_of_erk_eq (hB.union hC) ?_).symm
  exact WithTop.add_left_cancel (erk_lt_top k hA ∅).ne h1

end IndepTriple

/-! ### The combinatorics of the six points -/

/-- The incidence table of the four lines `{a, b, c}`, `{a, x, y}`, `{b, y, z}`, `{c, z, x}` on
the six points `0 = a, 1 = b, 2 = c, 3 = x, 4 = y, 5 = z`. -/
def gcIncidence : Fin 4 → Fin 6 → Bool :=
  ![![true, true, true, false, false, false], ![true, false, false, true, true, false],
    ![false, true, false, false, true, true], ![false, false, true, true, false, true]]

/-- Collinearity of three indices: they lie on a common line. -/
def GCCollinear (i j l : Fin 6) : Prop :=
  ∃ n : Fin 4, gcIncidence n i = true ∧ gcIncidence n j = true ∧ gcIncidence n l = true

instance (i j l : Fin 6) : Decidable (GCCollinear i j l) := by
  unfold GCCollinear
  infer_instance

/-! ### Relabelings of the indices -/

/-- The index permutation of the relabeling exchanging the lines `{b, y, z}` and `{c, z, x}`. -/
def swapBCIdx : Fin 6 → Fin 6
  | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5

/-- The index permutation of the relabeling exchanging the lines `{a, x, y}` and `{b, y, z}`. -/
def swapABIdx : Fin 6 → Fin 6
  | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3

/-- The line permutation induced by `swapBCIdx`. -/
def swapBCLine : Fin 4 → Fin 4
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2

/-- The line permutation induced by `swapABIdx`. -/
def swapABLine : Fin 4 → Fin 4
  | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3

theorem swapBCIdx_swapBCIdx (i : Fin 6) : swapBCIdx (swapBCIdx i) = i := by
  fin_cases i <;> rfl

theorem swapABIdx_swapABIdx (i : Fin 6) : swapABIdx (swapABIdx i) = i := by
  fin_cases i <;> rfl

theorem gcIncidence_swapBCIdx (n : Fin 4) (i : Fin 6) :
    gcIncidence n (swapBCIdx i) = gcIncidence (swapBCLine n) i := by
  fin_cases n <;> fin_cases i <;> rfl

theorem gcIncidence_swapABIdx (n : Fin 4) (i : Fin 6) :
    gcIncidence n (swapABIdx i) = gcIncidence (swapABLine n) i := by
  fin_cases n <;> fin_cases i <;> rfl

theorem swapBCIdx_injective : Function.Injective swapBCIdx := fun i j h ↦
  (swapBCIdx_swapBCIdx i).symm.trans ((congrArg swapBCIdx h).trans (swapBCIdx_swapBCIdx j))

theorem swapABIdx_injective : Function.Injective swapABIdx := fun i j h ↦
  (swapABIdx_swapABIdx i).symm.trans ((congrArg swapABIdx h).trans (swapABIdx_swapABIdx j))

theorem gcCollinear_of_swapBCIdx {i j l : Fin 6}
    (h : GCCollinear (swapBCIdx i) (swapBCIdx j) (swapBCIdx l)) : GCCollinear i j l := by
  obtain ⟨n, h1, h2, h3⟩ := h
  rw [gcIncidence_swapBCIdx] at h1 h2 h3
  exact ⟨_, h1, h2, h3⟩

theorem gcCollinear_of_swapABIdx {i j l : Fin 6}
    (h : GCCollinear (swapABIdx i) (swapABIdx j) (swapABIdx l)) : GCCollinear i j l := by
  obtain ⟨n, h1, h2, h3⟩ := h
  rw [gcIncidence_swapABIdx] at h1 h2 h3
  exact ⟨_, h1, h2, h3⟩

variable {ι₁ ι₂ ι₃ ι₄ ι₅ ι₆ : Type*}

/-- The six points of a configuration, as sets of coordinates. -/
def gcPoints (a : ι₁ → K) (b : ι₂ → K) (c : ι₃ → K) (x : ι₄ → K) (y : ι₅ → K) (z : ι₆ → K) :
    Fin 6 → Set K :=
  ![range a, range b, range c, range x, range y, range z]

omit [Field K] in
theorem gcPoints_finite [Finite ι₁] [Finite ι₂] [Finite ι₃] [Finite ι₄] [Finite ι₅] [Finite ι₆]
    (a : ι₁ → K) (b : ι₂ → K) (c : ι₃ → K) (x : ι₄ → K) (y : ι₅ → K) (z : ι₆ → K) (i : Fin 6) :
    (gcPoints a b c x y z i).Finite := by
  fin_cases i <;> exact finite_range _

theorem GCCollinear.swap {i j l : Fin 6} (h : GCCollinear i j l) : GCCollinear j i l :=
  let ⟨n, h1, h2, h3⟩ := h
  ⟨n, h2, h1, h3⟩

theorem GCCollinear.swap' {i j l : Fin 6} (h : GCCollinear i j l) : GCCollinear i l j :=
  let ⟨n, h1, h2, h3⟩ := h
  ⟨n, h1, h3, h2⟩

/-- A property of index triples which is symmetric and holds for the sorted non-collinear
triples holds for all distinct non-collinear triples. -/
theorem forall_of_sorted {P : Fin 6 → Fin 6 → Fin 6 → Prop}
    (hswap : ∀ i j l, P i j l → P j i l) (hswap' : ∀ i j l, P i j l → P i l j)
    (hs : ∀ i j l, i < j → j < l → ¬ GCCollinear i j l → P i j l) :
    ∀ i j l, i ≠ j → i ≠ l → j ≠ l → ¬ GCCollinear i j l → P i j l := by
  intro i j l hij hil hjl hcol
  rcases lt_trichotomy i j with h1 | h1 | h1
  · rcases lt_trichotomy j l with h2 | h2 | h2
    · exact hs i j l h1 h2 hcol
    · exact absurd h2 hjl
    · rcases lt_trichotomy i l with h3 | h3 | h3
      · exact hswap' _ _ _ (hs i l j h3 h2 fun h ↦ hcol h.swap')
      · exact absurd h3 hil
      · exact hswap' _ _ _ (hswap _ _ _ (hs l i j h3 h1 fun h ↦ hcol h.swap.swap'))
  · exact absurd h1 hij
  · rcases lt_trichotomy i l with h2 | h2 | h2
    · exact hswap _ _ _ (hs j i l h1 h2 fun h ↦ hcol h.swap)
    · exact absurd h2 hil
    · rcases lt_trichotomy j l with h3 | h3 | h3
      · exact hswap _ _ _ (hswap' _ _ _ (hs j l i h3 h2 fun h ↦ hcol h.swap'.swap))
      · exact absurd h3 hjl
      · exact hswap _ _ _ (hswap' _ _ _ (hswap _ _ _
          (hs l j i h3 h1 fun h ↦ hcol h.swap.swap'.swap)))

/-- (GC3) follows from independence of the sixteen non-collinear triples
`{a, b, x}, {a, b, y}, …` (indices `0 = a, 1 = b, 2 = c, 3 = x, 4 = y, 5 = z`). -/
theorem indep_of_sixteen {pts : Fin 6 → Set K}
    (h013 : IndepTriple k (pts 0) (pts 1) (pts 3))
    (h014 : IndepTriple k (pts 0) (pts 1) (pts 4))
    (h015 : IndepTriple k (pts 0) (pts 1) (pts 5))
    (h023 : IndepTriple k (pts 0) (pts 2) (pts 3))
    (h024 : IndepTriple k (pts 0) (pts 2) (pts 4))
    (h025 : IndepTriple k (pts 0) (pts 2) (pts 5))
    (h035 : IndepTriple k (pts 0) (pts 3) (pts 5))
    (h045 : IndepTriple k (pts 0) (pts 4) (pts 5))
    (h123 : IndepTriple k (pts 1) (pts 2) (pts 3))
    (h124 : IndepTriple k (pts 1) (pts 2) (pts 4))
    (h125 : IndepTriple k (pts 1) (pts 2) (pts 5))
    (h134 : IndepTriple k (pts 1) (pts 3) (pts 4))
    (h135 : IndepTriple k (pts 1) (pts 3) (pts 5))
    (h234 : IndepTriple k (pts 2) (pts 3) (pts 4))
    (h245 : IndepTriple k (pts 2) (pts 4) (pts 5))
    (h345 : IndepTriple k (pts 3) (pts 4) (pts 5)) :
    ∀ i j l : Fin 6, i ≠ j → i ≠ l → j ≠ l → ¬ GCCollinear i j l →
      IndepTriple k (pts i) (pts j) (pts l) := by
  refine forall_of_sorted (fun _ _ _ h ↦ h.perm_left) (fun _ _ _ h ↦ h.perm_right) ?_
  intro i j l hij hjl hcol
  fin_cases i <;> fin_cases j <;> fin_cases l
  all_goals
    first
    | exact absurd hij (by decide)
    | exact absurd hjl (by decide)
    | exact absurd (by decide) hcol
    | skip
  exacts [h013, h014, h015, h023, h024, h025, h035, h045, h123, h124, h125, h134, h135, h234,
    h245, h345]

variable [Finite ι₁] [Finite ι₂] [Finite ι₃] [Finite ι₄] [Finite ι₅] [Finite ι₆]

/-- The rank of a union of two independent finite sets. -/
theorem erk_union_of_indepOver {A B : Set K} (hB : B.Finite) (h : IndepOver k ∅ A B) :
    erk k ∅ (A ∪ B) = erk k ∅ A + erk k ∅ B := by
  rw [erk_union_eq, h.symm.erk_eq (subset_refl _) hB]

theorem erk_eq_of_racl_eq {A B : Set K} (h : racl k A = racl k B) : erk k ∅ A = erk k ∅ B := by
  rw [← erk_racl k ∅ A, ← erk_racl k ∅ B, empty_union, empty_union, h]

theorem racl_union_congr {A A' B B' : Set K} (hA : racl k A = racl k A')
    (hB : racl k B = racl k B') : racl k (A ∪ B) = racl k (A' ∪ B') := by
  have key : ∀ A A' B B' : Set K, racl k A = racl k A' → racl k B = racl k B' →
      racl k (A ∪ B) ≤ racl k (A' ∪ B') := by
    intro A A' B B' hA hB
    refine racl_le_of_subset_racl (union_subset ?_ ?_)
    · exact (subset_racl k A).trans (hA ▸ racl_mono (k := k) subset_union_left)
    · exact (subset_racl k B).trans (hB ▸ racl_mono (k := k) subset_union_right)
  exact le_antisymm (key A A' B B' hA hB) (key A' A B' B hA.symm hB.symm)

theorem indepTriple_of_racl_eq {A A' B B' C C' : Set K} (hA : racl k A = racl k A')
    (hB : racl k B = racl k B') (hC : racl k C = racl k C') (h : IndepTriple k A B C) :
    IndepTriple k A' B' C' := by
  unfold IndepTriple at h ⊢
  rw [← erk_eq_of_racl_eq (racl_union_congr (racl_union_congr hA hB) hC), ← erk_eq_of_racl_eq hA,
    ← erk_eq_of_racl_eq hB, ← erk_eq_of_racl_eq hC]
  exact h

variable (k) in
/-- `def:gc`: a group configuration over `k`, with lines `{a, b, c}`, `{a, x, y}`, `{b, y, z}`,
`{c, z, x}`. -/
structure GroupConfiguration (a : ι₁ → K) (b : ι₂ → K) (c : ι₃ → K) (x : ι₄ → K) (y : ι₅ → K)
    (z : ι₆ → K) : Prop where
  /-- (GC1) -/
  racl_ab_ac : racl k (range a ∪ range b) = racl k (range a ∪ range c)
  /-- (GC1) -/
  racl_ab_bc : racl k (range a ∪ range b) = racl k (range b ∪ range c)
  /-- (GC2) -/
  racl_ax_ay : racl k (range a ∪ range x) = racl k (range a ∪ range y)
  /-- (GC2) -/
  racl_by_bz : racl k (range b ∪ range y) = racl k (range b ∪ range z)
  /-- (GC2) -/
  racl_cx_cz : racl k (range c ∪ range x) = racl k (range c ∪ range z)
  /-- (GC3): non-collinear triples are independent. -/
  indep : ∀ i j l : Fin 6, i ≠ j → i ≠ l → j ≠ l → ¬ GCCollinear i j l →
    IndepTriple k (gcPoints a b c x y z i) (gcPoints a b c x y z j) (gcPoints a b c x y z l)
  /-- (GC4) -/
  cb_a : range a ⊆ racl k (canonicalBase (racl k (range a)) (Sum.elim x y) : Set K)
  /-- (GC4) -/
  cb_b : range b ⊆ racl k (canonicalBase (racl k (range b)) (Sum.elim y z) : Set K)
  /-- (GC4) -/
  cb_c : range c ⊆ racl k (canonicalBase (racl k (range c)) (Sum.elim x z) : Set K)
  /-- (GC5) -/
  one_le_erk : 1 ≤ erk k ∅ (range a)

namespace GroupConfiguration

variable {a : ι₁ → K} {b : ι₂ → K} {c : ι₃ → K} {x : ι₄ → K} {y : ι₅ → K} {z : ι₆ → K}
  (hc : GroupConfiguration k a b c x y z)
include hc

/-- `lem:gc-ranks`: any two distinct points are independent. -/
theorem indepOver_pts {i j : Fin 6} (hij : i ≠ j) :
    IndepOver k ∅ (gcPoints a b c x y z i) (gcPoints a b c x y z j) := by
  have key : ∀ i j : Fin 6, i ≠ j → ∃ l, i ≠ l ∧ j ≠ l ∧ ¬ GCCollinear i j l := by decide
  obtain ⟨l, hil, hjl, hcol⟩ := key i j hij
  exact (hc.indep i j l hij hil hjl hcol).indepOver_left (gcPoints_finite a b c x y z i)
    (gcPoints_finite a b c x y z j) (gcPoints_finite a b c x y z l)

theorem indepOver_ab : IndepOver k ∅ (range a) (range b) :=
  hc.indepOver_pts (i := 0) (j := 1) (by decide)
theorem indepOver_ac : IndepOver k ∅ (range a) (range c) :=
  hc.indepOver_pts (i := 0) (j := 2) (by decide)
theorem indepOver_bc : IndepOver k ∅ (range b) (range c) :=
  hc.indepOver_pts (i := 1) (j := 2) (by decide)
theorem indepOver_ax : IndepOver k ∅ (range a) (range x) :=
  hc.indepOver_pts (i := 0) (j := 3) (by decide)
theorem indepOver_ay : IndepOver k ∅ (range a) (range y) :=
  hc.indepOver_pts (i := 0) (j := 4) (by decide)
theorem indepOver_by : IndepOver k ∅ (range b) (range y) :=
  hc.indepOver_pts (i := 1) (j := 4) (by decide)
theorem indepOver_bz : IndepOver k ∅ (range b) (range z) :=
  hc.indepOver_pts (i := 1) (j := 5) (by decide)
theorem indepOver_cx : IndepOver k ∅ (range c) (range x) :=
  hc.indepOver_pts (i := 2) (j := 3) (by decide)
theorem indepOver_cz : IndepOver k ∅ (range c) (range z) :=
  hc.indepOver_pts (i := 2) (j := 5) (by decide)
theorem indepOver_xy : IndepOver k ∅ (range x) (range y) :=
  hc.indepOver_pts (i := 3) (j := 4) (by decide)

/-- `lem:gc-ranks`: the group points have the same rank. -/
theorem erk_b_eq : erk k ∅ (range b) = erk k ∅ (range a) := by
  have h1 := erk_eq_of_racl_eq hc.racl_ab_bc
  rw [erk_union_of_indepOver (finite_range b) hc.indepOver_ab,
    erk_union_of_indepOver (finite_range c) hc.indepOver_bc] at h1
  have h2 := erk_eq_of_racl_eq hc.racl_ab_ac
  rw [erk_union_of_indepOver (finite_range b) hc.indepOver_ab,
    erk_union_of_indepOver (finite_range c) hc.indepOver_ac] at h2
  have h3 := WithTop.add_left_cancel (erk_lt_top k (finite_range a) ∅).ne h2
  rw [h3, add_comm] at h1
  exact h3.trans (WithTop.add_left_cancel (erk_lt_top k (finite_range c) ∅).ne h1).symm

theorem erk_c_eq : erk k ∅ (range c) = erk k ∅ (range a) := by
  have h2 := erk_eq_of_racl_eq hc.racl_ab_ac
  rw [erk_union_of_indepOver (finite_range b) hc.indepOver_ab,
    erk_union_of_indepOver (finite_range c) hc.indepOver_ac] at h2
  rw [← hc.erk_b_eq]
  exact (WithTop.add_left_cancel (erk_lt_top k (finite_range a) ∅).ne h2).symm

/-- `lem:gc-ranks`: the space points have the same rank. -/
theorem erk_y_eq : erk k ∅ (range y) = erk k ∅ (range x) := by
  have h := erk_eq_of_racl_eq hc.racl_ax_ay
  rw [erk_union_of_indepOver (finite_range x) hc.indepOver_ax,
    erk_union_of_indepOver (finite_range y) hc.indepOver_ay] at h
  exact (WithTop.add_left_cancel (erk_lt_top k (finite_range a) ∅).ne h).symm

theorem erk_z_eq : erk k ∅ (range z) = erk k ∅ (range x) := by
  have h := erk_eq_of_racl_eq hc.racl_by_bz
  rw [erk_union_of_indepOver (finite_range y) hc.indepOver_by,
    erk_union_of_indepOver (finite_range z) hc.indepOver_bz] at h
  rw [← hc.erk_y_eq]
  exact (WithTop.add_left_cancel (erk_lt_top k (finite_range b) ∅).ne h).symm

theorem one_le_erk_b : 1 ≤ erk k ∅ (range b) := hc.erk_b_eq ▸ hc.one_le_erk

theorem one_le_erk_c : 1 ≤ erk k ∅ (range c) := hc.erk_c_eq ▸ hc.one_le_erk

/-! ### Relabelings -/

omit [Field K] [Finite ι₁] [Finite ι₂] [Finite ι₃] [Finite ι₄] [Finite ι₅] [Finite ι₆] hc in
theorem gcPoints_swapBC (i : Fin 6) :
    gcPoints a c b y x z i = gcPoints a b c x y z (swapBCIdx i) := by
  fin_cases i <;> rfl

omit [Field K] [Finite ι₁] [Finite ι₂] [Finite ι₃] [Finite ι₄] [Finite ι₅] [Finite ι₆] hc in
theorem gcPoints_swapAB (i : Fin 6) :
    gcPoints b a c z y x i = gcPoints a b c x y z (swapABIdx i) := by
  fin_cases i <;> rfl

omit [Finite ι₁] [Finite ι₂] [Finite ι₃] in
/-- Relabeling by exchanging the lines `{b, y, z}` and `{c, z, x}`. -/
theorem swapBC : GroupConfiguration k a c b y x z where
  racl_ab_ac := hc.racl_ab_ac.symm
  racl_ab_bc := by rw [← hc.racl_ab_ac, hc.racl_ab_bc, union_comm]
  racl_ax_ay := hc.racl_ax_ay.symm
  racl_by_bz := hc.racl_cx_cz
  racl_cx_cz := hc.racl_by_bz
  indep i j l hij hil hjl hcol := by
    rw [gcPoints_swapBC i, gcPoints_swapBC j, gcPoints_swapBC l]
    exact hc.indep (swapBCIdx i) (swapBCIdx j) (swapBCIdx l) (fun h ↦ hij (swapBCIdx_injective h))
      (fun h ↦ hil (swapBCIdx_injective h)) (fun h ↦ hjl (swapBCIdx_injective h))
      (fun h ↦ hcol (gcCollinear_of_swapBCIdx h))
  cb_a := by
    rw [canonicalBase_sum_elim_swap]
    exact hc.cb_a
  cb_b := hc.cb_c
  cb_c := hc.cb_b
  one_le_erk := hc.one_le_erk

/-- Relabeling by exchanging the lines `{a, x, y}` and `{b, y, z}`. -/
theorem swapAB : GroupConfiguration k b a c z y x where
  racl_ab_ac := by rw [union_comm, hc.racl_ab_bc]
  racl_ab_bc := by rw [union_comm, hc.racl_ab_ac]
  racl_ax_ay := hc.racl_by_bz.symm
  racl_by_bz := hc.racl_ax_ay.symm
  racl_cx_cz := hc.racl_cx_cz.symm
  indep i j l hij hil hjl hcol := by
    rw [gcPoints_swapAB i, gcPoints_swapAB j, gcPoints_swapAB l]
    exact hc.indep (swapABIdx i) (swapABIdx j) (swapABIdx l) (fun h ↦ hij (swapABIdx_injective h))
      (fun h ↦ hil (swapABIdx_injective h)) (fun h ↦ hjl (swapABIdx_injective h))
      (fun h ↦ hcol (gcCollinear_of_swapABIdx h))
  cb_a := by
    rw [canonicalBase_sum_elim_swap]
    exact hc.cb_b
  cb_b := by
    rw [canonicalBase_sum_elim_swap]
    exact hc.cb_a
  cb_c := by
    rw [canonicalBase_sum_elim_swap]
    exact hc.cb_c
  one_le_erk := hc.one_le_erk_b

/-! ### Invariance -/

omit [Finite ι₁] [Finite ι₂] [Finite ι₃] [Finite ι₄] [Finite ι₅] [Finite ι₆] hc in
theorem gcPoints_map (σ : K ≃ₐ[k] K) (i : Fin 6) :
    gcPoints (⇑σ ∘ a) (⇑σ ∘ b) (⇑σ ∘ c) (⇑σ ∘ x) (⇑σ ∘ y) (⇑σ ∘ z) i =
      ⇑σ '' gcPoints a b c x y z i := by
  fin_cases i <;> exact range_comp _ _

omit [Finite ι₁] [Finite ι₂] [Finite ι₃] [Finite ι₄] [Finite ι₅] [Finite ι₆] hc in
theorem racl_range_comp_union (σ : K ≃ₐ[k] K) {ι ι' : Type*} (u : ι → K) (v : ι' → K) :
    racl k (range (⇑σ ∘ u) ∪ range (⇑σ ∘ v)) =
      (racl k (range u ∪ range v)).map σ.toAlgHom := by
  rw [range_comp, range_comp, ← image_union, racl_map]

omit [Finite ι₁] [Finite ι₂] [Finite ι₃] [Finite ι₄] [Finite ι₅] [Finite ι₆] hc in
theorem IndepTriple.image {A B C : Set K} (σ : K ≃ₐ[k] K) (h : IndepTriple k A B C) :
    IndepTriple k (⇑σ '' A) (⇑σ '' B) (⇑σ '' C) := by
  unfold IndepTriple at h ⊢
  rw [← image_union, ← image_union, ← image_empty ⇑σ, erk_image, erk_image, erk_image, erk_image]
  exact h

omit [Finite ι₁] [Finite ι₂] [Finite ι₃] [Finite ι₄] [Finite ι₅] [Finite ι₆] hc in
theorem erk_range_comp (σ : K ≃ₐ[k] K) {ι : Type*} (u : ι → K) :
    erk k ∅ (range (⇑σ ∘ u)) = erk k ∅ (range u) := by
  calc erk k ∅ (range (⇑σ ∘ u)) = erk k (⇑σ '' ∅) (⇑σ '' range u) := by
        rw [image_empty, range_comp]
    _ = erk k ∅ (range u) := erk_image σ ∅ (range u)

omit [Finite ι₁] [Finite ι₂] [Finite ι₃] in
/-- `lem:gc-invariance`(1): the image of a configuration under an automorphism over `k`. -/
theorem map (σ : K ≃ₐ[k] K) :
    GroupConfiguration k (⇑σ ∘ a) (⇑σ ∘ b) (⇑σ ∘ c) (⇑σ ∘ x) (⇑σ ∘ y) (⇑σ ∘ z) where
  racl_ab_ac := by rw [racl_range_comp_union, racl_range_comp_union, hc.racl_ab_ac]
  racl_ab_bc := by rw [racl_range_comp_union, racl_range_comp_union, hc.racl_ab_bc]
  racl_ax_ay := by rw [racl_range_comp_union, racl_range_comp_union, hc.racl_ax_ay]
  racl_by_bz := by rw [racl_range_comp_union, racl_range_comp_union, hc.racl_by_bz]
  racl_cx_cz := by rw [racl_range_comp_union, racl_range_comp_union, hc.racl_cx_cz]
  indep i j l hij hil hjl hcol := by
    rw [gcPoints_map σ i, gcPoints_map σ j, gcPoints_map σ l]
    exact IndepTriple.image σ (hc.indep i j l hij hil hjl hcol)
  cb_a := by
    rw [← Sum.comp_elim, range_comp, ← racl_map, canonicalBase_map, coe_map,
      AlgEquiv.coe_toAlgHom, ← racl_map, coe_map, AlgEquiv.coe_toAlgHom]
    exact image_mono hc.cb_a
  cb_b := by
    rw [← Sum.comp_elim, range_comp, ← racl_map, canonicalBase_map, coe_map,
      AlgEquiv.coe_toAlgHom, ← racl_map, coe_map, AlgEquiv.coe_toAlgHom]
    exact image_mono hc.cb_b
  cb_c := by
    rw [← Sum.comp_elim, range_comp, ← racl_map, canonicalBase_map, coe_map,
      AlgEquiv.coe_toAlgHom, ← racl_map, coe_map, AlgEquiv.coe_toAlgHom]
    exact image_mono hc.cb_c
  one_le_erk := by
    rw [erk_range_comp]
    exact hc.one_le_erk

/-- `lem:gc-invariance`(3): replacing the points by interalgebraic ones. -/
theorem ofRaclEq [IsAlgClosed K] [UniversalDomain k K] {ι₁' ι₂' ι₃' ι₄' ι₅' ι₆' : Type*}
    [Finite ι₁'] [Finite ι₂'] [Finite ι₃'] [Finite ι₄'] [Finite ι₅'] [Finite ι₆']
    {a' : ι₁' → K} {b' : ι₂' → K} {c' : ι₃' → K} {x' : ι₄' → K} {y' : ι₅' → K} {z' : ι₆' → K}
    (ha : racl k (range a') = racl k (range a)) (hb : racl k (range b') = racl k (range b))
    (hc' : racl k (range c') = racl k (range c)) (hx : racl k (range x') = racl k (range x))
    (hy : racl k (range y') = racl k (range y)) (hz : racl k (range z') = racl k (range z)) :
    GroupConfiguration k a' b' c' x' y' z' := by
  have _ : IsAlgClosed ↥(racl k (range a)) := isAlgClosed_racl _
  have _ : IsAlgClosed ↥(racl k (range b)) := isAlgClosed_racl _
  have _ : IsAlgClosed ↥(racl k (range c)) := isAlgClosed_racl _
  have hpts : ∀ i, racl k (gcPoints a' b' c' x' y' z' i) = racl k (gcPoints a b c x y z i) := by
    intro i
    fin_cases i
    exacts [ha, hb, hc', hx, hy, hz]
  have hxy : racl k (range (Sum.elim x y)) = racl k (range (Sum.elim x' y')) := by
    rw [Sum.elim_range, Sum.elim_range]
    exact (racl_union_congr hx hy).symm
  have hyz : racl k (range (Sum.elim y z)) = racl k (range (Sum.elim y' z')) := by
    rw [Sum.elim_range, Sum.elim_range]
    exact (racl_union_congr hy hz).symm
  have hxz : racl k (range (Sum.elim x z)) = racl k (range (Sum.elim x' z')) := by
    rw [Sum.elim_range, Sum.elim_range]
    exact (racl_union_congr hx hz).symm
  exact
    { racl_ab_ac := by rw [racl_union_congr ha hb, racl_union_congr ha hc', hc.racl_ab_ac]
      racl_ab_bc := by rw [racl_union_congr ha hb, racl_union_congr hb hc', hc.racl_ab_bc]
      racl_ax_ay := by rw [racl_union_congr ha hx, racl_union_congr ha hy, hc.racl_ax_ay]
      racl_by_bz := by rw [racl_union_congr hb hy, racl_union_congr hb hz, hc.racl_by_bz]
      racl_cx_cz := by rw [racl_union_congr hc' hx, racl_union_congr hc' hz, hc.racl_cx_cz]
      indep i j l hij hil hjl hcol :=
        indepTriple_of_racl_eq (hpts i).symm (hpts j).symm (hpts l).symm
          (hc.indep i j l hij hil hjl hcol)
      cb_a := by
        have hL : IsSmall k ((racl k (range a) : IntermediateField k K) : Set K) :=
          (IsSmall.of_finite (finite_range a)).racl
        have e : racl k (canonicalBase (racl k (range a)) (Sum.elim x y) : Set K) =
            racl k (canonicalBase (racl k (range a)) (Sum.elim x' y') : Set K) :=
          racl_canonicalBase_eq_of_racl_eq hL hxy
        have h1 : (racl k (range a) : Set K) ⊆
            (racl k (canonicalBase (racl k (range a)) (Sum.elim x' y') : Set K) : Set K) := by
          rw [← e]
          exact SetLike.coe_subset_coe.2 (racl_le_of_subset_racl hc.cb_a)
        refine (subset_racl k (range a')).trans ?_
        rw [ha]
        exact h1
      cb_b := by
        have hL : IsSmall k ((racl k (range b) : IntermediateField k K) : Set K) :=
          (IsSmall.of_finite (finite_range b)).racl
        have e : racl k (canonicalBase (racl k (range b)) (Sum.elim y z) : Set K) =
            racl k (canonicalBase (racl k (range b)) (Sum.elim y' z') : Set K) :=
          racl_canonicalBase_eq_of_racl_eq hL hyz
        have h1 : (racl k (range b) : Set K) ⊆
            (racl k (canonicalBase (racl k (range b)) (Sum.elim y' z') : Set K) : Set K) := by
          rw [← e]
          exact SetLike.coe_subset_coe.2 (racl_le_of_subset_racl hc.cb_b)
        refine (subset_racl k (range b')).trans ?_
        rw [hb]
        exact h1
      cb_c := by
        have hL : IsSmall k ((racl k (range c) : IntermediateField k K) : Set K) :=
          (IsSmall.of_finite (finite_range c)).racl
        have e : racl k (canonicalBase (racl k (range c)) (Sum.elim x z) : Set K) =
            racl k (canonicalBase (racl k (range c)) (Sum.elim x' z') : Set K) :=
          racl_canonicalBase_eq_of_racl_eq hL hxz
        have h1 : (racl k (range c) : Set K) ⊆
            (racl k (canonicalBase (racl k (range c)) (Sum.elim x' z') : Set K) : Set K) := by
          rw [← e]
          exact SetLike.coe_subset_coe.2 (racl_le_of_subset_racl hc.cb_c)
        refine (subset_racl k (range c')).trans ?_
        rw [hc']
        exact h1
      one_le_erk := by
        rw [erk_eq_of_racl_eq ha]
        exact hc.one_le_erk }

end GroupConfiguration

end

end GroupConfig
