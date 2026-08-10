/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import AclGeom.Correspondence.Composition

/-!
# Generic members of finite-correspondence families

A parameterized family is represented at a generic member by a tuple
`(p, x, y)`: the parameter tuple `p` is independent, `x` is generic over
`p`, and `x,y` are interalgebraic over `k(p)`.  This is the elementwise
form of the generic graph used throughout blueprint §8.

The central relocation theorem in this module moves the independent prefix
`(p,x)` to any other independent tuple while preserving the complete
vanishing ideal of `(p,x,y)`.  Consequently the same family locus has a
member above every independent generic parameter/source pair.  Unlike an
unconstrained relocation, the new prefix is fixed literally; this is what
is needed to compose varying family members on compatible normal covers.

This module starts the positive-dimensional family layer above the finite
branch groupoids.
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- Relocate a finite algebraic tuple while fixing a chosen independent
coordinate subsystem literally.  The map `e` identifies the coordinates
of `u` that equal the independent tuple `t`; every coordinate of `u` is
algebraic over `k(t)`.  Any other independent tuple `s` can therefore be
installed at those same coordinate positions without changing the complete
vanishing ideal of the full tuple. -/
theorem exists_tuple_relocation_fixing [IsAlgClosed Ω] {n m : ℕ}
    {t s : Fin n → Ω} {u : Fin m → Ω} {e : Fin n → Fin m}
    (ht : AlgebraicIndependent k t) (hs : AlgebraicIndependent k s)
    (he : ∀ i, u (e i) = t i)
    (hu : ∀ j, u j ∈ racl k (Set.range t)) :
    ∃ v : Fin m → Ω,
      idealOf k v = idealOf k u ∧ ∀ i, v (e i) = s i := by
  classical
  let E := adjoin k (Set.range t)
  let L := adjoin k (Set.range u)
  have hle : E ≤ L := by
    apply adjoin.mono
    rintro _ ⟨i, rfl⟩
    have hti : t i ∈ Set.range u := ⟨e i, he i⟩
    exact hti
  have halg : Algebra.IsAlgebraic (↥E) (↥(extendScalars hle)) := by
    apply isAlgebraic_extendScalars_adjoin hle
    rintro _ ⟨j, rfl⟩
    exact (mem_racl_iff k).1 (hu j)
  obtain ⟨ψ, hψ⟩ := exists_extension_of_isAlgebraic
    (halg := halg) hle (adjoinTranscendentalAlgHom ht hs)
  have huMem (j : Fin m) : u j ∈ L :=
    subset_adjoin k _ (Set.mem_range_self j)
  let ua : Fin m → ↥L := fun j ↦ ⟨u j, huMem j⟩
  let v : Fin m → Ω := fun j ↦ ψ (ua j)
  have hfix (i : Fin n) : v (e i) = s i := by
    have hmem : t i ∈ E := subset_adjoin k _ ⟨i, rfl⟩
    have hua : ua (e i) = ⟨t i, hle hmem⟩ := by
      apply Subtype.ext
      exact he i
    change ψ (ua (e i)) = s i
    rw [hua, hψ ⟨t i, hmem⟩]
    exact adjoinTranscendentalAlgHom_apply ht hs i
  refine ⟨v, ?_, hfix⟩
  ext f
  rw [mem_idealOf_iff, mem_idealOf_iff]
  have h1 : MvPolynomial.aeval v f =
      ψ (MvPolynomial.aeval ua f) := by
    change MvPolynomial.aeval (fun j ↦ ψ (ua j)) f = _
    rw [MvPolynomial.comp_aeval_apply]
  have h2 : MvPolynomial.aeval u f =
      L.val (MvPolynomial.aeval ua f) := by
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  rw [h1, h2]
  constructor
  · intro hz
    have ha : ψ (MvPolynomial.aeval ua f) = ψ 0 := by
      rw [map_zero]
      exact hz
    rw [ψ.injective ha, map_zero]
  · intro hz
    have ha : L.val (MvPolynomial.aeval ua f) = L.val 0 := by
      rw [map_zero]
      exact hz
    rw [L.val.injective ha, map_zero]

/-- Equality of complete tuple ideals restricts to every chosen coordinate
subtuple. -/
theorem idealOf_comp_eq_of_idealOf_eq {ι κ : Type*}
    {a b : ι → Ω} (h : idealOf k a = idealOf k b) (e : κ → ι) :
    idealOf k (a ∘ e) = idealOf k (b ∘ e) := by
  ext f
  rw [mem_idealOf_iff, mem_idealOf_iff]
  have ha : MvPolynomial.aeval (a ∘ e) f =
      MvPolynomial.aeval a (MvPolynomial.rename e f) := by
    rw [MvPolynomial.aeval_rename]
  have hb : MvPolynomial.aeval (b ∘ e) f =
      MvPolynomial.aeval b (MvPolynomial.rename e f) := by
    rw [MvPolynomial.aeval_rename]
  rw [ha, hb]
  constructor
  · intro hz
    have hm : MvPolynomial.rename e f ∈ idealOf k a :=
      (mem_idealOf_iff k).2 hz
    exact (mem_idealOf_iff k).1 (h ▸ hm)
  · intro hz
    have hm : MvPolynomial.rename e f ∈ idealOf k b :=
      (mem_idealOf_iff k).2 hz
    exact (mem_idealOf_iff k).1 (h.symm ▸ hm)

/-- Relocate a one-element algebraic extension while fixing its entire
independent transcendence prefix.  If `u` is algebraic over `k(t)`, then
for every equally long independent tuple `s` there is `v` such that
`(s,v)` and `(t,u)` have the same vanishing ideal over `k`. -/
theorem exists_snoc_relocation_fixing [IsAlgClosed Ω] {n : ℕ}
    {t s : Fin n → Ω} {u : Ω}
    (ht : AlgebraicIndependent k t) (hs : AlgebraicIndependent k s)
    (hu : u ∈ racl k (Set.range t)) :
    ∃ v : Ω, idealOf k (Fin.snoc s v) = idealOf k (Fin.snoc t u) := by
  classical
  let E := adjoin k (Set.range t)
  let L := adjoin k (Set.range (Fin.snoc t u))
  have hle : E ≤ L := by
    apply adjoin.mono
    rw [Fin.range_snoc]
    exact Set.subset_insert u _
  have halg : Algebra.IsAlgebraic (↥E) (↥(extendScalars hle)) := by
    apply isAlgebraic_extendScalars_adjoin hle
    intro x hx
    rw [Fin.range_snoc] at hx
    rcases hx with rfl | hx
    · exact (mem_racl_iff k).1 hu
    · have hxE : x ∈ E := subset_adjoin k _ hx
      exact isAlgebraic_algebraMap (R := ↥E) (A := Ω) ⟨x, hxE⟩
  obtain ⟨ψ, hψ⟩ := exists_extension_of_isAlgebraic
    (halg := halg) hle (adjoinTranscendentalAlgHom ht hs)
  have htaMem (j : Fin n.succ) :
      (Fin.snoc t u : Fin n.succ → Ω) j ∈
        (adjoin k (Set.range (Fin.snoc t u : Fin n.succ → Ω)) :
          IntermediateField k Ω) :=
    subset_adjoin k _ (Set.mem_range_self j)
  let ta : Fin n.succ → ↥L :=
    fun j ↦ ⟨(Fin.snoc t u : Fin n.succ → Ω) j, htaMem j⟩
  let v : Ω := ψ (ta (Fin.last n))
  have hprefix (i : Fin n) : ψ (ta i.castSucc) = s i := by
    have hmem : t i ∈ E := subset_adjoin k _ ⟨i, rfl⟩
    have hta : ta i.castSucc = ⟨t i, hle hmem⟩ := by
      apply Subtype.ext
      simp [ta]
    rw [hta, hψ ⟨t i, hmem⟩]
    exact adjoinTranscendentalAlgHom_apply ht hs i
  have htuple : Fin.snoc s v = fun j ↦ ψ (ta j) := by
    funext j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp [v]
    · simpa using (hprefix i).symm
  refine ⟨v, ?_⟩
  rw [htuple]
  ext f
  rw [mem_idealOf_iff, mem_idealOf_iff]
  have h1 : MvPolynomial.aeval (fun j ↦ ψ (ta j)) f =
      ψ (MvPolynomial.aeval ta f) := by
    rw [MvPolynomial.comp_aeval_apply]
  have h2 : MvPolynomial.aeval (Fin.snoc t u) f =
      L.val (MvPolynomial.aeval ta f) := by
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  rw [h1, h2]
  constructor
  · intro hz
    have ha : ψ (MvPolynomial.aeval ta f) = ψ 0 := by
      rw [map_zero]
      exact hz
    rw [ψ.injective ha, map_zero]
  · intro hz
    have ha : L.val (MvPolynomial.aeval ta f) = L.val 0 := by
      rw [map_zero]
      exact hz
    rw [L.val.injective ha, map_zero]

/-- A generic member `(parameter, source, target)` of a
finite-correspondence family of parameter dimension `d`. -/
structure FiniteCorrespondenceFamilyMember (d : ℕ) where
  /-- The generic family parameter. -/
  parameter : Fin d → Ω
  /-- The source coordinate of the selected generic branch. -/
  source : Ω
  /-- The target coordinate of the selected generic branch. -/
  target : Ω
  /-- The parameter coordinates are algebraically independent. -/
  parameter_independent : AlgebraicIndependent k parameter
  /-- The source is generic over the parameter field. -/
  source_generic : source ∉ racl k (Set.range parameter)
  /-- The target is algebraic over the parameter and source. -/
  target_mem_parameter_source :
    target ∈ racl k (insert source (Set.range parameter))
  /-- The source is algebraic over the parameter and target. -/
  source_mem_parameter_target :
    source ∈ racl k (insert target (Set.range parameter))

namespace FiniteCorrespondenceFamilyMember

variable {d : ℕ} (F : FiniteCorrespondenceFamilyMember (k := k) (Ω := Ω) d)

/-- The coefficient field generated by the family parameter. -/
def parameterField : IntermediateField k Ω :=
  adjoin k (Set.range F.parameter)

/-- The independent parameter/source prefix of the generic family
member. -/
def parameterSource : Fin (d + 1) → Ω :=
  Fin.snoc F.parameter F.source

/-- The full generic family tuple `(parameter, source, target)`. -/
def tuple : Fin (d + 2) → Ω :=
  Fin.snoc F.parameterSource F.target

/-- The prime ideal of the total family locus. -/
def ideal : Ideal (MvPolynomial (Fin (d + 2)) k) :=
  idealOf k F.tuple

/-- The parameter and source form an algebraically independent tuple. -/
theorem parameterSource_independent :
    AlgebraicIndependent k F.parameterSource :=
  algebraicIndependent_snoc F.parameter_independent F.source_generic

/-- A generic family member specializes to a finite-correspondence pair
over its parameter field. -/
def toPair : FiniteCorrespondencePair (↥F.parameterField) Ω where
  source := F.source
  target := F.target
  source_generic := by
    rw [parameterField, mem_racl_adjoin_base_iff, Set.union_empty]
    exact F.source_generic
  target_mem_source := by
    rw [parameterField, mem_racl_adjoin_base_iff, Set.union_singleton]
    exact F.target_mem_parameter_source
  source_mem_target := by
    rw [parameterField, mem_racl_adjoin_base_iff, Set.union_singleton]
    exact F.source_mem_parameter_target

/-- The full family tuple is algebraic over its independent
parameter/source prefix. -/
theorem target_mem_parameterSource :
    F.target ∈ racl k (Set.range F.parameterSource) := by
  rw [parameterSource, Fin.range_snoc]
  exact F.target_mem_parameter_source

/-- A family locus can be relocated above any independent generic
parameter/source prefix, while preserving its complete prime ideal. -/
theorem exists_relocation [IsAlgClosed Ω] {q : Fin d → Ω} {x : Ω}
    (hqx : AlgebraicIndependent k (Fin.snoc q x)) :
    ∃ y : Ω,
      idealOf k (Fin.snoc (Fin.snoc q x) y) = F.ideal := by
  simpa [ideal, tuple, parameterSource] using
    exists_snoc_relocation_fixing F.parameterSource_independent hqx
      F.target_mem_parameterSource

end FiniteCorrespondenceFamilyMember

end

end AclGeom
