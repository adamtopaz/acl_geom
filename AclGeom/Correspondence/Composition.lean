/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.GenericPoints

/-!
# Composition of correspondence germs at generic points

The opening of the correspondence calculus (blueprint §8.1, checklist C2)
in the elementwise presentation of the rational-curve route (design issue
on the project tracker): an irreducible finite correspondence germ between
two point-curves is presented by an interalgebraic pair of transcendental
elements, and composition happens at a *shared middle representative*:

* `mem_racl_trans` / `comp_pair_of_shared_middle`: with a literally shared
  middle, the composite pair is automatically interalgebraic — all content
  lives in the matching step;
* `exists_pair_relocation_fixing`: the matching step — a germ presentation
  `(w', u)` relocates onto any prescribed interalgebraic representative
  `w` of its source point, preserving the vanishing ideal and hence the
  germ. This is blueprint Lemma 8.1(b) with the transcendence basis pinned
  to a prescribed image;
* `FiniteCorrespondencePair`, `FiniteCorrespondenceGerm`, and
  `FiniteCorrespondenceGerm.Composes`: the selected-branch presentation of
  finite correspondences and their composition;
* `FiniteCorrespondenceGerm.exists_composite`: matching makes the relational
  composite nonempty, while retaining the chosen irreducible component;
* `fiber_product_rank_count`: the explicit rank-five calculation used in
  blueprint equation (8.6).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** complete (M4a, issue #12 pipeline step 1).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

section SharedMiddle

/-- Interalgebraicity is transitive through a shared middle element. -/
theorem mem_racl_trans {z w u : Ω} (hzw : z ∈ racl k ({w} : Set Ω))
    (hwu : w ∈ racl k ({u} : Set Ω)) : z ∈ racl k ({u} : Set Ω) :=
  racl_le_of_subset_racl (Set.singleton_subset_iff.2 hwu) hzw

/-- Composition of correspondence germs at a shared middle
representative: the composite pair is interalgebraic. -/
theorem comp_pair_of_shared_middle {z w u : Ω}
    (hzw : z ∈ racl k ({w} : Set Ω)) (hwz : w ∈ racl k ({z} : Set Ω))
    (hwu : u ∈ racl k ({w} : Set Ω)) (huw : w ∈ racl k ({u} : Set Ω)) :
    u ∈ racl k ({z} : Set Ω) ∧ z ∈ racl k ({u} : Set Ω) :=
  ⟨mem_racl_trans hwu hwz, mem_racl_trans hzw huw⟩

end SharedMiddle

section SelectedBaseChange

/-- A polynomial relation remains a relation after extending between
nested intermediate coefficient fields. -/
theorem map_mem_idealOf_of_intermediateField_le
    {E F : IntermediateField k Ω} (hEF : E ≤ F)
    {q : Fin 2 → Ω} {f : MvPolynomial (Fin 2) E}
    (hf : f ∈ idealOf E q) :
    MvPolynomial.map (IntermediateField.inclusion hEF) f ∈
      idealOf F q := by
  rw [mem_idealOf_iff] at hf ⊢
  change MvPolynomial.eval₂ (algebraMap E Ω) q f = 0 at hf
  change MvPolynomial.eval₂ (algebraMap F Ω) q
    (MvPolynomial.map (IntermediateField.inclusion hEF) f) = 0
  rw [MvPolynomial.eval₂_map]
  have hcomp : (algebraMap F Ω).comp
      (IntermediateField.inclusion hEF).toRingHom =
      algebraMap E Ω := by
    ext x
    rfl
  change MvPolynomial.eval₂ ((algebraMap F Ω).comp
    (IntermediateField.inclusion hEF).toRingHom) q f = 0
  rw [hcomp]
  exact hf

/-- The extension of a vanishing ideal is contained in the selected prime
component determined by the same tuple over the larger coefficient
field.  Equality is intentionally not asserted: a finite base change may
split into several branches. -/
theorem idealOf_map_le_of_intermediateField_le
    {E F : IntermediateField k Ω} (hEF : E ≤ F) (q : Fin 2 → Ω) :
    Ideal.map (MvPolynomial.map (IntermediateField.inclusion hEF))
        (idealOf E q) ≤ idealOf F q := by
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  exact map_mem_idealOf_of_intermediateField_le hEF hf

end SelectedBaseChange

section Matching

/-- **The matching step of germ composition** (blueprint Lemma 8.1(b),
pinned form): a correspondence-germ presentation `(w', u)` relocates onto
any prescribed interalgebraic representative `w` of its source point —
there is `u'` with the pair `(w, u')` carrying the same vanishing ideal
as `(w', u)`. -/
theorem exists_pair_relocation_fixing [IsAlgClosed Ω] {w' u w : Ω}
    (hw'0 : w' ∉ racl k (∅ : Set Ω))
    (hu : u ∈ racl k ({w'} : Set Ω))
    (hw0 : w ∉ racl k (∅ : Set Ω)) :
    ∃ u' : Ω, idealOf k ![w, u'] = idealOf k ![w', u] := by
  classical
  -- The transcendence data for the relocation.
  have hw'tr : Transcendental k w' := fun halg ↦
    hw'0 (mem_racl_empty_of_isAlgebraic halg)
  have hwtr : Transcendental k w := fun halg ↦
    hw0 (mem_racl_empty_of_isAlgebraic halg)
  have ht : AlgebraicIndependent k ![w'] :=
    algebraicIndependent_unique_type_iff.2 hw'tr
  have hs : AlgebraicIndependent k ![w] :=
    algebraicIndependent_unique_type_iff.2 hwtr
  have hrt : Set.range (![w'] : Fin 1 → Ω) = ({w'} : Set Ω) := by
    ext z
    simp [Matrix.range_cons, Matrix.range_empty]
  have hrs : Set.range (![w] : Fin 1 → Ω) = ({w} : Set Ω) := by
    ext z
    simp [Matrix.range_cons, Matrix.range_empty]
  have hra : Set.range (![w', u] : Fin 2 → Ω) = ({w', u} : Set Ω) := by
    ext z
    simp [Matrix.range_cons, Matrix.range_empty]
    tauto
  have hle : adjoin k (Set.range (![w'] : Fin 1 → Ω)) ≤
      adjoin k (Set.range (![w', u] : Fin 2 → Ω)) := by
    rw [hrt, hra]
    exact adjoin.mono _ _ _ (by simp)
  have halg : Algebra.IsAlgebraic
      ↥(adjoin k (Set.range (![w'] : Fin 1 → Ω)))
      ↥(extendScalars hle) := by
    refine isAlgebraic_extendScalars_adjoin hle ?_
    intro x hx
    rw [hra] at hx
    rw [hrt]
    rcases hx with rfl | hx
    · have hmem : x ∈ adjoin k ({x} : Set Ω) := subset_adjoin k _ rfl
      have h := isAlgebraic_algebraMap
        (R := ↥(adjoin k ({x} : Set Ω))) (A := Ω) ⟨x, hmem⟩
      simpa using h
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (mem_racl_iff k).1 hu
  -- The relocation embedding, with the basis pinned to `w`.
  obtain ⟨ψ, hψ⟩ := exists_extension_of_isAlgebraic (halg := halg) hle
    (adjoinTranscendentalAlgHom ht hs)
  set ta : Fin 2 → ↥(adjoin k (Set.range (![w', u] : Fin 2 → Ω))) :=
    fun j ↦ ⟨(![w', u] : Fin 2 → Ω) j, subset_adjoin k _ ⟨j, rfl⟩⟩
    with hta
  refine ⟨ψ (ta 1), ?_⟩
  -- The relocated tuple starts at `w`.
  have hb0 : ψ (ta 0) = w := by
    have hmem : w' ∈ adjoin k (Set.range (![w'] : Fin 1 → Ω)) := by
      rw [hrt]
      exact subset_adjoin k _ rfl
    have h1 : ta 0 = ⟨w', hle hmem⟩ := Subtype.ext rfl
    rw [h1, hψ ⟨w', hmem⟩]
    have h2 : (⟨w', hmem⟩ :
        ↥(adjoin k (Set.range (![w'] : Fin 1 → Ω)))) =
        ⟨(![w'] : Fin 1 → Ω) 0, subset_adjoin k _ ⟨0, rfl⟩⟩ := rfl
    rw [h2, adjoinTranscendentalAlgHom_apply]
    exact rfl
  have hbfun : (![w, ψ (ta 1)] : Fin 2 → Ω) = fun j ↦ ψ (ta j) := by
    funext j
    fin_cases j
    · exact hb0.symm
    · rfl
  rw [hbfun]
  -- Same vanishing ideal: evaluation factors through the embedding.
  ext f
  rw [mem_idealOf_iff, mem_idealOf_iff]
  have h1 : MvPolynomial.aeval (fun j ↦ ψ (ta j)) f =
      ψ (MvPolynomial.aeval ta f) := by
    rw [MvPolynomial.comp_aeval_apply]
  have h2 : MvPolynomial.aeval (![w', u] : Fin 2 → Ω) f =
      (adjoin k (Set.range (![w', u] : Fin 2 → Ω))).val
        (MvPolynomial.aeval ta f) := by
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  rw [h1, h2]
  constructor
  · intro h
    have h4 : ψ (MvPolynomial.aeval ta f) = ψ 0 := by
      rw [map_zero]
      exact h
    rw [ψ.injective h4, map_zero]
  · intro h
    have h4 : (adjoin k (Set.range (![w', u] : Fin 2 → Ω))).val
        (MvPolynomial.aeval ta f) =
        (adjoin k (Set.range (![w', u] : Fin 2 → Ω))).val 0 := by
      rw [map_zero]
      exact h
    rw [(adjoin k (Set.range (![w', u] : Fin 2 → Ω))).val.injective h4,
      map_zero]

end Matching

section Germs

/-- A generic pair presenting a finite correspondence between two rational
curves.  The two coordinates are interalgebraic and the source is generic
over the ground field. -/
structure FiniteCorrespondencePair (k Ω : Type*) [Field k] [Field Ω]
    [Algebra k Ω] where
  /-- Source coordinate of the selected generic branch. -/
  source : Ω
  /-- Target coordinate of the selected generic branch. -/
  target : Ω
  /-- The source coordinate is transcendental over the ground field. -/
  source_generic : source ∉ racl k (∅ : Set Ω)
  /-- The target is algebraic over the source. -/
  target_mem_source : target ∈ racl k {source}
  /-- The source is algebraic over the target. -/
  source_mem_target : source ∈ racl k {target}

namespace FiniteCorrespondencePair

variable (P : FiniteCorrespondencePair k Ω)

/-- The target of a finite correspondence is generic whenever its source
is generic. -/
theorem target_generic : P.target ∉ racl k (∅ : Set Ω) := by
  intro ht
  exact P.source_generic
    (racl_le_of_subset_racl (Set.singleton_subset_iff.2 ht) P.source_mem_target)

/-- Reverse a selected correspondence branch. -/
def swap : FiniteCorrespondencePair k Ω where
  source := P.target
  target := P.source
  source_generic := P.target_generic
  target_mem_source := P.source_mem_target
  source_mem_target := P.target_mem_source

@[simp] theorem swap_source : P.swap.source = P.target := rfl

@[simp] theorem swap_target : P.swap.target = P.source := rfl

@[simp] theorem swap_swap : P.swap.swap = P := by
  cases P
  rfl

/-- The diagonal branch at a generic coordinate. -/
def identity (x : Ω) (hx : x ∉ racl k (∅ : Set Ω)) :
    FiniteCorrespondencePair k Ω where
  source := x
  target := x
  source_generic := hx
  target_mem_source := subset_racl k {x} rfl
  source_mem_target := subset_racl k {x} rfl

/-- The prime ideal of the selected generic branch. -/
def ideal : Ideal (MvPolynomial (Fin 2) k) :=
  idealOf k ![P.source, P.target]

/-- Composition at a literally shared middle coordinate. -/
def comp (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    FiniteCorrespondencePair k Ω where
  source := P.source
  target := Q.target
  source_generic := P.source_generic
  target_mem_source := by
    apply mem_racl_trans (w := P.target)
    · simpa [h] using Q.target_mem_source
    · exact P.target_mem_source
  source_mem_target := by
    apply mem_racl_trans (w := P.target)
    · exact P.source_mem_target
    · simpa [h] using Q.source_mem_target

@[simp] theorem comp_source (Q : FiniteCorrespondencePair k Ω)
    (h : P.target = Q.source) : (P.comp Q h).source = P.source := rfl

@[simp] theorem comp_target (Q : FiniteCorrespondencePair k Ω)
    (h : P.target = Q.source) : (P.comp Q h).target = Q.target := rfl

/-- Associativity of selected-branch composition.  Both parenthesizations
have the same endpoint pair, hence the same prime component ideal. -/
theorem comp_ideal_assoc (Q R : FiniteCorrespondencePair k Ω)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source) :
    ((P.comp Q hPQ).comp R (by simpa using hQR)).ideal =
      (P.comp (Q.comp R hQR) (by simpa using hPQ)).ideal := rfl

/-- A branch followed by its reverse has the diagonal endpoint ideal. -/
theorem comp_swap_ideal :
    (P.comp P.swap rfl).ideal =
      (identity P.source P.source_generic).ideal := rfl

/-- A reversed branch followed by the original branch has the diagonal
endpoint ideal at the target. -/
theorem swap_comp_ideal :
    (P.swap.comp P rfl).ideal =
      (identity P.target P.target_generic).ideal := rfl

end FiniteCorrespondencePair

/-- A finite-correspondence germ is its prime branch ideal together with a
generic interalgebraic pair presenting that ideal.  Keeping the witness is
intentional: composition of correspondences selects a component rather than
the whole scheme-theoretic fiber product. -/
@[ext] structure FiniteCorrespondenceGerm (k Ω : Type*) [Field k] [Field Ω]
    [Algebra k Ω] where
  /-- Prime ideal of the selected correspondence component. -/
  carrier : Ideal (MvPolynomial (Fin 2) k)
  /-- A generic pair presenting the component. -/
  presentation : ∃ P : FiniteCorrespondencePair k Ω, carrier = P.ideal

namespace FiniteCorrespondenceGerm

/-- The germ presented by a generic finite-correspondence pair. -/
def ofPair (P : FiniteCorrespondencePair k Ω) :
    FiniteCorrespondenceGerm k Ω where
  carrier := P.ideal
  presentation := ⟨P, rfl⟩

/-- The inverse germ of a selected presentation. -/
def inverseOfPair (P : FiniteCorrespondencePair k Ω) :
    FiniteCorrespondenceGerm k Ω :=
  ofPair P.swap

/-- The identity germ at a generic coordinate. -/
def identity (x : Ω) (hx : x ∉ racl k (∅ : Set Ω)) :
    FiniteCorrespondenceGerm k Ω :=
  ofPair (FiniteCorrespondencePair.identity x hx)

/-- Relational composition of selected correspondence components.  The
literal common middle records the chosen component of the fiber product. -/
def Composes (C D E : FiniteCorrespondenceGerm k Ω) : Prop :=
  ∃ (P Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source),
    C.carrier = P.ideal ∧ D.carrier = Q.ideal ∧
      E.carrier = (P.comp Q h).ideal

theorem composes_of_shared_middle (P Q : FiniteCorrespondencePair k Ω)
    (h : P.target = Q.source) :
    Composes (ofPair P) (ofPair Q) (ofPair (P.comp Q h)) :=
  ⟨P, Q, h, rfl, rfl, rfl⟩

/-- A selected branch composes with its reverse to the identity germ at
its source. -/
theorem composes_inverse_right (P : FiniteCorrespondencePair k Ω) :
    Composes (ofPair P) (inverseOfPair P)
      (identity P.source P.source_generic) := by
  refine ⟨P, P.swap, rfl, rfl, rfl, ?_⟩
  exact P.comp_swap_ideal

/-- The reverse branch composes with the original branch to the identity
germ at its target. -/
theorem composes_inverse_left (P : FiniteCorrespondencePair k Ω) :
    Composes (inverseOfPair P) (ofPair P)
      (identity P.target P.target_generic) := by
  refine ⟨P.swap, P, rfl, rfl, rfl, ?_⟩
  exact P.swap_comp_ideal

/-- Strict associativity of selected composition at two literal shared
middle representatives.  Both parenthesizations select the same endpoint
prime ideal. -/
theorem comp_assoc_of_shared_middles
    (P Q R : FiniteCorrespondencePair k Ω)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source) :
    ofPair ((P.comp Q hPQ).comp R (by simpa using hQR)) =
      ofPair (P.comp (Q.comp R hQR) (by simpa using hPQ)) := by
  apply FiniteCorrespondenceGerm.ext
  exact P.comp_ideal_assoc Q R hPQ hQR

/-- Every two finite-correspondence germs admit a selected composite.  The
second presentation is relocated onto the first target, and the resulting
end pair is the selected irreducible component. -/
theorem exists_composite [IsAlgClosed Ω] (C D : FiniteCorrespondenceGerm k Ω) :
    ∃ E : FiniteCorrespondenceGerm k Ω, Composes C D E := by
  obtain ⟨P, hP⟩ := C.presentation
  obtain ⟨Q, hQ⟩ := D.presentation
  obtain ⟨u, hu⟩ := exists_pair_relocation_fixing
    Q.source_generic Q.target_mem_source P.target_generic
  have htarget : u ∈ racl k {P.target} := by
    have hv : (![Q.source, Q.target] : Fin 2 → Ω) 1 ∈ racl k
        ((![Q.source, Q.target] : Fin 2 → Ω) '' {(0 : Fin 2)}) := by
      simpa [Set.image_singleton] using Q.target_mem_source
    have h := mem_racl_image_of_idealOf_eq k hu.symm
      (J := {(0 : Fin 2)}) (i := (1 : Fin 2)) hv
    simpa [Set.image_singleton] using h
  have hsource : P.target ∈ racl k {u} := by
    have hv : (![Q.source, Q.target] : Fin 2 → Ω) 0 ∈ racl k
        ((![Q.source, Q.target] : Fin 2 → Ω) '' {(1 : Fin 2)}) := by
      simpa [Set.image_singleton] using Q.source_mem_target
    have h := mem_racl_image_of_idealOf_eq k hu.symm
      (J := {(1 : Fin 2)}) (i := (0 : Fin 2)) hv
    simpa [Set.image_singleton] using h
  let Q' : FiniteCorrespondencePair k Ω :=
    { source := P.target
      target := u
      source_generic := P.target_generic
      target_mem_source := htarget
      source_mem_target := hsource }
  have hQ' : D.carrier = Q'.ideal := by
    rw [hQ, FiniteCorrespondencePair.ideal]
    change idealOf k ![Q.source, Q.target] = idealOf k ![P.target, u]
    exact hu.symm
  refine ⟨ofPair (P.comp Q' rfl), P, Q', rfl, hP, hQ', rfl⟩

end FiniteCorrespondenceGerm

end Germs

section FiberProductRank

/-- **The rank-five fiber-product count behind blueprint (8.6).**
If the four correspondence parameters are independent, `x` is generic over
them, and the successive fiber coordinates `y,z` are algebraic over those
five generators, then the seven-coordinate fiber-product tuple has the same
relative algebraic closure as the independent five-coordinate tuple.

The conclusion exposes both halves of the dimension calculation: the five
generators are independent and adjoining `y,z` does not enlarge their
relative algebraic closure. -/
theorem fiber_product_rank_count {p : Fin 4 → Ω} {x y z : Ω}
    (hp : AlgebraicIndependent k p)
    (hx : x ∉ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range (Fin.snoc p x)))
    (hz : z ∈ racl k (Set.range (Fin.snoc p x))) :
    AlgebraicIndependent k (Fin.snoc p x) ∧
      racl k (Set.range (Fin.snoc (Fin.snoc (Fin.snoc p x) y) z)) =
        racl k (Set.range (Fin.snoc p x)) := by
  have hpx : AlgebraicIndependent k (Fin.snoc p x) :=
    algebraicIndependent_snoc hp hx
  refine ⟨hpx, ?_⟩
  rw [Fin.range_snoc, Fin.range_snoc]
  rw [racl_insert_of_mem (racl_mono (Set.subset_insert y _) hz)]
  exact racl_insert_of_mem hy

end FiberProductRank

end

end AclGeom
