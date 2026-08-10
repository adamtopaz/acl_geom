/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.Family
import AclGeom.Correspondence.FiniteCover
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Transport of correspondence coordinates on algebraic closures

A selected finite correspondence `(x,y)` does not generally define an
automorphism of `k(x)`: the target `y` is only algebraic over `k(x)`.
It does, however, determine an equivalence between the abstract rational
function fields `k(x)` and `k(y)`, and that equivalence extends to their
algebraic closures.  This module packages the extension together with its
semilinearity square.

The extension is deliberately not treated as canonical.  Independently
chosen lifts need not preserve composition; their discrepancy is a deck
transformation fixing the target coordinate field.  Keeping that defect
explicit is the field-theoretic input for the finite-cover normalization in
blueprint Theorem 8.2.
-/

namespace AclGeom

noncomputable section

/-- A semilinear equivalence between algebraic closures, together with the
equivalence of base fields which it extends. -/
structure AlgebraicClosureTransport (E E' : Type*)
    [Field E] [Field E'] where
  /-- The equivalence of the base fields. -/
  baseEquiv : E ≃+* E'
  /-- The induced equivalence of chosen algebraic closures. -/
  closureEquiv : AlgebraicClosure E ≃+* AlgebraicClosure E'
  /-- The algebraic-closure equivalence extends the base equivalence. -/
  commutes :
    closureEquiv.toRingHom.comp (algebraMap E (AlgebraicClosure E)) =
      (algebraMap E' (AlgebraicClosure E')).comp baseEquiv.toRingHom

namespace AlgebraicClosureTransport

variable {E E' E'' : Type*} [Field E] [Field E'] [Field E'']

/-- Pointwise form of the semilinearity square. -/
@[simp] theorem commutes_apply (T : AlgebraicClosureTransport E E')
    (x : E) :
    T.closureEquiv (algebraMap E (AlgebraicClosure E) x) =
      algebraMap E' (AlgebraicClosure E') (T.baseEquiv x) :=
  DFunLike.congr_fun T.commutes x

/-- The identity transport. -/
def refl (E : Type*) [Field E] : AlgebraicClosureTransport E E where
  baseEquiv := RingEquiv.refl E
  closureEquiv := RingEquiv.refl (AlgebraicClosure E)
  commutes := rfl

/-- Reverse an algebraic-closure transport. -/
def symm (T : AlgebraicClosureTransport E E') :
    AlgebraicClosureTransport E' E where
  baseEquiv := T.baseEquiv.symm
  closureEquiv := T.closureEquiv.symm
  commutes := by
    apply RingHom.ext
    intro x
    apply T.closureEquiv.injective
    simp

/-- Compose algebraic-closure transports. -/
def trans (T : AlgebraicClosureTransport E E')
    (U : AlgebraicClosureTransport E' E'') :
    AlgebraicClosureTransport E E'' where
  baseEquiv := T.baseEquiv.trans U.baseEquiv
  closureEquiv := T.closureEquiv.trans U.closureEquiv
  commutes := by
    apply RingHom.ext
    intro x
    simp

/-- Extend a field equivalence to a chosen equivalence of algebraic
closures.  The choice is not functorial; `refl`, `symm`, and `trans` are
the coherent operations on already chosen transports. -/
noncomputable def lift (e : E ≃+* E') :
    AlgebraicClosureTransport E E' := by
  let L := IsAlgClosure.equivOfEquivAux
    (AlgebraicClosure E) (AlgebraicClosure E') e
  exact
    { baseEquiv := e
      closureEquiv := L.1
      commutes := L.2 }

@[simp] theorem refl_baseEquiv (E : Type*) [Field E] :
    (refl E).baseEquiv = RingEquiv.refl E := rfl

@[simp] theorem refl_closureEquiv (E : Type*) [Field E] :
    (refl E).closureEquiv = RingEquiv.refl (AlgebraicClosure E) := rfl

@[simp] theorem symm_baseEquiv (T : AlgebraicClosureTransport E E') :
    T.symm.baseEquiv = T.baseEquiv.symm := rfl

@[simp] theorem symm_closureEquiv (T : AlgebraicClosureTransport E E') :
    T.symm.closureEquiv = T.closureEquiv.symm := rfl

@[simp] theorem trans_baseEquiv (T : AlgebraicClosureTransport E E')
    (U : AlgebraicClosureTransport E' E'') :
    (T.trans U).baseEquiv = T.baseEquiv.trans U.baseEquiv := rfl

@[simp] theorem trans_closureEquiv (T : AlgebraicClosureTransport E E')
    (U : AlgebraicClosureTransport E' E'') :
    (T.trans U).closureEquiv =
      T.closureEquiv.trans U.closureEquiv := rfl

@[simp] theorem lift_baseEquiv (e : E ≃+* E') :
    (lift e).baseEquiv = e := rfl

end AlgebraicClosureTransport

open IntermediateField

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

namespace FiniteCorrespondencePair

variable (P : FiniteCorrespondencePair k Ω)

/-- The source coordinate is transcendental over the ground field. -/
theorem source_transcendental : Transcendental k P.source := by
  intro h
  exact P.source_generic (mem_racl_empty_of_isAlgebraic h)

/-- The target coordinate is transcendental over the ground field. -/
theorem target_transcendental : Transcendental k P.target := by
  intro h
  exact P.target_generic (mem_racl_empty_of_isAlgebraic h)

/-- Replace the singleton presentation of a one-variable function field by
the equivalent one-coordinate range presentation used by
`aevalEquivField`. -/
private def singletonRangeEquiv (x : Ω) :
    (↥(adjoin k {x})) ≃ₐ[k]
      (↥(adjoin k (Set.range (![x] : Fin 1 → Ω)))) :=
  IntermediateField.equivOfEq (by
    congr 1
    ext z
    simp [Matrix.range_cons, Matrix.range_empty])

/-- The one-coordinate source and target tuples have the same complete
locus: both are generic points of the affine line. -/
private theorem coordinateIdealEq :
    idealOf k (![P.source] : Fin 1 → Ω) =
      idealOf k (![P.target] : Fin 1 → Ω) := by
  have hx : AlgebraicIndependent k (![P.source] : Fin 1 → Ω) :=
    algebraicIndependent_unique_type_iff.2 P.source_transcendental
  have hy : AlgebraicIndependent k (![P.target] : Fin 1 → Ω) :=
    algebraicIndependent_unique_type_iff.2 P.target_transcendental
  calc
    idealOf k (![P.source] : Fin 1 → Ω) = ⊥ :=
      (idealOf_eq_bot_iff k).2 hx
    _ = idealOf k (![P.target] : Fin 1 → Ω) :=
      ((idealOf_eq_bot_iff k).2 hy).symm

/-- The abstract coordinate equivalence attached to a selected
correspondence branch, sending its source generator to its target
generator. -/
def coordinateEquiv : (↥P.sourceField) ≃ₐ[k] (↥P.targetField) :=
  (singletonRangeEquiv P.source).trans
    ((locusFunctionFieldEquivOfIdealEq P.coordinateIdealEq).trans
      (singletonRangeEquiv P.target).symm)

/-- The coordinate equivalence sends the displayed source coordinate to
the displayed target coordinate. -/
@[simp] theorem coordinateEquiv_source :
    P.coordinateEquiv
        ⟨P.source, subset_adjoin k _ (by simp)⟩ =
      ⟨P.target, subset_adjoin k _ (by simp)⟩ := by
  have hsource :
      singletonRangeEquiv P.source
          ⟨P.source, subset_adjoin k _ (by simp)⟩ =
        ⟨P.source, subset_adjoin k _ (Set.mem_range_self 0)⟩ := by
    rfl
  apply Subtype.ext
  change ((locusFunctionFieldEquivOfIdealEq P.coordinateIdealEq)
      ((singletonRangeEquiv P.source)
        ⟨P.source, subset_adjoin k _ (by simp)⟩) : Ω) = P.target
  rw [hsource]
  exact congrArg Subtype.val
    (locusFunctionFieldEquivOfIdealEq_apply P.coordinateIdealEq 0)

/-- A chosen extension of the selected coordinate equivalence to the
algebraic closures of the source and target function fields. -/
noncomputable def coordinateClosureTransport :
    AlgebraicClosureTransport (↥P.sourceField) (↥P.targetField) :=
  AlgebraicClosureTransport.lift P.coordinateEquiv.toRingEquiv

/-- The algebraic-closure transport carries the source coordinate to the
selected target coordinate. -/
@[simp] theorem coordinateClosureTransport_source :
    P.coordinateClosureTransport.closureEquiv
        (algebraMap (↥P.sourceField) (AlgebraicClosure (↥P.sourceField))
          ⟨P.source, subset_adjoin k _ (by simp)⟩) =
      algebraMap (↥P.targetField) (AlgebraicClosure (↥P.targetField))
        ⟨P.target, subset_adjoin k _ (by simp)⟩ := by
  rw [AlgebraicClosureTransport.commutes_apply]
  exact congrArg
    (algebraMap (↥P.targetField) (AlgebraicClosure (↥P.targetField)))
    P.coordinateEquiv_source

/-- Identify the target coordinate field of one selected branch with the
source coordinate field of a branch whose source is literally the same
ambient coordinate. -/
def middleFieldEquiv (Q : FiniteCorrespondencePair k Ω)
    (h : P.target = Q.source) :
    (↥P.targetField) ≃ₐ[k] (↥Q.sourceField) :=
  IntermediateField.equivOfEq (by
    unfold targetField sourceField
    rw [h])

/-- The middle-field identification preserves the shared coordinate. -/
@[simp] theorem middleFieldEquiv_target
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    P.middleFieldEquiv Q h
        ⟨P.target, subset_adjoin k _ (by simp)⟩ =
      ⟨Q.source, subset_adjoin k _ (by simp)⟩ := by
  apply Subtype.ext
  exact h

/-- The shared-middle field identification lifted to algebraic closures. -/
noncomputable def middleClosureTransport
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    AlgebraicClosureTransport (↥P.targetField) (↥Q.sourceField) :=
  AlgebraicClosureTransport.lift (P.middleFieldEquiv Q h).toRingEquiv

/-- The lifted middle-field identification still preserves the shared
coordinate. -/
@[simp] theorem middleClosureTransport_target
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    (P.middleClosureTransport Q h).closureEquiv
        (algebraMap (↥P.targetField)
          (AlgebraicClosure (↥P.targetField))
          ⟨P.target, subset_adjoin k _ (by simp)⟩) =
      algebraMap (↥Q.sourceField)
        (AlgebraicClosure (↥Q.sourceField))
        ⟨Q.source, subset_adjoin k _ (by simp)⟩ := by
  rw [AlgebraicClosureTransport.commutes_apply]
  exact congrArg
    (algebraMap (↥Q.sourceField) (AlgebraicClosure (↥Q.sourceField)))
    (P.middleFieldEquiv_target Q h)

/-- The algebraic-closure transport along two composable selected
correspondences.  It is built by actual composition of the two chosen
transports, so its coherence is strict. -/
noncomputable def chainCoordinateClosureTransport
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    AlgebraicClosureTransport (↥P.sourceField) (↥Q.targetField) :=
  P.coordinateClosureTransport.trans
    ((P.middleClosureTransport Q h).trans Q.coordinateClosureTransport)

/-- The strictly composed transport carries the first source coordinate
to the second target coordinate. -/
@[simp] theorem chainCoordinateClosureTransport_source
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    (P.chainCoordinateClosureTransport Q h).closureEquiv
        (algebraMap (↥P.sourceField)
          (AlgebraicClosure (↥P.sourceField))
          ⟨P.source, subset_adjoin k _ (by simp)⟩) =
      algebraMap (↥Q.targetField)
        (AlgebraicClosure (↥Q.targetField))
        ⟨Q.target, subset_adjoin k _ (by simp)⟩ := by
  change Q.coordinateClosureTransport.closureEquiv
      ((P.middleClosureTransport Q h).closureEquiv
        (P.coordinateClosureTransport.closureEquiv
          (algebraMap (↥P.sourceField)
            (AlgebraicClosure (↥P.sourceField))
            ⟨P.source, subset_adjoin k _ (by simp)⟩))) = _
  rw [P.coordinateClosureTransport_source,
    P.middleClosureTransport_target, Q.coordinateClosureTransport_source]

/-- An independently chosen algebraic-closure lift of the composite
coordinate equivalence, expressed on exactly the same source and target
field types as the strict chain transport. -/
noncomputable def directCompositeClosureTransport
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    AlgebraicClosureTransport (↥P.sourceField) (↥Q.targetField) :=
  AlgebraicClosureTransport.lift
    (P.chainCoordinateClosureTransport Q h).baseEquiv

/-- The discrepancy between the strictly composed algebraic-closure
transport and the independently chosen transport of the composite branch.
It is a genuine deck transformation fixing the target coordinate field. -/
noncomputable def compositionDefect
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    AlgebraicClosure (↥Q.targetField) ≃ₐ[↥Q.targetField]
      AlgebraicClosure (↥Q.targetField) := by
  let chain := P.chainCoordinateClosureTransport Q h
  let direct := P.directCompositeClosureTransport Q h
  let d : AlgebraicClosure (↥Q.targetField) ≃+*
      AlgebraicClosure (↥Q.targetField) :=
    chain.closureEquiv.symm.trans direct.closureEquiv
  apply AlgEquiv.ofRingEquiv (f := d)
  intro x
  have hchain :
      chain.closureEquiv.symm
          (algebraMap (↥Q.targetField)
            (AlgebraicClosure (↥Q.targetField)) x) =
        algebraMap (↥P.sourceField)
          (AlgebraicClosure (↥P.sourceField))
          (chain.baseEquiv.symm x) := by
    apply chain.closureEquiv.injective
    simp
  change direct.closureEquiv
      (chain.closureEquiv.symm
        (algebraMap (↥Q.targetField)
          (AlgebraicClosure (↥Q.targetField)) x)) =
      algebraMap (↥Q.targetField)
        (AlgebraicClosure (↥Q.targetField)) x
  rw [hchain, AlgebraicClosureTransport.commutes_apply]
  have hbase : direct.baseEquiv = chain.baseEquiv := rfl
  rw [hbase, chain.baseEquiv.apply_symm_apply]

/-- The underlying ring equivalence of the composition defect is the
quotient of the direct lift by the strict chain lift. -/
theorem compositionDefect_toRingEquiv
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    (P.compositionDefect Q h).toRingEquiv =
      (P.chainCoordinateClosureTransport Q h).closureEquiv.symm.trans
        (P.directCompositeClosureTransport Q h).closureEquiv := by
  rfl

/-- Composing with the deck defect recovers the independently selected
transport of the composite branch exactly. -/
theorem chainCoordinateClosureTransport_trans_compositionDefect
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    (P.chainCoordinateClosureTransport Q h).closureEquiv.trans
        (P.compositionDefect Q h).toRingEquiv =
      (P.directCompositeClosureTransport Q h).closureEquiv := by
  rw [P.compositionDefect_toRingEquiv Q h]
  apply RingEquiv.ext
  intro x
  simp

/-- The composition defect fixes the displayed target coordinate. -/
@[simp] theorem compositionDefect_target
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    P.compositionDefect Q h
        (algebraMap (↥Q.targetField)
          (AlgebraicClosure (↥Q.targetField))
          ⟨Q.target, subset_adjoin k _ (by simp)⟩) =
      algebraMap (↥Q.targetField)
        (AlgebraicClosure (↥Q.targetField))
        ⟨Q.target, subset_adjoin k _ (by simp)⟩ := by
  exact (P.compositionDefect Q h).commutes _

end FiniteCorrespondencePair

end

end AclGeom
