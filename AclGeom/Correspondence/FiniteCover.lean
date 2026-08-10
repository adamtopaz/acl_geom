/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import AclGeom.Correspondence.Composition
import Mathlib.FieldTheory.Normal.Closure

/-!
# Finite covers carried by selected correspondence branches

A selected finite-correspondence pair `(x,y)` determines three concrete
subfields of the ambient algebraically closed field: `k(x)`, `k(y)`, and
`k(x,y)`.  Interalgebraicity says exactly that the joint branch field is a
finite extension of either endpoint field.  This is the field-theoretic
finite cover needed before passing to normal closures and gluing the
selected correspondence groupoid.

This module is part of the finite-cover integration in blueprint §8.1.
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

namespace FiniteCover

variable {E L : IntermediateField k Ω}

/-- An equivalence between two nested intermediate-field extensions.

Both the base and total fields are transported as `k`-algebras, and the
displayed square with the two inclusions commutes.  This is the appropriate
notion of equivalence when the coefficient field varies: an equivalence of
the total fields alone does not remember which finite extension is being
normalized. -/
structure ExtensionEquiv {E L E' L' : IntermediateField k Ω}
    (h : E ≤ L) (h' : E' ≤ L') where
  /-- Equivalence of the base fields. -/
  baseEquiv : (↥E) ≃ₐ[k] (↥E')
  /-- Equivalence of the total fields. -/
  totalEquiv : (↥L) ≃ₐ[k] (↥L')
  /-- The total-field equivalence restricts to the base-field equivalence. -/
  commutes :
    totalEquiv.toAlgHom.comp (IntermediateField.inclusion h) =
      (IntermediateField.inclusion h').comp baseEquiv.toAlgHom

namespace ExtensionEquiv

variable {E L E' L' E'' L'' : IntermediateField k Ω}
  {h : E ≤ L} {h' : E' ≤ L'} {h'' : E'' ≤ L''}

/-- Two extension equivalences are equal when their base and total
equivalences are equal. -/
@[ext] theorem ext {e e' : ExtensionEquiv h h'}
    (hbase : e.baseEquiv = e'.baseEquiv)
    (htotal : e.totalEquiv = e'.totalEquiv) : e = e' := by
  cases e
  cases e'
  cases hbase
  cases htotal
  rfl

/-- Pointwise form of the commutative-square condition. -/
@[simp] theorem commutes_apply (e : ExtensionEquiv h h') (x : E) :
    e.totalEquiv (IntermediateField.inclusion h x) =
      IntermediateField.inclusion h' (e.baseEquiv x) :=
  DFunLike.congr_fun e.commutes x

/-- The identity equivalence of a nested extension. -/
def refl (h : E ≤ L) : ExtensionEquiv h h where
  baseEquiv := AlgEquiv.refl
  totalEquiv := AlgEquiv.refl
  commutes := rfl

/-- Equal nested intermediate fields determine an extension equivalence.
The inclusion proofs themselves are immaterial. -/
def ofEq (hE : E = E') (hL : L = L') : ExtensionEquiv h h' := by
  subst E'
  subst L'
  exact refl h

/-- Reverse an equivalence of nested extensions. -/
def symm (e : ExtensionEquiv h h') : ExtensionEquiv h' h where
  baseEquiv := e.baseEquiv.symm
  totalEquiv := e.totalEquiv.symm
  commutes := by
    apply AlgHom.ext
    intro x
    apply e.totalEquiv.injective
    simp

/-- Compose equivalences of nested extensions. -/
def trans (e : ExtensionEquiv h h') (e' : ExtensionEquiv h' h'') :
    ExtensionEquiv h h'' where
  baseEquiv := e.baseEquiv.trans e'.baseEquiv
  totalEquiv := e.totalEquiv.trans e'.totalEquiv
  commutes := by
    apply AlgHom.ext
    intro x
    simp

@[simp] theorem refl_baseEquiv (h : E ≤ L) :
    (refl h).baseEquiv = AlgEquiv.refl := rfl

@[simp] theorem refl_totalEquiv (h : E ≤ L) :
    (refl h).totalEquiv = AlgEquiv.refl := rfl

@[simp] theorem symm_baseEquiv (e : ExtensionEquiv h h') :
    e.symm.baseEquiv = e.baseEquiv.symm := rfl

@[simp] theorem symm_totalEquiv (e : ExtensionEquiv h h') :
    e.symm.totalEquiv = e.totalEquiv.symm := rfl

@[simp] theorem trans_baseEquiv (e : ExtensionEquiv h h')
    (e' : ExtensionEquiv h' h'') :
    (e.trans e').baseEquiv = e.baseEquiv.trans e'.baseEquiv := rfl

@[simp] theorem trans_totalEquiv (e : ExtensionEquiv h h')
    (e' : ExtensionEquiv h' h'') :
    (e.trans e').totalEquiv = e.totalEquiv.trans e'.totalEquiv := rfl

end ExtensionEquiv

/-- The normal closure in the ambient field of a nested intermediate-field
extension. -/
def normalClosureOver (h : E ≤ L) : IntermediateField (↥E) Ω :=
  normalClosure (↥E) (extendScalars h) Ω

/-- The original finite extension embeds in its normal closure. -/
theorem extendScalars_le_normalClosureOver (h : E ≤ L) :
    extendScalars h ≤ normalClosureOver h :=
  le_normalClosure _

/-- A normal closure of a finite extension remains finite. -/
theorem normalClosureOver_finiteDimensional (h : E ≤ L)
    (hfin : FiniteDimensional (↥E) (↥(extendScalars h))) :
    FiniteDimensional (↥E) (↥(normalClosureOver h)) := by
  letI := hfin
  exact normalClosure.is_finiteDimensional (↥E) (↥(extendScalars h)) Ω

/-- Inside an algebraically closed ambient field, the normal closure of an
algebraic extension is normal over its base. -/
theorem normalClosureOver_normal [IsAlgClosed Ω] (h : E ≤ L)
    (halg : Algebra.IsAlgebraic (↥E) (↥(extendScalars h))) :
    Normal (↥E) (↥(normalClosureOver h)) := by
  letI := halg
  exact
    (Algebra.IsAlgebraic.isNormalClosure_normalClosure
      (F := ↥E) (K := ↥(extendScalars h)) (L := Ω)
      (fun _ ↦ IsAlgClosed.splits _)).normal

/-- Embeddings of the original extension into the ambient field are
equivalent to embeddings into its normal closure.  Thus every conjugate
branch already lives on the normal cover. -/
def embeddingEquivNormal (h : E ≤ L) :
    ((↥(extendScalars h)) →ₐ[↥E] (↥(normalClosureOver h))) ≃
      ((↥(extendScalars h)) →ₐ[↥E] Ω) :=
  normalClosure.algHomEquiv (↥E) (↥(extendScalars h)) Ω

/-- The unique lift of an ambient embedding of the finite extension to
the normal cover. -/
def liftEmbedding (h : E ≤ L)
    (f : (↥(extendScalars h)) →ₐ[↥E] Ω) :
    (↥(extendScalars h)) →ₐ[↥E] (↥(normalClosureOver h)) :=
  (embeddingEquivNormal h).symm f

/-- Composing a lifted branch with the normal-cover inclusion recovers
the original ambient embedding. -/
@[simp] theorem normalClosure_val_comp_liftEmbedding (h : E ≤ L)
    (f : (↥(extendScalars h)) →ₐ[↥E] Ω) :
    (normalClosureOver h).val.comp (liftEmbedding h f) = f :=
  (embeddingEquivNormal h).apply_symm_apply f

/-- The literal selected component is the lift of the inclusion of the
original extension into the ambient field. -/
def selectedEmbedding (h : E ≤ L) :
    (↥(extendScalars h)) →ₐ[↥E] (↥(normalClosureOver h)) :=
  liftEmbedding h (extendScalars h).val

/-- The selected embedding evaluates to the original literal branch in
the ambient field. -/
@[simp] theorem normalClosure_val_comp_selectedEmbedding (h : E ≤ L) :
    (normalClosureOver h).val.comp (selectedEmbedding h) =
      (extendScalars h).val :=
  normalClosure_val_comp_liftEmbedding h _

/-- Embeddings of a finite normal cover into the ambient field are exactly
its automorphisms. -/
def normalEmbeddingEquivAut (h : E ≤ L)
    [Normal (↥E) (↥(normalClosureOver h))] :
    ((↥(normalClosureOver h)) →ₐ[↥E] Ω) ≃
      ((↥(normalClosureOver h)) ≃ₐ[↥E] (↥(normalClosureOver h))) :=
  Normal.algHomEquivAut (↥E) Ω (↥(normalClosureOver h))

/-- A finite extension has only finitely many ambient conjugate
embeddings. -/
theorem finite_ambientEmbeddings (h : E ≤ L)
    (hfin : FiniteDimensional (↥E) (↥(extendScalars h))) :
    Finite ((↥(extendScalars h)) →ₐ[↥E] Ω) := by
  letI := hfin
  infer_instance

/-- The automorphism group of the finite normal cover is finite. -/
theorem finite_normalAutomorphisms (h : E ≤ L)
    (hfin : FiniteDimensional (↥E) (↥(extendScalars h))) :
    Finite ((↥(normalClosureOver h)) ≃ₐ[↥E]
      (↥(normalClosureOver h))) := by
  letI := normalClosureOver_finiteDimensional h hfin
  infer_instance

end FiniteCover

namespace FiniteCorrespondencePair

variable (P : FiniteCorrespondencePair k Ω)

/-- The one-variable function field generated by the source coordinate. -/
def sourceField : IntermediateField k Ω :=
  adjoin k {P.source}

/-- The one-variable function field generated by the target coordinate. -/
def targetField : IntermediateField k Ω :=
  adjoin k {P.target}

/-- The joint function field of the selected correspondence branch. -/
def branchField : IntermediateField k Ω :=
  adjoin k {P.source, P.target}

/-- The source function field embeds in the selected branch field. -/
theorem sourceField_le_branchField : P.sourceField ≤ P.branchField :=
  adjoin.mono k _ _ (by simp)

/-- The target function field embeds in the selected branch field. -/
theorem targetField_le_branchField : P.targetField ≤ P.branchField :=
  adjoin.mono k _ _ (by simp)

/-- The selected branch field regarded as a cover of its source field. -/
def branchOverSource : IntermediateField (↥P.sourceField) Ω :=
  extendScalars P.sourceField_le_branchField

/-- The selected branch field regarded as a cover of its target field. -/
def branchOverTarget : IntermediateField (↥P.targetField) Ω :=
  extendScalars P.targetField_le_branchField

/-- Over the source field, the branch field is generated by the target. -/
theorem branchOverSource_eq_adjoin_target :
    P.branchOverSource = adjoin (↥P.sourceField) {P.target} := by
  refine restrictScalars_injective k ?_
  unfold branchOverSource sourceField branchField
  rw [adjoin_adjoin_left, extendScalars_restrictScalars]
  simp only [Set.union_singleton, Set.pair_comm]

/-- Over the target field, the branch field is generated by the source. -/
theorem branchOverTarget_eq_adjoin_source :
    P.branchOverTarget = adjoin (↥P.targetField) {P.source} := by
  refine restrictScalars_injective k ?_
  unfold branchOverTarget targetField branchField
  rw [adjoin_adjoin_left, extendScalars_restrictScalars]
  simp only [Set.union_singleton]

/-- The selected branch is a finite cover of its source function field. -/
theorem branchOverSource_finiteDimensional :
    FiniteDimensional (↥P.sourceField) (↥P.branchOverSource) := by
  rw [P.branchOverSource_eq_adjoin_target]
  exact finiteDimensional_adjoin fun x hx ↦ by
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ((mem_racl_iff k).1 P.target_mem_source).isIntegral

/-- The selected branch is a finite cover of its target function field. -/
theorem branchOverTarget_finiteDimensional :
    FiniteDimensional (↥P.targetField) (↥P.branchOverTarget) := by
  rw [P.branchOverTarget_eq_adjoin_source]
  exact finiteDimensional_adjoin fun x hx ↦ by
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ((mem_racl_iff k).1 P.source_mem_target).isIntegral

/-- The normal closure of the selected branch over its source function
field, taken inside the ambient algebraically closed field. -/
def sourceNormalField : IntermediateField (↥P.sourceField) Ω :=
  FiniteCover.normalClosureOver P.sourceField_le_branchField

/-- The branch field embeds in its normal closure over the source. -/
theorem branchOverSource_le_sourceNormalField :
    P.branchOverSource ≤ P.sourceNormalField :=
  FiniteCover.extendScalars_le_normalClosureOver
    P.sourceField_le_branchField

/-- The normal closure over the source is still a finite extension. -/
theorem sourceNormalField_finiteDimensional :
    FiniteDimensional (↥P.sourceField) (↥P.sourceNormalField) :=
  FiniteCover.normalClosureOver_finiteDimensional
    P.sourceField_le_branchField
    P.branchOverSource_finiteDimensional

/-- The source normalization field is normal in an algebraically closed
ambient field. -/
theorem sourceNormalField_normal [IsAlgClosed Ω] :
    Normal (↥P.sourceField) (↥P.sourceNormalField) := by
  letI := P.branchOverSource_finiteDimensional
  exact FiniteCover.normalClosureOver_normal
    P.sourceField_le_branchField
    (Algebra.IsAlgebraic.of_finite (↥P.sourceField)
      (↥P.branchOverSource))

/-- The normal closure of the selected branch over its target function
field. -/
def targetNormalField : IntermediateField (↥P.targetField) Ω :=
  FiniteCover.normalClosureOver P.targetField_le_branchField

/-- The branch field embeds in its normal closure over the target. -/
theorem branchOverTarget_le_targetNormalField :
    P.branchOverTarget ≤ P.targetNormalField :=
  FiniteCover.extendScalars_le_normalClosureOver
    P.targetField_le_branchField

/-- The normal closure over the target is still a finite extension. -/
theorem targetNormalField_finiteDimensional :
    FiniteDimensional (↥P.targetField) (↥P.targetNormalField) :=
  FiniteCover.normalClosureOver_finiteDimensional
    P.targetField_le_branchField
    P.branchOverTarget_finiteDimensional

/-- The target normalization field is normal in an algebraically closed
ambient field. -/
theorem targetNormalField_normal [IsAlgClosed Ω] :
    Normal (↥P.targetField) (↥P.targetNormalField) := by
  letI := P.branchOverTarget_finiteDimensional
  exact FiniteCover.normalClosureOver_normal
    P.targetField_le_branchField
    (Algebra.IsAlgebraic.of_finite (↥P.targetField)
      (↥P.branchOverTarget))

/-- The joint field of two consecutive selected branches. -/
def chainField (Q : FiniteCorrespondencePair k Ω) :
    IntermediateField k Ω :=
  adjoin k {P.source, P.target, Q.target}

/-- The left branch field embeds in the joint chain field. -/
theorem branchField_le_chainField (Q : FiniteCorrespondencePair k Ω) :
    P.branchField ≤ P.chainField Q := by
  unfold branchField chainField
  apply adjoin.mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

/-- When the middle coordinates agree, the right branch field embeds in
the joint chain field. -/
theorem rightBranchField_le_chainField
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    Q.branchField ≤ P.chainField Q :=
  adjoin.mono k _ _ (by simp [← h])

/-- The endpoint branch selected by composition embeds in the joint chain
field. -/
theorem compositeBranchField_le_chainField
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    (P.comp Q h).branchField ≤ P.chainField Q := by
  unfold branchField chainField
  apply adjoin.mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)

/-- The chain field as an extension of the left branch field. -/
def chainOverLeft (Q : FiniteCorrespondencePair k Ω) :
    IntermediateField (↥P.branchField) Ω :=
  extendScalars (P.branchField_le_chainField Q)

/-- The chain field as an extension of the right branch field. -/
def chainOverRight (Q : FiniteCorrespondencePair k Ω)
    (h : P.target = Q.source) : IntermediateField (↥Q.branchField) Ω :=
  extendScalars (P.rightBranchField_le_chainField Q h)

/-- The chain field as an extension of the composite endpoint branch. -/
def chainOverComposite (Q : FiniteCorrespondencePair k Ω)
    (h : P.target = Q.source) :
    IntermediateField (↥(P.comp Q h).branchField) Ω :=
  extendScalars (P.compositeBranchField_le_chainField Q h)

/-- Over the left branch, the chain field is generated by the final
coordinate. -/
theorem chainOverLeft_eq_adjoin_target
    (Q : FiniteCorrespondencePair k Ω) :
    P.chainOverLeft Q = adjoin (↥P.branchField) {Q.target} := by
  refine restrictScalars_injective k ?_
  unfold chainOverLeft branchField chainField
  rw [adjoin_adjoin_left, extendScalars_restrictScalars]
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  tauto

/-- Over the right branch, the chain field is generated by the initial
coordinate. -/
theorem chainOverRight_eq_adjoin_source
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    P.chainOverRight Q h = adjoin (↥Q.branchField) {P.source} := by
  refine restrictScalars_injective k ?_
  unfold chainOverRight branchField chainField
  rw [adjoin_adjoin_left, extendScalars_restrictScalars]
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  rw [← h]
  tauto

/-- Over the composite endpoint branch, the chain field is generated by
the shared middle coordinate. -/
theorem chainOverComposite_eq_adjoin_middle
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    P.chainOverComposite Q h =
      adjoin (↥(P.comp Q h).branchField) {P.target} := by
  refine restrictScalars_injective k ?_
  unfold chainOverComposite branchField chainField
  rw [adjoin_adjoin_left, extendScalars_restrictScalars]
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  tauto

/-- The joint chain field is finite over the left selected branch. -/
theorem chainOverLeft_finiteDimensional
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    FiniteDimensional (↥P.branchField) (↥(P.chainOverLeft Q)) := by
  rw [P.chainOverLeft_eq_adjoin_target Q]
  exact finiteDimensional_adjoin fun x hx ↦ by
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact (isAlgebraic_of_le P.targetField_le_branchField
      (by
        unfold targetField
        rw [h]
        exact (mem_racl_iff k).1 Q.target_mem_source)).isIntegral

/-- The joint chain field is finite over the right selected branch. -/
theorem chainOverRight_finiteDimensional
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    FiniteDimensional (↥Q.branchField) (↥(P.chainOverRight Q h)) := by
  rw [P.chainOverRight_eq_adjoin_source Q h]
  exact finiteDimensional_adjoin fun x hx ↦ by
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact (isAlgebraic_of_le Q.sourceField_le_branchField
      (by
        unfold sourceField
        rw [← h]
        exact (mem_racl_iff k).1 P.source_mem_target)).isIntegral

/-- The joint chain field is finite over the selected composite endpoint
branch. -/
theorem chainOverComposite_finiteDimensional
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    FiniteDimensional (↥(P.comp Q h).branchField)
      (↥(P.chainOverComposite Q h)) := by
  rw [P.chainOverComposite_eq_adjoin_middle Q h]
  exact finiteDimensional_adjoin fun x hx ↦ by
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact (isAlgebraic_of_le
      (P.comp Q h).sourceField_le_branchField
      ((mem_racl_iff k).1 P.target_mem_source)).isIntegral

/-- The normal closure of a chain field over its selected composite
endpoint branch.  It adjoins all ambient conjugates of the shared middle
coordinate. -/
def chainNormalOverComposite
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    IntermediateField (↥(P.comp Q h).branchField) Ω :=
  FiniteCover.normalClosureOver
    (P.compositeBranchField_le_chainField Q h)

/-- The three-coordinate chain field embeds in its normal closure over the
composite endpoint branch. -/
theorem chainOverComposite_le_normal
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    P.chainOverComposite Q h ≤ P.chainNormalOverComposite Q h :=
  FiniteCover.extendScalars_le_normalClosureOver
    (P.compositeBranchField_le_chainField Q h)

/-- The chain normal closure is finite over the selected composite
branch. -/
theorem chainNormalOverComposite_finiteDimensional
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    FiniteDimensional (↥(P.comp Q h).branchField)
      (↥(P.chainNormalOverComposite Q h)) :=
  FiniteCover.normalClosureOver_finiteDimensional
    (P.compositeBranchField_le_chainField Q h)
    (P.chainOverComposite_finiteDimensional Q h)

/-- The chain normal closure is normal over the selected composite branch
inside an algebraically closed ambient field. -/
theorem chainNormalOverComposite_normal [IsAlgClosed Ω]
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    Normal (↥(P.comp Q h).branchField)
      (↥(P.chainNormalOverComposite Q h)) := by
  letI := P.chainOverComposite_finiteDimensional Q h
  exact FiniteCover.normalClosureOver_normal
    (P.compositeBranchField_le_chainField Q h)
    (Algebra.IsAlgebraic.of_finite
      (↥(P.comp Q h).branchField) (↥(P.chainOverComposite Q h)))

end FiniteCorrespondencePair

end

end AclGeom
