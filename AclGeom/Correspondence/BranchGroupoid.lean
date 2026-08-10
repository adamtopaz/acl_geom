/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import AclGeom.Correspondence.FiniteCover
import AclGeom.Correspondence.GroupConfiguration
import Mathlib.CategoryTheory.Action

/-!
# The groupoid of conjugate branches on a normal cover

A finite selected correspondence becomes single-valued only after choosing
one embedding of its branch field into a common normal cover.  The deck
transformation group of that cover acts on all such embeddings by
postcomposition.  Its action groupoid is the precise categorical object
which records the selected branch and all of its conjugates:

* `NormalBranchEmbedding` wraps an embedding of the branch field into the
  normal cover;
* deck transformations act by postcomposition;
* normality makes this action transitive, since every branch embedding
  extends to an automorphism of the normal cover;
* `normalBranchGroupoid` is therefore a connected genuine groupoid;
* every chosen arrow family in it carries the rational group chunk supplied
  by `groupoidArrowChunk`.

This construction resolves the finite branch ambiguity on a fixed normal
cover.  The separate geometric task is to assemble the varying generic
parameter families into the normal covers used here.

This module is part of the finite-cover integration in blueprint §8.1.
-/

namespace AclGeom

noncomputable section

open CategoryTheory

section NormalBranchAction

variable (E M N : Type*) [Field E] [Field M] [Field N]
  [Algebra E M] [Algebra E N]

/-- An embedding of a selected branch field `M` into a normal cover `N`,
over the endpoint field `E`. -/
@[ext]
structure NormalBranchEmbedding where
  /-- The underlying embedding of function fields. -/
  toAlgHom : M →ₐ[E] N

namespace NormalBranchEmbedding

variable {E M N}

/-- A deck transformation acts on a branch embedding by
postcomposition. -/
instance : SMul (N ≃ₐ[E] N) (NormalBranchEmbedding E M N) where
  smul σ f := ⟨σ.toAlgHom.comp f.toAlgHom⟩

@[simp] theorem smul_toAlgHom (σ : N ≃ₐ[E] N)
    (f : NormalBranchEmbedding E M N) :
    (σ • f).toAlgHom = σ.toAlgHom.comp f.toAlgHom := rfl

/-- Postcomposition is a genuine action of the deck-transformation
group. -/
instance : MulAction (N ≃ₐ[E] N) (NormalBranchEmbedding E M N) where
  one_smul f := by
    ext x
    rfl
  mul_smul σ τ f := by
    ext x
    rfl

variable [Algebra M N] [IsScalarTower E M N]

/-- The literal inclusion of the branch field in its cover. -/
def canonical : NormalBranchEmbedding E M N :=
  ⟨IsScalarTower.toAlgHom E M N⟩

@[simp] theorem canonical_apply (x : M) :
    (canonical (E := E) (M := M) (N := N)).toAlgHom x =
      algebraMap M N x := rfl

/-- Normality extends any branch embedding to a deck transformation. -/
def extendToAut [Normal E N] (f : NormalBranchEmbedding E M N) :
    N ≃ₐ[E] N :=
  AlgEquiv.ofBijective (f.toAlgHom.liftNormal N)
    (AlgHom.normal_bijective E N N _)

/-- The extended deck transformation sends the literal branch to the
chosen conjugate branch. -/
theorem extendToAut_smul_canonical [Normal E N]
    (f : NormalBranchEmbedding E M N) :
    f.extendToAut • canonical (E := E) (M := M) (N := N) = f := by
  ext x
  exact f.toAlgHom.liftNormal_commutes N x

/-- The deck-transformation action on branches of a normal cover is
transitive. -/
theorem exists_smul_eq [Normal E N]
    (f g : NormalBranchEmbedding E M N) :
    ∃ σ : N ≃ₐ[E] N, σ • f = g := by
  let α := f.extendToAut
  let β := g.extendToAut
  refine ⟨β * α⁻¹, ?_⟩
  ext x
  change (β * α⁻¹) (f.toAlgHom x) = g.toAlgHom x
  rw [AlgEquiv.mul_apply]
  have hf : α (algebraMap M N x) = f.toAlgHom x :=
    congrArg (fun h ↦ h.toAlgHom x) f.extendToAut_smul_canonical
  have hg : β (algebraMap M N x) = g.toAlgHom x :=
    congrArg (fun h ↦ h.toAlgHom x) g.extendToAut_smul_canonical
  rw [← hf]
  change β (α.symm (α (algebraMap M N x))) = g.toAlgHom x
  rw [α.symm_apply_apply, hg]

end NormalBranchEmbedding

/-- The action groupoid of conjugate embeddings of a branch field into a
normal cover. -/
abbrev normalBranchGroupoid :=
  ActionCategory (N ≃ₐ[E] N) (NormalBranchEmbedding E M N)

namespace normalBranchGroupoid

variable {E M N} [Algebra M N] [IsScalarTower E M N]

/-- The object represented by the literal inclusion of the branch field. -/
def selectedObject : normalBranchGroupoid E M N :=
  NormalBranchEmbedding.canonical (E := E) (M := M) (N := N)

/-- The object represented by a chosen conjugate branch. -/
def object (f : NormalBranchEmbedding E M N) :
    normalBranchGroupoid E M N := f

/-- Normality makes the branch action groupoid connected. -/
theorem isConnected [Normal E N] :
    IsConnected (normalBranchGroupoid E M N) := by
  letI : Nonempty (NormalBranchEmbedding E M N) :=
    ⟨NormalBranchEmbedding.canonical⟩
  letI : MulAction.IsPretransitive (N ≃ₐ[E] N)
      (NormalBranchEmbedding E M N) :=
    MulAction.IsPretransitive.mk NormalBranchEmbedding.exists_smul_eq
  infer_instance

/-- The canonical arrow from the selected branch to any conjugate branch,
labelled by the normal extension of that branch embedding. -/
def selectedArrow [Normal E N] (f : NormalBranchEmbedding E M N) :
    selectedObject (E := E) (M := M) (N := N) ⟶ object f :=
  ⟨f.extendToAut, f.extendToAut_smul_canonical⟩

@[simp] theorem selectedArrow_val [Normal E N]
    (f : NormalBranchEmbedding E M N) :
    (selectedArrow f).val = f.extendToAut := rfl

/-- Every based conjugate-branch arrow family on the normal cover carries
the rational group chunk transported from the genuine action groupoid. -/
def arrowChunk [Normal E N] (f : NormalBranchEmbedding E M N) :
    RationalGroupChunk
      (selectedObject (E := E) (M := M) (N := N) ⟶ object f) :=
  groupoidArrowChunk (selectedArrow f)

end normalBranchGroupoid

end NormalBranchAction

section FiniteCoverBranches

open IntermediateField

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
  {E L : IntermediateField k Ω}

/-- Branch embeddings of a concrete finite cover into its normal closure. -/
abbrev FiniteCoverBranch (h : E ≤ L) :=
  NormalBranchEmbedding (↥E) (↥(extendScalars h))
    (↥(FiniteCover.normalClosureOver h))

/-- Deck transformations of a concrete finite normal cover. -/
abbrev FiniteCoverDeck (h : E ≤ L) :=
  (↥(FiniteCover.normalClosureOver h)) ≃ₐ[↥E]
    (↥(FiniteCover.normalClosureOver h))

/-- The genuine action groupoid of all conjugate branches of a concrete
finite cover. -/
abbrev finiteCoverBranchGroupoid (h : E ≤ L) :=
  normalBranchGroupoid (↥E) (↥(extendScalars h))
    (↥(FiniteCover.normalClosureOver h))

/-- The literal selected branch, regarded as an object of the normal-cover
branch action. -/
def finiteCoverSelectedBranch (h : E ≤ L) : FiniteCoverBranch h :=
  ⟨FiniteCover.selectedEmbedding h⟩

/-- The selected branch as an object of its conjugate-branch groupoid. -/
def finiteCoverSelectedObject (h : E ≤ L) :
    finiteCoverBranchGroupoid h :=
  finiteCoverSelectedBranch h

/-- A concrete finite cover has only finitely many branches in its normal
closure. -/
theorem finite_coverBranches (h : E ≤ L)
    (hfin : FiniteDimensional (↥E) (↥(extendScalars h))) :
    Finite (FiniteCoverBranch h) := by
  letI := hfin
  exact Finite.of_injective NormalBranchEmbedding.toAlgHom
    fun f g hfg ↦ NormalBranchEmbedding.ext hfg

/-- Inside an algebraically closed ambient field, deck transformations act
transitively on the conjugate branches of a finite cover. -/
theorem finiteCoverBranch_exists_smul_eq [IsAlgClosed Ω]
    (h : E ≤ L)
    (hfin : FiniteDimensional (↥E) (↥(extendScalars h)))
    (f g : FiniteCoverBranch h) :
    ∃ σ : FiniteCoverDeck h, σ • f = g := by
  letI : Algebra (↥(extendScalars h))
      (↥(FiniteCover.normalClosureOver h)) :=
    (FiniteCover.selectedEmbedding h).toAlgebra
  letI : IsScalarTower (↥E) (↥(extendScalars h))
      (↥(FiniteCover.normalClosureOver h)) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (FiniteCover.selectedEmbedding h).commutes x |>.symm
  letI : FiniteDimensional (↥E) (↥(extendScalars h)) := hfin
  letI : Normal (↥E) (↥(FiniteCover.normalClosureOver h)) :=
    FiniteCover.normalClosureOver_normal h
      (Algebra.IsAlgebraic.of_finite (↥E) (↥(extendScalars h)))
  exact NormalBranchEmbedding.exists_smul_eq f g

/-- The conjugate-branch groupoid of a concrete finite cover is connected. -/
theorem finiteCoverBranchGroupoid_isConnected [IsAlgClosed Ω]
    (h : E ≤ L)
    (hfin : FiniteDimensional (↥E) (↥(extendScalars h))) :
    IsConnected (finiteCoverBranchGroupoid h) := by
  letI : Nonempty (FiniteCoverBranch h) :=
    ⟨finiteCoverSelectedBranch h⟩
  letI : MulAction.IsPretransitive (FiniteCoverDeck h)
      (FiniteCoverBranch h) :=
    MulAction.IsPretransitive.mk
      (finiteCoverBranch_exists_smul_eq h hfin)
  infer_instance

/-- A chosen arrow from the literal branch to any conjugate branch of a
finite normal cover.  Connectedness makes the relevant hom-set nonempty;
the choice is deliberately kept behind this interface. -/
def finiteCoverSelectedArrow [IsAlgClosed Ω]
    (h : E ≤ L) (hfin : FiniteDimensional (↥E) (↥(extendScalars h)))
    (b : finiteCoverBranchGroupoid h) :
    finiteCoverSelectedObject h ⟶ b := by
  let hex := finiteCoverBranch_exists_smul_eq h hfin
    (finiteCoverSelectedBranch h) b.back
  let σ := Classical.choose hex
  have hσ := Classical.choose_spec hex
  exact ⟨σ, hσ⟩

/-- Every conjugate branch of a finite normal cover carries the rational
group chunk obtained from arrows based at the literal selected branch. -/
def finiteCoverArrowChunk [IsAlgClosed Ω]
    (h : E ≤ L) (hfin : FiniteDimensional (↥E) (↥(extendScalars h)))
    (b : finiteCoverBranchGroupoid h) :
    RationalGroupChunk (finiteCoverSelectedObject h ⟶ b) :=
  groupoidArrowChunk (finiteCoverSelectedArrow h hfin b)

end FiniteCoverBranches

end

end AclGeom
