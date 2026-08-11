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

section Reparametrize

variable {M' : Type*} [Field M'] [Algebra E M']

/-- Regard an embedding of an equivalent branch field as an embedding of
the original branch field.  This is the domain-side operation needed before
two selected branches can be compared by a deck transformation of one
normal cover. -/
def reparametrize (g : NormalBranchEmbedding E M' N)
    (e : M ≃ₐ[E] M') : NormalBranchEmbedding E M N :=
  ⟨g.toAlgHom.comp e.toAlgHom⟩

@[simp] theorem reparametrize_apply
    (g : NormalBranchEmbedding E M' N) (e : M ≃ₐ[E] M') (x : M) :
    (g.reparametrize e).toAlgHom x = g.toAlgHom (e x) :=
  rfl

end Reparametrize

section Transport

variable {E' M' N' : Type*} [Field E'] [Field M'] [Field N']
  [Algebra E' M'] [Algebra E' N']

/-- Transport a branch embedding along compatible equivalences of its
base, branch field, and normal-cover field. -/
def mapOfEquiv (eE : E ≃+* E') (eM : M ≃+* M') (eN : N ≃+* N')
    (hM : eM.toRingHom.comp (algebraMap E M) =
      (algebraMap E' M').comp eE.toRingHom)
    (hN : eN.toRingHom.comp (algebraMap E N) =
      (algebraMap E' N').comp eE.toRingHom)
    (f : NormalBranchEmbedding E M N) :
    NormalBranchEmbedding E' M' N' := by
  have hM_symm (x : E') :
      eM.symm (algebraMap E' M' x) =
        algebraMap E M (eE.symm x) := by
    apply eM.injective
    rw [eM.apply_symm_apply]
    have hm := DFunLike.congr_fun hM (eE.symm x)
    change eM (algebraMap E M (eE.symm x)) =
      algebraMap E' M' (eE (eE.symm x)) at hm
    rw [eE.apply_symm_apply] at hm
    exact hm.symm
  refine ⟨{
    toRingHom := (eN.toRingHom.comp f.toAlgHom.toRingHom).comp
      eM.symm.toRingHom
    commutes' := fun x ↦ ?_ }⟩
  change eN (f.toAlgHom (eM.symm (algebraMap E' M' x))) =
    algebraMap E' N' x
  rw [hM_symm, f.toAlgHom.commutes]
  have hn := DFunLike.congr_fun hN (eE.symm x)
  change eN (algebraMap E N (eE.symm x)) =
    algebraMap E' N' (eE (eE.symm x)) at hn
  rwa [eE.apply_symm_apply] at hn

/-- Transport of branch embeddings is pointwise conjugation by the branch-
and normal-field equivalences. -/
@[simp] theorem mapOfEquiv_apply
    (eE : E ≃+* E') (eM : M ≃+* M') (eN : N ≃+* N')
    (hM : eM.toRingHom.comp (algebraMap E M) =
      (algebraMap E' M').comp eE.toRingHom)
    (hN : eN.toRingHom.comp (algebraMap E N) =
      (algebraMap E' N').comp eE.toRingHom)
    (f : NormalBranchEmbedding E M N) (x : M') :
    (mapOfEquiv eE eM eN hM hN f).toAlgHom x =
      eN (f.toAlgHom (eM.symm x)) := by
  change eN (f.toAlgHom (eM.symm x)) = _
  rfl

/-- Compatible field equivalences induce an equivalence of the corresponding
types of conjugate branches. -/
def equivOfEquiv (eE : E ≃+* E') (eM : M ≃+* M') (eN : N ≃+* N')
    (hM : eM.toRingHom.comp (algebraMap E M) =
      (algebraMap E' M').comp eE.toRingHom)
    (hN : eN.toRingHom.comp (algebraMap E N) =
      (algebraMap E' N').comp eE.toRingHom) :
    NormalBranchEmbedding E M N ≃ NormalBranchEmbedding E' M' N' := by
  have hM' : eM.symm.toRingHom.comp (algebraMap E' M') =
      (algebraMap E M).comp eE.symm.toRingHom := by
    apply RingHom.ext
    intro x
    change eM.symm (algebraMap E' M' x) =
      algebraMap E M (eE.symm x)
    apply eM.injective
    rw [eM.apply_symm_apply]
    have hm := DFunLike.congr_fun hM (eE.symm x)
    change eM (algebraMap E M (eE.symm x)) =
      algebraMap E' M' (eE (eE.symm x)) at hm
    rw [eE.apply_symm_apply] at hm
    exact hm.symm
  have hN' : eN.symm.toRingHom.comp (algebraMap E' N') =
      (algebraMap E N).comp eE.symm.toRingHom := by
    apply RingHom.ext
    intro x
    change eN.symm (algebraMap E' N' x) =
      algebraMap E N (eE.symm x)
    apply eN.injective
    rw [eN.apply_symm_apply]
    have hn := DFunLike.congr_fun hN (eE.symm x)
    change eN (algebraMap E N (eE.symm x)) =
      algebraMap E' N' (eE (eE.symm x)) at hn
    rw [eE.apply_symm_apply] at hn
    exact hn.symm
  exact
    { toFun := mapOfEquiv eE eM eN hM hN
      invFun := mapOfEquiv eE.symm eM.symm eN.symm hM' hN'
      left_inv := fun f ↦ by
        ext x
        simp
      right_inv := fun f ↦ by
        ext x
        simp }

/-- Conjugation by a semilinear equivalence of normal-cover fields
transports deck transformations between the two base fields. -/
def deckMapOfEquiv (eE : E ≃+* E') (eN : N ≃+* N')
    (hN : eN.toRingHom.comp (algebraMap E N) =
      (algebraMap E' N').comp eE.toRingHom)
    (σ : N ≃ₐ[E] N) : N' ≃ₐ[E'] N' := by
  let r : N' ≃+* N' := eN.symm.trans (σ.toRingEquiv.trans eN)
  apply AlgEquiv.ofRingEquiv (f := r)
  intro x
  change eN (σ (eN.symm (algebraMap E' N' x))) =
    algebraMap E' N' x
  have hN_symm :
      eN.symm (algebraMap E' N' x) =
        algebraMap E N (eE.symm x) := by
    apply eN.injective
    rw [eN.apply_symm_apply]
    have hn := DFunLike.congr_fun hN (eE.symm x)
    change eN (algebraMap E N (eE.symm x)) =
      algebraMap E' N' (eE (eE.symm x)) at hn
    rw [eE.apply_symm_apply] at hn
    exact hn.symm
  rw [hN_symm, σ.commutes]
  have hn := DFunLike.congr_fun hN (eE.symm x)
  change eN (algebraMap E N (eE.symm x)) =
    algebraMap E' N' (eE (eE.symm x)) at hn
  rwa [eE.apply_symm_apply] at hn

/-- Deck transport acts by conjugation on the underlying normal-cover
field. -/
@[simp] theorem deckMapOfEquiv_apply
    (eE : E ≃+* E') (eN : N ≃+* N')
    (hN : eN.toRingHom.comp (algebraMap E N) =
      (algebraMap E' N').comp eE.toRingHom)
    (σ : N ≃ₐ[E] N) (x : N') :
    deckMapOfEquiv eE eN hN σ x = eN (σ (eN.symm x)) := by
  rfl

/-- A compatible equivalence of normal-cover fields identifies their
deck-transformation groups. -/
def deckEquivOfEquiv (eE : E ≃+* E') (eN : N ≃+* N')
    (hN : eN.toRingHom.comp (algebraMap E N) =
      (algebraMap E' N').comp eE.toRingHom) :
    (N ≃ₐ[E] N) ≃* (N' ≃ₐ[E'] N') := by
  have hN' : eN.symm.toRingHom.comp (algebraMap E' N') =
      (algebraMap E N).comp eE.symm.toRingHom := by
    apply RingHom.ext
    intro x
    change eN.symm (algebraMap E' N' x) =
      algebraMap E N (eE.symm x)
    apply eN.injective
    rw [eN.apply_symm_apply]
    have hn := DFunLike.congr_fun hN (eE.symm x)
    change eN (algebraMap E N (eE.symm x)) =
      algebraMap E' N' (eE (eE.symm x)) at hn
    rw [eE.apply_symm_apply] at hn
    exact hn.symm
  exact
    { toFun := deckMapOfEquiv eE eN hN
      invFun := deckMapOfEquiv eE.symm eN.symm hN'
      left_inv := fun σ ↦ by
        ext x
        simp
      right_inv := fun σ ↦ by
        ext x
        simp
      map_mul' := fun σ τ ↦ by
        ext x
        simp [AlgEquiv.mul_apply] }

end Transport

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

section TransportAction

variable {E' M' N' : Type*} [Field E'] [Field M'] [Field N']
  [Algebra E' M'] [Algebra E' N']

/-- Branch transport is equivariant for conjugation transport of deck
transformations. -/
@[simp] theorem mapOfEquiv_smul
    (eE : E ≃+* E') (eM : M ≃+* M') (eN : N ≃+* N')
    (hM : eM.toRingHom.comp (algebraMap E M) =
      (algebraMap E' M').comp eE.toRingHom)
    (hN : eN.toRingHom.comp (algebraMap E N) =
      (algebraMap E' N').comp eE.toRingHom)
    (σ : N ≃ₐ[E] N) (f : NormalBranchEmbedding E M N) :
    mapOfEquiv eE eM eN hM hN (σ • f) =
      deckMapOfEquiv eE eN hN σ •
        mapOfEquiv eE eM eN hM hN f := by
  ext x
  simp

end TransportAction

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

end NormalBranchEmbedding

namespace NormalBranchEmbedding

variable {E M N}

/-- The distinguished deck transformation carrying one branch embedding
to another.  The first embedding supplies the temporary algebra structure
on the branch field, so this definition does not depend on an unrelated
ambient inclusion of that field into the normal cover. -/
noncomputable def alignmentAut [Normal E N]
    (f g : NormalBranchEmbedding E M N) : N ≃ₐ[E] N := by
  letI : Algebra M N := f.toAlgHom.toAlgebra
  letI : IsScalarTower E M N :=
    IsScalarTower.of_algebraMap_eq fun x ↦ f.toAlgHom.commutes x |>.symm
  exact g.extendToAut

/-- The distinguished alignment automorphism sends its anchoring branch
embedding to the requested branch embedding. -/
theorem alignmentAut_smul [Normal E N]
    (f g : NormalBranchEmbedding E M N) :
    alignmentAut f g • f = g := by
  letI : Algebra M N := f.toAlgHom.toAlgebra
  letI : IsScalarTower E M N :=
    IsScalarTower.of_algebraMap_eq fun x ↦ f.toAlgHom.commutes x |>.symm
  exact g.extendToAut_smul_canonical

/-- After identifying two branch domains over the common base, the
distinguished deck transformation carries the first embedding to the
reparametrized second embedding. -/
theorem alignmentAut_smul_reparametrize [Normal E N]
    {M' : Type*} [Field M'] [Algebra E M']
    (f : NormalBranchEmbedding E M N)
    (g : NormalBranchEmbedding E M' N) (e : M ≃ₐ[E] M') :
    alignmentAut f (g.reparametrize e) • f = g.reparametrize e :=
  alignmentAut_smul f (g.reparametrize e)

/-- The deck-transformation action on branches of a normal cover is
transitive. -/
theorem exists_smul_eq [Normal E N]
    (f g : NormalBranchEmbedding E M N) :
    ∃ σ : N ≃ₐ[E] N, σ • f = g := by
  exact ⟨alignmentAut f g, alignmentAut_smul f g⟩

end NormalBranchEmbedding

section ActionCategoryTransport

variable {G H X Y : Type*} [Group G] [Group H]
  [MulAction G X] [MulAction H Y]

/-- Left multiplication by a group element as an equivalence of the
underlying action. -/
def mulActionEquiv (g : G) : X ≃ X where
  toFun := (g • ·)
  invFun := (g⁻¹ • ·)
  left_inv x := by simp
  right_inv x := by simp

@[simp] theorem mulActionEquiv_apply (g : G) (x : X) :
    mulActionEquiv g x = g • x := rfl

/-- An equivalence of acting groups together with an equivariant equivalence
of their actions induces a functor of action categories. -/
def actionCategoryFunctorOfEquivariantEquiv
    (eG : G ≃* H) (eX : X ≃ Y)
    (heq : ∀ g x, eX (g • x) = eG g • eX x) :
    ActionCategory G X ⥤ ActionCategory H Y where
  obj x := eX x.back
  map {x y} f := ⟨eG f.val, by
    change eG f.val • eX x.back = eX y.back
    rw [← heq]
    exact congrArg eX f.property⟩
  map_id x := by
    apply Subtype.ext
    change eG 1 = 1
    simp
  map_comp f g := by
    apply Subtype.ext
    change eG (g.val * f.val) = eG g.val * eG f.val
    simp

/-- The groupoid inverse in an action category inverts its group label. -/
@[simp] theorem actionCategory_groupoidInv_val
    {x y : ActionCategory G X} (f : x ⟶ y) :
    (CategoryTheory.Groupoid.inv f).val = f.val⁻¹ := rfl

/-- The acting-group label of an action-category arrow, exposing the group
element hidden by the category-of-elements presentation. -/
def actionCategoryLabel {x y : ActionCategory G X} (f : x ⟶ y) : G :=
  f.val

/-- Action-category labels determine arrows. -/
theorem actionCategoryLabel_injective {x y : ActionCategory G X} :
    Function.Injective (actionCategoryLabel : (x ⟶ y) → G) := by
  intro f g h
  apply Subtype.ext
  exact h

/-- Action-category composition reverses the order of acting-group labels. -/
@[simp] theorem actionCategoryLabel_comp
    {x y z : ActionCategory G X} (f : x ⟶ y) (g : y ⟶ z) :
    actionCategoryLabel (f ≫ g) =
      actionCategoryLabel g * actionCategoryLabel f := by
  unfold actionCategoryLabel
  exact ActionCategory.comp_val f g

/-- The inverse arrow written directly in the action-category presentation. -/
def actionCategoryArrowInv {x y : ActionCategory G X} (f : x ⟶ y) : y ⟶ x :=
  ⟨(actionCategoryLabel f)⁻¹, by
    rcases x with ⟨⟨⟩, x⟩
    rcases y with ⟨⟨⟩, y⟩
    change X at x y
    change (actionCategoryLabel f)⁻¹ • y = x
    have hf : actionCategoryLabel f • x = y := f.property
    calc
      (actionCategoryLabel f)⁻¹ • y =
          (actionCategoryLabel f)⁻¹ • (actionCategoryLabel f • x) :=
        congrArg (fun z : X ↦ (actionCategoryLabel f)⁻¹ • z) hf.symm
      _ = x := by simp⟩

/-- Direct inversion has the inverse acting-group label. -/
@[simp] theorem actionCategoryLabel_arrowInv
    {x y : ActionCategory G X} (f : x ⟶ y) :
    actionCategoryLabel (actionCategoryArrowInv f) =
      (actionCategoryLabel f)⁻¹ := rfl

/-- The based product on an action-category arrow family. -/
def actionCategoryArrowProduct {x y : ActionCategory G X}
    (e a b : x ⟶ y) : x ⟶ y :=
  a ≫ actionCategoryArrowInv e ≫ b

/-- The acting-group label of the based arrow product. -/
@[simp] theorem actionCategoryLabel_arrowProduct
    {x y : ActionCategory G X} (e a b : x ⟶ y) :
    actionCategoryLabel (actionCategoryArrowProduct e a b) =
      actionCategoryLabel b *
        ((actionCategoryLabel e)⁻¹ * actionCategoryLabel a) := by
  simp [actionCategoryArrowProduct, actionCategoryLabel_comp, mul_assoc]

/-- The based inverse on an action-category arrow family. -/
def actionCategoryArrowInverse {x y : ActionCategory G X}
    (e a : x ⟶ y) : x ⟶ y :=
  e ≫ actionCategoryArrowInv a ≫ e

/-- The acting-group label of the based arrow inverse. -/
@[simp] theorem actionCategoryLabel_arrowInverse
    {x y : ActionCategory G X} (e a : x ⟶ y) :
    actionCategoryLabel (actionCategoryArrowInverse e a) =
      actionCategoryLabel e *
        ((actionCategoryLabel a)⁻¹ * actionCategoryLabel e) := by
  simp [actionCategoryArrowInverse, actionCategoryLabel_comp, mul_assoc]

/-- The rational group chunk carried directly by a based arrow family in
an action category. -/
def actionCategoryArrowChunk {x y : ActionCategory G X} (e : x ⟶ y) :
    RationalGroupChunk (x ⟶ y) where
  mul := actionCategoryArrowProduct e
  inv := actionCategoryArrowInverse e
  mul_assoc a b c := by
    apply actionCategoryLabel_injective
    simp [mul_assoc]
  inv_mul_mul a b := by
    apply actionCategoryLabel_injective
    simp [mul_assoc]
  mul_mul_inv a b := by
    apply actionCategoryLabel_injective
    simp [mul_assoc]

/-- Equivariant equivalences of group actions induce equivalences of their
action categories. -/
noncomputable def actionCategoryEquivalenceOfEquivariantEquiv
    (eG : G ≃* H) (eX : X ≃ Y)
    (heq : ∀ g x, eX (g • x) = eG g • eX x) :
    ActionCategory G X ≌ ActionCategory H Y := by
  let F := actionCategoryFunctorOfEquivariantEquiv eG eX heq
  have hFF : F.FullyFaithful := by
    refine
      { preimage := fun {x y} f ↦ ⟨eG.symm f.val, by
          change eG.symm f.val • x.back = y.back
          apply eX.injective
          calc
            eX (eG.symm f.val • x.back) =
                eG (eG.symm f.val) • eX x.back := heq _ _
            _ = f.val • eX x.back := by simp
            _ = eX y.back := f.property⟩
        map_preimage := fun f ↦ by
          apply Subtype.ext
          change eG (eG.symm f.val) = f.val
          simp
        preimage_map := fun f ↦ by
          apply Subtype.ext
          change eG.symm (eG f.val) = f.val
          simp }
  letI : F.Full := hFF.full
  letI : F.Faithful := hFF.faithful
  letI : F.EssSurj := ⟨fun y ↦ by
    let x : ActionCategory G X := eX.symm y.back
    have hy : F.obj x = y := by
      rw [← ActionCategory.back_coe (x := F.obj x),
        ← ActionCategory.back_coe (x := y)]
      congr 1
      simp [F, x, actionCategoryFunctorOfEquivariantEquiv]
    exact ⟨x, ⟨eqToIso hy⟩⟩⟩
  letI : F.IsEquivalence := { }
  exact F.asEquivalence

end ActionCategoryTransport

section ActionCategoryTranslationChunk

variable {E N X : Type*} [Field E] [Field N] [Algebra E N]
  [MulAction (N ≃ₐ[E] N) X]
  {x y : ActionCategory (N ≃ₐ[E] N) X}

/-- A based arrow family in an action groupoid acts faithfully on the
underlying field.  The inverse on the arrow label corrects the convention
`(f ≫ g).val = g.val * f.val`, so the groupoid difference chart becomes
an honest homomorphic translation chart. -/
def actionCategoryTranslationChunk (e : x ⟶ y) :
    TranslationGroupChunk E N (x ⟶ y) where
  toRationalGroupChunk := actionCategoryArrowChunk e
  translation a :=
    ((actionCategoryLabel e)⁻¹ * actionCategoryLabel a)⁻¹
  translation_mul a b := by
    change (((actionCategoryLabel e)⁻¹ *
      actionCategoryLabel (actionCategoryArrowProduct e a b))⁻¹) = _
    simp [mul_assoc]
  translation_inv a := by
    change (((actionCategoryLabel e)⁻¹ *
      actionCategoryLabel (actionCategoryArrowInverse e a))⁻¹) = _
    simp
  translation_injective := by
    intro a b hab
    apply actionCategoryLabel_injective
    exact mul_left_cancel (inv_injective hab)

/-- The faithful action attached to a based action-groupoid arrow is
literally the inverse of its difference-chart label. -/
@[simp] theorem actionCategoryTranslationChunk_translation
    (e a : x ⟶ y) :
    (actionCategoryTranslationChunk e).translation a =
      ((actionCategoryLabel e)⁻¹ * actionCategoryLabel a)⁻¹ := rfl

end ActionCategoryTranslationChunk

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

/-- Based arrows to a conjugate branch act faithfully by `E`-automorphisms
of the normal-cover field.  This is the normalized finite deck action, not
the positive-dimensional parameter group reconstructed from a quadrangle. -/
def translationChunk [Normal E N] (f : NormalBranchEmbedding E M N) :
    TranslationGroupChunk E N
      (selectedObject (E := E) (M := M) (N := N) ⟶ object f) :=
  actionCategoryTranslationChunk (selectedArrow f)

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

/-- A compatible equivalence of selected finite extensions and their
concrete normal-cover fields transports the corresponding branch types. -/
def finiteCoverBranchEquivOfExtensionEquiv
    {E' L' : IntermediateField k Ω} (h : E ≤ L) (h' : E' ≤ L')
    (e : FiniteCover.ExtensionEquiv h h')
    (n : (↥(FiniteCover.normalClosureOver h)) ≃+*
      (↥(FiniteCover.normalClosureOver h')))
    (hn : n.toRingHom.comp
        (algebraMap (↥E) (↥(FiniteCover.normalClosureOver h))) =
      (algebraMap (↥E') (↥(FiniteCover.normalClosureOver h'))).comp
        e.baseEquiv.toRingEquiv.toRingHom) :
    FiniteCoverBranch h ≃ FiniteCoverBranch h' := by
  let eM : (↥(extendScalars h)) ≃+* (↥(extendScalars h')) :=
    e.totalEquiv.toRingEquiv
  apply NormalBranchEmbedding.equivOfEquiv
    e.baseEquiv.toRingEquiv eM n
  · apply RingHom.ext
    intro x
    exact e.commutes_apply x
  · exact hn

/-- The same compatible normal-cover equivalence transports deck
transformations by conjugation. -/
def finiteCoverDeckEquivOfExtensionEquiv
    {E' L' : IntermediateField k Ω} (h : E ≤ L) (h' : E' ≤ L')
    (e : FiniteCover.ExtensionEquiv h h')
    (n : (↥(FiniteCover.normalClosureOver h)) ≃+*
      (↥(FiniteCover.normalClosureOver h')))
    (hn : n.toRingHom.comp
        (algebraMap (↥E) (↥(FiniteCover.normalClosureOver h))) =
      (algebraMap (↥E') (↥(FiniteCover.normalClosureOver h'))).comp
        e.baseEquiv.toRingEquiv.toRingHom) :
    FiniteCoverDeck h ≃* FiniteCoverDeck h' :=
  NormalBranchEmbedding.deckEquivOfEquiv
    e.baseEquiv.toRingEquiv n hn

/-- Branch transport is equivariant for the corresponding transport of
deck transformations. -/
@[simp] theorem finiteCoverBranchEquivOfExtensionEquiv_smul
    {E' L' : IntermediateField k Ω} (h : E ≤ L) (h' : E' ≤ L')
    (e : FiniteCover.ExtensionEquiv h h')
    (n : (↥(FiniteCover.normalClosureOver h)) ≃+*
      (↥(FiniteCover.normalClosureOver h')))
    (hn : n.toRingHom.comp
        (algebraMap (↥E) (↥(FiniteCover.normalClosureOver h))) =
      (algebraMap (↥E') (↥(FiniteCover.normalClosureOver h'))).comp
        e.baseEquiv.toRingEquiv.toRingHom)
    (σ : FiniteCoverDeck h) (b : FiniteCoverBranch h) :
    finiteCoverBranchEquivOfExtensionEquiv h h' e n hn (σ • b) =
      finiteCoverDeckEquivOfExtensionEquiv h h' e n hn σ •
        finiteCoverBranchEquivOfExtensionEquiv h h' e n hn b := by
  unfold finiteCoverBranchEquivOfExtensionEquiv
    finiteCoverDeckEquivOfExtensionEquiv
    NormalBranchEmbedding.equivOfEquiv
    NormalBranchEmbedding.deckEquivOfEquiv
  ext x
  simp

/-- The genuine action groupoid of all conjugate branches of a concrete
finite cover. -/
abbrev finiteCoverBranchGroupoid (h : E ≤ L) :=
  normalBranchGroupoid (↥E) (↥(extendScalars h))
    (↥(FiniteCover.normalClosureOver h))

/-- The literal selected branch, regarded as an object of the normal-cover
branch action. -/
def finiteCoverSelectedBranch (h : E ≤ L) : FiniteCoverBranch h :=
  ⟨FiniteCover.selectedEmbedding h⟩

/-- The literal selected branch inside the canonical normal-closure model.
Unlike an arbitrary equivalence between normal closures, this embedding is
the algebra map used in the definition of the canonical normal closure. -/
def finiteCoverCanonicalSelectedBranch [IsAlgClosed Ω] (h : E ≤ L)
    (halg : Algebra.IsAlgebraic (↥E) (↥(extendScalars h))) :
    NormalBranchEmbedding (↥E) (↥(extendScalars h))
      (↥(FiniteCover.canonicalNormalClosure h)) :=
  ⟨FiniteCover.canonicalSelectedEmbedding h halg⟩

/-- Place the distinguished canonical branch in any larger canonical
source cover which contains its normal closure. -/
def finiteCoverCanonicalSelectedBranchIn
    [IsAlgClosed Ω] (h : E ≤ L)
    (halg : Algebra.IsAlgebraic (↥E) (↥(extendScalars h)))
    (N : IntermediateField (↥E) (AlgebraicClosure (↥E)))
    (hle : FiniteCover.canonicalNormalClosure h ≤ N) :
    NormalBranchEmbedding (↥E) (↥(extendScalars h)) (↥N) :=
  ⟨(IntermediateField.inclusion hle).comp
    (FiniteCover.canonicalSelectedEmbedding h halg)⟩

/-- Evaluation in the larger cover factors through the distinguished
canonical branch. -/
theorem finiteCoverCanonicalSelectedBranchIn_apply
    [IsAlgClosed Ω] (h : E ≤ L)
    (halg : Algebra.IsAlgebraic (↥E) (↥(extendScalars h)))
    (N : IntermediateField (↥E) (AlgebraicClosure (↥E)))
    (hle : FiniteCover.canonicalNormalClosure h ≤ N)
    (x : extendScalars h) :
    (finiteCoverCanonicalSelectedBranchIn h halg N hle).toAlgHom x =
      IntermediateField.inclusion hle
        (FiniteCover.canonicalSelectedEmbedding h halg x) :=
  rfl

/-- The selected branch as an object of its conjugate-branch groupoid. -/
def finiteCoverSelectedObject (h : E ≤ L) :
    finiteCoverBranchGroupoid h :=
  finiteCoverSelectedBranch h

/-- An equivalence of finite-cover branch actions which additionally
preserves the literal selected branch. -/
structure FiniteCoverBasedBranchEquiv
    {E' L' : IntermediateField k Ω} (h : E ≤ L) (h' : E' ≤ L') where
  /-- The induced equivalence of deck-transformation groups. -/
  deckEquiv : FiniteCoverDeck h ≃* FiniteCoverDeck h'
  /-- The induced equivalence of conjugate branch types. -/
  branchEquiv : FiniteCoverBranch h ≃ FiniteCoverBranch h'
  /-- Deck actions and branch transport commute. -/
  map_smul : ∀ σ b,
    branchEquiv (σ • b) = deckEquiv σ • branchEquiv b
  /-- The literal selected branch is preserved. -/
  map_selected :
    branchEquiv (finiteCoverSelectedBranch h) =
      finiteCoverSelectedBranch h'

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

/-- A semilinear equivalence of concrete normal-cover fields which preserves
the literal selected finite-extension branch.  The base and total
equivalences are retained explicitly so the selected-branch equation can be
evaluated on named coordinates after transport. -/
structure FiniteCoverBasedNormalEquiv
    {E' L' : IntermediateField k Ω} (h : E ≤ L) (h' : E' ≤ L')
    (e : FiniteCover.ExtensionEquiv h h') where
  /-- The selected-branch-preserving equivalence of normal-cover fields. -/
  toRingEquiv :
    (↥(FiniteCover.normalClosureOver h)) ≃+*
      (↥(FiniteCover.normalClosureOver h'))
  /-- The normal-cover equivalence is semilinear over the displayed base
  equivalence. -/
  commutes :
    toRingEquiv.toRingHom.comp
        (algebraMap (↥E) (↥(FiniteCover.normalClosureOver h))) =
      (algebraMap (↥E') (↥(FiniteCover.normalClosureOver h'))).comp
        e.baseEquiv.toRingEquiv.toRingHom
  /-- The corrected normal-cover equivalence carries the literal selected
  branch to the literal selected target branch through the total-field
  equivalence. -/
  map_selected :
    toRingEquiv.toRingHom.comp
        (FiniteCover.selectedEmbedding h).toRingHom =
      (FiniteCover.selectedEmbedding h').toRingHom.comp
        e.totalEquiv.toRingEquiv.toRingHom

namespace FiniteCoverBasedNormalEquiv

variable {E' L' : IntermediateField k Ω} {h : E ≤ L} {h' : E' ≤ L'}
  {e : FiniteCover.ExtensionEquiv h h'}

/-- Pointwise form of the selected-branch preservation equation. -/
@[simp] theorem map_selected_apply (T : FiniteCoverBasedNormalEquiv h h' e)
    (x : extendScalars h) :
    T.toRingEquiv (FiniteCover.selectedEmbedding h x) =
      FiniteCover.selectedEmbedding h' (e.totalEquiv x) :=
  DFunLike.congr_fun T.map_selected x

/-- A based normal-cover equivalence induces the corresponding equivalence
of based conjugate-branch actions, without making any further branch
choice. -/
def toBasedBranchEquiv (T : FiniteCoverBasedNormalEquiv h h' e) :
    FiniteCoverBasedBranchEquiv h h' := by
  let branchEquiv := finiteCoverBranchEquivOfExtensionEquiv
    h h' e T.toRingEquiv T.commutes
  let deckEquiv := finiteCoverDeckEquivOfExtensionEquiv
    h h' e T.toRingEquiv T.commutes
  refine
    { deckEquiv := deckEquiv
      branchEquiv := branchEquiv
      map_smul := fun σ b ↦ ?_
      map_selected := ?_ }
  · exact finiteCoverBranchEquivOfExtensionEquiv_smul
      h h' e T.toRingEquiv T.commutes σ b
  · apply NormalBranchEmbedding.ext
    apply AlgHom.ext
    intro y
    have hy := T.map_selected_apply (e.totalEquiv.symm y)
    change T.toRingEquiv
        (FiniteCover.selectedEmbedding h (e.totalEquiv.symm y)) =
      FiniteCover.selectedEmbedding h' y
    rw [e.totalEquiv.apply_symm_apply] at hy
    exact hy

end FiniteCoverBasedNormalEquiv

/-- A transported normal cover can be based at the literal target branch:
transitivity supplies a target deck transformation correcting the raw
field-theoretic equivalence.  The corrected field equivalence remains
semilinear over the original base equivalence and now carries the entire
literal selected branch through the displayed total-field equivalence. -/
noncomputable def finiteCoverBasedNormalEquivOfExtensionEquiv [IsAlgClosed Ω]
    {E' L' : IntermediateField k Ω} (h : E ≤ L) (h' : E' ≤ L')
    (hfin' : FiniteDimensional (↥E') (↥(extendScalars h')))
    (e : FiniteCover.ExtensionEquiv h h')
    (n : (↥(FiniteCover.normalClosureOver h)) ≃+*
      (↥(FiniteCover.normalClosureOver h')))
    (hn : n.toRingHom.comp
        (algebraMap (↥E) (↥(FiniteCover.normalClosureOver h))) =
      (algebraMap (↥E') (↥(FiniteCover.normalClosureOver h'))).comp
        e.baseEquiv.toRingEquiv.toRingHom) :
    FiniteCoverBasedNormalEquiv h h' e := by
  let rawBranch := finiteCoverBranchEquivOfExtensionEquiv h h' e n hn
  let hex := finiteCoverBranch_exists_smul_eq h' hfin'
    (rawBranch (finiteCoverSelectedBranch h))
    (finiteCoverSelectedBranch h')
  let τ : FiniteCoverDeck h' := Classical.choose hex
  have hτ : τ • rawBranch (finiteCoverSelectedBranch h) =
      finiteCoverSelectedBranch h' := Classical.choose_spec hex
  refine
    { toRingEquiv := n.trans τ.toRingEquiv
      commutes := ?_
      map_selected := ?_ }
  · apply RingHom.ext
    intro x
    have hx := DFunLike.congr_fun hn x
    change n (algebraMap (↥E)
        (↥(FiniteCover.normalClosureOver h)) x) =
      algebraMap (↥E') (↥(FiniteCover.normalClosureOver h'))
        (e.baseEquiv x) at hx
    change τ (n (algebraMap (↥E)
        (↥(FiniteCover.normalClosureOver h)) x)) =
      algebraMap (↥E') (↥(FiniteCover.normalClosureOver h'))
        (e.baseEquiv x)
    rw [hx]
    exact τ.commutes (e.baseEquiv x)
  · apply RingHom.ext
    intro x
    have hx := congrArg (fun f ↦ f.toAlgHom (e.totalEquiv x)) hτ
    change τ (n (FiniteCover.selectedEmbedding h
        (e.totalEquiv.symm (e.totalEquiv x)))) =
      FiniteCover.selectedEmbedding h' (e.totalEquiv x) at hx
    change τ (n (FiniteCover.selectedEmbedding h x)) =
      FiniteCover.selectedEmbedding h' (e.totalEquiv x)
    simpa using hx

/-- Forgetting the corrected field equivalence recovers a selected-branch-
preserving equivalence of the corresponding conjugate-branch actions. -/
noncomputable def finiteCoverBasedBranchEquivOfExtensionEquiv [IsAlgClosed Ω]
    {E' L' : IntermediateField k Ω} (h : E ≤ L) (h' : E' ≤ L')
    (hfin' : FiniteDimensional (↥E') (↥(extendScalars h')))
    (e : FiniteCover.ExtensionEquiv h h')
    (n : (↥(FiniteCover.normalClosureOver h)) ≃+*
      (↥(FiniteCover.normalClosureOver h')))
    (hn : n.toRingHom.comp
        (algebraMap (↥E) (↥(FiniteCover.normalClosureOver h))) =
      (algebraMap (↥E') (↥(FiniteCover.normalClosureOver h'))).comp
        e.baseEquiv.toRingEquiv.toRingHom) :
    FiniteCoverBasedBranchEquiv h h' :=
  (finiteCoverBasedNormalEquivOfExtensionEquiv
    h h' hfin' e n hn).toBasedBranchEquiv

namespace FiniteCoverBasedBranchEquiv

variable {E' L' : IntermediateField k Ω} {h : E ≤ L} {h' : E' ≤ L'}

/-- Identity transport of a based finite-cover branch action. -/
def refl (h : E ≤ L) : FiniteCoverBasedBranchEquiv h h where
  deckEquiv := MulEquiv.refl _
  branchEquiv := Equiv.refl _
  map_smul _ _ := rfl
  map_selected := rfl

/-- Reverse a based transport of finite-cover branch actions. -/
def symm (T : FiniteCoverBasedBranchEquiv h h') :
    FiniteCoverBasedBranchEquiv h' h where
  deckEquiv := T.deckEquiv.symm
  branchEquiv := T.branchEquiv.symm
  map_smul σ b := by
    apply T.branchEquiv.injective
    calc
      T.branchEquiv (T.branchEquiv.symm (σ • b)) = σ • b := by simp
      _ = T.deckEquiv (T.deckEquiv.symm σ) •
          T.branchEquiv (T.branchEquiv.symm b) := by simp
      _ = T.branchEquiv
          (T.deckEquiv.symm σ • T.branchEquiv.symm b) :=
        (T.map_smul _ _).symm
  map_selected := by
    apply T.branchEquiv.injective
    simp [T.map_selected]

/-- Compose two based transports of finite-cover branch actions. -/
def trans {E'' L'' : IntermediateField k Ω} {h'' : E'' ≤ L''}
    (T : FiniteCoverBasedBranchEquiv h h')
    (U : FiniteCoverBasedBranchEquiv h' h'') :
    FiniteCoverBasedBranchEquiv h h'' where
  deckEquiv := T.deckEquiv.trans U.deckEquiv
  branchEquiv := T.branchEquiv.trans U.branchEquiv
  map_smul σ b := by
    change U.branchEquiv (T.branchEquiv (σ • b)) =
      U.deckEquiv (T.deckEquiv σ) •
        U.branchEquiv (T.branchEquiv b)
    rw [T.map_smul, U.map_smul]
  map_selected := by
    change U.branchEquiv (T.branchEquiv (finiteCoverSelectedBranch h)) =
      finiteCoverSelectedBranch h''
    rw [T.map_selected, U.map_selected]

/-- Based branch transports are determined by their deck and branch
equivalences; the compatibility witnesses are propositions. -/
@[ext] theorem ext {T U : FiniteCoverBasedBranchEquiv h h'}
    (hdeck : T.deckEquiv = U.deckEquiv)
    (hbranch : T.branchEquiv = U.branchEquiv) : T = U := by
  cases T
  cases U
  cases hdeck
  cases hbranch
  rfl

/-- Passing from a common source to one fiber and back gives identity
transport. -/
theorem symm_trans_self (T : FiniteCoverBasedBranchEquiv h h') :
    T.symm.trans T = refl h' := by
  apply ext
  · apply MulEquiv.ext
    intro σ
    simp [symm, trans, refl]
  · apply Equiv.ext
    intro b
    simp [symm, trans, refl]

/-- Reversing a transition defined through a common source swaps its two
target fibers. -/
theorem symm_trans_symm
    {E'' L'' : IntermediateField k Ω} {h'' : E'' ≤ L''}
    (T : FiniteCoverBasedBranchEquiv h h')
    (U : FiniteCoverBasedBranchEquiv h h'') :
    (T.symm.trans U).symm = U.symm.trans T := by
  apply ext
  · apply MulEquiv.ext
    intro σ
    simp [symm, trans]
  · apply Equiv.ext
    intro b
    simp [symm, trans]

/-- Transitions formed through one common source satisfy the cocycle
identity. -/
theorem symm_trans_trans_symm_trans
    {E'' L'' E''' L''' : IntermediateField k Ω}
    {h'' : E'' ≤ L''} {h''' : E''' ≤ L'''}
    (T : FiniteCoverBasedBranchEquiv h h')
    (U : FiniteCoverBasedBranchEquiv h h'')
    (V : FiniteCoverBasedBranchEquiv h h''') :
    (T.symm.trans U).trans (U.symm.trans V) = T.symm.trans V := by
  apply ext
  · apply MulEquiv.ext
    intro σ
    simp [symm, trans]
  · apply Equiv.ext
    intro b
    simp [symm, trans]

/-- A based equivalence of finite-cover branch actions induces an
equivalence of the corresponding genuine action groupoids. -/
noncomputable def groupoidEquivalence (T : FiniteCoverBasedBranchEquiv h h') :
    finiteCoverBranchGroupoid h ≌ finiteCoverBranchGroupoid h' :=
  actionCategoryEquivalenceOfEquivariantEquiv
    T.deckEquiv T.branchEquiv T.map_smul

/-- The forward groupoid equivalence acts on objects by the based branch
equivalence. -/
@[simp] theorem groupoidEquivalence_obj_back
    (T : FiniteCoverBasedBranchEquiv h h')
    (b : finiteCoverBranchGroupoid h) :
    (T.groupoidEquivalence.functor.obj b).back = T.branchEquiv b.back := by
  rfl

/-- The induced groupoid equivalence preserves the distinguished object. -/
theorem groupoidEquivalence_obj_selected
    (T : FiniteCoverBasedBranchEquiv h h') :
    T.groupoidEquivalence.functor.obj (finiteCoverSelectedObject h) =
      finiteCoverSelectedObject h' := by
  rw [← ActionCategory.back_coe
      (x := T.groupoidEquivalence.functor.obj
        (finiteCoverSelectedObject h)),
    ← ActionCategory.back_coe (x := finiteCoverSelectedObject h')]
  congr 1
  exact T.map_selected

/-- On each based arrow family, a based branch transport is the explicit
equivalence obtained by transporting the deck label.  The target family is
based at the literal target branch because `map_selected` removes the
otherwise necessary object cast. -/
def arrowEquiv (T : FiniteCoverBasedBranchEquiv h h')
    (b : finiteCoverBranchGroupoid h) :
    (finiteCoverSelectedObject h ⟶ b) ≃
      (finiteCoverSelectedObject h' ⟶
        (T.branchEquiv b.back : finiteCoverBranchGroupoid h')) where
  toFun a := ⟨T.deckEquiv a.val, by
    change T.deckEquiv a.val • finiteCoverSelectedBranch h' =
      T.branchEquiv b.back
    rw [← T.map_selected, ← T.map_smul]
    exact congrArg T.branchEquiv a.property⟩
  invFun a := by
    let σ : FiniteCoverDeck h' := a.val
    have ha := a.property
    change σ • finiteCoverSelectedBranch h' = T.branchEquiv b.back at ha
    refine ⟨T.deckEquiv.symm σ, ?_⟩
    change T.deckEquiv.symm σ • finiteCoverSelectedBranch h = b.back
    apply T.branchEquiv.injective
    calc
      T.branchEquiv
          (T.deckEquiv.symm σ • finiteCoverSelectedBranch h) =
          T.deckEquiv (T.deckEquiv.symm σ) •
            T.branchEquiv (finiteCoverSelectedBranch h) := T.map_smul _ _
      _ = σ • finiteCoverSelectedBranch h' := by simp [T.map_selected]
      _ = T.branchEquiv b.back := ha
  left_inv a := by
    apply Subtype.ext
    simp
  right_inv a := by
    apply Subtype.ext
    simp

/-- The based-arrow equivalence sends an arrow's deck label through the
deck-transformation equivalence. -/
@[simp] theorem arrowEquiv_val (T : FiniteCoverBasedBranchEquiv h h')
    (b : finiteCoverBranchGroupoid h)
    (a : finiteCoverSelectedObject h ⟶ b) :
    (T.arrowEquiv b a).val = T.deckEquiv a.val := rfl

/-- Based-arrow transport intertwines the difference-product operation. -/
theorem arrowEquiv_differenceProduct
    (T : FiniteCoverBasedBranchEquiv h h')
    (b : finiteCoverBranchGroupoid h)
    (e a c : finiteCoverSelectedObject h ⟶ b) :
    T.arrowEquiv b (groupoidDifferenceProduct e a c) =
      groupoidDifferenceProduct
        (T.arrowEquiv b e) (T.arrowEquiv b a) (T.arrowEquiv b c) := by
  let ε : FiniteCoverDeck h := e.val
  let α : FiniteCoverDeck h := a.val
  let γ : FiniteCoverDeck h := c.val
  have hsrc : (a ≫ CategoryTheory.Groupoid.inv e ≫ c).val =
      γ * ε⁻¹ * α := rfl
  have htgt : (T.arrowEquiv b a ≫
      CategoryTheory.Groupoid.inv (T.arrowEquiv b e) ≫
        T.arrowEquiv b c).val =
      T.deckEquiv γ * (T.deckEquiv ε)⁻¹ * T.deckEquiv α := rfl
  apply Subtype.ext
  rw [arrowEquiv_val]
  unfold groupoidDifferenceProduct
  rw [← CategoryTheory.Groupoid.inv_eq_inv e,
    ← CategoryTheory.Groupoid.inv_eq_inv (T.arrowEquiv b e)]
  calc
    T.deckEquiv (a ≫ CategoryTheory.Groupoid.inv e ≫ c).val =
        T.deckEquiv (γ * ε⁻¹ * α) := congrArg T.deckEquiv hsrc
    _ = T.deckEquiv γ * (T.deckEquiv ε)⁻¹ * T.deckEquiv α := by simp
    _ = (T.arrowEquiv b a ≫
        CategoryTheory.Groupoid.inv (T.arrowEquiv b e) ≫
          T.arrowEquiv b c).val := htgt.symm

/-- Based-arrow transport intertwines the difference-inverse operation. -/
theorem arrowEquiv_differenceInverse
    (T : FiniteCoverBasedBranchEquiv h h')
    (b : finiteCoverBranchGroupoid h)
    (e a : finiteCoverSelectedObject h ⟶ b) :
    T.arrowEquiv b (groupoidDifferenceInverse e a) =
      groupoidDifferenceInverse (T.arrowEquiv b e) (T.arrowEquiv b a) := by
  let ε : FiniteCoverDeck h := e.val
  let α : FiniteCoverDeck h := a.val
  have hsrc : (e ≫ CategoryTheory.Groupoid.inv a ≫ e).val =
      ε * α⁻¹ * ε := rfl
  have htgt : (T.arrowEquiv b e ≫
      CategoryTheory.Groupoid.inv (T.arrowEquiv b a) ≫
        T.arrowEquiv b e).val =
      T.deckEquiv ε * (T.deckEquiv α)⁻¹ * T.deckEquiv ε := rfl
  apply Subtype.ext
  rw [arrowEquiv_val]
  unfold groupoidDifferenceInverse
  rw [← CategoryTheory.Groupoid.inv_eq_inv a,
    ← CategoryTheory.Groupoid.inv_eq_inv (T.arrowEquiv b a)]
  calc
    T.deckEquiv (e ≫ CategoryTheory.Groupoid.inv a ≫ e).val =
        T.deckEquiv (ε * α⁻¹ * ε) := congrArg T.deckEquiv hsrc
    _ = T.deckEquiv ε * (T.deckEquiv α)⁻¹ * T.deckEquiv ε := by simp
    _ = (T.arrowEquiv b e ≫
        CategoryTheory.Groupoid.inv (T.arrowEquiv b a) ≫
          T.arrowEquiv b e).val := htgt.symm

end FiniteCoverBasedBranchEquiv

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

/-- Based arrows of a concrete finite cover act faithfully on its normal
closure by automorphisms over the endpoint field.  The resulting finite
deck action is the normalized branch interface; it is not identified with
the positive-dimensional group parameter. -/
def finiteCoverTranslationChunk [IsAlgClosed Ω]
    (h : E ≤ L) (hfin : FiniteDimensional (↥E) (↥(extendScalars h)))
    (b : finiteCoverBranchGroupoid h) :
    TranslationGroupChunk (↥E) (↥(FiniteCover.normalClosureOver h))
      (finiteCoverSelectedObject h ⟶ b) :=
  actionCategoryTranslationChunk (finiteCoverSelectedArrow h hfin b)

end FiniteCoverBranches

end

end AclGeom
