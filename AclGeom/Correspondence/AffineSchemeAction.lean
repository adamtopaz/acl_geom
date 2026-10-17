/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.AffineGroupScheme
import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# The affine group acting on the line

The algebraic affine group acts on the line by `x ↦ a x + b`; this is the standard affine action
of blueprint equation (8.4a). On coordinate rings it is the coaction `X ↦ a ⊗ X + b ⊗ 1`
(`coaction`). The action morphism `smul` is the spectrum of the coaction, and `modObj` proves
its unit and associativity laws as identities of morphisms of schemes over `Spec k`.

Points with values in a commutative `k`-algebra `C` are used throughout. A point of the group
is a pair `(a, b)` with `a` a unit of `C` (`groupPoint`), a point of the line is an element `x`
of `C` (`linePoint`), and the action sends them to `a x + b`
(`lift_groupPoint_linePoint_smul`). Both laws are checked on such points. The action is
faithful on them for every `C`, not only for `C = k` (`eq_one_of_lift_smul_eq`).

The classification of an arbitrary action on a curve (`lem:affine-action`) remains open.

**Status:** the standard affine scheme action, its point formula and faithfulness are proved.
Arbitrary-action classification remains open.
-/

namespace AclGeom.AffineSchemeAction

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct

universe u v

variable (k : Type u) [Field k]

/-- The coordinate of the line. -/
def lineCoordinate : AdditiveGroupScheme.CoordinateRing k 1 :=
  SymmetricAlgebra.ι k (Fin 1 → k) (Pi.basisFun k (Fin 1) 0)

/-- The coaction `X ↦ a ⊗ X + b ⊗ 1` of the affine coordinate algebra on the line. Named consumer:
the action morphism `smul`. -/
def coaction : AdditiveGroupScheme.CoordinateRing k 1 →ₐ[k]
    AffineGroupScheme.CoordinateRing k ⊗[k] AdditiveGroupScheme.CoordinateRing k 1 :=
  (AdditiveGroupScheme.algebraCoordinates k 1 _).symm fun _ ↦
    (AffineGroupScheme.dilationUnit k : AffineGroupScheme.CoordinateRing k) ⊗ₜ lineCoordinate k +
      AffineGroupScheme.translation k ⊗ₜ 1

theorem coaction_lineCoordinate :
    coaction k (lineCoordinate k) =
      (AffineGroupScheme.dilationUnit k : AffineGroupScheme.CoordinateRing k) ⊗ₜ lineCoordinate k +
        AffineGroupScheme.translation k ⊗ₜ 1 :=
  AdditiveGroupScheme.algebraCoordinates_symm_apply_ι _ 0

variable {k}

/-- The point `x` of the line with values in `C`, as an algebra map. -/
def lineEval {C : Type v} [CommRing C] [Algebra k C] (x : C) :
    AdditiveGroupScheme.CoordinateRing k 1 →ₐ[k] C :=
  (AdditiveGroupScheme.algebraCoordinates k 1 C).symm fun _ ↦ x

theorem lineEval_lineCoordinate {C : Type v} [CommRing C] [Algebra k C] (x : C) :
    lineEval x (lineCoordinate k) = x :=
  AdditiveGroupScheme.algebraCoordinates_symm_apply_ι _ 0

/-- An algebra map out of the coordinate ring of the line is determined by the coordinate. -/
theorem lineHom_ext {C : Type v} [CommRing C] [Algebra k C]
    {f g : AdditiveGroupScheme.CoordinateRing k 1 →ₐ[k] C}
    (h : f (lineCoordinate k) = g (lineCoordinate k)) : f = g := by
  apply (AdditiveGroupScheme.algebraCoordinates k 1 C).injective
  funext i
  rw [AdditiveGroupScheme.algebraCoordinates_apply, AdditiveGroupScheme.algebraCoordinates_apply,
    Subsingleton.elim i 0]
  exact h

/-- **The coaction at points**: at a point `(a, b)` of the affine group and a point `x` of the
line, with values in any commutative `k`-algebra, the coaction gives `a x + b`. -/
theorem coactionEval {C : Type v} [CommRing C] [Algebra k C] (a : Cˣ) (b x : C) :
    (Algebra.TensorProduct.lift (AffineGroupScheme.eval k a b) (lineEval x)
        (fun _ _ ↦ Commute.all _ _)).comp (coaction k) = lineEval (a * x + b) := by
  apply lineHom_ext
  rw [AlgHom.comp_apply, coaction_lineCoordinate, lineEval_lineCoordinate, map_add,
    Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
    AffineGroupScheme.eval_dilation, AffineGroupScheme.eval_translation, lineEval_lineCoordinate,
    map_one, _root_.mul_one]

variable (k)

/-- The product of two affine spectra over `Spec k` is the spectrum of their tensor product.
Named consumers: the action morphism `smul` and its associativity law. -/
def tensorSpecIso (S T : Type u) [CommRing S] [CommRing T] [Algebra k S] [Algebra k T] :
    (Spec (.of S)).asOver (Spec (.of k)) ⊗ (Spec (.of T)).asOver (Spec (.of k)) ≅
      (Spec (.of (S ⊗[k] T))).asOver (Spec (.of k)) :=
  Over.isoMk (pullbackSpecIso k S T) (pullbackSpecIso_hom_base k S T)

/-- A pair of points of two affine spectra corresponds to the tensor product of their
coordinate maps. -/
theorem lift_tensorSpecIso_hom {S T C : Type u} [CommRing S] [CommRing T] [CommRing C]
    [Algebra k S] [Algebra k T] [Algebra k C] (f : S →ₐ[k] C) (g : T →ₐ[k] C) :
    lift ((Spec.map (CommRingCat.ofHom f.toRingHom)).asOver (Spec (.of k)))
        ((Spec.map (CommRingCat.ofHom g.toRingHom)).asOver (Spec (.of k))) ≫
        (tensorSpecIso k S T).hom =
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.lift f g fun _ _ ↦ Commute.all _ _).toRingHom)).asOver
          (Spec (.of k)) := by
  apply Over.OverMorphism.ext
  have w : Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k S)) =
        Spec.map (CommRingCat.ofHom g.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k T)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp
  change Limits.pullback.lift (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) w ≫ (pullbackSpecIso k S T).hom =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lift f g fun _ _ ↦ Commute.all _ _).toRingHom)
  rw [← Iso.eq_comp_inv]
  apply Limits.pullback.hom_ext
  · rw [Limits.pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    ext s
    simp
  · rw [Limits.pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    ext t
    simp

/-- The action morphism of the affine group on the line, over `Spec k`: the spectrum of the
coaction. Named consumer: the action `modObj` of blueprint equation (8.4a). -/
def smul : (AffineGroupScheme.algebraicGroup k).toGroupScheme.X ⊗
      (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ⟶
    (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X :=
  (tensorSpecIso k (AffineGroupScheme.CoordinateRing k)
      (AdditiveGroupScheme.CoordinateRing k 1)).hom ≫
    (Spec.map (CommRingCat.ofHom (coaction k).toRingHom)).asOver (Spec (.of k))

/-- The point `(a, b)` of the affine group with values in a commutative `k`-algebra `C`: the
spectrum of evaluation at `(a, b)`. -/
def groupPoint {C : Type u} [CommRing C] [Algebra k C] (a : Cˣ) (b : C) :
    (Spec (.of C)).asOver (Spec (.of k)) ⟶ (AffineGroupScheme.algebraicGroup k).toGroupScheme.X :=
  Spec.mapMulEquiv (R := k) (S := AffineGroupScheme.CoordinateRing k) (T := C)
    (WithConv.toConv (AffineGroupScheme.eval k a b))

/-- The point `x` of the line with values in a commutative `k`-algebra `C`: the spectrum of
evaluation at `x`. -/
def linePoint {C : Type u} [CommRing C] [Algebra k C] (x : C) :
    (Spec (.of C)).asOver (Spec (.of k)) ⟶
      (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X :=
  Spec.mapMulEquiv (R := k) (S := AdditiveGroupScheme.CoordinateRing k 1) (T := C)
    (WithConv.toConv (lineEval x))

/-- Every point of the affine group with values in `C` has coordinates `(a, b)`. -/
theorem exists_groupPoint {C : Type u} [CommRing C] [Algebra k C]
    (g : (Spec (.of C)).asOver (Spec (.of k)) ⟶
      (AffineGroupScheme.algebraicGroup k).toGroupScheme.X) :
    ∃ (a : Cˣ) (b : C), groupPoint k a b = g := by
  obtain ⟨φ, rfl⟩ := (Spec.mapMulEquiv (R := k) (S := AffineGroupScheme.CoordinateRing k)
    (T := C)).surjective g
  refine ⟨(AffineGroupScheme.homCoordinates k C φ.ofConv).1,
    (AffineGroupScheme.homCoordinates k C φ.ofConv).2, ?_⟩
  exact congrArg (fun f ↦ Spec.mapMulEquiv (WithConv.toConv f))
    ((AffineGroupScheme.homCoordinates k C).symm_apply_apply φ.ofConv)

/-- Every point of the line with values in `C` is an element of `C`. -/
theorem exists_linePoint {C : Type u} [CommRing C] [Algebra k C]
    (y : (Spec (.of C)).asOver (Spec (.of k)) ⟶
      (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X) :
    ∃ x : C, linePoint k x = y := by
  obtain ⟨φ, rfl⟩ := (Spec.mapMulEquiv (R := k) (S := AdditiveGroupScheme.CoordinateRing k 1)
    (T := C)).surjective y
  exact ⟨φ.ofConv (lineCoordinate k), congrArg (fun f ↦ Spec.mapMulEquiv (WithConv.toConv f))
    (lineHom_ext (lineEval_lineCoordinate _))⟩

theorem linePoint_injective {C : Type u} [CommRing C] [Algebra k C] :
    Function.Injective (linePoint k : C → _) := by
  intro x y hxy
  have h := (Spec.mapMulEquiv (R := k) (S := AdditiveGroupScheme.CoordinateRing k 1)
    (T := C)).injective hxy
  calc x = lineEval x (lineCoordinate k) := (lineEval_lineCoordinate x).symm
    _ = lineEval y (lineCoordinate k) :=
      congrArg (fun f : WithConv (AdditiveGroupScheme.CoordinateRing k 1 →ₐ[k] C) ↦
        f.ofConv (lineCoordinate k)) h
    _ = y := lineEval_lineCoordinate y

/-- Points of the affine group multiply as affine transformations: `(a,b)(c,d) = (ac, ad+b)`. -/
theorem groupPoint_mul {C : Type u} [CommRing C] [Algebra k C] (a c : Cˣ) (b d : C) :
    groupPoint k a b * groupPoint k c d = groupPoint k (a * c) (a * d + b) := by
  have h : WithConv.toConv (AffineGroupScheme.eval k a b) *
      WithConv.toConv (AffineGroupScheme.eval k c d) =
        WithConv.toConv (AffineGroupScheme.eval k (a * c) (a * d + b)) := by
    apply WithConv.ofConv_injective
    apply AffineGroupScheme.hom_ext
    · rw [AlgHom.convMul_apply, AffineGroupScheme.coalgebra_comul,
        AffineGroupScheme.comul_dilation]
      simp
    · rw [AlgHom.convMul_apply, AffineGroupScheme.coalgebra_comul,
        AffineGroupScheme.comul_translation]
      simp
  have h' := congrArg (Spec.mapMulEquiv (R := k) (S := AffineGroupScheme.CoordinateRing k)
    (T := C)) h
  rw [map_mul] at h'
  exact h'

/-- The identity of the affine group has coordinates `(1, 0)`. -/
theorem groupPoint_one {C : Type u} [CommRing C] [Algebra k C] :
    groupPoint k (1 : Cˣ) 0 = 1 := by
  have h : WithConv.toConv (AffineGroupScheme.eval k (1 : Cˣ) 0) = 1 := by
    apply WithConv.ofConv_injective
    apply AffineGroupScheme.hom_ext <;> simp
  exact (congrArg (Spec.mapMulEquiv (R := k) (S := AffineGroupScheme.CoordinateRing k)
    (T := C)) h).trans (map_one _)

/-- **The action at points**: with values in any commutative `k`-algebra, the point `(a, b)` of
the affine group sends the point `x` of the line to `a x + b`. -/
theorem lift_groupPoint_linePoint_smul {C : Type u} [CommRing C] [Algebra k C] (a : Cˣ)
    (b x : C) : lift (groupPoint k a b) (linePoint k x) ≫ smul k = linePoint k (a * x + b) := by
  change lift ((Spec.map (CommRingCat.ofHom (AffineGroupScheme.eval k a b).toRingHom)).asOver
      (Spec (.of k))) ((Spec.map (CommRingCat.ofHom (lineEval x).toRingHom)).asOver
        (Spec (.of k))) ≫ (tensorSpecIso k _ _).hom ≫
      (Spec.map (CommRingCat.ofHom (coaction k).toRingHom)).asOver (Spec (.of k)) =
    (Spec.map (CommRingCat.ofHom (lineEval (a * x + b)).toRingHom)).asOver (Spec (.of k))
  rw [← Category.assoc, lift_tensorSpecIso_hom, ← coactionEval a b x]
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The affine group acts on the line by `x ↦ a x + b`: blueprint equation (8.4a). -/
instance modObj : ModObj (AffineGroupScheme.algebraicGroup k).toGroupScheme.X
    (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X where
  smul := smul k
  one_smul := by
    have key : ∀ {C : Type u} [CommRing C] [Algebra k C]
        (p : (Spec (.of C)).asOver (Spec (.of k)) ⟶
          𝟙_ (Over (Spec (.of k))) ⊗ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X),
        p ≫ η[(AffineGroupScheme.algebraicGroup k).toGroupScheme.X] ▷
            (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ≫ smul k =
          p ≫ (λ_ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X).hom := by
      intro C _ _ p
      obtain ⟨x, hx⟩ := exists_linePoint k (p ≫ snd _ _)
      have hp : lift (toUnit _) (linePoint k x) = p := by
        rw [hx]
        exact CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (lift_snd _ _)
      rw [← hp, lift_whiskerRight_assoc, ← Hom.one_def, ← groupPoint_one k,
        lift_groupPoint_linePoint_smul, CartesianMonoidalCategory.leftUnitor_hom, lift_snd,
        Units.val_one, _root_.one_mul, add_zero]
    exact (cancel_epi (λ_ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X).inv).1
      (key (C := AdditiveGroupScheme.CoordinateRing k 1)
        (λ_ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X).inv)
  mul_smul := by
    have key : ∀ {C : Type u} [CommRing C] [Algebra k C]
        (p : (Spec (.of C)).asOver (Spec (.of k)) ⟶
          ((AffineGroupScheme.algebraicGroup k).toGroupScheme.X ⊗
            (AffineGroupScheme.algebraicGroup k).toGroupScheme.X) ⊗
              (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X),
        p ≫ μ[(AffineGroupScheme.algebraicGroup k).toGroupScheme.X] ▷
            (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ≫ smul k =
          p ≫ (α_ _ _ _).hom ≫ (AffineGroupScheme.algebraicGroup k).toGroupScheme.X ◁ smul k ≫
            smul k := by
      intro C _ _ p
      obtain ⟨a, b, ha⟩ := exists_groupPoint k (p ≫ fst _ _ ≫ fst _ _)
      obtain ⟨c, d, hc⟩ := exists_groupPoint k (p ≫ fst _ _ ≫ snd _ _)
      obtain ⟨x, hx⟩ := exists_linePoint k (p ≫ snd _ _)
      have hp : lift (lift (groupPoint k a b) (groupPoint k c d)) (linePoint k x) = p := by
        rw [ha, hc, hx]
        exact CartesianMonoidalCategory.hom_ext _ _
          (CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp)) (by simp)
      rw [← hp, lift_whiskerRight_assoc, ← Hom.mul_def, groupPoint_mul,
        lift_groupPoint_linePoint_smul, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc,
        lift_groupPoint_linePoint_smul, lift_groupPoint_linePoint_smul, Units.val_mul]
      congr 1
      ring
    let e := (tensorSpecIso k (AffineGroupScheme.CoordinateRing k ⊗[k]
        AffineGroupScheme.CoordinateRing k) (AdditiveGroupScheme.CoordinateRing k 1)).symm ≪≫
      whiskerRightIso (tensorSpecIso k (AffineGroupScheme.CoordinateRing k)
        (AffineGroupScheme.CoordinateRing k)).symm _
    exact (cancel_epi e.hom).1 (key e.hom)

/-- **Faithfulness**: a point of the affine group, with values in any commutative `k`-algebra,
that fixes every point of the line is the identity. -/
theorem eq_one_of_lift_smul_eq {C : Type u} [CommRing C] [Algebra k C]
    (g : (Spec (.of C)).asOver (Spec (.of k)) ⟶
      (AffineGroupScheme.algebraicGroup k).toGroupScheme.X)
    (h : ∀ x : (Spec (.of C)).asOver (Spec (.of k)) ⟶
      (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X, lift g x ≫ smul k = x) :
    g = 1 := by
  obtain ⟨a, b, rfl⟩ := exists_groupPoint k g
  have h0 := h (linePoint k 0)
  have h1 := h (linePoint k 1)
  rw [lift_groupPoint_linePoint_smul] at h0 h1
  have hb : b = 0 := by
    have := linePoint_injective k h0
    rwa [mul_zero, zero_add] at this
  have ha : a = 1 := by
    have := linePoint_injective k h1
    rw [_root_.mul_one, hb, add_zero] at this
    exact Units.ext this
  subst ha hb
  exact groupPoint_one k

end

end AclGeom.AffineSchemeAction
