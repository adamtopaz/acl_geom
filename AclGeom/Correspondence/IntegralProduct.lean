/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.RegularACF
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Products of integral schemes over an algebraically closed field

The named consumers are the source-generic and subgroup-scheme bridges for blueprint
`lem:curve-coset`. The product of the two generic residue fields has domain coordinate ring
by `isDomain_tensorProduct_of_isAlgClosed`. Its morphism into the product of the original
schemes is scheme-theoretically dominant by two flat base changes. This gives both reducedness
and irreducibility of the actual scheme product.

**Status:** proved. The general source consumer is `curveCoset_of_genericProduct`.
-/

namespace AclGeom

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace TensorProduct

universe u

/-- Products of integral schemes over an algebraically closed field are integral.
Named consumers: the actual source-generic product and reduced subgroup operations in
blueprint `lem:curve-coset`. -/
theorem isIntegral_pullback_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) : IsIntegral (pullback f g) := by
  let E := X.residueField (genericPoint X)
  let F := Y.residueField (genericPoint Y)
  let a : Spec E ⟶ X := X.fromSpecResidueField (genericPoint X)
  let b : Spec F ⟶ Y := Y.fromSpecResidueField (genericPoint Y)
  have : IsDominant a := ⟨by
    rw [denseRange_iff_closure_range]
    change closure (Set.range (X.fromSpecResidueField (genericPoint X))) = Set.univ
    rw [Scheme.range_fromSpecResidueField]
    exact genericPoint_closure X⟩
  have : IsDominant b := ⟨by
    rw [denseRange_iff_closure_range]
    change closure (Set.range (Y.fromSpecResidueField (genericPoint Y))) = Set.univ
    rw [Scheme.range_fromSpecResidueField]
    exact genericPoint_closure Y⟩
  have : IsSchemeTheoreticallyDominant a := .of_isDominant a
  have : IsSchemeTheoreticallyDominant b := .of_isDominant b
  have : QuasiCompact a := inferInstance
  have : QuasiCompact b := inferInstance
  let : Algebra k E := (Spec.preimage (a ≫ f)).hom.toAlgebra
  let : Algebra k F := (Spec.preimage (b ≫ g)).hom.toAlgebra
  have ea : Spec.map (CommRingCat.ofHom (algebraMap k E)) = a ≫ f :=
    Spec.map_preimage (a ≫ f)
  have eb : Spec.map (CommRingCat.ofHom (algebraMap k F)) = b ≫ g :=
    Spec.map_preimage (b ≫ g)
  let Q : Scheme := pullback (a ≫ f) (b ≫ g)
  let M : Scheme := pullback f (b ≫ g)
  let P : Scheme := pullback f g
  have : IsIntegral Q := by
    have : IsDomain (E ⊗[k] F) := isDomain_tensorProduct_of_isAlgClosed
    let e : Q ≅ Spec (.of (E ⊗[k] F)) :=
      pullback.congrHom ea.symm eb.symm ≪≫ pullbackSpecIso k E F
    exact IsIntegral.of_isIso e.inv
  have m : IsPullback (pullback.fst f (b ≫ g)) (pullback.snd f (b ≫ g)) f (b ≫ g) :=
    .of_hasPullback _ _
  let q : Q ⟶ M := m.lift (pullback.fst (a ≫ f) (b ≫ g) ≫ a)
    (pullback.snd (a ≫ f) (b ≫ g)) (by rw [Category.assoc]; exact pullback.condition)
  have hq : IsPullback (pullback.fst (a ≫ f) (b ≫ g)) q a
      (pullback.fst f (b ≫ g)) :=
    IsPullback.of_bot' (IsPullback.of_hasPullback (a ≫ f) (b ≫ g)) m
  have : Flat (pullback.fst f (b ≫ g)) := inferInstance
  have : QuasiCompact q := MorphismProperty.of_isPullback hq (inferInstance : QuasiCompact a)
  have : IsSchemeTheoreticallyDominant q := .of_isPullback hq
  have p : IsPullback (pullback.snd f g) (pullback.fst f g) g f :=
    (IsPullback.of_hasPullback f g).flip
  let r : M ⟶ P := p.lift (pullback.snd f (b ≫ g) ≫ b) (pullback.fst f (b ≫ g))
    (by rw [Category.assoc]; exact pullback.condition.symm)
  have hr : IsPullback (pullback.snd f (b ≫ g)) r b (pullback.snd f g) :=
    IsPullback.of_bot' (IsPullback.of_hasPullback f (b ≫ g)).flip p
  have : Flat (pullback.snd f g) := inferInstance
  have : QuasiCompact r := MorphismProperty.of_isPullback hr (inferInstance : QuasiCompact b)
  have : IsSchemeTheoreticallyDominant r := .of_isPullback hr
  have : IsReduced P := IsSchemeTheoreticallyDominant.isReduced (q ≫ r)
  have : IrreducibleSpace P := by
    apply (irreducibleSpace_def P).2
    change IsIrreducible (Set.univ : Set P)
    rw [← (q ≫ r).denseRange.closure_eq, ← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ Q).image (q ≫ r)
      (q ≫ r).continuous.continuousOn).closure
  exact isIntegral_of_irreducibleSpace_of_isReduced P

/-- An integral scheme over an algebraically closed field is geometrically integral.
Named consumer: the geometrically integral closed subgroup in blueprint `lem:curve-coset`. -/
theorem geometricallyIntegral_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k)) : GeometricallyIntegral f := by
  constructor
  intro K _ y Z fst snd h
  have : IsIntegral (pullback f y) := isIntegral_pullback_of_isAlgClosed f y
  exact IsIntegral.of_isIso h.isoPullback.inv

end

end AclGeom
