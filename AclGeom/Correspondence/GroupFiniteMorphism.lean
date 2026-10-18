/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.ActionOrbitTransitivity
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Global finiteness from an actual group parameter square

**Status:** proved criterion over an ACF base (#21). A group morphism to a connected
algebraic-group package, injective on base-field points and agreeing with a finite
surjective map on nonempty opens, is globally finite and surjective. The source algebraic
group need not be connected. Connectedness of the target gives the nonempty intersection
of translated parameter opens. Point injectivity identifies the FULL inverse image of the
target open, so the given map is the actual target pullback. Translated target opens cover;
finiteness and surjectivity are local at the target. No source-local finiteness argument,
separability, degree-one conclusion or scheme monomorphism is asserted.

Named consumer: `SchemeAffineFinite.exists_finite_surjective_morphism` supplies the whole
parameter square internally from the genuine regular-affine action. Arbitrary normal-
subgroup/isogeny classification and the original full affine-action classifier remain owed.
-/

namespace AclGeom.GroupFinite
noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Named consumer: a point in the finite parameter open. -/
theorem exists_point_of_nonempty (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [Nonempty X.left] :
    Nonempty (𝟙_ (Over (Spec (.of k))) ⟶ X) := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨z, _, hzc⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set X.left).Nonempty) isClosed_univ.isLocallyClosed
  have hz : IsClosed ({z} : Set X.left) := hzc
  exact ⟨Over.homMk (pointOfClosedPoint X.hom z hz) (pointOfClosedPoint_comp X.hom z hz)⟩

omit [IsAlgClosed k] in
/-- Named consumer: lift a closed point through an actual parameter open. -/
theorem exists_point_lift {X Y : Over (Spec (.of k))} (j : X ⟶ Y)
    [IsOpenImmersion j.left] (p : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    (hp : p.left (IsLocalRing.closedPoint k) ∈ Set.range j.left) :
    ∃ q : 𝟙_ (Over (Spec (.of k))) ⟶ X, q ≫ j = p := by
  have hr : Set.range p.left ⊆ Set.range j.left := by
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint k := by
      apply Subsingleton.elim (α := PrimeSpectrum k)
    simpa only [hz] using hp
  let q : 𝟙_ (Over (Spec (.of k))) ⟶ X :=
    Over.homMk (IsOpenImmersion.lift j.left p.left hr) (by
      rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w p)
  exact ⟨q, Over.OverMorphism.ext (IsOpenImmersion.lift_fac j.left p.left hr)⟩

omit [IsAlgClosed k] in
/-- Named consumer: translates of the parameter square remain open immersions. -/
theorem translated_open (G : AlgebraicGroup k) (U : Over (Spec (.of k)))
    (j : U ⟶ G.toGroupScheme.X) [IsOpenImmersion j.left]
    (q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :
    IsOpenImmersion (j ≫ GroupScheme.leftMul G.toGroupScheme.X q).left := by
  have : IsIso (GroupScheme.leftMul G.toGroupScheme.X q).left := by
    change IsIso (((Over.forget (Spec (.of k))).mapIso (GroupScheme.leftMulIso q)).hom)
    infer_instance
  change IsOpenImmersion (j.left ≫ (GroupScheme.leftMul G.toGroupScheme.X q).left)
  infer_instance

/-- A group point map whose image contains a nonempty open is onto a connected target.
Named consumer: globalization of the finite affine parameter square. -/
theorem surjective_points (G : AlgebraicGroup k) (H : ConnectedAlgebraicGroup k)
    (f : G.Hom H.toAlgebraicGroup)
    (U T : Over (Spec (.of k)))
    (jU : U ⟶ G.toGroupScheme.X) (jT : T ⟶ H.toGroupScheme.X)
    (π : U ⟶ T) [IsOpenImmersion jU.left] [IsOpenImmersion jT.left]
    [Nonempty T.left] [Surjective π.left]
    (hsq : jU ≫ f.hom.hom = π ≫ jT) :
    Function.Surjective (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X ↦
      q ≫ f.hom.hom) := by
  have : LocallyOfFiniteType U.hom := by rw [← Over.w jU]; infer_instance
  have : LocallyOfFiniteType T.hom := by rw [← Over.w jT]; infer_instance
  have : JacobsonSpace H.carrier := LocallyOfFiniteType.jacobsonSpace H.structureMap
  intro h
  let jh := jT ≫ GroupScheme.leftMul H.toGroupScheme.X h
  have : IsOpenImmersion jh.left := translated_open H.toAlgebraicGroup T jT h
  have hne : (Set.range jT.left ∩ Set.range jh.left).Nonempty :=
    nonempty_preirreducible_inter (IsOpenImmersion.isOpen_range jT.left)
      (IsOpenImmersion.isOpen_range jh.left) (Set.range_nonempty _) (Set.range_nonempty _)
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints hne
    ((IsOpenImmersion.isOpen_range jT.left).inter
      (IsOpenImmersion.isOpen_range jh.left)).isLocallyClosed
  have hzclosed : IsClosed ({z} : Set H.carrier) := hzc
  let w : 𝟙_ (Over (Spec (.of k))) ⟶ H.toGroupScheme.X :=
    Over.homMk (pointOfClosedPoint H.structureMap z hzclosed)
      (pointOfClosedPoint_comp H.structureMap z hzclosed)
  have hw : w.left (IsLocalRing.closedPoint k) = z := pointOfClosedPoint_apply _ _ _ _
  obtain ⟨a, ha⟩ := exists_point_lift jT w (by rw [hw]; exact hz.1)
  obtain ⟨b, hb⟩ := exists_point_lift jh w (by rw [hw]; exact hz.2)
  obtain ⟨aU, haU⟩ := CurveGlobalCoordinate.surjective_points_of_surjective π a
  obtain ⟨bU, hbU⟩ := CurveGlobalCoordinate.surjective_points_of_surjective π b
  change aU ≫ π = a at haU
  change bU ≫ π = b at hbU
  have haG : (aU ≫ jU) ≫ f.hom.hom = a ≫ jT := by
    rw [Category.assoc, hsq, ← Category.assoc, haU]
  have hbG : (bU ≫ jU) ≫ f.hom.hom = b ≫ jT := by
    rw [Category.assoc, hsq, ← Category.assoc, hbU]
  have hrel : h * (b ≫ jT) = a ≫ jT := by
    rw [← GroupScheme.point_comp_leftMul, Category.assoc]
    exact hb.trans ha.symm
  refine ⟨(aU ≫ jU) * (bU ≫ jU)⁻¹, ?_⟩
  change ((aU ≫ jU) * (bU ≫ jU)⁻¹) ≫ f.hom.hom = h
  rw [MonObj.mul_comp, GrpObj.inv_comp, haG, hbG, ← hrel,
    _root_.mul_assoc, mul_inv_cancel, _root_.mul_one]

/-- The whole inverse image of the target open is the given source open.
Named consumer: finiteness is used at the target, after this identification. -/
theorem preimage_open_eq {X Y U T : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (hinj : Function.Injective
      (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ X ↦ q ≫ f))
    (jU : U ⟶ X) (jT : T ⟶ Y) (π : U ⟶ T)
    [IsOpenImmersion jU.left] [IsOpenImmersion jT.left] [Surjective π.left]
    (hsq : jU ≫ f = π ≫ jT) :
    f.left ⁻¹' Set.range jT.left = Set.range jU.left := by
  have : LocallyOfFiniteType U.hom := by rw [← Over.w jU]; infer_instance
  have : LocallyOfFiniteType T.hom := by rw [← Over.w jT]; infer_instance
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  apply Set.Subset.antisymm
  · intro z hz
    by_contra hn
    have hne : ((f.left ⁻¹' Set.range jT.left) ∩ (Set.range jU.left)ᶜ).Nonempty :=
      ⟨z, hz, hn⟩
    obtain ⟨w, hw, hwclosed⟩ := nonempty_inter_closedPoints hne
      (((IsOpenImmersion.isOpen_range jT.left).preimage f.left.continuous).isLocallyClosed.inter
        (IsOpenImmersion.isOpen_range jU.left).isClosed_compl.isLocallyClosed)
    have hwc : IsClosed ({w} : Set X.left) := hwclosed
    let p : 𝟙_ (Over (Spec (.of k))) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom w hwc) (pointOfClosedPoint_comp X.hom w hwc)
    have hp : p.left (IsLocalRing.closedPoint k) = w := pointOfClosedPoint_apply _ _ _ _
    obtain ⟨a, ha⟩ := exists_point_lift jT (p ≫ f) (by
      change f.left (p.left (IsLocalRing.closedPoint k)) ∈ Set.range jT.left
      rw [hp]
      exact hw.1)
    obtain ⟨r, hr⟩ := CurveGlobalCoordinate.surjective_points_of_surjective π a
    change r ≫ π = a at hr
    have he : (r ≫ jU) ≫ f = p ≫ f := by
      rw [Category.assoc, hsq, ← Category.assoc, hr, ha]
    have heq := congrArg (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ X ↦
      q.left (IsLocalRing.closedPoint k)) (hinj he)
    exact hw.2 ⟨r.left (IsLocalRing.closedPoint k), heq.trans hp⟩
  · rintro z ⟨w, rfl⟩
    refine ⟨π.left w, ?_⟩
    exact (congrArg (fun q : U ⟶ Y ↦ q.left w) hsq).symm

/-- The finite map on the open square is the full target pullback.
Named consumer: target-local finiteness and surjectivity of the whole group morphism. -/
theorem finite_surjective_pullback {X Y U T : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (hinj : Function.Injective
      (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ X ↦ q ≫ f))
    (jU : U ⟶ X) (jT : T ⟶ Y) (π : U ⟶ T)
    [IsOpenImmersion jU.left] [IsOpenImmersion jT.left]
    [IsFinite π.left] [Surjective π.left]
    (hsq : jU ≫ f = π ≫ jT) :
    IsFinite (pullback.snd f.left jT.left) ∧ Surjective (pullback.snd f.left jT.left) := by
  have hr : Set.range jU.left = Set.range (pullback.fst f.left jT.left) := by
    rw [IsOpenImmersion.range_pullbackFst]
    exact (preimage_open_eq f hinj jU jT π hsq).symm
  let e := IsOpenImmersion.isoOfRangeEq jU.left (pullback.fst f.left jT.left) hr
  have he : e.hom ≫ pullback.snd f.left jT.left = π.left := by
    apply (cancel_mono jT.left).mp
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      IsOpenImmersion.isoOfRangeEq_hom_fac]
    exact congrArg (fun q : U ⟶ Y ↦ q.left) hsq
  have hres : pullback.snd f.left jT.left = e.inv ≫ π.left := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  rw [hres]
  exact ⟨inferInstance, inferInstance⟩

omit [IsAlgClosed k] in
/-- Named consumer: translating the finite parameter square. -/
theorem leftMul_hom (G H : AlgebraicGroup k) (f : G.Hom H)
    (q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X) :
    GroupScheme.leftMul G.toGroupScheme.X q ≫ f.hom.hom =
      f.hom.hom ≫ GroupScheme.leftMul H.toGroupScheme.X (q ≫ f.hom.hom) := by
  change ((toUnit G.toGroupScheme.X ≫ q) * 𝟙 G.toGroupScheme.X) ≫ f.hom.hom = _
  rw [MonObj.mul_comp, Category.id_comp, GroupScheme.comp_leftMul, Category.assoc]

/-- A point-injective group morphism with a finite surjective nonempty open square is
finite and surjective globally when its target is connected. Named consumer: the actual
affine morphism produced from the regular curve action. -/
theorem finite_surjective (G : AlgebraicGroup k) (H : ConnectedAlgebraicGroup k)
    (f : G.Hom H.toAlgebraicGroup)
    (hinj : Function.Injective
      (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X ↦ q ≫ f.hom.hom))
    (U T : Over (Spec (.of k)))
    (jU : U ⟶ G.toGroupScheme.X) (jT : T ⟶ H.toGroupScheme.X) (π : U ⟶ T)
    [IsOpenImmersion jU.left] [IsOpenImmersion jT.left]
    [Nonempty T.left] [IsFinite π.left] [Surjective π.left]
    (hsq : jU ≫ f.hom.hom = π ≫ jT) :
    IsFinite f.hom.hom.left ∧ Surjective f.hom.hom.left := by
  classical
  have hsurj := surjective_points G H f U T jU jT π hsq
  have : LocallyOfFiniteType T.hom := by rw [← Over.w jT]; infer_instance
  let p0 := (exists_point_of_nonempty T).some
  let : ModObj H.toGroupScheme.X H.toGroupScheme.X := ModObj.regular _
  have htrans (a b : 𝟙_ (Over (Spec (.of k))) ⟶ H.toGroupScheme.X) :
      ∃ q : 𝟙_ (Over (Spec (.of k))) ⟶ H.toGroupScheme.X,
        a ≫ ModObj.pointAct H.toGroupScheme.X q = b := by
    refine ⟨b * a⁻¹, ?_⟩
    change a ≫ GroupScheme.leftMul H.toGroupScheme.X (b * a⁻¹) = b
    rw [GroupScheme.point_comp_leftMul, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
  let Q := CurveGlobalCoordinate.translatedCover H.toAlgebraicGroup
    H.toGroupScheme.X T jT p0 htrans
  have hlocal (h : Q.I₀) :
      IsFinite (Q.pullbackHom f.hom.hom.left h) ∧
        Surjective (Q.pullbackHom f.hom.hom.left h) := by
    obtain ⟨q, hq⟩ := hsurj h
    change q ≫ f.hom.hom = h at hq
    let jU' := jU ≫ GroupScheme.leftMul G.toGroupScheme.X q
    let jT' := jT ≫ GroupScheme.leftMul H.toGroupScheme.X h
    have : IsOpenImmersion jU'.left := translated_open G U jU q
    have : IsOpenImmersion jT'.left := translated_open H.toAlgebraicGroup T jT h
    have hsq' : jU' ≫ f.hom.hom = π ≫ jT' := by
      dsimp only [jU', jT']
      rw [Category.assoc, leftMul_hom, hq, ← Category.assoc, hsq, Category.assoc]
    exact finite_surjective_pullback f.hom.hom hinj jU' jT' π hsq'
  have : IsZariskiLocalAtTarget (@IsFinite.{u}) := by
    -- Mathlib finite-property instances use transparent elaboration; kernel checking is unchanged.
    set_option backward.isDefEq.respectTransparency false in infer_instance
  exact ⟨IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) Q (fun h ↦ (hlocal h).1),
    IsZariskiLocalAtTarget.of_openCover (P := @Surjective) Q (fun h ↦ (hlocal h).2)⟩

end
end AclGeom.GroupFinite
