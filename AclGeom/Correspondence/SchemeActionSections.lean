/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.ActionFunctionField
import AclGeom.Correspondence.AffineSchemeAction

/-!
# Regular actions on global sections, in coordinates

Let an algebraic group `G` act regularly on an affine scheme `V` over `Spec k`, and let `U` be an
affine open of `G`. A global section `r` of `V` pulls back along the action, restricted to
`U × V`, to a finite sum `∑ cᵢ ⊗ sᵢ` with `cᵢ ∈ Γ(G, U)` and `sᵢ ∈ Γ(V, ⊤)`. Hence a `k`-point
`g` of `G` lying in `U` moves `r` to `∑ cᵢ(g) sᵢ` (`exists_pointAut_appTop_eq_sum`), where
`cᵢ(g)` is the value of `cᵢ` at `g` (`pointEval`). The coefficients `cᵢ` and `sᵢ` do not depend
on `g`.

The `k`-algebra structure of `Γ(V, ⊤)` is the explicit ring map induced by the structure morphism
of `V`; no `Algebra k Γ(V, ⊤)` instance appears in the statement.

Named consumer: the upper semicontinuity of place orders along the action
(`ActionSemicontinuity`), a step of the fixed-boundary argument for `lem:affine-action`.

**Status:** proved; consumed by the actual connected regular-action fixed-boundary theorem.
-/

namespace AclGeom.SchemeActionSections

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct

universe u

variable {k : Type u} [Field k]

/-- A `k`-point lying in an open `U` maps all of `Spec k` into `U`, since `Spec k` is a single
point. Named consumers: `pointEval` and its evaluation lemmas. -/
theorem top_le_preimage {X : Over (Spec (.of k))} (g : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    {U : X.left.Opens} (hg : g.left (IsLocalRing.closedPoint k) ∈ U) : ⊤ ≤ g.left ⁻¹ᵁ U :=
  fun y _ ↦ by
    obtain rfl : y = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
    exact hg

/-- The value at a `k`-point `g` of a section over an open `U` containing `g`. The point is the
morphism `g.left : Spec k ⟶ X`, which maps `Spec k` into `U`. -/
def pointEval {X : Over (Spec (.of k))} (g : 𝟙_ (Over (Spec (.of k))) ⟶ X) (U : X.left.Opens)
    (hg : g.left (IsLocalRing.closedPoint k) ∈ U) : Γ(X.left, U) →+* k :=
  (Scheme.Hom.appLE (X := Spec (.of k)) g.left U ⊤ (top_le_preimage g hg) ≫
    (Scheme.ΓSpecIso (.of k)).hom).hom

/-- Evaluation at a `k`-point fixes the constants: it is a `k`-algebra map for the base algebra
induced by the structure morphism. -/
theorem pointEval_appLE {X : Over (Spec (.of k))} (g : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (U : X.left.Opens) (hg : g.left (IsLocalRing.closedPoint k) ∈ U) (c : k) :
    pointEval g U hg (((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appLE ⊤ U le_top).hom c) = c := by
  have hid : ∀ (f : Spec (.of k) ⟶ Spec (.of k)) (h : ⊤ ≤ f ⁻¹ᵁ ⊤), f = 𝟙 _ →
      f.appLE ⊤ ⊤ h = 𝟙 _ := by
    rintro f h rfl
    exact Scheme.Hom.appLE_eq_app (𝟙 _)
  have key := (Scheme.Hom.appLE_comp_appLE (X := Spec (.of k)) g.left X.hom ⊤ U ⊤ le_top
    (top_le_preimage g hg)).trans (hid _ _ (by exact Over.w g))
  exact congrArg (fun φ : CommRingCat.of k ⟶ CommRingCat.of k ↦ φ.hom c)
    (show (Scheme.ΓSpecIso (.of k)).inv ≫ (X.hom.appLE ⊤ U le_top ≫
        Scheme.Hom.appLE (X := Spec (.of k)) g.left U ⊤ (top_le_preimage g hg)) ≫
          (Scheme.ΓSpecIso (.of k)).hom = 𝟙 _ by
      rw [key, Category.id_comp, Iso.inv_hom_id])

/-- A section vanishes at a `k`-point exactly when the point lies outside its basic open set. -/
theorem pointEval_eq_zero_iff {X : Over (Spec (.of k))} (g : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    {U : X.left.Opens} (hg : g.left (IsLocalRing.closedPoint k) ∈ U) (c : Γ(X.left, U)) :
    pointEval g U hg c = 0 ↔ g.left (IsLocalRing.closedPoint k) ∉ X.left.basicOpen c := by
  have hpt : ∀ t : Γ(Spec (.of k), ⊤),
      IsLocalRing.closedPoint k ∈ (Spec (.of k)).basicOpen t ↔ t ≠ 0 := by
    intro t
    constructor
    · rintro hx rfl
      rw [Scheme.basicOpen_zero] at hx
      exact TopologicalSpace.Opens.mem_bot.1 hx
    · intro ht
      obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1
        (mt (basicOpen_eq_bot_iff t).1 ht)
      obtain rfl : y = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
      exact hy
  have key : ∀ (p : Spec (.of k) ⟶ X.left) (h : ⊤ ≤ p ⁻¹ᵁ U),
      p.appLE U ⊤ h c = 0 ↔ p (IsLocalRing.closedPoint k) ∉ X.left.basicOpen c := by
    intro p h
    have hmem : p (IsLocalRing.closedPoint k) ∈ X.left.basicOpen c ↔
        IsLocalRing.closedPoint k ∈ (Spec (.of k)).basicOpen (p.appLE U ⊤ h c) := by
      change _ ↔ IsLocalRing.closedPoint k ∈ (Spec (.of k)).basicOpen
        ((Spec (.of k)).presheaf.map (homOfLE h).op (p.app U c))
      rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
      exact ⟨fun hx ↦ TopologicalSpace.Opens.mem_inf.2 ⟨trivial, hx⟩,
        fun hx ↦ (TopologicalSpace.Opens.mem_inf.1 hx).2⟩
    rw [hmem, hpt]
    exact not_not.symm
  have hinj : Function.Injective (Scheme.ΓSpecIso (.of k)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).hom).1
  exact (map_eq_zero_iff _ hinj).trans (key g.left (top_le_preimage g hg))

/-- **The action on global sections in coordinates.** For an affine open `U` of `G` and a global
section `r` of `V`, there are finitely many sections `cᵢ` of `G` over `U` and `sᵢ` of `V` such that
every `k`-point `g ∈ U` moves `r` to `∑ cᵢ(g) sᵢ`. -/
theorem exists_pointAut_appTop_eq_sum (G : AlgebraicGroup k) (V : Over (Spec (.of k)))
    [IsAffine V.left] [ModObj G.toGroupScheme.X V] {U : G.carrier.Opens} (hU : IsAffineOpen U)
    (r : Γ(V.left, ⊤)) :
    ∃ (n : ℕ) (c : Fin n → Γ(G.carrier, U)) (s : Fin n → Γ(V.left, ⊤)),
      ∀ (g : 𝟙_ (Over (Spec (.of k))) ⟶ G.toGroupScheme.X)
        (hg : g.left (IsLocalRing.closedPoint k) ∈ U),
        (ModObj.pointAut V g).hom.left.appTop r =
          ∑ i, ((Scheme.ΓSpecIso (.of k)).inv ≫ V.hom.appTop).hom (pointEval g U hg (c i)) *
            s i := by
  -- The base algebras of the two coordinate rings, induced by the structure morphisms.
  let algU : CommRingCat.of k ⟶ Γ(G.carrier, U) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ G.structureMap.appLE ⊤ U le_top
  let algV : CommRingCat.of k ⟶ Γ(V.left, ⊤) := (Scheme.ΓSpecIso (.of k)).inv ≫ V.hom.appTop
  let _ : Algebra k Γ(G.carrier, U) := algU.hom.toAlgebra
  let _ : Algebra k Γ(V.left, ⊤) := algV.hom.toAlgebra
  have hu : hU.fromSpec ≫ G.structureMap = Spec.map algU := by
    change _ = Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ G.structureMap.appLE ⊤ U le_top)
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
    exact (IsAffineOpen.SpecMap_appLE_fromSpec G.structureMap (isAffineOpen_top _) hU _).symm
  have hv : V.left.isoSpec.hom ≫ Spec.map algV = V.hom := by
    change V.left.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ V.hom.appTop) = V.hom
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  -- The universal point of `U` and the spectrum model of `V`, over `Spec k`.
  let u : (Spec (.of Γ(G.carrier, U))).asOver (Spec (.of k)) ⟶ G.toGroupScheme.X :=
    Over.homMk hU.fromSpec hu
  let vIso : V ≅ (Spec (.of Γ(V.left, ⊤))).asOver (Spec (.of k)) :=
    Over.isoMk V.left.isoSpec hv
  -- The action restricted to `U × V`, and its comorphism on coordinate rings.
  let Φ : (Spec (.of Γ(G.carrier, U))).asOver (Spec (.of k)) ⊗
      (Spec (.of Γ(V.left, ⊤))).asOver (Spec (.of k)) ⟶ V :=
    (fst ((Spec (.of Γ(G.carrier, U))).asOver (Spec (.of k)))
        ((Spec (.of Γ(V.left, ⊤))).asOver (Spec (.of k))) ≫ u) •
      (snd ((Spec (.of Γ(G.carrier, U))).asOver (Spec (.of k)))
        ((Spec (.of Γ(V.left, ⊤))).asOver (Spec (.of k))) ≫ vIso.inv)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : CommRingCat.of Γ(V.left, ⊤) ⟶
      CommRingCat.of (Γ(G.carrier, U) ⊗[k] Γ(V.left, ⊤)),
      Spec.map ψ =
        ((AffineSchemeAction.tensorSpecIso k Γ(G.carrier, U) Γ(V.left, ⊤)).inv ≫ Φ ≫
          vIso.hom).left :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  obtain ⟨S, hS⟩ :=
    TensorProduct.exists_finset (ψ.hom r : Γ(G.carrier, U) ⊗[k] Γ(V.left, ⊤))
  have hsum : ψ.hom r = ∑ i : Fin S.card,
      (S.equivFin.symm i : Γ(G.carrier, U) × Γ(V.left, ⊤)).1 ⊗ₜ[k]
        (S.equivFin.symm i : Γ(G.carrier, U) × Γ(V.left, ⊤)).2 := by
    rw [hS, ← Finset.sum_coe_sort S]
    exact (Equiv.sum_comp S.equivFin.symm
      (fun p : S ↦ (p : Γ(G.carrier, U) × Γ(V.left, ⊤)).1 ⊗ₜ[k]
        (p : Γ(G.carrier, U) × Γ(V.left, ⊤)).2)).symm
  refine ⟨S.card, fun i ↦ (S.equivFin.symm i : Γ(G.carrier, U) × Γ(V.left, ⊤)).1,
    fun i ↦ (S.equivFin.symm i : Γ(G.carrier, U) × Γ(V.left, ⊤)).2, fun g hg ↦ ?_⟩
  -- The point `g` factors through `U` as the spectrum of its evaluation map.
  have hle := top_le_preimage g hg
  have hpt : g.left = Spec.map (Scheme.Hom.appLE (X := Spec (.of k)) g.left U ⊤ hle ≫
      (Scheme.ΓSpecIso (.of k)).hom) ≫ hU.fromSpec := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec (X := Spec (.of k)) g.left hU
      (isAffineOpen_top _) hle
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.id_comp]
  -- Evaluation at `g`, as a `k`-algebra map into the coordinate ring of `V`.
  obtain ⟨ev, hev⟩ : ∃ ev : Γ(G.carrier, U) →ₐ[k] Γ(V.left, ⊤),
      ∀ a, ev a = algebraMap k Γ(V.left, ⊤) (pointEval g U hg a) :=
    ⟨⟨(algebraMap k Γ(V.left, ⊤)).comp (pointEval g U hg), fun c ↦
      congrArg (algebraMap k Γ(V.left, ⊤)) (pointEval_appLE g U hg c)⟩, fun _ ↦ rfl⟩
  have hevH : CommRingCat.ofHom ev.toRingHom =
      (Scheme.Hom.appLE (X := Spec (.of k)) g.left U ⊤ hle ≫ (Scheme.ΓSpecIso (.of k)).hom) ≫
        algV := by
    ext a
    exact hev a
  have ha : vIso.hom ≫ (Spec.map (CommRingCat.ofHom ev.toRingHom)).asOver (Spec (.of k)) ≫ u =
      toUnit V ≫ g := by
    apply Over.OverMorphism.ext
    change V.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ev.toRingHom) ≫ hU.fromSpec =
      V.hom ≫ g.left
    rw [hevH, Spec.map_comp, Category.assoc, ← Category.assoc V.left.isoSpec.hom, hv, ← hpt]
  have hb : vIso.hom ≫ (Spec.map (CommRingCat.ofHom (AlgHom.id k Γ(V.left, ⊤)).toRingHom)).asOver
      (Spec (.of k)) ≫ vIso.inv = 𝟙 V := by
    apply Over.OverMorphism.ext
    change V.left.isoSpec.hom ≫ Spec.map (𝟙 _) ≫ V.left.isoSpec.inv = 𝟙 V.left
    rw [Spec.map_id, Category.id_comp, Iso.hom_inv_id]
  -- The action of `g` is the spectrum of `ψ` followed by evaluation at `g`.
  have hleft : (ModObj.pointAct V g).left = V.left.isoSpec.hom ≫
      Spec.map (ψ ≫ CommRingCat.ofHom (Algebra.TensorProduct.lift ev
        (AlgHom.id k Γ(V.left, ⊤)) fun _ _ ↦ Commute.all _ _).toRingHom) ≫
      V.left.isoSpec.inv := by
    have e : ModObj.pointAct V g = vIso.hom ≫
        (lift ((Spec.map (CommRingCat.ofHom ev.toRingHom)).asOver (Spec (.of k)))
          ((Spec.map (CommRingCat.ofHom (AlgHom.id k Γ(V.left, ⊤)).toRingHom)).asOver
            (Spec (.of k))) ≫
          (AffineSchemeAction.tensorSpecIso k Γ(G.carrier, U) Γ(V.left, ⊤)).hom) ≫
        ((AffineSchemeAction.tensorSpecIso k Γ(G.carrier, U) Γ(V.left, ⊤)).inv ≫ Φ ≫
          vIso.hom) ≫ vIso.inv := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
      change (toUnit V ≫ g) • 𝟙 V = vIso.hom ≫ _ ≫
        ((fst ((Spec (.of Γ(G.carrier, U))).asOver (Spec (.of k)))
            ((Spec (.of Γ(V.left, ⊤))).asOver (Spec (.of k))) ≫ u) •
          (snd ((Spec (.of Γ(G.carrier, U))).asOver (Spec (.of k)))
            ((Spec (.of Γ(V.left, ⊤))).asOver (Spec (.of k))) ≫ vIso.inv))
      rw [ModObj.comp_smul, ModObj.comp_smul, lift_fst_assoc, lift_snd_assoc, ha, hb]
    rw [e, AffineSchemeAction.lift_tensorSpecIso_hom, Spec.map_comp ψ, hψ]
    simp only [Over.comp_left, Category.assoc]
    rfl
  have happ : (ModObj.pointAct V g).left.appTop = ψ ≫ CommRingCat.ofHom
      (Algebra.TensorProduct.lift ev (AlgHom.id k Γ(V.left, ⊤)) fun _ _ ↦ Commute.all _ _).toRingHom
      := by
    apply Spec.map_injective
    rw [← cancel_mono V.left.isoSpec.inv, Scheme.isoSpec_inv_naturality, hleft,
      Iso.inv_hom_id_assoc]
  change ((ModObj.pointAct V g).left.appTop).hom r = _
  rw [happ]
  change (Algebra.TensorProduct.lift ev (AlgHom.id k Γ(V.left, ⊤)) fun _ _ ↦ Commute.all _ _)
    (ψ.hom r) = _
  rw [hsum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦
    (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans (congrArg (· * _) (hev _))

end

end AclGeom.SchemeActionSections
