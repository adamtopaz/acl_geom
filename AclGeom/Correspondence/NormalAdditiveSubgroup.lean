/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AdditiveAutomorphisms
import AclGeom.Correspondence.MultiplicativeLift
import AclGeom.Correspondence.MultiplicativeScalarAction
import AclGeom.Correspondence.SchemePointExt
import AclGeom.Correspondence.NormalConjugation
import AclGeom.Correspondence.IntegralProduct

/-!
# The regular conjugation character of an actual normal additive subgroup

**Status:** the normal-Ga case of blueprint equation (8.4b) is proved over an ACF base, in
every characteristic (#21). The actual connected algebraic group, group morphism and
genuine normality supply a regular group character to Gm and the actual joint conjugation
diagram internally. No coefficient, scalar, regularity or character certificate is a
caller premise. No group-dimension hypothesis is needed for this auxiliary statement.

Normality supplies a regular conjugation lift. Its field-point slices are group-scheme
automorphisms, hence nonzero scalar maps. Evaluation at one gives a regular coefficient;
Jacobson density makes its global section invertible, giving the actual Gm morphism.
Monic cancellation proves scalar multiplicativity. Reduced-product point extensionality
proves the actual character's group laws and joint scheme conjugation diagram. The group
parameter is reduced; no Aut-Ga representability over nonreduced rings is asserted.

Identifying arbitrary one-dimensional normal subgroups with Ga or Gm, their required
finite-isogeny classification, the dense-orbit curve coordinate, non-affine/rational actions,
regularization, completion/points, the full classifier, original group/chunk/six-point
results, algebraization/descent and every true bypassed auxiliary remain owed. All eight
original #21 work items and the full durable goal stay open.
-/

namespace AclGeom.AdditiveRigidity
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.GrpObj CategoryTheory.MonObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The regular normal additive-subgroup conjugation character in (8.4b), constructed
internally from the actual group morphism and genuine normality. -/
theorem normal_additiveGroup_conj
    (G : ConnectedAlgebraicGroup k)
    (i : (AdditiveGroupScheme.algebraicGroup k 1).Hom G.toAlgebraicGroup)
    [IsMonHom.Normal i.hom.hom] :
    ∃ χ : G.toAlgebraicGroup.Hom (multiplicativeGroup k),
      G.toGroupScheme.X ◁ i.hom.hom ≫ conj G.toGroupScheme.X =
        lift (fst G.toGroupScheme.X (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ≫
          χ.hom.hom) (snd G.toGroupScheme.X
            (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X) ≫
          scalarMul k ≫ i.hom.hom := by
  classical
  let GX := G.toGroupScheme.X
  let N := (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
  let i₀ : N ⟶ GX := i.hom.hom
  obtain ⟨ψ, hψ⟩ := IsMonHom.Normal.exists_comp_eq_conj i₀
  let c (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : N ⟶ N :=
    lift (toUnit N ≫ q) (𝟙 N) ≫ ψ
  have hauto (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) :
      ∃ a : kˣ, c q = scale k (a : k) := by
    obtain ⟨e, he⟩ := NormalConjugation.exists_groupIso_conjugation_lift i₀ ψ hψ q
    simpa only [he] using groupIso_eq_scale k e
  let a (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : kˣ := (hauto q).choose
  have ha (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : c q = scale k (a q : k) :=
    (hauto q).choose_spec
  have hc₁ : c 1 = 𝟙 N := by
    apply (cancel_mono i₀).mp
    simp [c, hψ, lift_whiskerLeft_assoc]
  have hcomp (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX)
      (p : 𝟙_ (Over (Spec (.of k))) ⟶ N) : p ≫ c q = lift q p ≫ ψ := by
    simp only [c, comp_lift_assoc, Category.comp_id]
    simp only [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  have hc (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) {T : Over (Spec (.of k))} (p : T ⟶ N) :
      (p ≫ c q) ≫ i₀ = (toUnit T ≫ q) * (p ≫ i₀) * (toUnit T ≫ q)⁻¹ := by
    simp only [c, Category.assoc, hψ, comp_lift_assoc,
      Category.comp_id, lift_whiskerLeft_assoc, lift_conj_eq_mul_mul_inv]
    simp only [← Category.assoc, comp_toUnit]
  have hcmul (q r : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : c (q * r) = c r ≫ c q := by
    apply (cancel_mono i₀).mp
    have hleft := hc (q * r) (𝟙 N)
    have hright := hc q (c r)
    have hr := hc r (𝟙 N)
    simp only [Category.id_comp] at hleft hr
    rw [hleft, hright, hr, comp_mul, _root_.mul_inv_rev]
    simp only [_root_.mul_assoc]
  let P (x : k) : 𝟙_ (Over (Spec (.of k))) ⟶ N :=
    (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k x
  have hPinj : Function.Injective P := by
    intro x y hxy
    apply AffineSchemeAction.linePoint_injective k
    exact (cancel_epi (unitIsoSpecAsOver k).hom).mp hxy
  have hPscale (x b : k) : P x ≫ scale k b = P (b * x) := by
    exact (Category.assoc _ _ _).trans
      (congrArg (fun f ↦ (unitIsoSpecAsOver k).hom ≫ f) (linePoint_comp_scale k b x))
  have ha₁ : a 1 = 1 := by
    apply Units.ext
    apply hPinj
    have hh := congrArg (fun f : N ⟶ N ↦ P 1 ≫ f) (ha 1).symm
    rw [hc₁, Category.comp_id, hPscale, _root_.mul_one] at hh
    exact hh
  have hamul (q r : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : a (q * r) = a q * a r := by
    apply Units.ext
    apply hPinj
    have hh := congrArg (fun f : N ⟶ N ↦ P 1 ≫ f) (hcmul q r)
    rw [ha, ha, ha, ← Category.assoc, hPscale, hPscale, hPscale,
      _root_.mul_one, _root_.mul_one] at hh
    exact hh
  let O : GX ⟶ N := lift (𝟙 GX) (toUnit GX ≫ P 1) ≫ ψ
  have hOcomp (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : q ≫ O = P 1 ≫ c q := by
    rw [hcomp]
    simp only [O, comp_lift_assoc, Category.comp_id]
    simp only [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  obtain ⟨χ, hχ⟩ := exists_multiplicative_lift GX O (fun q ↦
    ⟨a q, by rw [hOcomp, ha, hPscale, _root_.mul_one]⟩)
  let E := multiplicativeGroup.pointsMulEquiv k
  have hχpoint (q : 𝟙_ (Over (Spec (.of k))) ⟶ GX) : q ≫ χ = E.symm (a q) := by
    let b := E (q ≫ χ)
    have hb : q ≫ χ = (unitIsoSpecAsOver k).hom ≫ unitPoint k b := by
      rw [unitPoint_eq_points]
      exact (E.symm_apply_apply (q ≫ χ)).symm
    have hvalue := congrArg (fun f : GX ⟶ N ↦ q ≫ f) hχ
    rw [← Category.assoc, hb, Category.assoc, unitPoint_comp_multiplicativeValue,
      hOcomp, ha, hPscale, _root_.mul_one] at hvalue
    have hba : b = a q := Units.ext (hPinj hvalue)
    rw [hb, unitPoint_eq_points, hba]
  have hχone : (1 : 𝟙_ (Over (Spec (.of k))) ⟶ GX) ≫ χ = 1 := by
    rw [hχpoint, ha₁, map_one]
  have hχmul (q r : 𝟙_ (Over (Spec (.of k))) ⟶ GX) :
      (q * r) ≫ χ = (q ≫ χ) * (r ≫ χ) := by
    rw [hχpoint, hχpoint, hχpoint, hamul, map_mul]
  have : IsIntegral (GX ⊗ GX).left := isIntegral_pullback_of_isAlgClosed GX.hom GX.hom
  have : LocallyOfFiniteType (GX ⊗ GX).hom := by
    change LocallyOfFiniteType (Limits.pullback.fst GX.hom GX.hom ≫ GX.hom)
    infer_instance
  have : IsMonHom χ := by
    constructor
    · simpa only [one_eq_one] using hχone
    · have heq : μ[GX] ≫ χ = (χ ⊗ₘ χ) ≫ μ[(multiplicativeGroup k).toGroupScheme.X] := by
        apply over_hom_ext_of_points
        intro p
        have hp : lift (p ≫ fst GX GX) (p ≫ snd GX GX) = p := by simp
        have hh := hχmul (p ≫ fst GX GX) (p ≫ snd GX GX)
        simp only [Hom.mul_def] at hh
        rw [← lift_map_assoc (p ≫ fst GX GX) (p ≫ snd GX GX) χ χ, hp] at hh
        simpa only [Category.assoc] using hh
      simpa only [tensorHom_def, Category.assoc] using heq
  let χG : G.toAlgebraicGroup.Hom (multiplicativeGroup k) := Grp.homMk χ
  have : IsIntegral N.left := by
    change IsIntegral (Spec (.of (AdditiveGroupScheme.CoordinateRing k 1)))
    infer_instance
  have : IsIntegral (GX ⊗ N).left := isIntegral_pullback_of_isAlgClosed GX.hom N.hom
  have : LocallyOfFiniteType (GX ⊗ N).hom := by
    change LocallyOfFiniteType (Limits.pullback.fst GX.hom N.hom ≫ GX.hom)
    infer_instance
  have hψeq : ψ = lift (fst GX N ≫ χ) (snd GX N) ≫ scalarMul k := by
    apply over_hom_ext_of_points
    intro p
    let qg := p ≫ fst GX N
    let qn := p ≫ snd GX N
    obtain ⟨x, hx⟩ := AffineSchemeAction.exists_linePoint k ((unitIsoSpecAsOver k).inv ≫ qn)
    have hqn : qn = P x := by
      change qn = (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k x
      rw [hx, Iso.hom_inv_id_assoc]
    have hp : lift qg qn = p := by simp [qg, qn]
    calc
      p ≫ ψ = qn ≫ c qg := by rw [hcomp, hp]
      _ = P ((a qg : k) * x) := by rw [ha, hqn, hPscale]
      _ = lift (E.symm (a qg)) qn ≫ scalarMul k := by
        rw [hqn, ← unitPoint_eq_points]
        change (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k _ =
          lift ((unitIsoSpecAsOver k).hom ≫ unitPoint k (a qg))
            ((unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k x) ≫ scalarMul k
        rw [← comp_lift_assoc, unitPoint_linePoint_scalarMul]
      _ = _ := by rw [← hχpoint]; simp [qg, qn, comp_lift_assoc]
  refine ⟨χG, ?_⟩
  change GX ◁ i₀ ≫ conj GX = lift (fst GX N ≫ χ) (snd GX N) ≫ scalarMul k ≫ i₀
  rw [← hψ, hψeq, Category.assoc]
end
end AclGeom.AdditiveRigidity
