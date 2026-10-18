/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.SchemeGlobalSections
import AclGeom.Correspondence.SchemeGlobalUnits
import AclGeom.Correspondence.MultiplicativeValue

/-!
# Lifting a nowhere-zero regular line coefficient to Gm

**Status:** over an ACF base, an actual regular line map on a locally finite-type scheme
whose base-field values are nonzero lifts to an actual regular Gm map. Pullback gives a
global section; pointwise invertibility makes it a global unit. The Laurent algebra map
and actual spectrum map are constructed internally. Named consumer:
`AdditiveRigidity.normal_additiveGroup_conj`, which supplies the nonvanishing internally.
-/

namespace AclGeom.AdditiveRigidity
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
attribute [local instance] SchemeGenericTranslate.sectionsAlgebra

/-- Named consumer: the actual normal additive-subgroup regular conjugation character. -/
theorem exists_multiplicative_lift (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    (f : X ⟶ (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X)
    (hpoint : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ X, ∃ a : kˣ,
      q ≫ f = (unitIsoSpecAsOver k).hom ≫ AffineSchemeAction.linePoint k (a : k)) :
    ∃ χ : X ⟶ (multiplicativeGroup k).toGroupScheme.X, χ ≫ multiplicativeValue k = f := by
  let R := AdditiveGroupScheme.CoordinateRing k 1
  obtain ⟨φ, hφ, hrec⟩ := exists_spec_pullback X R f
  let f₀ : X.left ⟶ Spec (.of R) := f.left
  have hφ₀ : CommRingCat.ofHom φ.toRingHom = (Scheme.ΓSpecIso (.of R)).inv ≫ f₀.appTop := by
    apply CommRingCat.hom_ext
    exact hφ
  let s := φ (AffineSchemeAction.lineCoordinate k)
  have hunit : IsUnit s := by
    apply isUnit_section_of_point_values X s
    intro q
    obtain ⟨a, ha⟩ := hpoint q
    let q₀ : Spec (.of k) ⟶ X.left := q.left
    have hspec : q₀ ≫ f₀ =
        Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval (a : k)).toRingHom) := by
      have hh := congrArg Over.Hom.left ha
      change q₀ ≫ f₀ = 𝟙 _ ≫
        Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval (a : k)).toRingHom) at hh
      simpa only [Category.id_comp] using hh
    have hΓ : CommRingCat.ofHom φ.toRingHom ≫ q₀.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom =
        CommRingCat.ofHom (AffineSchemeAction.lineEval (a : k)).toRingHom := by
      calc
        _ = (Scheme.ΓSpecIso (.of R)).inv ≫ (q₀ ≫ f₀).appTop ≫
            (Scheme.ΓSpecIso (.of k)).hom := by
          simp only [hφ₀, Scheme.Hom.comp_appTop, Category.assoc]
        _ = (Scheme.ΓSpecIso (.of R)).inv ≫
            (Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval (a : k)).toRingHom)).appTop ≫
            (Scheme.ΓSpecIso (.of k)).hom := by rw [hspec]
        _ = CommRingCat.ofHom (AffineSchemeAction.lineEval (a : k)).toRingHom ≫
            (Scheme.ΓSpecIso (.of k)).inv ≫ (Scheme.ΓSpecIso (.of k)).hom :=
          (Scheme.ΓSpecIso_inv_naturality_assoc _ _).symm
        _ = _ := by rw [Iso.inv_hom_id, Category.comp_id]
    have hvalue := congrArg (fun h : CommRingCat.of R ⟶ CommRingCat.of k ↦
      h (AffineSchemeAction.lineCoordinate k)) hΓ
    change (Scheme.ΓSpecIso (.of k)).hom (q₀.appTop s) =
      (AffineSchemeAction.lineEval (a : k)) (AffineSchemeAction.lineCoordinate k) at hvalue
    rw [AffineSchemeAction.lineEval_lineCoordinate] at hvalue
    have hu : IsUnit ((Scheme.ΓSpecIso (.of k)).hom (q₀.appTop s)) := by
      rw [hvalue]
      exact a.isUnit
    have hv := hu.map (Scheme.ΓSpecIso (.of k)).inv.hom
    have hz : (Scheme.ΓSpecIso (.of k)).inv ((Scheme.ΓSpecIso (.of k)).hom (q₀.appTop s)) =
        q₀.appTop s := by
      have hh := congrArg (fun h : Γ(Spec (.of k), ⊤) ⟶ Γ(Spec (.of k), ⊤) ↦
        h (q₀.appTop s)) (Scheme.ΓSpecIso (.of k)).hom_inv_id
      exact hh
    rwa [hz] at hv
  let evalUnit : AddMonoidAlgebra k ℤ →ₐ[k] Γ(X.left, ⊤) :=
    ((unitsMulEquivConv k Γ(X.left, ⊤)).symm hunit.unit).ofConv
  have hevalUnit : evalUnit (AddMonoidAlgebra.single (1 : ℤ) (1 : k)) = s :=
    (unitsMulEquivConv_symm_apply_single k Γ(X.left, ⊤) hunit.unit).trans hunit.unit_spec
  let χ : X ⟶ (multiplicativeGroup k).toGroupScheme.X := fromGlobal X _ evalUnit
  refine ⟨χ, ?_⟩
  have hcomp : evalUnit.comp (AffineSchemeAction.lineEval
      (AddMonoidAlgebra.single (1 : ℤ) (1 : k))) = φ := by
    apply AffineSchemeAction.lineHom_ext
    rw [AlgHom.comp_apply, AffineSchemeAction.lineEval_lineCoordinate, hevalUnit]
  have hring : CommRingCat.ofHom (AffineSchemeAction.lineEval
      (AddMonoidAlgebra.single (1 : ℤ) (1 : k))).toRingHom ≫
      CommRingCat.ofHom evalUnit.toRingHom = CommRingCat.ofHom φ.toRingHom := by
    apply CommRingCat.hom_ext
    change (evalUnit.comp (AffineSchemeAction.lineEval
      (AddMonoidAlgebra.single (1 : ℤ) (1 : k)))).toRingHom = φ.toRingHom
    exact congrArg AlgHom.toRingHom hcomp
  apply Over.OverMorphism.ext
  change (X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom evalUnit.toRingHom)) ≫
    Spec.map (CommRingCat.ofHom (AffineSchemeAction.lineEval
      (AddMonoidAlgebra.single (1 : ℤ) (1 : k))).toRingHom) = f₀
  rw [Category.assoc, ← Spec.map_comp, hring]
  exact hrec
end
end AclGeom.AdditiveRigidity
