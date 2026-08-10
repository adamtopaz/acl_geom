/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
import Mathlib.CategoryTheory.Monoidal.Cartesian.Normal

/-!
# Finite-type algebraic groups and their kernels

This module fixes the scheme-theoretic target of the rational group-chunk
construction used in blueprint Theorem 8.2.  An `AlgebraicGroup k` is a
separated finite-type group object over `Spec k`; a
`ConnectedAlgebraicGroup k` is geometrically integral as well.  Thus the
word "algebraic" here is not a synonym for an abstract group carried by a
parameter type: the multiplication, unit, and inverse are actual morphisms
of schemes.

The final section exposes the scheme-theoretic kernel of a group-scheme
morphism.  This is the target with which the categorical kernel constructed
from the Psi parameter groupoid must eventually be identified.

This module is part of the formalization of the
Evans--Hrushovski--Gismatullin reconstruction theorem; the source of truth is
`sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u

/-- Group schemes over the spectrum of a field. -/
abbrev GroupScheme (k : Type u) [Field k] :=
  CategoryTheory.Grp (Over (Spec (.of k)))

/-- A separated finite-type group scheme over a field.

Finite type is recorded by its two standard constituents in Mathlib:
`LocallyOfFiniteType` and `QuasiCompact`. -/
structure AlgebraicGroup (k : Type u) [Field k] where
  /-- The underlying group object over `Spec k`. -/
  toGroupScheme : GroupScheme k
  /-- The structure morphism is locally of finite type. -/
  [locallyOfFiniteType : LocallyOfFiniteType toGroupScheme.X.hom]
  /-- The structure morphism is quasi-compact. -/
  [quasiCompact : QuasiCompact toGroupScheme.X.hom]
  /-- The structure morphism is separated. -/
  [isSeparated : IsSeparated toGroupScheme.X.hom]

attribute [instance] AlgebraicGroup.locallyOfFiniteType
  AlgebraicGroup.quasiCompact AlgebraicGroup.isSeparated

namespace AlgebraicGroup

variable {k : Type u} [Field k]

/-- The underlying scheme of an algebraic group. -/
abbrev carrier (G : AlgebraicGroup k) : Scheme := G.toGroupScheme.X.left

/-- The structure morphism of an algebraic group. -/
abbrev structureMap (G : AlgebraicGroup k) : G.carrier ⟶ Spec (.of k) :=
  G.toGroupScheme.X.hom

/-- A morphism of algebraic groups is a morphism of the underlying group
objects over `Spec k`. -/
abbrev Hom (G H : AlgebraicGroup k) := G.toGroupScheme ⟶ H.toGroupScheme

/-- The underlying morphism of schemes of a morphism of algebraic groups. -/
abbrev Hom.schemeHom {G H : AlgebraicGroup k} (f : G.Hom H) :
    G.carrier ⟶ H.carrier := f.hom.hom.left

end AlgebraicGroup

/-- A connected algebraic group, represented by a geometrically integral
finite-type group scheme.  Geometric integrality is the property produced
by the irreducible-chart gluing in blueprint Theorem 8.2 and is stronger
than connectedness after every field extension. -/
structure ConnectedAlgebraicGroup (k : Type u) [Field k]
    extends AlgebraicGroup k where
  /-- Every geometric fiber is integral. -/
  [geometricallyIntegral : GeometricallyIntegral toGroupScheme.X.hom]

attribute [instance] ConnectedAlgebraicGroup.geometricallyIntegral

namespace ConnectedAlgebraicGroup

variable {k : Type u} [Field k]

/-- The underlying scheme of a connected algebraic group is integral. -/
instance isIntegral (G : ConnectedAlgebraicGroup k) :
    IsIntegral G.toGroupScheme.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton
    G.toGroupScheme.X.hom

/-- In particular, the underlying topological space is connected. -/
instance connectedSpace (G : ConnectedAlgebraicGroup k) :
    ConnectedSpace G.toGroupScheme.X.left := inferInstance

end ConnectedAlgebraicGroup

namespace AlgebraicGroup.Hom

variable {k : Type u} [Field k] {G H : AlgebraicGroup k}

/-- The group object underlying the scheme-theoretic kernel. -/
def kernelGroupScheme (f : G.Hom H) : GroupScheme k :=
  Limits.kernel f

/-- The kernel inclusion as a morphism of group schemes. -/
def kernelι (f : G.Hom H) : f.kernelGroupScheme ⟶ G.toGroupScheme :=
  Limits.kernel.ι f

/-- The underlying scheme of the scheme-theoretic kernel. -/
abbrev kernelScheme (f : G.Hom H) : Scheme :=
  f.kernelGroupScheme.X.left

/-- The underlying scheme morphism of the kernel inclusion. -/
abbrev kernelιScheme (f : G.Hom H) : f.kernelScheme ⟶ G.carrier :=
  f.kernelι.hom.hom.left

/-- The structure morphism of the scheme-theoretic kernel. -/
abbrev kernelStructureMap (f : G.Hom H) :
    f.kernelScheme ⟶ Spec (.of k) := f.kernelGroupScheme.X.hom

/-- The kernel inclusion followed by the original group morphism is the
trivial group-scheme morphism. -/
theorem kernelι_comp (f : G.Hom H) :
    f.kernelι ≫ f = 0 :=
  Limits.kernel.condition f

/-- In the category of group objects, a kernel is the pullback of the
group morphism along the zero morphism from the trivial group. -/
theorem kernel_isPullback_trivial (f : G.Hom H) :
    IsPullback (Limits.kernel.ι f)
      (0 : Limits.kernel f ⟶ CategoryTheory.Grp.trivial
        (Over (Spec (.of k)))) f
      (0 : CategoryTheory.Grp.trivial (Over (Spec (.of k))) ⟶
        H.toGroupScheme) := by
  refine
    { w := by simp
      isLimit' := ⟨PullbackCone.IsLimit.mk _
        (fun s ↦ Limits.kernel.lift f s.fst (by simpa using s.condition))
        (by intro s; simp)
        (by intro s; apply Subsingleton.elim)
        (by
          intro s m hm _
          exact Fork.IsLimit.hom_ext (Limits.kernelIsKernel f)
            (hm.trans (Limits.kernel.lift_ι f s.fst _).symm))⟩ }

/-- After forgetting to schemes over the base, the kernel square is the
pullback of the group morphism along the unit section. -/
theorem kernel_isPullback_unit (f : G.Hom H) :
    IsPullback f.kernelι.hom.hom (toUnit _)
      f.hom.hom η[H.toGroupScheme.X] := by
  let F := CategoryTheory.Grp.forget (Over (Spec (.of k)))
  let h := f.kernel_isPullback_trivial.map F
  let e₃ : F.obj (CategoryTheory.Grp.trivial
      (Over (Spec (.of k)))) ≅ 𝟙_ (Over (Spec (.of k))) := Iso.refl _
  refine h.of_iso (Iso.refl _) (Iso.refl _) e₃ (Iso.refl _) ?_ ?_ ?_ ?_
  all_goals cat_disch

/-- The kernel inclusion is a morphism over the base field. -/
theorem kernelιScheme_comp_structureMap (f : G.Hom H) :
    f.kernelιScheme ≫ G.structureMap = f.kernelStructureMap := by
  simp

/-- The scheme-theoretic kernel is a closed subgroup scheme. -/
instance kernelι_isClosedImmersion (f : G.Hom H) :
    IsClosedImmersion f.kernelιScheme := by
  change IsClosedImmersion
    (((CategoryTheory.Grp.forget (Over (Spec (.of k)))).map
      (Limits.kernel.ι f)).left)
  change IsClosedImmersion
    (((CategoryTheory.Grp.forget (Over (Spec (.of k)))).map
      (Limits.equalizer.ι f 0)).left)
  rw [← equalizerComparison_comp_π f 0
    (CategoryTheory.Grp.forget (Over (Spec (.of k))))]
  rw [Over.comp_left]
  let e := asIso (equalizerComparison f 0
    (CategoryTheory.Grp.forget (Over (Spec (.of k)))))
  change IsClosedImmersion
    ((Comma.leftIso e).hom ≫
      (Limits.equalizer.ι
        ((CategoryTheory.Grp.forget (Over (Spec (.of k)))).map f)
        ((CategoryTheory.Grp.forget (Over (Spec (.of k)))).map 0)).left)
  have he : IsClosedImmersion (Comma.leftIso e).hom := inferInstance
  letI : IsSeparated
      ((CategoryTheory.Grp.forget (Over (Spec (.of k)))).obj
        H.toGroupScheme).hom := H.isSeparated
  have hι : IsClosedImmersion
      (Limits.equalizer.ι
        ((CategoryTheory.Grp.forget (Over (Spec (.of k)))).map f)
        ((CategoryTheory.Grp.forget (Over (Spec (.of k)))).map 0)).left :=
    isClosedImmersion_equalizer_ι_left
      ((CategoryTheory.Grp.forget (Over (Spec (.of k)))).map f)
      ((CategoryTheory.Grp.forget (Over (Spec (.of k)))).map 0)
  exact MorphismProperty.comp_mem _ _ _ he hι

/-- The scheme-theoretic kernel is locally of finite type over the base. -/
instance kernel_locallyOfFiniteType (f : G.Hom H) :
    LocallyOfFiniteType f.kernelStructureMap := by
  rw [← f.kernelιScheme_comp_structureMap]
  infer_instance

/-- The scheme-theoretic kernel is quasi-compact over the base. -/
instance kernel_quasiCompact (f : G.Hom H) :
    QuasiCompact f.kernelStructureMap := by
  rw [← f.kernelιScheme_comp_structureMap]
  infer_instance

/-- The scheme-theoretic kernel is separated over the base. -/
instance kernel_isSeparated (f : G.Hom H) :
    IsSeparated f.kernelStructureMap := by
  rw [← f.kernelιScheme_comp_structureMap]
  infer_instance

/-- The scheme-theoretic kernel, packaged as a finite-type algebraic
group.  It need not be connected; the affine-action argument uses its
identity component. -/
def kernelAlgebraicGroup (f : G.Hom H) : AlgebraicGroup k where
  toGroupScheme := f.kernelGroupScheme
  locallyOfFiniteType := f.kernel_locallyOfFiniteType
  quasiCompact := f.kernel_quasiCompact
  isSeparated := f.kernel_isSeparated

/-- The inclusion of the packaged scheme-theoretic kernel. -/
def kernelInclusion (f : G.Hom H) : f.kernelAlgebraicGroup.Hom G :=
  f.kernelι

/-- The inclusion of a scheme-theoretic group kernel is a normal subgroup
morphism. -/
instance kernelInclusion_normal (f : G.Hom H) :
    CategoryTheory.IsMonHom.Normal f.kernelInclusion.hom.hom :=
  CategoryTheory.IsMonHom.Normal.of_isPullback_η f.hom.hom
    f.kernel_isPullback_unit

@[simp] theorem kernelInclusion_schemeHom (f : G.Hom H) :
    f.kernelInclusion.schemeHom = f.kernelιScheme := rfl

end AlgebraicGroup.Hom

end

end AclGeom
