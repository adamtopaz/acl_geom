/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Properties

/-!
# Scheme-theoretic consequences of Weil chart gluing

This module supplies the gluing layer used in blueprint Theorem 8.2.  It
starts with Mathlib's explicit `Scheme.GlueData`, so the output is an
actual scheme obtained from open charts and transition isomorphisms.

Compatible chart morphisms descend to the glued scheme.  In particular,
compatible structure morphisms to a base scheme make the gluing relative
over that base.  Local finite type then descends from the charts, while a
finite atlas of quasi-compact chart morphisms is quasi-compact.  Finally,
integral charts with nonempty pairwise overlaps glue to an integral
scheme.  These are precisely the local finite-type and irreducibility
arguments in Weil's construction; separatedness and the finite atlas for
the eventual group are established only after multiplication and inverse
have been glued.

This module is part of the formalization of the
Evans--Hrushovski--Gismatullin reconstruction theorem; the source of truth
is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open CategoryTheory CategoryTheory.Limits Function
open AlgebraicGeometry

universe u

namespace WeilGluing

variable (D : Scheme.GlueData.{u})

/-- A family of morphisms on the charts is compatible when the two maps
from every transition overlap agree. -/
def CompatibleMaps {X : Scheme.{u}} (g : ∀ i, D.U i ⟶ X) : Prop :=
  ∀ i j, D.f i j ≫ g i = D.t i j ≫ D.f j i ≫ g j

/-- Compatible morphisms from the charts descend to the glued scheme. -/
def desc {X : Scheme.{u}} (g : ∀ i, D.U i ⟶ X)
    (hg : CompatibleMaps D g) : D.glued ⟶ X := by
  fapply Multicoequalizer.desc
  · exact g
  · rintro ⟨i, j⟩
    change D.f i j ≫ g i = (D.t i j ≫ D.f j i) ≫ g j
    simpa only [Category.assoc] using hg i j

/-- The descended morphism restricts to the prescribed map on every
chart. -/
@[simp, reassoc]
theorem ι_desc {X : Scheme.{u}} (g : ∀ i, D.U i ⟶ X)
    (hg : CompatibleMaps D g) (i : D.J) :
    D.ι i ≫ desc D g hg = g i :=
  Multicoequalizer.π_desc _ _ _ _ _

/-- Morphisms out of a glued scheme are determined on its charts. -/
theorem hom_ext {X : Scheme.{u}} (f g : D.glued ⟶ X)
    (h : ∀ i, D.ι i ≫ f = D.ι i ≫ g) : f = g := by
  apply Multicoequalizer.hom_ext
  exact h

/-- The structure morphism obtained by gluing compatible chart morphisms
to a fixed base scheme. -/
abbrev toBase {S : Scheme.{u}} (s : ∀ i, D.U i ⟶ S)
    (hs : CompatibleMaps D s) : D.glued ⟶ S :=
  desc D s hs

/-- Local finite type over the base descends from every chart of a
scheme gluing. -/
instance toBase_locallyOfFiniteType {S : Scheme.{u}}
    (s : ∀ i, D.U i ⟶ S) (hs : CompatibleMaps D s)
    [∀ i, LocallyOfFiniteType (s i)] :
    LocallyOfFiniteType (toBase D s hs) := by
  apply IsZariskiLocalAtSource.of_openCover D.openCover
  intro i
  change LocallyOfFiniteType (D.ι i ≫ toBase D s hs)
  rw [ι_desc D s hs i]
  infer_instance

/-- A finite gluing of charts quasi-compact over the base is
quasi-compact over the base. -/
instance toBase_quasiCompact {S : Scheme.{u}}
    (s : ∀ i, D.U i ⟶ S) (hs : CompatibleMaps D s)
    [Finite D.J] [∀ i, QuasiCompact (s i)] :
    QuasiCompact (toBase D s hs) := by
  constructor
  intro U hU hUc
  have hpreimage :
      toBase D s hs ⁻¹' U =
        ⋃ i, D.ι i '' ((s i) ⁻¹' U) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
      refine Set.mem_iUnion.2 ⟨i, ⟨y, ?_, rfl⟩⟩
      have heq : toBase D s hs (D.ι i y) = s i y := by
        rw [← Scheme.Hom.comp_apply, ι_desc D s hs i]
      change toBase D s hs (D.ι i y) ∈ U at hx
      change s i y ∈ U
      rwa [heq] at hx
    · intro hx
      obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
      have heq : toBase D s hs (D.ι i y) = s i y := by
        rw [← Scheme.Hom.comp_apply, ι_desc D s hs i]
      change s i y ∈ U at hy
      change toBase D s hs (D.ι i y) ∈ U
      rwa [heq]
  rw [hpreimage]
  apply isCompact_iUnion
  intro i
  have hi : IsCompact ((s i) ⁻¹' U) :=
    QuasiCompact.isCompact_preimage U hU hUc
  exact hi.image (D.ι i).continuous

/-- The glued scheme is reduced when every chart is reduced. -/
instance isReduced [∀ i, IsReduced (D.U i)] : IsReduced D.glued := by
  letI (i : D.openCover.I₀) : IsReduced (D.openCover.X i) :=
    show IsReduced (D.U i) from inferInstance
  exact IsReduced.of_openCover D.glued D.openCover

/-- If every chart is irreducible and every pairwise overlap is nonempty,
then the glued topological space is preirreducible. -/
instance preirreducibleSpace
    [∀ i, IrreducibleSpace (D.U i)]
    [∀ i j, Nonempty (D.V (i, j)).carrier] :
    PreirreducibleSpace D.glued := by
  let U : D.J → TopologicalSpace.Opens D.glued :=
    fun i ↦ (D.ι i).opensRange
  have hU (i : D.J) : IsPreirreducible (U i : Set D.glued) := by
    change IsPreirreducible (Set.range (D.ι i))
    rw [← Set.image_univ]
    exact PreirreducibleSpace.isPreirreducible_univ.image
      (D.ι i) (D.ι i).continuous.continuousOn
  have hpair : Pairwise ((¬ Disjoint · ·) on U) := by
    intro i j hij
    change ¬ Disjoint (U i) (U j)
    rw [disjoint_iff]
    intro hdisj
    let x : (D.V (i, j)).carrier := Classical.choice inferInstance
    have hx : D.ι i (D.f i j x) ∈ U i ∧
        D.ι i (D.f i j x) ∈ U j := by
      constructor
      · exact ⟨D.f i j x, rfl⟩
      · refine ⟨D.f j i (D.t i j x), ?_⟩
        change (D.t i j ≫ D.f j i ≫ D.ι j) x =
          (D.f i j ≫ D.ι i) x
        rw [D.glue_condition]
    have : D.ι i (D.f i j x) ∈ U i ⊓ U j := hx
    rw [hdisj] at this
    exact this
  exact PreirreducibleSpace.of_isOpenCover hpair
    D.openCover.isOpenCover_opensRange (fun i ↦
      (isPreirreducible_iff_preirreducibleSpace.mp (hU i)))

/-- A nonempty gluing has a nonempty underlying topological space when
its charts are nonempty. -/
instance nonemptyGlued [Nonempty D.J] [∀ i, Nonempty (D.U i).carrier] :
    Nonempty D.glued.carrier := by
  let i : D.J := Classical.choice inferInstance
  let x : (D.U i).carrier := Classical.choice inferInstance
  exact ⟨D.ι i x⟩

/-- A nonempty gluing of irreducible charts with nonempty pairwise
overlaps is irreducible. -/
instance irreducibleSpace [Nonempty D.J]
    [∀ i, IrreducibleSpace (D.U i)]
    [∀ i j, Nonempty (D.V (i, j)).carrier] :
    IrreducibleSpace D.glued where
  toPreirreducibleSpace := inferInstance
  toNonempty := inferInstance

/-- Integral charts with nonempty pairwise overlaps glue to an integral
scheme. -/
instance isIntegral [Nonempty D.J] [∀ i, IsIntegral (D.U i)]
    [∀ i j, Nonempty (D.V (i, j)).carrier] : IsIntegral D.glued := by
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨inferInstance, inferInstance⟩

end WeilGluing

end

end AclGeom
