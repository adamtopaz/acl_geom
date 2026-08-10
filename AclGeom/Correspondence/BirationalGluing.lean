/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Birational.Composition
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Dense-open isomorphisms from inverse rational maps

This module supplies the bridge from birational algebra to Weil gluing.  Two
dominant partial maps whose composites are literally the inclusion of their
domains can be restricted once more to mutually inverse maps.  Consequently,
mutually inverse dominant rational maps between integral separated schemes
produce a concrete `Scheme.PartialIso` between dense open subschemes.

The second construction is the form used by the normalized correspondence
charts: field equivalences first produce inverse rational maps, and this file
turns those maps into the dense-open transition isomorphisms required by
`Scheme.GlueData`.

This module is part of the formalization of the
Evans--Hrushovski--Gismatullin reconstruction theorem; the source of truth
is `sources/blueprint.tex`.
-/

open CategoryTheory
open AlgebraicGeometry

namespace AclGeom

noncomputable section

universe u

namespace BirationalGluing

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]

/-- Mutually inverse dominant partial maps restrict to an isomorphism between
dense open subschemes.  The hypotheses ask for equality of actual scheme
morphisms on the pullback domains of the two composites. -/
def partialIsoOfMutualInversePartialMaps
    (f : X.PartialMap Y) [IsDominant f.hom]
    (g : Y.PartialMap X) [IsDominant g.hom]
    (hfg : (f.comp g).hom = (f.comp g).domain.ι)
    (hgf : (g.comp f).hom = (g.comp f).domain.ι) :
    X.PartialIso Y := by
  let fPre : f.domain.toScheme.Opens := f.hom ⁻¹ᵁ g.domain
  let gPre : g.domain.toScheme.Opens := g.hom ⁻¹ᵁ f.domain
  let U : X.Opens := f.domain.ι ''ᵁ fPre
  let V : Y.Opens := g.domain.ι ''ᵁ gPre
  let uToF : U.toScheme ⟶ f.domain.toScheme :=
    (f.domain.ι.isoImage fPre).inv ≫ fPre.ι
  let fToG : U.toScheme ⟶ g.domain.toScheme :=
    (f.domain.ι.isoImage fPre).inv ≫ f.hom ∣_ g.domain
  let vToG : V.toScheme ⟶ g.domain.toScheme :=
    (g.domain.ι.isoImage gPre).inv ≫ gPre.ι
  let gToF : V.toScheme ⟶ f.domain.toScheme :=
    (g.domain.ι.isoImage gPre).inv ≫ g.hom ∣_ f.domain
  have hu : uToF ≫ f.domain.ι = U.ι := by
    exact f.domain.ι.isoImage_inv_ι fPre
  have hv : vToG ≫ g.domain.ι = V.ι := by
    exact g.domain.ι.isoImage_inv_ι gPre
  have hfg' : fToG ≫ g.hom = U.ι := by
    have h := hfg
    dsimp [Scheme.PartialMap.comp, fToG, U, fPre] at h ⊢
    simpa only [Category.assoc] using h
  have hgf' : gToF ≫ f.hom = V.ι := by
    have h := hgf
    dsimp [Scheme.PartialMap.comp, gToF, V, gPre] at h ⊢
    simpa only [Category.assoc] using h
  have hsqU : uToF ≫ f.domain.ι = fToG ≫ g.hom := by
    rw [hu, hfg']
  let liftU : U.toScheme ⟶ gPre.toScheme :=
    (isPullback_morphismRestrict g.hom f.domain).lift uToF fToG hsqU
  let liftV : V.toScheme ⟶ fPre.toScheme :=
    (isPullback_morphismRestrict f.hom g.domain).lift vToG gToF (by
      rw [hv, hgf'])
  let F : U.toScheme ⟶ V.toScheme :=
    liftU ≫ (g.domain.ι.isoImage gPre).hom
  let G : V.toScheme ⟶ U.toScheme :=
    liftV ≫ (f.domain.ι.isoImage fPre).hom
  have hFv : F ≫ vToG = fToG := by
    dsimp [F, vToG, liftU]
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact (isPullback_morphismRestrict g.hom f.domain).lift_snd
      uToF fToG hsqU
  have hGu : G ≫ uToF = gToF := by
    dsimp [G, uToF, liftV]
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact (isPullback_morphismRestrict f.hom g.domain).lift_snd
      vToG gToF (by rw [hv, hgf'])
  have hGι : G ≫ U.ι = vToG ≫ g.hom := by
    calc
      G ≫ U.ι = (G ≫ uToF) ≫ f.domain.ι := by
        simp only [Category.assoc, hu]
      _ = gToF ≫ f.domain.ι := by rw [hGu]
      _ = vToG ≫ g.hom := by
        dsimp [gToF, vToG]
        rw [Category.assoc, morphismRestrict_ι]
        simp only [Category.assoc]
        rfl
  have hFι : F ≫ V.ι = uToF ≫ f.hom := by
    calc
      F ≫ V.ι = (F ≫ vToG) ≫ g.domain.ι := by
        simp only [Category.assoc, hv]
      _ = fToG ≫ g.domain.ι := by rw [hFv]
      _ = uToF ≫ f.hom := by
        dsimp [fToG, uToF]
        rw [Category.assoc, morphismRestrict_ι]
        simp only [Category.assoc]
        rfl
  refine
    { source := U
      dense_source := (f.comp g).dense_domain
      target := V
      dense_target := (g.comp f).dense_domain
      iso :=
        { hom := F
          inv := G
          hom_inv_id := ?_
          inv_hom_id := ?_ } }
  · rw [← cancel_mono U.ι]
    rw [Category.assoc, hGι, ← Category.assoc, hFv, hfg', Category.id_comp]
  · rw [← cancel_mono V.ι]
    rw [Category.assoc, hFι, ← Category.assoc, hGu, hgf', Category.id_comp]

/-- Mutually inverse dominant rational maps between integral separated schemes
are represented by an isomorphism between concrete dense open subschemes. -/
def partialIsoOfMutualInverseRationalMaps
    [IsIntegral X] [IsIntegral Y] [X.IsSeparated] [Y.IsSeparated]
    (f : X ⤏ Y) [f.IsDominant]
    (g : Y ⤏ X) [g.IsDominant]
    (hfg : f.comp g = Scheme.RationalMap.id X)
    (hgf : g.comp f = Scheme.RationalMap.id Y) :
    X.PartialIso Y := by
  let F := f.toPartialMap
  let G := g.toPartialMap
  letI : IsDominant F.hom := by
    rw [← F.isDominant_toRationalMap_iff]
    simpa [F] using (inferInstance : f.IsDominant)
  letI : IsDominant G.hom := by
    rw [← G.isDominant_toRationalMap_iff]
    simpa [G] using (inferInstance : g.IsDominant)
  have hFGrat : (F.comp G).toRationalMap = Scheme.RationalMap.id X := by
    rw [← Scheme.RationalMap.toRationalMap_comp]
    simpa [F, G] using hfg
  have hGFrat : (G.comp F).toRationalMap = Scheme.RationalMap.id Y := by
    rw [← Scheme.RationalMap.toRationalMap_comp]
    simpa [F, G] using hgf
  have hFG : (F.comp G).hom = (F.comp G).domain.ι := by
    have he := Scheme.PartialMap.toRationalMap_eq_iff.mp hFGrat
    have hh := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
      (S := ⊤_ Scheme)).mp he
    simpa using hh
  have hGF : (G.comp F).hom = (G.comp F).domain.ι := by
    have he := Scheme.PartialMap.toRationalMap_eq_iff.mp hGFrat
    have hh := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
      (S := ⊤_ Scheme)).mp he
    simpa using hh
  exact partialIsoOfMutualInversePartialMaps F G hFG hGF

/-- The two indices of the gluing datum attached to one partial
isomorphism. -/
inductive TwoChartIndex : Type u
  | source
  | target
  deriving DecidableEq

private theorem TwoChartIndex.no_three_distinct
    (i j k : TwoChartIndex)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : False := by
  cases i <;> cases j <;> cases k <;> simp_all

/-- The categorical two-chart gluing datum determined by a partial
isomorphism.  Its only off-diagonal overlaps are the source and target
opens, and its transition maps are the two directions of the displayed
isomorphism. -/
def partialIsoGlueData' (e : X.PartialIso Y) :
    CategoryTheory.GlueData'.{u, u + 1} Scheme.{u} where
  J := TwoChartIndex
  U
    | .source => X
    | .target => Y
  V i j h := by
    cases i <;> cases j
    · exact (h rfl).elim
    · exact e.source.toScheme
    · exact e.target.toScheme
    · exact (h rfl).elim
  f i j h := by
    cases i <;> cases j
    · exact (h rfl).elim
    · exact e.source.ι
    · exact e.target.ι
    · exact (h rfl).elim
  f_mono i j h := by
    cases i <;> cases j
    · exact (h rfl).elim
    · infer_instance
    · infer_instance
    · exact (h rfl).elim
  f_hasPullback i j k hij hik := by infer_instance
  t i j h := by
    cases i <;> cases j
    · exact (h rfl).elim
    · exact e.iso.hom
    · exact e.iso.inv
    · exact (h rfl).elim
  t' i j k hij hik hjk := by
    exact (TwoChartIndex.no_three_distinct i j k hij hik hjk).elim
  t_fac i j k hij hik hjk := by
    exact (TwoChartIndex.no_three_distinct i j k hij hik hjk).elim
  t_inv i j hij := by
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact e.iso.hom_inv_id
    · exact e.iso.inv_hom_id
    · exact (hij rfl).elim
  cocycle i j k hij hik hjk := by
    exact (TwoChartIndex.no_three_distinct i j k hij hik hjk).elim

/-- A partial isomorphism between dense open subschemes determines an
actual two-chart `Scheme.GlueData`. -/
def partialIsoGlueData (e : X.PartialIso Y) : Scheme.GlueData where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (partialIsoGlueData' e)
  f_open i j := by
    classical
    change IsOpenImmersion ((partialIsoGlueData' e).f' i j)
    cases i <;> cases j
    · delta CategoryTheory.GlueData'.f'
      split
      · infer_instance
      · rename_i h
        exact (h rfl).elim
    · delta CategoryTheory.GlueData'.f'
      split
      · rename_i h
        exact TwoChartIndex.noConfusion h
      · delta partialIsoGlueData'
        infer_instance
    · delta CategoryTheory.GlueData'.f'
      split
      · rename_i h
        exact TwoChartIndex.noConfusion h
      · delta partialIsoGlueData'
        infer_instance
    · delta CategoryTheory.GlueData'.f'
      split
      · infer_instance
      · rename_i h
        exact (h rfl).elim

end BirationalGluing

end

end AclGeom
