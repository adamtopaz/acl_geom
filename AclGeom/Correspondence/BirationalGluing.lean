/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Birational.Composition

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

end BirationalGluing

end

end AclGeom
