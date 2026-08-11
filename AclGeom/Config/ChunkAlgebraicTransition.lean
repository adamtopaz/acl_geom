/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkAlgebraicChart
import AclGeom.Correspondence.FiniteExtensionTransition

/-!
# Dense-open transitions for normalized Ψ charts

The normal-cover equivalence between two realizations of the same scalar
projection locus is promoted to an equivalence over the ground field.  The
generic finite-extension transition construction then clears its coordinate
denominators and produces a dominant partial map on one dense principal open.
The same field equivalence and its inverse induce mutually inverse rational
maps, hence an actual isomorphism between dense open chart subschemes.
Finite reference-normalized families are restricted to one common dense
source and assembled into an actual multi-chart scheme atlas.

This is instantiated for all four repeated rank-two blocks of a lifted
four-arrow Ψ diagram.  Thus the branch comparisons at `s`, `u`, `sA`, and
`uB` now act on concrete integral affine charts rather than only on abstract
normal fields.

This module is part of the formalization of the
Evans--Hrushovski--Gismatullin reconstruction theorem; the source of truth
is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open IntermediateField
open AlgebraicGeometry

universe u

namespace QWitness

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  [IsAlgClosed K]

/-- The semilinear normal-cover equivalence between arbitrary generic
realizations of one scalar projection locus, upgraded to a ground-field
algebra equivalence. -/
noncomputable def rankTwoScalarLocusNormalCoverAlgEquiv
    {p q : Fin 2 → K} {x y : K}
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range q))
    (hxy : idealOf k (rankTwoScalarTuple p x) =
      idealOf k (rankTwoScalarTuple q y)) :
    rankTwoScalarNormalField (k := k) p x ≃ₐ[k]
      rankTwoScalarNormalField (k := k) q y :=
  { rankTwoScalarNormalCoverEquivOfIdealEq hx hy hxy with
    commutes' := fun r ↦ by
      rw [IsScalarTower.algebraMap_apply k
          (rankTwoParameterField (k := k) p)
          (rankTwoScalarNormalField (k := k) p x),
        IsScalarTower.algebraMap_apply k
          (rankTwoParameterField (k := k) q)
          (rankTwoScalarNormalField (k := k) q y)]
      calc
        _ = algebraMap (↥(rankTwoParameterField (k := k) q))
              (rankTwoScalarNormalField (k := k) q y)
              (locusFunctionFieldEquivOfIdealEq
                (rankTwoParameter_ideal_eq_of_scalar_ideal_eq hxy)
                (algebraMap k
                  (rankTwoParameterField (k := k) p) r)) :=
          rankTwoScalarNormalCoverEquivOfIdealEq_algebraMap
            hx hy hxy (algebraMap k
              (rankTwoParameterField (k := k) p) r)
        _ = _ := by
          congr 1
          exact (locusFunctionFieldEquivOfIdealEq
            (rankTwoParameter_ideal_eq_of_scalar_ideal_eq hxy)).commutes r }

omit [IsAlgClosed K] in
/-- The literal selected scalar coordinate in its concrete normal cover. -/
def rankTwoScalarSelectedNormalElement
    (p : Fin 2 → K) (x : K) :
    rankTwoScalarNormalField (k := k) p x :=
  FiniteCover.selectedEmbedding
    (rankTwoParameterField_le_rankTwoScalarField (k := k) p x)
    ⟨x, by
      change x ∈ rankTwoScalarField (k := k) p x
      exact subset_adjoin k _ (Set.mem_range_self (2 : Fin 3))⟩

/-- Equal scalar loci have a semilinear normal-cover equivalence corrected
to carry the literal selected scalar branch to the literal selected target
branch. -/
noncomputable def rankTwoScalarLocusBasedNormalEquiv
    {p q : Fin 2 → K} {x y : K}
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range q))
    (hxy : idealOf k (rankTwoScalarTuple p x) =
      idealOf k (rankTwoScalarTuple q y)) :
    FiniteCoverBasedNormalEquiv
      (rankTwoParameterField_le_rankTwoScalarField (k := k) p x)
      (rankTwoParameterField_le_rankTwoScalarField (k := k) q y)
      (rankTwoScalarExtensionEquivOfIdealEq (k := k) hxy) := by
  let hp := rankTwoParameterField_le_rankTwoScalarField (k := k) p x
  let hq := rankTwoParameterField_le_rankTwoScalarField (k := k) q y
  apply finiteCoverBasedNormalEquivOfExtensionEquiv hp hq
    (rankTwoScalarExtension_finiteDimensional (k := k) (K := K) hy)
    (rankTwoScalarExtensionEquivOfIdealEq (k := k) hxy)
    (rankTwoScalarNormalCoverEquivOfIdealEq hx hy hxy)
  apply RingHom.ext
  intro z
  exact rankTwoScalarNormalCoverEquivOfIdealEq_algebraMap hx hy hxy z

omit [IsAlgClosed K] in
@[simp] theorem rankTwoScalarSelectedNormalElement_val
    (p : Fin 2 → K) (x : K) :
    (rankTwoScalarSelectedNormalElement (k := k) p x : K) = x :=
  rfl

/-- Ground-field algebra equivalence underlying the based scalar-locus
normal-cover transport. -/
noncomputable def rankTwoScalarLocusBasedNormalCoverAlgEquiv
    {p q : Fin 2 → K} {x y : K}
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range q))
    (hxy : idealOf k (rankTwoScalarTuple p x) =
      idealOf k (rankTwoScalarTuple q y)) :
    rankTwoScalarNormalField (k := k) p x ≃ₐ[k]
      rankTwoScalarNormalField (k := k) q y :=
  { (rankTwoScalarLocusBasedNormalEquiv hx hy hxy).toRingEquiv with
    commutes' := fun r ↦ by
      rw [IsScalarTower.algebraMap_apply k
          (rankTwoParameterField (k := k) p)
          (rankTwoScalarNormalField (k := k) p x),
        IsScalarTower.algebraMap_apply k
          (rankTwoParameterField (k := k) q)
          (rankTwoScalarNormalField (k := k) q y)]
      calc
        _ = algebraMap (↥(rankTwoParameterField (k := k) q))
              (rankTwoScalarNormalField (k := k) q y)
              ((rankTwoScalarExtensionEquivOfIdealEq
                (k := k) hxy).baseEquiv
                (algebraMap k
                  (rankTwoParameterField (k := k) p) r)) :=
          DFunLike.congr_fun
            (rankTwoScalarLocusBasedNormalEquiv hx hy hxy).commutes
            (algebraMap k (rankTwoParameterField (k := k) p) r)
        _ = _ := by
          congr 1
          exact (rankTwoScalarExtensionEquivOfIdealEq
            (k := k) hxy).baseEquiv.commutes r }

/-- The based normal-cover equivalence remains semilinear over the
canonical parameter-field equivalence. -/
@[simp] theorem rankTwoScalarLocusBasedNormalCoverAlgEquiv_algebraMap
    {p q : Fin 2 → K} {x y : K}
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range q))
    (hxy : idealOf k (rankTwoScalarTuple p x) =
      idealOf k (rankTwoScalarTuple q y))
    (v : rankTwoParameterField (k := k) p) :
    rankTwoScalarLocusBasedNormalCoverAlgEquiv hx hy hxy
        (algebraMap (↥(rankTwoParameterField (k := k) p))
          (rankTwoScalarNormalField (k := k) p x) v) =
      algebraMap (↥(rankTwoParameterField (k := k) q))
        (rankTwoScalarNormalField (k := k) q y)
        ((rankTwoScalarExtensionEquivOfIdealEq
          (k := k) hxy).baseEquiv v) :=
  DFunLike.congr_fun
    (rankTwoScalarLocusBasedNormalEquiv hx hy hxy).commutes v

/-- The based scalar-locus transport sends the selected scalar coordinate
to the selected scalar coordinate, not merely to an unspecified conjugate. -/
@[simp] theorem rankTwoScalarLocusBasedNormalCoverAlgEquiv_selected
    {p q : Fin 2 → K} {x y : K}
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range q))
    (hxy : idealOf k (rankTwoScalarTuple p x) =
      idealOf k (rankTwoScalarTuple q y)) :
    rankTwoScalarLocusBasedNormalCoverAlgEquiv hx hy hxy
        (rankTwoScalarSelectedNormalElement (k := k) p x) =
      rankTwoScalarSelectedNormalElement (k := k) q y := by
  let sx : rankTwoScalarExtension (k := k) p x :=
    ⟨x, by
      change x ∈ rankTwoScalarField (k := k) p x
      exact subset_adjoin k _ (Set.mem_range_self (2 : Fin 3))⟩
  have hmap :=
    (rankTwoScalarLocusBasedNormalEquiv hx hy hxy).map_selected_apply sx
  have htotal :
      (rankTwoScalarExtensionEquivOfIdealEq (k := k) hxy).totalEquiv sx =
        (⟨y, by
          change y ∈ rankTwoScalarField (k := k) q y
          exact subset_adjoin k _ (Set.mem_range_self (2 : Fin 3))⟩ :
            rankTwoScalarExtension (k := k) q y) := by
    exact locusFunctionFieldEquivOfIdealEq_apply hxy 2
  rw [htotal] at hmap
  exact hmap

/-- Normalize transitions between arbitrary realizations of one projection
locus through a fixed generic realization.  This removes all dependence on
independently chosen normal-closure lifts. -/
noncomputable def rankTwoScalarLocusReferenceAlgEquiv
    {r p q : Fin 2 → K} {z x y : K}
    (hz : z ∈ racl k (Set.range r))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range q))
    (hrx : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple q y)) :
    rankTwoScalarNormalField (k := k) p x ≃ₐ[k]
      rankTwoScalarNormalField (k := k) q y :=
  (rankTwoScalarLocusBasedNormalCoverAlgEquiv hz hx hrx).symm.trans
    (rankTwoScalarLocusBasedNormalCoverAlgEquiv hz hy hry)

@[simp] theorem rankTwoScalarLocusReferenceAlgEquiv_self
    {r p : Fin 2 → K} {z x : K}
    (hz : z ∈ racl k (Set.range r))
    (hx : x ∈ racl k (Set.range p))
    (hrx : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple p x)) :
    rankTwoScalarLocusReferenceAlgEquiv hz hx hx hrx hrx =
      AlgEquiv.refl := by
  unfold rankTwoScalarLocusReferenceAlgEquiv
  ext t
  simp

@[simp] theorem rankTwoScalarLocusReferenceAlgEquiv_symm
    {r p q : Fin 2 → K} {z x y : K}
    (hz : z ∈ racl k (Set.range r))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range q))
    (hrx : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple q y)) :
    (rankTwoScalarLocusReferenceAlgEquiv hz hx hy hrx hry).symm =
      rankTwoScalarLocusReferenceAlgEquiv hz hy hx hry hrx := by
  unfold rankTwoScalarLocusReferenceAlgEquiv
  ext t
  simp

@[simp] theorem rankTwoScalarLocusReferenceAlgEquiv_trans
    {r p q v : Fin 2 → K} {z x y u : K}
    (hz : z ∈ racl k (Set.range r))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range q))
    (hu : u ∈ racl k (Set.range v))
    (hrx : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple q y))
    (hru : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple v u)) :
    (rankTwoScalarLocusReferenceAlgEquiv hz hx hy hrx hry).trans
        (rankTwoScalarLocusReferenceAlgEquiv hz hy hu hry hru) =
      rankTwoScalarLocusReferenceAlgEquiv hz hx hu hrx hru := by
  unfold rankTwoScalarLocusReferenceAlgEquiv
  ext t
  simp

/-- The strict reference-normalized field comparison between two arbitrary
generic realizations of one projection locus, spread to a rational map
between their affine normal-cover models. -/
noncomputable def rankTwoScalarLocusReferenceRationalMap
    {r p q : Fin 2 → K} {z x y : K}
    (hz : z ∈ racl k (Set.range r))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range q))
    (hrx : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple q y)) :
    Scheme.RationalMap
      (rankTwoScalarAlgebraicChart (k := k) p x hx)
      (rankTwoScalarAlgebraicChart (k := k) q y hy) := by
  letI : FiniteDimensional (↥(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p x) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hx
  letI : FiniteDimensional (↥(rankTwoParameterField (k := k) q))
      (rankTwoScalarNormalField (k := k) q y) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hy
  unfold rankTwoScalarAlgebraicChart
  exact FiniteExtensionTransition.rationalMap
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates (k := k) q)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) q)
    (rankTwoScalarLocusReferenceAlgEquiv hz hx hy hrx hry)

/-- The function-field equivalence underlying a reference-normalized
scalar-chart transition. -/
noncomputable def rankTwoScalarLocusReferenceFunctionFieldRingEquiv
    {r p q : Fin 2 → K} {z x y : K}
    (hz : z ∈ racl k (Set.range r))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range q))
    (hrx : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple q y)) :
    (rankTwoScalarAlgebraicChart (k := k) p x hx).functionField ≃+*
      (rankTwoScalarAlgebraicChart (k := k) q y hy).functionField := by
  letI := rankTwoScalarNormalField_finiteDimensional (k := k) hx
  letI := rankTwoScalarNormalField_finiteDimensional (k := k) hy
  exact (FiniteExtensionTransition.functionFieldAlgEquiv
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates (k := k) q)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) q)
    (rankTwoScalarLocusReferenceAlgEquiv hz hx hy hrx hry)).toRingEquiv

/-- The generic-point morphism of a reference-normalized scalar-chart
transition is the one induced by its explicit function-field equivalence. -/
theorem rankTwoScalarLocusReferenceRationalMap_fromFunctionField
    {r p q : Fin 2 → K} {z x y : K}
    (hz : z ∈ racl k (Set.range r))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range q))
    (hrx : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple q y)) :
    (rankTwoScalarLocusReferenceRationalMap
      hz hx hy hrx hry).fromFunctionField =
      Scheme.functionFieldMorphism
        (rankTwoScalarLocusReferenceFunctionFieldRingEquiv
          hz hx hy hrx hry) := by
  letI := rankTwoScalarNormalField_finiteDimensional (k := k) hx
  letI := rankTwoScalarNormalField_finiteDimensional (k := k) hy
  unfold rankTwoScalarLocusReferenceRationalMap
    rankTwoScalarLocusReferenceFunctionFieldRingEquiv
    rankTwoScalarAlgebraicChart
  exact FiniteExtensionTransition.rationalMap_fromFunctionField
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates (k := k) q)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) q)
    (rankTwoScalarLocusReferenceAlgEquiv hz hx hy hrx hry)

instance rankTwoScalarLocusReferenceRationalMap_isDominant
    {r p q : Fin 2 → K} {z x y : K}
    (hz : z ∈ racl k (Set.range r))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range q))
    (hrx : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple q y)) :
    (rankTwoScalarLocusReferenceRationalMap
      hz hx hy hrx hry).IsDominant := by
  letI : FiniteDimensional (↥(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p x) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hx
  letI : FiniteDimensional (↥(rankTwoParameterField (k := k) q))
      (rankTwoScalarNormalField (k := k) q y) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hy
  change (FiniteExtensionTransition.rationalMap
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates (k := k) q)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) q)
    (rankTwoScalarLocusReferenceAlgEquiv
      hz hx hy hrx hry)).IsDominant
  infer_instance

/-- Reference-normalized rational comparisons between arbitrary generic
realizations obey a strict transitive cocycle. -/
theorem rankTwoScalarLocusReferenceRationalMap_comp
    {r p q v : Fin 2 → K} {z x y u : K}
    (hz : z ∈ racl k (Set.range r))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range q))
    (hu : u ∈ racl k (Set.range v))
    (hrx : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple q y))
    (hru : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple v u)) :
    (rankTwoScalarLocusReferenceRationalMap
      hz hx hy hrx hry).comp
        (rankTwoScalarLocusReferenceRationalMap
          hz hy hu hry hru) =
      rankTwoScalarLocusReferenceRationalMap
        hz hx hu hrx hru := by
  letI : FiniteDimensional (↥(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p x) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hx
  letI : FiniteDimensional (↥(rankTwoParameterField (k := k) q))
      (rankTwoScalarNormalField (k := k) q y) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hy
  letI : FiniteDimensional (↥(rankTwoParameterField (k := k) v))
      (rankTwoScalarNormalField (k := k) v u) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hu
  change (FiniteExtensionTransition.rationalMap
      (rankTwoParameterCoordinates (k := k) p)
      (rankTwoParameterCoordinates (k := k) q)
      (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
      (rankTwoParameterCoordinates_adjoin_eq_top (k := k) q)
      (rankTwoScalarLocusReferenceAlgEquiv
        hz hx hy hrx hry)).comp
      (FiniteExtensionTransition.rationalMap
        (rankTwoParameterCoordinates (k := k) q)
        (rankTwoParameterCoordinates (k := k) v)
        (rankTwoParameterCoordinates_adjoin_eq_top (k := k) q)
        (rankTwoParameterCoordinates_adjoin_eq_top (k := k) v)
        (rankTwoScalarLocusReferenceAlgEquiv
          hz hy hu hry hru)) =
    FiniteExtensionTransition.rationalMap
      (rankTwoParameterCoordinates (k := k) p)
      (rankTwoParameterCoordinates (k := k) v)
      (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
      (rankTwoParameterCoordinates_adjoin_eq_top (k := k) v)
      (rankTwoScalarLocusReferenceAlgEquiv
        hz hx hu hrx hru)
  rw [FiniteExtensionTransition.rationalMap_comp]
  rw [rankTwoScalarLocusReferenceAlgEquiv_trans]

/-- Arbitrary generic realizations of one scalar projection locus have
isomorphic dense open subschemes in their affine normal-cover models. -/
noncomputable def rankTwoScalarLocusReferencePartialIso
    {r p q : Fin 2 → K} {z x y : K}
    (hz : z ∈ racl k (Set.range r))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range q))
    (hrx : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple q y)) :
    (rankTwoScalarAlgebraicChart (k := k) p x hx).PartialIso
      (rankTwoScalarAlgebraicChart (k := k) q y hy) := by
  letI : FiniteDimensional (↥(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p x) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hx
  letI : FiniteDimensional (↥(rankTwoParameterField (k := k) q))
      (rankTwoScalarNormalField (k := k) q y) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hy
  unfold rankTwoScalarAlgebraicChart
  exact FiniteExtensionTransition.partialIso
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates (k := k) q)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) q)
    (rankTwoScalarLocusReferenceAlgEquiv hz hx hy hrx hry)

/-- The dense-open comparison between generic locus models is a morphism
over the ground-field spectrum. -/
theorem rankTwoScalarLocusReferencePartialIso_isOver
    {r p q : Fin 2 → K} {z x y : K}
    (hz : z ∈ racl k (Set.range r))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range q))
    (hrx : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple r z) =
      idealOf k (rankTwoScalarTuple q y)) :
    (rankTwoScalarLocusReferencePartialIso
      hz hx hy hrx hry).IsOver
      (rankTwoScalarAlgebraicChartToSpec (k := k) p x hx)
      (rankTwoScalarAlgebraicChartToSpec (k := k) q y hy) := by
  letI : FiniteDimensional (↥(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p x) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hx
  letI : FiniteDimensional (↥(rankTwoParameterField (k := k) q))
      (rankTwoScalarNormalField (k := k) q y) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hy
  unfold rankTwoScalarLocusReferencePartialIso
    rankTwoScalarAlgebraicChartToSpec rankTwoScalarAlgebraicChart
  apply FiniteExtensionTransition.partialIso_isOver

/-- The affine normal-cover model attached to an arbitrary generic
realization of the Ψ `B/T` projection locus. -/
noncomputable abbrev psiBProjectionAlgebraicChart
    (w : QWitness k K) (hψ : w.Psi)
    {p : Fin 2 → K} {x : K} (h : w.psiBProjectionRelation p x) :
    Scheme :=
  rankTwoScalarAlgebraicChart (k := k) p x
    (PsiBProjectionRelation.scalar_mem_racl w hψ h)

/-- Any two generic realizations of the Ψ `B/T` parameter chart are related
by the strict rational comparison normalized through the selected
`(B,T)` realization. -/
noncomputable def psiBProjectionReferenceRationalMap
    (w : QWitness k K) (hψ : w.Psi)
    {p q : Fin 2 → K} {x y : K}
    (hp : w.psiBProjectionRelation p x)
    (hq : w.psiBProjectionRelation q y) :
    Scheme.RationalMap
      (w.psiBProjectionAlgebraicChart hψ hp)
      (w.psiBProjectionAlgebraicChart hψ hq) :=
  rankTwoScalarLocusReferenceRationalMap
    (w.T_rep_mem_racl_bReps hψ)
    (PsiBProjectionRelation.scalar_mem_racl w hψ hp)
    (PsiBProjectionRelation.scalar_mem_racl w hψ hq)
    hp.symm hq.symm

/-- Exact generic-point description of the reference-normalized comparison
between two realizations of the Ψ `B/T` projection locus. -/
theorem psiBProjectionReferenceRationalMap_fromFunctionField
    (w : QWitness k K) (hψ : w.Psi)
    {p q : Fin 2 → K} {x y : K}
    (hp : w.psiBProjectionRelation p x)
    (hq : w.psiBProjectionRelation q y) :
    (w.psiBProjectionReferenceRationalMap hψ hp hq).fromFunctionField =
      Scheme.functionFieldMorphism
        (rankTwoScalarLocusReferenceFunctionFieldRingEquiv
          (w.T_rep_mem_racl_bReps hψ)
          (PsiBProjectionRelation.scalar_mem_racl w hψ hp)
          (PsiBProjectionRelation.scalar_mem_racl w hψ hq)
          hp.symm hq.symm) := by
  unfold psiBProjectionReferenceRationalMap
  exact rankTwoScalarLocusReferenceRationalMap_fromFunctionField
    (w.T_rep_mem_racl_bReps hψ)
    (PsiBProjectionRelation.scalar_mem_racl w hψ hp)
    (PsiBProjectionRelation.scalar_mem_racl w hψ hq)
    hp.symm hq.symm

instance psiBProjectionReferenceRationalMap_isDominant
    (w : QWitness k K) (hψ : w.Psi)
    {p q : Fin 2 → K} {x y : K}
    (hp : w.psiBProjectionRelation p x)
    (hq : w.psiBProjectionRelation q y) :
    (w.psiBProjectionReferenceRationalMap hψ hp hq).IsDominant := by
  unfold psiBProjectionReferenceRationalMap
  infer_instance

/-- The Ψ `B/T` chart comparisons obey the strict transitive cocycle needed
to use one fixed affine model for every generic parameter realization. -/
theorem psiBProjectionReferenceRationalMap_comp
    (w : QWitness k K) (hψ : w.Psi)
    {p q v : Fin 2 → K} {x y u : K}
    (hp : w.psiBProjectionRelation p x)
    (hq : w.psiBProjectionRelation q y)
    (hv : w.psiBProjectionRelation v u) :
    (w.psiBProjectionReferenceRationalMap hψ hp hq).comp
        (w.psiBProjectionReferenceRationalMap hψ hq hv) =
      w.psiBProjectionReferenceRationalMap hψ hp hv := by
  exact rankTwoScalarLocusReferenceRationalMap_comp
    (w.T_rep_mem_racl_bReps hψ)
    (PsiBProjectionRelation.scalar_mem_racl w hψ hp)
    (PsiBProjectionRelation.scalar_mem_racl w hψ hq)
    (PsiBProjectionRelation.scalar_mem_racl w hψ hv)
    hp.symm hq.symm hv.symm

/-- Two generic realizations of the Ψ `B/T` parameter chart have isomorphic
dense open subschemes of their affine normal-cover models. -/
noncomputable def psiBProjectionReferencePartialIso
    (w : QWitness k K) (hψ : w.Psi)
    {p q : Fin 2 → K} {x y : K}
    (hp : w.psiBProjectionRelation p x)
    (hq : w.psiBProjectionRelation q y) :
    (w.psiBProjectionAlgebraicChart hψ hp).PartialIso
      (w.psiBProjectionAlgebraicChart hψ hq) :=
  rankTwoScalarLocusReferencePartialIso
    (w.T_rep_mem_racl_bReps hψ)
    (PsiBProjectionRelation.scalar_mem_racl w hψ hp)
    (PsiBProjectionRelation.scalar_mem_racl w hψ hq)
    hp.symm hq.symm

/-- The dense-open comparison between Ψ `B/T` parameter realizations is a
morphism over the ground-field spectrum. -/
theorem psiBProjectionReferencePartialIso_isOver
    (w : QWitness k K) (hψ : w.Psi)
    {p q : Fin 2 → K} {x y : K}
    (hp : w.psiBProjectionRelation p x)
    (hq : w.psiBProjectionRelation q y) :
    (w.psiBProjectionReferencePartialIso hψ hp hq).IsOver
      (rankTwoScalarAlgebraicChartToSpec (k := k) p x
        (PsiBProjectionRelation.scalar_mem_racl w hψ hp))
      (rankTwoScalarAlgebraicChartToSpec (k := k) q y
        (PsiBProjectionRelation.scalar_mem_racl w hψ hq)) :=
  rankTwoScalarLocusReferencePartialIso_isOver
    (w.T_rep_mem_racl_bReps hψ)
    (PsiBProjectionRelation.scalar_mem_racl w hψ hp)
    (PsiBProjectionRelation.scalar_mem_racl w hψ hq)
    hp.symm hq.symm

/-- The normal-cover equivalence between two scalar branches on the same
rank-two locus, upgraded to an equivalence over the ground field. -/
noncomputable def rankTwoScalarNormalCoverAlgEquiv
    {p : Fin 2 → K} {x y : K}
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range p))
    (hxy : idealOf k (rankTwoScalarTuple p x) =
      idealOf k (rankTwoScalarTuple p y)) :
    rankTwoScalarNormalField (k := k) p x ≃ₐ[k]
      rankTwoScalarNormalField (k := k) p y :=
  { rankTwoScalarNormalCoverEquiv hx hy hxy with
    commutes' := fun r ↦ by
      rw [IsScalarTower.algebraMap_apply k
          (rankTwoParameterField (k := k) p)
          (rankTwoScalarNormalField (k := k) p x),
        IsScalarTower.algebraMap_apply k
          (rankTwoParameterField (k := k) p)
          (rankTwoScalarNormalField (k := k) p y)]
      exact rankTwoScalarNormalCoverEquiv_algebraMap hx hy hxy
        (algebraMap k (rankTwoParameterField (k := k) p) r) }

/-- Two scalar branches on the same projection locus determine a dominant
partial map between their concrete affine charts, defined on one dense
principal open. -/
noncomputable def rankTwoScalarTransitionPartialMap
    {p : Fin 2 → K} {x y : K}
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range p))
    (hxy : idealOf k (rankTwoScalarTuple p x) =
      idealOf k (rankTwoScalarTuple p y)) :
    (rankTwoScalarAlgebraicChart (k := k) p x hx).PartialMap
      (rankTwoScalarAlgebraicChart (k := k) p y hy) := by
  letI : FiniteDimensional (↥(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p x) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hx
  letI : FiniteDimensional (↥(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p y) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hy
  unfold rankTwoScalarAlgebraicChart
  exact FiniteExtensionTransition.partialMap
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
    (rankTwoScalarNormalCoverAlgEquiv hx hy hxy)

/-- The principal-open transition between scalar charts is dominant. -/
instance rankTwoScalarTransitionPartialMap_isDominant
    {p : Fin 2 → K} {x y : K}
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range p))
    (hxy : idealOf k (rankTwoScalarTuple p x) =
      idealOf k (rankTwoScalarTuple p y)) :
    IsDominant (rankTwoScalarTransitionPartialMap hx hy hxy).hom := by
  letI : FiniteDimensional (↥(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p x) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hx
  letI : FiniteDimensional (↥(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p y) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hy
  change IsDominant (FiniteExtensionTransition.partialMap
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
    (rankTwoScalarNormalCoverAlgEquiv hx hy hxy)).hom
  infer_instance

/-- Two scalar branches on the same projection locus are isomorphic on
explicit dense open subschemes of their affine charts. -/
noncomputable def rankTwoScalarTransitionPartialIso
    {p : Fin 2 → K} {x y : K}
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range p))
    (hxy : idealOf k (rankTwoScalarTuple p x) =
      idealOf k (rankTwoScalarTuple p y)) :
    (rankTwoScalarAlgebraicChart (k := k) p x hx).PartialIso
      (rankTwoScalarAlgebraicChart (k := k) p y hy) := by
  letI : FiniteDimensional (↑(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p x) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hx
  letI : FiniteDimensional (↑(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p y) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hy
  unfold rankTwoScalarAlgebraicChart
  exact FiniteExtensionTransition.partialIso
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
    (rankTwoScalarNormalCoverAlgEquiv hx hy hxy)

/-- A transition between two scalar normal covers, normalized through one
fixed reference branch.  Using the reference branch makes composition
strict rather than depending on independent normal-closure lift choices. -/
noncomputable def rankTwoScalarReferenceTransitionAlgEquiv
    {p : Fin 2 → K} {r x y : K}
    (hr : r ∈ racl k (Set.range p))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range p))
    (hrx : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p y)) :
    rankTwoScalarNormalField (k := k) p x ≃ₐ[k]
      rankTwoScalarNormalField (k := k) p y :=
  (rankTwoScalarNormalCoverAlgEquiv hr hx hrx).symm.trans
    (rankTwoScalarNormalCoverAlgEquiv hr hy hry)

/-- A reference-normalized scalar-cover transition from a branch to itself
is the identity. -/
@[simp] theorem rankTwoScalarReferenceTransitionAlgEquiv_self
    {p : Fin 2 → K} {r x : K}
    (hr : r ∈ racl k (Set.range p))
    (hx : x ∈ racl k (Set.range p))
    (hrx : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p x)) :
    rankTwoScalarReferenceTransitionAlgEquiv hr hx hx hrx hrx =
      AlgEquiv.refl := by
  unfold rankTwoScalarReferenceTransitionAlgEquiv
  ext z
  simp

/-- Reversing a reference-normalized scalar-cover transition gives the
transition in the opposite direction. -/
@[simp] theorem rankTwoScalarReferenceTransitionAlgEquiv_symm
    {p : Fin 2 → K} {r x y : K}
    (hr : r ∈ racl k (Set.range p))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range p))
    (hrx : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p y)) :
    (rankTwoScalarReferenceTransitionAlgEquiv hr hx hy hrx hry).symm =
      rankTwoScalarReferenceTransitionAlgEquiv hr hy hx hry hrx := by
  unfold rankTwoScalarReferenceTransitionAlgEquiv
  ext z
  simp

/-- Reference-normalized scalar-cover transitions satisfy the strict
cocycle law. -/
@[simp] theorem rankTwoScalarReferenceTransitionAlgEquiv_trans
    {p : Fin 2 → K} {r x y z : K}
    (hr : r ∈ racl k (Set.range p))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range p))
    (hz : z ∈ racl k (Set.range p))
    (hrx : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p y))
    (hrz : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p z)) :
    (rankTwoScalarReferenceTransitionAlgEquiv hr hx hy hrx hry).trans
        (rankTwoScalarReferenceTransitionAlgEquiv hr hy hz hry hrz) =
      rankTwoScalarReferenceTransitionAlgEquiv hr hx hz hrx hrz := by
  unfold rankTwoScalarReferenceTransitionAlgEquiv
  ext t
  simp

/-- The rational transition between two scalar charts obtained from the
strict reference-normalized field transition. -/
noncomputable def rankTwoScalarReferenceTransitionRationalMap
    {p : Fin 2 → K} {r x y : K}
    (hr : r ∈ racl k (Set.range p))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range p))
    (hrx : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p y)) :
    Scheme.RationalMap
      (rankTwoScalarAlgebraicChart (k := k) p x hx)
      (rankTwoScalarAlgebraicChart (k := k) p y hy) := by
  letI : FiniteDimensional (↑(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p x) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hx
  letI : FiniteDimensional (↑(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p y) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hy
  unfold rankTwoScalarAlgebraicChart
  exact FiniteExtensionTransition.rationalMap
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
    (rankTwoScalarReferenceTransitionAlgEquiv hr hx hy hrx hry)

/-- Reference-normalized scalar-chart rational transitions are dominant. -/
instance rankTwoScalarReferenceTransitionRationalMap_isDominant
    {p : Fin 2 → K} {r x y : K}
    (hr : r ∈ racl k (Set.range p))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range p))
    (hrx : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p y)) :
    (rankTwoScalarReferenceTransitionRationalMap hr hx hy hrx hry).IsDominant := by
  letI : FiniteDimensional (↑(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p x) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hx
  letI : FiniteDimensional (↑(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p y) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hy
  change (FiniteExtensionTransition.rationalMap
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
    (rankTwoScalarReferenceTransitionAlgEquiv hr hx hy hrx hry)).IsDominant
  infer_instance

/-- The strict reference-normalized field cocycle induces a strict cocycle
of rational transitions between the affine scalar charts. -/
theorem rankTwoScalarReferenceTransitionRationalMap_comp
    {p : Fin 2 → K} {r x y z : K}
    (hr : r ∈ racl k (Set.range p))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range p))
    (hz : z ∈ racl k (Set.range p))
    (hrx : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p y))
    (hrz : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p z)) :
    (rankTwoScalarReferenceTransitionRationalMap hr hx hy hrx hry).comp
        (rankTwoScalarReferenceTransitionRationalMap hr hy hz hry hrz) =
      rankTwoScalarReferenceTransitionRationalMap hr hx hz hrx hrz := by
  letI : FiniteDimensional (↑(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p x) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hx
  letI : FiniteDimensional (↑(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p y) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hy
  letI : FiniteDimensional (↑(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p z) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hz
  change (FiniteExtensionTransition.rationalMap
      (rankTwoParameterCoordinates (k := k) p)
      (rankTwoParameterCoordinates (k := k) p)
      (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
      (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
      (rankTwoScalarReferenceTransitionAlgEquiv hr hx hy hrx hry)).comp
      (FiniteExtensionTransition.rationalMap
        (rankTwoParameterCoordinates (k := k) p)
        (rankTwoParameterCoordinates (k := k) p)
        (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
        (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
        (rankTwoScalarReferenceTransitionAlgEquiv hr hy hz hry hrz)) =
    FiniteExtensionTransition.rationalMap
      (rankTwoParameterCoordinates (k := k) p)
      (rankTwoParameterCoordinates (k := k) p)
      (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
      (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
      (rankTwoScalarReferenceTransitionAlgEquiv hr hx hz hrx hrz)
  rw [FiniteExtensionTransition.rationalMap_comp]
  rw [rankTwoScalarReferenceTransitionAlgEquiv_trans]

/-- The reference-normalized field transition produces a concrete dense-open
partial isomorphism of scalar charts. -/
noncomputable def rankTwoScalarReferenceTransitionPartialIso
    {p : Fin 2 → K} {r x y : K}
    (hr : r ∈ racl k (Set.range p))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range p))
    (hrx : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p y)) :
    (rankTwoScalarAlgebraicChart (k := k) p x hx).PartialIso
      (rankTwoScalarAlgebraicChart (k := k) p y hy) := by
  letI : FiniteDimensional (↑(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p x) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hx
  letI : FiniteDimensional (↑(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p y) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hy
  unfold rankTwoScalarAlgebraicChart
  exact FiniteExtensionTransition.partialIso
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)
    (rankTwoScalarReferenceTransitionAlgEquiv hr hx hy hrx hry)

/-- A reference-normalized dense-open scalar transition commutes with the
structure maps of its two affine charts to `Spec k`. -/
theorem rankTwoScalarReferenceTransitionPartialIso_isOver
    {p : Fin 2 → K} {r x y : K}
    (hr : r ∈ racl k (Set.range p))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range p))
    (hrx : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p y)) :
    (rankTwoScalarReferenceTransitionPartialIso hr hx hy hrx hry).IsOver
      (rankTwoScalarAlgebraicChartToSpec (k := k) p x hx)
      (rankTwoScalarAlgebraicChartToSpec (k := k) p y hy) := by
  letI : FiniteDimensional (↑(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p x) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hx
  letI : FiniteDimensional (↑(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p y) :=
    rankTwoScalarNormalField_finiteDimensional (k := k) hy
  unfold rankTwoScalarReferenceTransitionPartialIso
    rankTwoScalarAlgebraicChartToSpec rankTwoScalarAlgebraicChart
  apply FiniteExtensionTransition.partialIso_isOver

/-- The overlap associated to a reference-normalized scalar transition is
packaged as an actual two-chart scheme gluing datum. -/
noncomputable def rankTwoScalarReferenceTransitionGlueData
    {p : Fin 2 → K} {r x y : K}
    (hr : r ∈ racl k (Set.range p))
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range p))
    (hrx : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p x))
    (hry : idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p y)) : Scheme.GlueData :=
  BirationalGluing.partialIsoGlueData
    (rankTwoScalarReferenceTransitionPartialIso hr hx hy hrx hry)

/-- Normalize a pairwise scalar transition by taking its source branch as
the reference, then package its dense overlap as two-chart scheme gluing
data. -/
noncomputable def rankTwoScalarNormalizedTransitionGlueData
    {p : Fin 2 → K} {x y : K}
    (hx : x ∈ racl k (Set.range p))
    (hy : y ∈ racl k (Set.range p))
    (hxy : idealOf k (rankTwoScalarTuple p x) =
      idealOf k (rankTwoScalarTuple p y)) : Scheme.GlueData :=
  rankTwoScalarReferenceTransitionGlueData hx hx hy rfl hxy

/-- A finite family of scalar branches on one rank-two locus, all normalized
through a fixed reference branch, forms a single scheme atlas.  The family of
reference-to-branch partial isomorphisms is restricted to one common dense
source before gluing, so all triple-overlap cocycles are strict. -/
noncomputable def rankTwoScalarReferenceAtlasGlueData
    {J : Type u} [Finite J]
    {p : Fin 2 → K} {r : K} (x : J → K)
    (hr : r ∈ racl k (Set.range p))
    (hx : ∀ i, x i ∈ racl k (Set.range p))
    (hrx : ∀ i, idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p (x i))) : Scheme.GlueData :=
  BirationalGluing.partialIsoFamilyGlueData
    (U := fun i ↦ rankTwoScalarAlgebraicChart (k := k) p (x i) (hx i))
    (fun i ↦ rankTwoScalarReferenceTransitionPartialIso
      hr hr (hx i) rfl (hrx i))

/-- The scheme obtained by gluing a finite reference-normalized family of
scalar charts along their common dense overlap. -/
noncomputable abbrev rankTwoScalarReferenceAtlas
    {J : Type u} [Finite J]
    {p : Fin 2 → K} {r : K} (x : J → K)
    (hr : r ∈ racl k (Set.range p))
    (hx : ∀ i, x i ∈ racl k (Set.range p))
    (hrx : ∀ i, idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p (x i))) : Scheme.{u} :=
  (rankTwoScalarReferenceAtlasGlueData x hr hx hrx).glued

/-- The structure morphism of the finite reference-normalized scalar atlas.
It is obtained by descending the affine chart structure maps through their
common dense reference overlap. -/
noncomputable def rankTwoScalarReferenceAtlasToSpec
    {J : Type u} [Finite J]
    {p : Fin 2 → K} {r : K} (x : J → K)
    (hr : r ∈ racl k (Set.range p))
    (hx : ∀ i, x i ∈ racl k (Set.range p))
    (hrx : ∀ i, idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p (x i))) :
    rankTwoScalarReferenceAtlas x hr hx hrx ⟶ Spec (.of k) :=
  BirationalGluing.partialIsoFamilyToBase
    (U := fun i ↦ rankTwoScalarAlgebraicChart (k := k) p (x i) (hx i))
    (e := fun i ↦ rankTwoScalarReferenceTransitionPartialIso
      hr hr (hx i) rfl (hrx i))
    (rankTwoScalarAlgebraicChartToSpec (k := k) p r hr)
    (fun i ↦ rankTwoScalarAlgebraicChartToSpec (k := k) p (x i) (hx i))
    (fun i ↦ rankTwoScalarReferenceTransitionPartialIso_isOver
      hr hr (hx i) rfl (hrx i))

instance rankTwoScalarReferenceAtlasToSpec_locallyOfFiniteType
    {J : Type u} [Finite J]
    {p : Fin 2 → K} {r : K} (x : J → K)
    (hr : r ∈ racl k (Set.range p))
    (hx : ∀ i, x i ∈ racl k (Set.range p))
    (hrx : ∀ i, idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p (x i))) :
    LocallyOfFiniteType
      (rankTwoScalarReferenceAtlasToSpec x hr hx hrx) := by
  unfold rankTwoScalarReferenceAtlasToSpec
  apply @BirationalGluing.partialIsoFamilyToBase_locallyOfFiniteType

instance rankTwoScalarReferenceAtlasToSpec_quasiCompact
    {J : Type u} [Finite J]
    {p : Fin 2 → K} {r : K} (x : J → K)
    (hr : r ∈ racl k (Set.range p))
    (hx : ∀ i, x i ∈ racl k (Set.range p))
    (hrx : ∀ i, idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p (x i))) :
    QuasiCompact (rankTwoScalarReferenceAtlasToSpec x hr hx hrx) := by
  unfold rankTwoScalarReferenceAtlasToSpec
  apply @BirationalGluing.partialIsoFamilyToBase_quasiCompact

instance rankTwoScalarReferenceAtlas_integral
    {J : Type u} [Finite J] [Nonempty J]
    {p : Fin 2 → K} {r : K} (x : J → K)
    (hr : r ∈ racl k (Set.range p))
    (hx : ∀ i, x i ∈ racl k (Set.range p))
    (hrx : ∀ i, idealOf k (rankTwoScalarTuple p r) =
      idealOf k (rankTwoScalarTuple p (x i))) :
    IsIntegral (rankTwoScalarReferenceAtlas x hr hx hrx) := by
  unfold rankTwoScalarReferenceAtlas rankTwoScalarReferenceAtlasGlueData
  infer_instance

namespace PsiChunkFourArrowEdgeLifts

variable {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (L : w.PsiChunkFourArrowEdgeLifts hψ D)

/-- The dominant principal-open transition reconciling the two scalar
branches above the repeated `s` block. -/
noncomputable def sAlgebraicTransitionPartialMap :
    (rankTwoScalarAlgebraicChart (k := k) s L.se_s
      (PsiAProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.aProjection w L.se_lift))).PartialMap
    (rankTwoScalarAlgebraicChart (k := k) s L.s_b_s
      (PsiAProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.aProjection w L.s_b_lift))) :=
  rankTwoScalarTransitionPartialMap
    (PsiAProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.aProjection w L.se_lift))
    (PsiAProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.aProjection w L.s_b_lift))
    L.s_graph_eq

instance sAlgebraicTransitionPartialMap_isDominant :
    IsDominant L.sAlgebraicTransitionPartialMap.hom := by
  unfold sAlgebraicTransitionPartialMap
  infer_instance

/-- The dense-open isomorphism reconciling the two scalar branches above the
repeated `s` block. -/
noncomputable def sAlgebraicTransitionPartialIso :
    (rankTwoScalarAlgebraicChart (k := k) s L.se_s
      (PsiAProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.aProjection w L.se_lift))).PartialIso
    (rankTwoScalarAlgebraicChart (k := k) s L.s_b_s
      (PsiAProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.aProjection w L.s_b_lift))) :=
  rankTwoScalarTransitionPartialIso
    (PsiAProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.aProjection w L.se_lift))
    (PsiAProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.aProjection w L.s_b_lift))
    L.s_graph_eq

/-- The normalized dense overlap at the repeated `s` block, packaged as
scheme gluing data. -/
noncomputable def sAlgebraicTransitionGlueData : Scheme.GlueData :=
  rankTwoScalarNormalizedTransitionGlueData
    (PsiAProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.aProjection w L.se_lift))
    (PsiAProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.aProjection w L.s_b_lift))
    L.s_graph_eq

/-- The dominant principal-open transition reconciling the two scalar
branches above the repeated output `u` block. -/
noncomputable def uAlgebraicTransitionPartialMap :
    (rankTwoScalarAlgebraicChart (k := k) D.u L.se_u
      (PsiCProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.cProjection w L.se_lift))).PartialMap
    (rankTwoScalarAlgebraicChart (k := k) D.u L.sA_a_u
      (PsiCProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.cProjection w L.sA_a_lift))) :=
  rankTwoScalarTransitionPartialMap
    (PsiCProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.cProjection w L.se_lift))
    (PsiCProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.cProjection w L.sA_a_lift))
    L.u_graph_eq

instance uAlgebraicTransitionPartialMap_isDominant :
    IsDominant L.uAlgebraicTransitionPartialMap.hom := by
  unfold uAlgebraicTransitionPartialMap
  infer_instance

/-- The dense-open isomorphism reconciling the two scalar branches above the
repeated output `u` block. -/
noncomputable def uAlgebraicTransitionPartialIso :
    (rankTwoScalarAlgebraicChart (k := k) D.u L.se_u
      (PsiCProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.cProjection w L.se_lift))).PartialIso
    (rankTwoScalarAlgebraicChart (k := k) D.u L.sA_a_u
      (PsiCProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.cProjection w L.sA_a_lift))) :=
  rankTwoScalarTransitionPartialIso
    (PsiCProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.cProjection w L.se_lift))
    (PsiCProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.cProjection w L.sA_a_lift))
    L.u_graph_eq

/-- The normalized dense overlap at the repeated `u` block, packaged as
scheme gluing data. -/
noncomputable def uAlgebraicTransitionGlueData : Scheme.GlueData :=
  rankTwoScalarNormalizedTransitionGlueData
    (PsiCProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.cProjection w L.se_lift))
    (PsiCProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.cProjection w L.sA_a_lift))
    L.u_graph_eq

/-- The dominant principal-open transition reconciling the two scalar
branches above the repeated quotient `sA` block. -/
noncomputable def sAAlgebraicTransitionPartialMap :
    (rankTwoScalarAlgebraicChart (k := k) D.sA L.sA_a_sA
      (PsiAProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.aProjection w L.sA_a_lift))).PartialMap
    (rankTwoScalarAlgebraicChart (k := k) D.sA L.sA_c_sA
      (PsiAProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.aProjection w L.sA_c_lift))) :=
  rankTwoScalarTransitionPartialMap
    (PsiAProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.aProjection w L.sA_a_lift))
    (PsiAProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.aProjection w L.sA_c_lift))
    L.sA_graph_eq

instance sAAlgebraicTransitionPartialMap_isDominant :
    IsDominant L.sAAlgebraicTransitionPartialMap.hom := by
  unfold sAAlgebraicTransitionPartialMap
  infer_instance

/-- The dense-open isomorphism reconciling the two scalar branches above the
repeated quotient `sA` block. -/
noncomputable def sAAlgebraicTransitionPartialIso :
    (rankTwoScalarAlgebraicChart (k := k) D.sA L.sA_a_sA
      (PsiAProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.aProjection w L.sA_a_lift))).PartialIso
    (rankTwoScalarAlgebraicChart (k := k) D.sA L.sA_c_sA
      (PsiAProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.aProjection w L.sA_c_lift))) :=
  rankTwoScalarTransitionPartialIso
    (PsiAProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.aProjection w L.sA_a_lift))
    (PsiAProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.aProjection w L.sA_c_lift))
    L.sA_graph_eq

/-- The normalized dense overlap at the repeated `sA` block, packaged as
scheme gluing data. -/
noncomputable def sAAlgebraicTransitionGlueData : Scheme.GlueData :=
  rankTwoScalarNormalizedTransitionGlueData
    (PsiAProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.aProjection w L.sA_a_lift))
    (PsiAProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.aProjection w L.sA_c_lift))
    L.sA_graph_eq

/-- The dominant principal-open transition reconciling the two scalar
branches above the repeated output `uB` block. -/
noncomputable def uBAlgebraicTransitionPartialMap :
    (rankTwoScalarAlgebraicChart (k := k) D.uB L.s_b_uB
      (PsiCProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.cProjection w L.s_b_lift))).PartialMap
    (rankTwoScalarAlgebraicChart (k := k) D.uB L.sA_c_uB
      (PsiCProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.cProjection w L.sA_c_lift))) :=
  rankTwoScalarTransitionPartialMap
    (PsiCProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.cProjection w L.s_b_lift))
    (PsiCProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.cProjection w L.sA_c_lift))
    L.uB_graph_eq

instance uBAlgebraicTransitionPartialMap_isDominant :
    IsDominant L.uBAlgebraicTransitionPartialMap.hom := by
  unfold uBAlgebraicTransitionPartialMap
  infer_instance

/-- The dense-open isomorphism reconciling the two scalar branches above the
repeated output `uB` block. -/
noncomputable def uBAlgebraicTransitionPartialIso :
    (rankTwoScalarAlgebraicChart (k := k) D.uB L.s_b_uB
      (PsiCProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.cProjection w L.s_b_lift))).PartialIso
    (rankTwoScalarAlgebraicChart (k := k) D.uB L.sA_c_uB
      (PsiCProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.cProjection w L.sA_c_lift))) :=
  rankTwoScalarTransitionPartialIso
    (PsiCProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.cProjection w L.s_b_lift))
    (PsiCProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.cProjection w L.sA_c_lift))
    L.uB_graph_eq

/-- The normalized dense overlap at the repeated `uB` block, packaged as
scheme gluing data. -/
noncomputable def uBAlgebraicTransitionGlueData : Scheme.GlueData :=
  rankTwoScalarNormalizedTransitionGlueData
    (PsiCProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.cProjection w L.s_b_lift))
    (PsiCProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.cProjection w L.sA_c_lift))
    L.uB_graph_eq

end PsiChunkFourArrowEdgeLifts

end QWitness

end

end AclGeom
