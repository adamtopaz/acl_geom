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
