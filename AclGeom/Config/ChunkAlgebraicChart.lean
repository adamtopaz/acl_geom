/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkBranchCover
import AclGeom.Correspondence.FiniteExtensionChart

/-!
# Integral affine charts for the normalized Ψ parameter chunk

The finite scalar branches over a rank-two Ψ parameter were previously
packaged as finite normal field extensions.  This module applies
`FiniteExtensionChart` to those extensions.  Every branch now has an honest
integral affine scheme, separated and of finite type over the ground field,
whose fraction field is exactly the chosen normal cover.

The two lifted parameter coordinates generate the base function field.  On
the selected `A`, `B`, and `C` branches they remain algebraically independent,
so these schemes retain the positive-dimensional rank-two parameter base;
they are not finite deck groups.

These are the concrete affine models on which the normalized branch
equivalences will next be localized to dense open transition isomorphisms.
-/

namespace AclGeom

noncomputable section

open IntermediateField
open AlgebraicGeometry

universe u

namespace QWitness

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable (w : QWitness k K)

/-- The normal field of a scalar branch over a rank-two parameter field. -/
abbrev rankTwoScalarNormalField (p : Fin 2 → K) (x : K) :=
  ↥(FiniteCover.normalClosureOver
    (rankTwoParameterField_le_rankTwoScalarField (k := k) p x))

/-- The two parameter coordinates lifted into their generated function
field. -/
def rankTwoParameterCoordinates (p : Fin 2 → K) :
    Fin 2 → rankTwoParameterField (k := k) p :=
  FiniteExtensionChart.liftedCoordinates
    (k := k) (K := K) (ι := Fin 2) p

/-- The lifted parameter coordinates generate the full rank-two parameter
field. -/
theorem rankTwoParameterCoordinates_adjoin_eq_top (p : Fin 2 → K) :
    adjoin k (Set.range (rankTwoParameterCoordinates (k := k) p)) = ⊤ := by
  exact FiniteExtensionChart.adjoin_liftedCoordinates_eq_top
    (k := k) (K := K) (ι := Fin 2) p

/-- Algebraicity of a scalar branch makes its normal-cover field finite
over the rank-two parameter field. -/
theorem rankTwoScalarNormalField_finiteDimensional
    {p : Fin 2 → K} {x : K} (hx : x ∈ racl k (Set.range p)) :
    FiniteDimensional (↥(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p x) := by
  apply FiniteCover.normalClosureOver_finiteDimensional
  exact rankTwoScalarExtension_finiteDimensional (k := k) hx

/-- Over an algebraically closed ambient field, the scalar normal-cover
field is normal over its rank-two parameter field. -/
theorem rankTwoScalarNormalField_normal [IsAlgClosed K]
    {p : Fin 2 → K} {x : K} (hx : x ∈ racl k (Set.range p)) :
    Normal (↥(rankTwoParameterField (k := k) p))
      (rankTwoScalarNormalField (k := k) p x) := by
  apply FiniteCover.normalClosureOver_normal
  letI : FiniteDimensional (↥(rankTwoParameterField (k := k) p))
      (↥(rankTwoScalarExtension (k := k) p x)) :=
    rankTwoScalarExtension_finiteDimensional (k := k) hx
  change Algebra.IsAlgebraic (↥(rankTwoParameterField (k := k) p))
    (↥(rankTwoScalarExtension (k := k) p x))
  exact Algebra.IsAlgebraic.of_finite _ _

/-- The integral affine scheme attached to one finite normal scalar branch
over a rank-two parameter. -/
def rankTwoScalarAlgebraicChart (p : Fin 2 → K) (x : K)
    (hx : x ∈ racl k (Set.range p)) : Scheme := by
  letI := rankTwoScalarNormalField_finiteDimensional (k := k) hx
  exact FiniteExtensionChart.scheme (k := k)
    (K := ↥(rankTwoParameterField (k := k) p))
    (L := rankTwoScalarNormalField (k := k) p x)
    (ι := Fin 2)
    (rankTwoParameterCoordinates (k := k) p)

/-- The structure morphism of a normalized scalar-branch chart. -/
def rankTwoScalarAlgebraicChartToSpec (p : Fin 2 → K) (x : K)
    (hx : x ∈ racl k (Set.range p)) :
    rankTwoScalarAlgebraicChart (k := k) p x hx ⟶ Spec (.of k) := by
  letI := rankTwoScalarNormalField_finiteDimensional (k := k) hx
  exact FiniteExtensionChart.structureMap (k := k)
    (K := ↥(rankTwoParameterField (k := k) p))
    (L := rankTwoScalarNormalField (k := k) p x)
    (ι := Fin 2)
    (rankTwoParameterCoordinates (k := k) p)

instance rankTwoScalarAlgebraicChart_locallyOfFiniteType
    (p : Fin 2 → K) (x : K) (hx : x ∈ racl k (Set.range p)) :
    LocallyOfFiniteType
      (rankTwoScalarAlgebraicChartToSpec (k := k) p x hx) := by
  letI := rankTwoScalarNormalField_finiteDimensional (k := k) hx
  unfold rankTwoScalarAlgebraicChartToSpec rankTwoScalarAlgebraicChart
  infer_instance

instance rankTwoScalarAlgebraicChart_quasiCompact
    (p : Fin 2 → K) (x : K) (hx : x ∈ racl k (Set.range p)) :
    QuasiCompact (rankTwoScalarAlgebraicChartToSpec (k := k) p x hx) := by
  letI := rankTwoScalarNormalField_finiteDimensional (k := k) hx
  unfold rankTwoScalarAlgebraicChartToSpec rankTwoScalarAlgebraicChart
  infer_instance

instance rankTwoScalarAlgebraicChart_separated
    (p : Fin 2 → K) (x : K) (hx : x ∈ racl k (Set.range p)) :
    IsSeparated (rankTwoScalarAlgebraicChartToSpec (k := k) p x hx) := by
  letI := rankTwoScalarNormalField_finiteDimensional (k := k) hx
  unfold rankTwoScalarAlgebraicChartToSpec rankTwoScalarAlgebraicChart
  infer_instance

instance rankTwoScalarAlgebraicChart_integral
    (p : Fin 2 → K) (x : K) (hx : x ∈ racl k (Set.range p)) :
    IsIntegral (rankTwoScalarAlgebraicChart (k := k) p x hx) := by
  letI := rankTwoScalarNormalField_finiteDimensional (k := k) hx
  unfold rankTwoScalarAlgebraicChart
  infer_instance

/-- The concrete intermediate field generated by the coordinate ring of a
scalar-branch chart. -/
def rankTwoScalarAlgebraicChartGeneratedField
    (p : Fin 2 → K) (x : K) (hx : x ∈ racl k (Set.range p)) :
    IntermediateField k (rankTwoScalarNormalField (k := k) p x) := by
  letI := rankTwoScalarNormalField_finiteDimensional (k := k) hx
  exact FiniteExtensionChart.generatedField (k := k)
    (K := ↥(rankTwoParameterField (k := k) p))
    (L := rankTwoScalarNormalField (k := k) p x)
    (ι := Fin 2)
    (rankTwoParameterCoordinates (k := k) p)

/-- The fraction field of a scalar-branch chart is canonically its selected
finite normal cover. -/
def rankTwoScalarAlgebraicChartFunctionFieldEquiv
    (p : Fin 2 → K) (x : K) (hx : x ∈ racl k (Set.range p)) :
    rankTwoScalarAlgebraicChartGeneratedField (k := k) p x hx ≃ₐ[k]
      rankTwoScalarNormalField (k := k) p x := by
  letI := rankTwoScalarNormalField_finiteDimensional (k := k) hx
  unfold rankTwoScalarAlgebraicChartGeneratedField
  exact FiniteExtensionChart.generatedFieldEquiv
    (ι := Fin 2)
    (rankTwoParameterCoordinates (k := k) p)
    (rankTwoParameterCoordinates_adjoin_eq_top (k := k) p)

/-- Algebraic independence of a rank-two parameter is preserved after
lifting its coordinates into the generated parameter field. -/
theorem rankTwoParameterCoordinates_independent {p : Fin 2 → K}
    (hp : AlgebraicIndependent k p) :
    AlgebraicIndependent k (rankTwoParameterCoordinates (k := k) p) := by
  apply AlgebraicIndependent.of_comp
    (rankTwoParameterField (k := k) p).val
  have hcomp : (rankTwoParameterField (k := k) p).val ∘
      rankTwoParameterCoordinates (k := k) p = p := by
    funext i
    rfl
  rw [hcomp]
  exact hp

/-- The selected normalized `A/S` affine chart. -/
abbrev psiAAlgebraicChart (hψ : w.Psi) : Scheme :=
  rankTwoScalarAlgebraicChart (k := k) w.aReps w.S.rep
    (w.S_rep_mem_racl_aReps hψ)

/-- The selected normalized `B/T` affine chart. -/
abbrev psiBAlgebraicChart (hψ : w.Psi) : Scheme :=
  rankTwoScalarAlgebraicChart (k := k) w.bReps w.T.rep
    (w.T_rep_mem_racl_bReps hψ)

/-- The selected normalized `C/U` affine chart. -/
abbrev psiCAlgebraicChart (hψ : w.Psi) : Scheme :=
  rankTwoScalarAlgebraicChart (k := k) w.cReps w.U.rep
    (w.U_rep_mem_racl_cReps hψ)

/-- The two function-field coordinates of the selected `A` chart are
algebraically independent. -/
theorem psiAParameterCoordinates_independent (hψ : w.Psi) :
    AlgebraicIndependent k
      (rankTwoParameterCoordinates (k := k) w.aReps) :=
  rankTwoParameterCoordinates_independent (w.aReps_independent hψ)

/-- The two function-field coordinates of the selected `B` chart are
algebraically independent. -/
theorem psiBParameterCoordinates_independent (hψ : w.Psi) :
    AlgebraicIndependent k
      (rankTwoParameterCoordinates (k := k) w.bReps) :=
  rankTwoParameterCoordinates_independent (w.bReps_independent hψ)

/-- The two function-field coordinates of the selected `C` chart are
algebraically independent. -/
theorem psiCParameterCoordinates_independent (hψ : w.Psi) :
    AlgebraicIndependent k
      (rankTwoParameterCoordinates (k := k) w.cReps) :=
  rankTwoParameterCoordinates_independent (w.cReps_independent hψ)

end QWitness

end

end AclGeom
