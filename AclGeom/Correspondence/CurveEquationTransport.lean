/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveEquation
import AclGeom.Correspondence.FiniteCover

/-!
# Canonical curve equations under normal-cover transport

The canonical monic equation of a finite correspondence is first moved
from its coefficient field to its source-coordinate field.  Its selected
source and target points satisfy that equation inside the branch field.
Consequently every source-linear embedding of the branch into another
field, and every subsequent source-fixing automorphism, preserves the
equation exactly.

This is the coefficient-faithfulness bridge used when strict finite-cover
composition triangles are conjugated through chosen normal-cover charts.
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

namespace FiniteCorrespondencePair

variable (P : FiniteCorrespondencePair k Ω)

/-- The selected source coordinate as an element of the branch field over
the source-coordinate field. -/
def sourceInBranchOverSource : P.branchOverSource :=
  algebraMap (↥P.sourceField) (↥P.branchOverSource)
    ⟨P.source, subset_adjoin k {P.source} (by simp)⟩

/-- The selected target coordinate as an element of the branch field over
the source-coordinate field. -/
def targetInBranchOverSource : P.branchOverSource :=
  ⟨P.target, by
    change P.target ∈ P.branchField
    exact subset_adjoin k {P.source, P.target} (by simp)⟩

/-- The canonical curve equation after extending its coefficients to the
source-coordinate field. -/
def curveEquationOverSourceField :
    MvPolynomial (Fin 2) (↥P.sourceField) :=
  MvPolynomial.map (algebraMap k (↥P.sourceField)) P.curveEquation

/-- The selected source and target coordinates satisfy the canonical
equation already inside the selected branch field. -/
theorem aeval_curveEquationOverSourceField :
    MvPolynomial.aeval
        ![P.sourceInBranchOverSource, P.targetInBranchOverSource]
        P.curveEquationOverSourceField = 0 := by
  let q : Fin 2 → P.branchOverSource :=
    ![P.sourceInBranchOverSource, P.targetInBranchOverSource]
  let v := P.branchOverSource.val
  have hq : (fun i ↦ v (q i)) = (![P.source, P.target] : Fin 2 → Ω) := by
    funext i
    fin_cases i <;> rfl
  apply v.injective
  change v (MvPolynomial.aeval q P.curveEquationOverSourceField) = v 0
  calc
    v (MvPolynomial.aeval q P.curveEquationOverSourceField) =
        MvPolynomial.aeval (fun i ↦ v (q i))
          P.curveEquationOverSourceField :=
      MvPolynomial.comp_aeval_apply (f := q) v
        P.curveEquationOverSourceField
    _ = MvPolynomial.aeval ![P.source, P.target]
        P.curveEquationOverSourceField := by rw [hq]
    _ = 0 := by
      rw [curveEquationOverSourceField,
        MvPolynomial.aeval_map_algebraMap, P.aeval_curveEquation]
    _ = v 0 := by rw [map_zero]

/-- The same selected branch point satisfies the original equation over
the coefficient field.  This formulation survives charts which fix only
the coefficients, rather than the entire source-coordinate field. -/
theorem aeval_curveEquation_inBranchOverSource :
    MvPolynomial.aeval
        ![P.sourceInBranchOverSource, P.targetInBranchOverSource]
        P.curveEquation = 0 := by
  have h := P.aeval_curveEquationOverSourceField
  rw [curveEquationOverSourceField,
    MvPolynomial.aeval_map_algebraMap] at h
  exact h

variable {N : Type*} [Field N] [Algebra (↥P.sourceField) N]

/-- Every source-linear embedding of the selected branch carries its two
distinguished coordinates to another zero of the same canonical equation. -/
theorem aeval_curveEquationOverSourceField_map
    (f : (↥P.branchOverSource) →ₐ[↥P.sourceField] N) :
    MvPolynomial.aeval
        ![f P.sourceInBranchOverSource, f P.targetInBranchOverSource]
        P.curveEquationOverSourceField = 0 := by
  let q : Fin 2 → P.branchOverSource :=
    ![P.sourceInBranchOverSource, P.targetInBranchOverSource]
  have hq : (fun i ↦ f (q i)) =
      ![f P.sourceInBranchOverSource, f P.targetInBranchOverSource] := by
    funext i
    fin_cases i <;> rfl
  rw [← hq, ← MvPolynomial.comp_aeval_apply]
  rw [P.aeval_curveEquationOverSourceField, map_zero]

/-- A source-fixing automorphism of the target normal cover preserves the
canonical equation on the transported selected branch. -/
theorem aeval_curveEquationOverSourceField_map_aut
    (f : (↥P.branchOverSource) →ₐ[↥P.sourceField] N)
    (σ : N ≃ₐ[↥P.sourceField] N) :
    MvPolynomial.aeval
        ![σ (f P.sourceInBranchOverSource),
          σ (f P.targetInBranchOverSource)]
        P.curveEquationOverSourceField = 0 := by
  exact P.aeval_curveEquationOverSourceField_map (σ.toAlgHom.comp f)

variable {M : Type*} [Field M] [Algebra k M]

/-- Every coefficient-linear realization of the selected branch carries
its two distinguished coordinates to a zero of the original canonical
equation.  In particular this applies after a coefficient-fixing chart
which need not fix the source coordinate. -/
theorem aeval_curveEquation_map
    (f : (↥P.branchOverSource) →ₐ[k] M) :
    MvPolynomial.aeval
        ![f P.sourceInBranchOverSource, f P.targetInBranchOverSource]
        P.curveEquation = 0 := by
  let q : Fin 2 → P.branchOverSource :=
    ![P.sourceInBranchOverSource, P.targetInBranchOverSource]
  have hq : (fun i ↦ f (q i)) =
      ![f P.sourceInBranchOverSource, f P.targetInBranchOverSource] := by
    funext i
    fin_cases i <;> rfl
  rw [← hq, ← MvPolynomial.comp_aeval_apply]
  rw [P.aeval_curveEquation_inBranchOverSource, map_zero]

end FiniteCorrespondencePair

end

end AclGeom
