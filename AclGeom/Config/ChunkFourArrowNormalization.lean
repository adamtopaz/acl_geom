/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkAlgebraicTransition
import AclGeom.Correspondence.FourArrowNormalization

/-!
# Joint normalization of a lifted Ψ four-arrow component

An ambient four-arrow difference diagram has sixteen rank-two coordinates.
Choosing a complete joint lift on each of its four edges adds twelve scalar
coordinates.  This file keeps all twenty-eight coordinates together, proves
that they are algebraic over the original eight independent ambient inputs,
and places the complete lifted component in one finite normal cover.

The four nine-coordinate edge restrictions remain the selected complete
rank-two/scalar projection locus.  The common affine chart consequently has
dominant rational projections to the four displayed `B/T` scalar branch
fields.  These targets are deliberately the raw finite branch fields; the
next normalization step adjoins their normal closures and compares all four
targets with the selected reference `B/T` model.
-/

namespace AclGeom

open IntermediateField
open AlgebraicGeometry

noncomputable section

universe u

namespace QWitness.PsiChunkFourArrowEdgeLifts

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (L : w.PsiChunkFourArrowEdgeLifts hψ D)

/-- The complete lifted four-arrow tuple.  The first sixteen entries are
the ambient blocks `(s,e,a,b,u,sA,uB,c)`; the remaining entries are the
three scalar branches on each of the four edges. -/
def jointTuple : Fin 28 → K :=
  ![s 0, s 1, e 0, e 1, a 0, a 1, b 0, b 1,
    D.u 0, D.u 1, D.sA 0, D.sA 1, D.uB 0, D.uB 1, D.c 0, D.c 1,
    L.se_s, L.se_e, L.se_u,
    L.sA_a_sA, L.sA_a_a, L.sA_a_u,
    L.s_b_s, L.s_b_b, L.s_b_uB,
    L.sA_c_sA, L.sA_c_c, L.sA_c_uB]

/-- The ambient sixteen-coordinate component inside the joint tuple. -/
def ambientIndex : Fin 16 → Fin 28 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The eight independent ambient inputs inside the joint tuple. -/
def inputIndex : Fin 8 → Fin 28 := ![0, 1, 2, 3, 4, 5, 6, 7]

/-- The complete `s·e=u` edge inside the joint tuple. -/
def seIndex : Fin 9 → Fin 28 := ![0, 1, 2, 3, 8, 9, 16, 17, 18]

/-- The complete `sA·a=u` edge inside the joint tuple. -/
def sAaIndex : Fin 9 → Fin 28 := ![10, 11, 4, 5, 8, 9, 19, 20, 21]

/-- The complete `s·b=uB` edge inside the joint tuple. -/
def sbIndex : Fin 9 → Fin 28 := ![0, 1, 6, 7, 12, 13, 22, 23, 24]

/-- The complete `sA·c=uB` edge inside the joint tuple. -/
def sAcIndex : Fin 9 → Fin 28 := ![10, 11, 14, 15, 12, 13, 25, 26, 27]

/-- The ambient part of the joint tuple is the original four-arrow tuple. -/
@[simp] theorem jointTuple_comp_ambientIndex :
    L.jointTuple ∘ ambientIndex = D.totalTuple := by
  funext i
  fin_cases i <;> rfl

/-- The independent part of the joint tuple is `(s,e,a,b)`. -/
@[simp] theorem jointTuple_comp_inputIndex :
    L.jointTuple ∘ inputIndex = rankTwoFourTuple s e a b := by
  funext i
  fin_cases i <;> rfl

/-- Restriction to the first edge recovers its complete joint tuple. -/
@[simp] theorem jointTuple_comp_seIndex :
    L.jointTuple ∘ seIndex =
      chunkProjectionTuple s e D.u L.se_s L.se_e L.se_u := by
  funext i
  fin_cases i <;> rfl

/-- Restriction to the second edge recovers its complete joint tuple. -/
@[simp] theorem jointTuple_comp_sAaIndex :
    L.jointTuple ∘ sAaIndex =
      chunkProjectionTuple D.sA a D.u
        L.sA_a_sA L.sA_a_a L.sA_a_u := by
  funext i
  fin_cases i <;> rfl

/-- Restriction to the third edge recovers its complete joint tuple. -/
@[simp] theorem jointTuple_comp_sbIndex :
    L.jointTuple ∘ sbIndex =
      chunkProjectionTuple s b D.uB L.s_b_s L.s_b_b L.s_b_uB := by
  funext i
  fin_cases i <;> rfl

/-- Restriction to the fourth edge recovers its complete joint tuple. -/
@[simp] theorem jointTuple_comp_sAcIndex :
    L.jointTuple ∘ sAcIndex =
      chunkProjectionTuple D.sA D.c D.uB
        L.sA_c_sA L.sA_c_c L.sA_c_uB := by
  funext i
  fin_cases i <;> rfl

/-- The first restriction of the joint tuple lies on the selected complete
rank-two/scalar projection locus. -/
theorem se_relation :
    idealOf k (L.jointTuple ∘ seIndex) = idealOf k w.abcStuReps := by
  simpa [psiChunkProjectionRelation] using L.se_lift

/-- The second restriction of the joint tuple lies on the selected complete
rank-two/scalar projection locus. -/
theorem sAa_relation :
    idealOf k (L.jointTuple ∘ sAaIndex) = idealOf k w.abcStuReps := by
  simpa [psiChunkProjectionRelation] using L.sA_a_lift

/-- The third restriction of the joint tuple lies on the selected complete
rank-two/scalar projection locus. -/
theorem sb_relation :
    idealOf k (L.jointTuple ∘ sbIndex) = idealOf k w.abcStuReps := by
  simpa [psiChunkProjectionRelation] using L.s_b_lift

/-- The fourth restriction of the joint tuple lies on the selected complete
rank-two/scalar projection locus. -/
theorem sAc_relation :
    idealOf k (L.jointTuple ∘ sAcIndex) = idealOf k w.abcStuReps := by
  simpa [psiChunkProjectionRelation] using L.sA_c_lift

private theorem scalar_mem_input_racl
    {p : Fin 2 → K} {x : K}
    (hx : x ∈ racl k (Set.range p))
    (hp : ∀ i, p i ∈ racl k (Set.range (rankTwoFourTuple s e a b))) :
    x ∈ racl k (Set.range (rankTwoFourTuple s e a b)) := by
  refine racl_le_of_subset_racl ?_ hx
  rintro _ ⟨i, rfl⟩
  exact hp i

/-- Every ambient or scalar coordinate of the lifted component is
algebraic over the eight independent ambient inputs. -/
theorem jointTuple_mem_input_racl (i : Fin 28) :
    L.jointTuple i ∈ racl k (Set.range (rankTwoFourTuple s e a b)) := by
  fin_cases i
  · exact D.totalTuple_mem_input_racl 0
  · exact D.totalTuple_mem_input_racl 1
  · exact D.totalTuple_mem_input_racl 2
  · exact D.totalTuple_mem_input_racl 3
  · exact D.totalTuple_mem_input_racl 4
  · exact D.totalTuple_mem_input_racl 5
  · exact D.totalTuple_mem_input_racl 6
  · exact D.totalTuple_mem_input_racl 7
  · exact D.totalTuple_mem_input_racl 8
  · exact D.totalTuple_mem_input_racl 9
  · exact D.totalTuple_mem_input_racl 10
  · exact D.totalTuple_mem_input_racl 11
  · exact D.totalTuple_mem_input_racl 12
  · exact D.totalTuple_mem_input_racl 13
  · exact D.totalTuple_mem_input_racl 14
  · exact D.totalTuple_mem_input_racl 15
  · exact scalar_mem_input_racl (s := s) (e := e) (a := a) (b := b)
      (PsiAProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.aProjection w L.se_lift))
      (fun i ↦ by
        fin_cases i
        · exact D.totalTuple_mem_input_racl 0
        · exact D.totalTuple_mem_input_racl 1)
  · exact scalar_mem_input_racl (s := s) (e := e) (a := a) (b := b)
      (PsiBProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.bProjection w L.se_lift))
      (fun i ↦ by
        fin_cases i
        · exact D.totalTuple_mem_input_racl 2
        · exact D.totalTuple_mem_input_racl 3)
  · exact scalar_mem_input_racl (s := s) (e := e) (a := a) (b := b)
      (PsiCProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.cProjection w L.se_lift))
      D.u_mem_input_racl
  · exact scalar_mem_input_racl (s := s) (e := e) (a := a) (b := b)
      (PsiAProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.aProjection w L.sA_a_lift))
      D.sA_mem_input_racl
  · exact scalar_mem_input_racl (s := s) (e := e) (a := a) (b := b)
      (PsiBProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.bProjection w L.sA_a_lift))
      (fun i ↦ by
        fin_cases i
        · exact D.totalTuple_mem_input_racl 4
        · exact D.totalTuple_mem_input_racl 5)
  · exact scalar_mem_input_racl (s := s) (e := e) (a := a) (b := b)
      (PsiCProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.cProjection w L.sA_a_lift))
      D.u_mem_input_racl
  · exact scalar_mem_input_racl (s := s) (e := e) (a := a) (b := b)
      (PsiAProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.aProjection w L.s_b_lift))
      (fun i ↦ by
        fin_cases i
        · exact D.totalTuple_mem_input_racl 0
        · exact D.totalTuple_mem_input_racl 1)
  · exact scalar_mem_input_racl (s := s) (e := e) (a := a) (b := b)
      (PsiBProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.bProjection w L.s_b_lift))
      (fun i ↦ by
        fin_cases i
        · exact D.totalTuple_mem_input_racl 6
        · exact D.totalTuple_mem_input_racl 7)
  · exact scalar_mem_input_racl (s := s) (e := e) (a := a) (b := b)
      (PsiCProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.cProjection w L.s_b_lift))
      D.uB_mem_input_racl
  · exact scalar_mem_input_racl (s := s) (e := e) (a := a) (b := b)
      (PsiAProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.aProjection w L.sA_c_lift))
      D.sA_mem_input_racl
  · exact scalar_mem_input_racl (s := s) (e := e) (a := a) (b := b)
      (PsiBProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.bProjection w L.sA_c_lift))
      D.c_mem_input_racl
  · exact scalar_mem_input_racl (s := s) (e := e) (a := a) (b := b)
      (PsiCProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.cProjection w L.sA_c_lift))
      D.uB_mem_input_racl

/-- The field generated by the complete twenty-eight-coordinate lifted
four-arrow component. -/
def jointField : IntermediateField k K := adjoin k (Set.range L.jointTuple)

/-- The eight-coordinate ambient input field embeds in the complete joint
field. -/
theorem inputField_le_jointField : D.inputField ≤ L.jointField := by
  apply adjoin.mono
  rintro _ ⟨i, rfl⟩
  exact ⟨inputIndex i, congrFun L.jointTuple_comp_inputIndex i⟩

/-- The sixteen-coordinate ambient component embeds in the complete joint
field. -/
theorem ambientTotalField_le_jointField : D.totalField ≤ L.jointField := by
  apply adjoin.mono
  rintro _ ⟨i, rfl⟩
  exact ⟨ambientIndex i, congrFun L.jointTuple_comp_ambientIndex i⟩

/-- The complete lifted component as an extension of its eight independent
ambient inputs. -/
def jointOverInput : IntermediateField (↥D.inputField) K :=
  extendScalars L.inputField_le_jointField

/-- The complete lifted four-arrow component is finite over its eight
independent ambient inputs. -/
theorem jointOverInput_finiteDimensional :
    FiniteDimensional (↥D.inputField) (↥L.jointOverInput) := by
  have key : L.jointOverInput =
      adjoin (↥D.inputField) (Set.range L.jointTuple) := by
    refine restrictScalars_injective k ?_
    unfold jointOverInput jointField
      RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.inputField
    rw [adjoin_adjoin_left, extendScalars_restrictScalars, adjoin_union]
    exact (sup_eq_right.2 L.inputField_le_jointField).symm
  rw [key]
  letI : Fintype (Set.range L.jointTuple) :=
    Set.Finite.fintype (Set.finite_range L.jointTuple)
  exact finiteDimensional_adjoin fun x hx ↦ by
    obtain ⟨i, rfl⟩ := hx
    exact ((mem_racl_iff k).1 (L.jointTuple_mem_input_racl i)).isIntegral

/-- One finite normal cover containing all four complete lifted edges. -/
def normalCover : IntermediateField (↥D.inputField) K :=
  FiniteCover.normalClosureOver L.inputField_le_jointField

/-- The full twenty-eight-coordinate field embeds in the common normal
cover. -/
theorem jointOverInput_le_normalCover : L.jointOverInput ≤ L.normalCover :=
  FiniteCover.extendScalars_le_normalClosureOver L.inputField_le_jointField

/-- The common lifted four-arrow cover is finite over the eight-coordinate
input field. -/
theorem normalCover_finiteDimensional :
    FiniteDimensional (↥D.inputField) (↥L.normalCover) :=
  FiniteCover.normalClosureOver_finiteDimensional
    L.inputField_le_jointField L.jointOverInput_finiteDimensional

/-- In the algebraically closed ambient field, the common lifted four-arrow
cover is normal over the eight-coordinate input field. -/
theorem normalCover_normal [IsAlgClosed K] :
    Normal (↥D.inputField) (↥L.normalCover) := by
  letI := L.jointOverInput_finiteDimensional
  exact FiniteCover.normalClosureOver_normal L.inputField_le_jointField
    (Algebra.IsAlgebraic.of_finite (↥D.inputField) (↥L.jointOverInput))

/-- The integral affine chart of the complete lifted four-arrow component. -/
abbrev algebraicChart : Scheme := by
  letI := L.normalCover_finiteDimensional
  exact FiniteExtensionChart.scheme (k := k)
    (K := ↥D.inputField) (L := ↥L.normalCover) D.inputCoordinates

/-- The finite-extension affine chart of one unnormalized scalar branch. -/
abbrev rawScalarAlgebraicChart (p : Fin 2 → K) (x : K)
    (hx : x ∈ racl k (Set.range p)) : Scheme := by
  letI := rankTwoScalarExtension_finiteDimensional (k := k) hx
  exact FiniteExtensionChart.scheme (k := k)
    (K := ↥(rankTwoParameterField (k := k) p))
    (L := ↥(rankTwoScalarExtension (k := k) p x))
    (rankTwoParameterCoordinates (k := k) p)

/-- The first based `B/T` scalar branch field lies in the complete joint
field. -/
theorem eScalarField_le_jointField :
    rankTwoScalarField (k := k) e L.se_e ≤ L.jointField := by
  apply adjoin.mono
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨17, rfl⟩

/-- The inverse-input `B/T` scalar branch field lies in the complete joint
field. -/
theorem aScalarField_le_jointField :
    rankTwoScalarField (k := k) a L.sA_a_a ≤ L.jointField := by
  apply adjoin.mono
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨20, rfl⟩

/-- The second based `B/T` scalar branch field lies in the complete joint
field. -/
theorem bScalarField_le_jointField :
    rankTwoScalarField (k := k) b L.s_b_b ≤ L.jointField := by
  apply adjoin.mono
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨23, rfl⟩

/-- The output `B/T` scalar branch field lies in the complete joint field. -/
theorem cScalarField_le_jointField :
    rankTwoScalarField (k := k) D.c L.sA_c_c ≤ L.jointField := by
  apply adjoin.mono
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨14, rfl⟩
  · exact ⟨15, rfl⟩
  · exact ⟨26, rfl⟩

/-- Any displayed raw scalar branch field contained in the joint field
embeds in the common lifted normal cover. -/
def rawScalarFieldToNormalCover (p : Fin 2 → K) (x : K)
    (hx : rankTwoScalarField (k := k) p x ≤ L.jointField) :
    (↥(rankTwoScalarExtension (k := k) p x)) →ₐ[k] (↥L.normalCover) := by
  let hle :
      (rankTwoScalarExtension (k := k) p x).restrictScalars k ≤
        L.normalCover.restrictScalars k := by
    intro z hz
    apply L.jointOverInput_le_normalCover
    exact hx hz
  exact IntermediateField.inclusion hle

/-- A dominant rational projection from the complete lifted component to
any one of its displayed raw scalar branch charts. -/
def projectionToRawScalar (p : Fin 2 → K) (x : K)
    (hx : x ∈ racl k (Set.range p))
    (hfield : rankTwoScalarField (k := k) p x ≤ L.jointField) :
    Scheme.RationalMap L.algebraicChart (rawScalarAlgebraicChart p x hx) := by
  letI := L.normalCover_finiteDimensional
  letI := rankTwoScalarExtension_finiteDimensional (k := k) hx
  exact FiniteExtensionProjection.rationalMap
    D.inputCoordinates (rankTwoParameterCoordinates (k := k) p)
    D.adjoin_inputCoordinates_eq_top
    (L.rawScalarFieldToNormalCover p x hfield)

instance projectionToRawScalar_isDominant (p : Fin 2 → K) (x : K)
    (hx : x ∈ racl k (Set.range p))
    (hfield : rankTwoScalarField (k := k) p x ≤ L.jointField) :
    (L.projectionToRawScalar p x hx hfield).IsDominant := by
  letI := L.normalCover_finiteDimensional
  letI := rankTwoScalarExtension_finiteDimensional (k := k) hx
  unfold projectionToRawScalar
  infer_instance

/-- Projection to the first based `B/T` scalar branch. -/
abbrev toRawE : Scheme.RationalMap L.algebraicChart
    (rawScalarAlgebraicChart e L.se_e
      (PsiBProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.bProjection w L.se_lift))) :=
  L.projectionToRawScalar e L.se_e
    (PsiBProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.bProjection w L.se_lift))
    L.eScalarField_le_jointField

/-- Projection to the inverse-input `B/T` scalar branch. -/
abbrev toRawA : Scheme.RationalMap L.algebraicChart
    (rawScalarAlgebraicChart a L.sA_a_a
      (PsiBProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.bProjection w L.sA_a_lift))) :=
  L.projectionToRawScalar a L.sA_a_a
    (PsiBProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.bProjection w L.sA_a_lift))
    L.aScalarField_le_jointField

/-- Projection to the second based `B/T` scalar branch. -/
abbrev toRawB : Scheme.RationalMap L.algebraicChart
    (rawScalarAlgebraicChart b L.s_b_b
      (PsiBProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.bProjection w L.s_b_lift))) :=
  L.projectionToRawScalar b L.s_b_b
    (PsiBProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.bProjection w L.s_b_lift))
    L.bScalarField_le_jointField

/-- Projection to the output `B/T` scalar branch. -/
abbrev toRawC : Scheme.RationalMap L.algebraicChart
    (rawScalarAlgebraicChart D.c L.sA_c_c
      (PsiBProjectionRelation.scalar_mem_racl w hψ
        (PsiChunkProjectionRelation.bProjection w L.sA_c_lift))) :=
  L.projectionToRawScalar D.c L.sA_c_c
    (PsiBProjectionRelation.scalar_mem_racl w hψ
      (PsiChunkProjectionRelation.bProjection w L.sA_c_lift))
    L.cScalarField_le_jointField

instance toRawE_isDominant : L.toRawE.IsDominant := by infer_instance
instance toRawA_isDominant : L.toRawA.IsDominant := by infer_instance
instance toRawB_isDominant : L.toRawB.IsDominant := by infer_instance
instance toRawC_isDominant : L.toRawC.IsDominant := by infer_instance

end QWitness.PsiChunkFourArrowEdgeLifts

end

end AclGeom
