/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.FiniteExtensionProjection
import AclGeom.Correspondence.FiniteExtensionTransition
import AclGeom.Correspondence.FiniteCover
import AclGeom.Correspondence.RankTwoMultiplication

/-!
# Normalization of the rank-two four-arrow component

A four-arrow difference diagram starts with four independent rank-two
parameters, hence eight free coordinates, and selects four further rank-two
blocks by multiplication and division.  This file proves that all sixteen
displayed coordinates are algebraic over the eight input coordinates.  It
then packages the total coordinate field in one finite normal cover and
constructs its integral affine model.

This is a normalization of the full relational component.  It does not
assert that the final block is a single-valued rational function of any
smaller pair of inputs; that assertion requires the subsequent based-chart
cancellation argument.
-/

namespace AclGeom

open IntermediateField
open AlgebraicGeometry

noncomputable section

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The sixteen coordinates of a four-arrow diagram: the four input blocks
`s,e,a,b`, followed by the selected blocks `u,sA,uB,c`. -/
def RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram.totalTuple
    {M : RankTwoFiniteCorrespondenceMultiplication (k := k) (Ω := K)}
    {s a b e : Fin 2 → K}
    (D : M.FourArrowDifferenceDiagram s a b e) : Fin 16 → K :=
  ![s 0, s 1, e 0, e 1, a 0, a 1, b 0, b 1,
    D.u 0, D.u 1, D.sA 0, D.sA 1, D.uB 0, D.uB 1, D.c 0, D.c 1]

namespace RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram

variable {M : RankTwoFiniteCorrespondenceMultiplication (k := k) (Ω := K)}
  {s a b e : Fin 2 → K}
  (D : M.FourArrowDifferenceDiagram s a b e)

/-- Each coordinate of the first selected output `u` is algebraic over the
eight input coordinates. -/
theorem u_mem_input_racl (i : Fin 2) :
    D.u i ∈ racl k (Set.range (rankTwoFourTuple s e a b)) := by
  refine racl_mono ?_ (D.se_u.output_mem_left_right i)
  rintro z ⟨j, rfl⟩
  fin_cases j
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

/-- Each coordinate of the selected left quotient `sA` is algebraic over
the eight input coordinates. -/
theorem sA_mem_input_racl (i : Fin 2) :
    D.sA i ∈ racl k (Set.range (rankTwoFourTuple s e a b)) := by
  refine racl_le_of_subset_racl ?_ (D.sA_a_u.left_mem_right_output i)
  rintro z ⟨j, rfl⟩
  fin_cases j
  · exact subset_racl k _ ⟨4, rfl⟩
  · exact subset_racl k _ ⟨5, rfl⟩
  · exact D.u_mem_input_racl 0
  · exact D.u_mem_input_racl 1

/-- Each coordinate of the second selected output `uB` is algebraic over
the eight input coordinates. -/
theorem uB_mem_input_racl (i : Fin 2) :
    D.uB i ∈ racl k (Set.range (rankTwoFourTuple s e a b)) := by
  refine racl_mono ?_ (D.s_b_uB.output_mem_left_right i)
  rintro z ⟨j, rfl⟩
  fin_cases j
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩

/-- Each coordinate of the difference output `c` is algebraic over the
eight input coordinates. -/
theorem c_mem_input_racl (i : Fin 2) :
    D.c i ∈ racl k (Set.range (rankTwoFourTuple s e a b)) := by
  refine racl_le_of_subset_racl ?_ (D.sA_c_uB.right_mem_left_output i)
  rintro z ⟨j, rfl⟩
  fin_cases j
  · exact D.sA_mem_input_racl 0
  · exact D.sA_mem_input_racl 1
  · exact D.uB_mem_input_racl 0
  · exact D.uB_mem_input_racl 1

/-- Every displayed coordinate of the four-arrow component is algebraic
over its eight input coordinates. -/
theorem totalTuple_mem_input_racl (i : Fin 16) :
    D.totalTuple i ∈ racl k (Set.range (rankTwoFourTuple s e a b)) := by
  fin_cases i
  · exact subset_racl k _ ⟨0, rfl⟩
  · exact subset_racl k _ ⟨1, rfl⟩
  · exact subset_racl k _ ⟨2, rfl⟩
  · exact subset_racl k _ ⟨3, rfl⟩
  · exact subset_racl k _ ⟨4, rfl⟩
  · exact subset_racl k _ ⟨5, rfl⟩
  · exact subset_racl k _ ⟨6, rfl⟩
  · exact subset_racl k _ ⟨7, rfl⟩
  · exact D.u_mem_input_racl 0
  · exact D.u_mem_input_racl 1
  · exact D.sA_mem_input_racl 0
  · exact D.sA_mem_input_racl 1
  · exact D.uB_mem_input_racl 0
  · exact D.uB_mem_input_racl 1
  · exact D.c_mem_input_racl 0
  · exact D.c_mem_input_racl 1

/-- The eight input positions inside the sixteen-coordinate total tuple. -/
def inputIndex : Fin 8 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7]

/-- The positions of the `s·e=u` edge inside the total tuple. -/
def seIndex : Fin 6 → Fin 16 := ![0, 1, 2, 3, 8, 9]

/-- The positions of the `sA·a=u` edge inside the total tuple. -/
def sAaIndex : Fin 6 → Fin 16 := ![10, 11, 4, 5, 8, 9]

/-- The positions of the `s·b=uB` edge inside the total tuple. -/
def sbIndex : Fin 6 → Fin 16 := ![0, 1, 6, 7, 12, 13]

/-- The positions of the `sA·c=uB` edge inside the total tuple. -/
def sAcIndex : Fin 6 → Fin 16 := ![10, 11, 14, 15, 12, 13]

/-- The total tuple restricts to its original eight input coordinates. -/
@[simp] theorem totalTuple_comp_inputIndex :
    D.totalTuple ∘ inputIndex = rankTwoFourTuple s e a b := by
  funext i
  fin_cases i <;> rfl

/-- The first six-coordinate edge is a coordinate restriction of the total
tuple. -/
@[simp] theorem totalTuple_comp_seIndex :
    D.totalTuple ∘ seIndex = rankTwoTripleTuple s e D.u := by
  funext i
  fin_cases i <;> rfl

/-- The second six-coordinate edge is a coordinate restriction of the total
tuple. -/
@[simp] theorem totalTuple_comp_sAaIndex :
    D.totalTuple ∘ sAaIndex = rankTwoTripleTuple D.sA a D.u := by
  funext i
  fin_cases i <;> rfl

/-- The third six-coordinate edge is a coordinate restriction of the total
tuple. -/
@[simp] theorem totalTuple_comp_sbIndex :
    D.totalTuple ∘ sbIndex = rankTwoTripleTuple s b D.uB := by
  funext i
  fin_cases i <;> rfl

/-- The fourth six-coordinate edge is a coordinate restriction of the total
tuple. -/
@[simp] theorem totalTuple_comp_sAcIndex :
    D.totalTuple ∘ sAcIndex = rankTwoTripleTuple D.sA D.c D.uB := by
  funext i
  fin_cases i <;> rfl

/-- The selected sixteen-coordinate component relocates over every other
independent eight-coordinate input tuple.  All four edge relations and the
complete prime locus are preserved simultaneously. -/
theorem exists_relocation [IsAlgClosed K]
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b))
    {s' e' a' b' : Fin 2 → K}
    (hind' : AlgebraicIndependent k (rankTwoFourTuple s' e' a' b')) :
    ∃ D' : M.FourArrowDifferenceDiagram s' a' b' e',
      idealOf k D'.totalTuple = idealOf k D.totalTuple := by
  classical
  obtain ⟨v, hv, hfix⟩ := exists_tuple_relocation_fixing
    (t := rankTwoFourTuple s e a b)
    (s := rankTwoFourTuple s' e' a' b')
    (u := D.totalTuple) (e := inputIndex)
    hind hind' (fun i ↦ congrFun D.totalTuple_comp_inputIndex i)
    D.totalTuple_mem_input_racl
  let u' : Fin 2 → K := ![v 8, v 9]
  let sA' : Fin 2 → K := ![v 10, v 11]
  let uB' : Fin 2 → K := ![v 12, v 13]
  let c' : Fin 2 → K := ![v 14, v 15]
  have hinput (i : Fin 8) : v (inputIndex i) =
      rankTwoFourTuple s' e' a' b' i := hfix i
  have hse : M.IsRealization s' e' u' := by
    have h := idealOf_comp_eq_of_idealOf_eq hv seIndex
    change idealOf k (rankTwoTripleTuple s' e' u') = M.ideal
    calc
      idealOf k (rankTwoTripleTuple s' e' u') =
          idealOf k (v ∘ seIndex) := by
        congr 1
        funext i
        fin_cases i
        · exact (hinput 0).symm
        · exact (hinput 1).symm
        · exact (hinput 2).symm
        · exact (hinput 3).symm
        · rfl
        · rfl
      _ = idealOf k (D.totalTuple ∘ seIndex) := h
      _ = M.ideal := by
        simpa [RankTwoFiniteCorrespondenceMultiplication.IsRealization]
          using D.se_u
  have hsAa : M.IsRealization sA' a' u' := by
    have h := idealOf_comp_eq_of_idealOf_eq hv sAaIndex
    change idealOf k (rankTwoTripleTuple sA' a' u') = M.ideal
    calc
      idealOf k (rankTwoTripleTuple sA' a' u') =
          idealOf k (v ∘ sAaIndex) := by
        congr 1
        funext i
        fin_cases i
        · rfl
        · rfl
        · exact (hinput 4).symm
        · exact (hinput 5).symm
        · rfl
        · rfl
      _ = idealOf k (D.totalTuple ∘ sAaIndex) := h
      _ = M.ideal := by
        simpa [RankTwoFiniteCorrespondenceMultiplication.IsRealization]
          using D.sA_a_u
  have hsb : M.IsRealization s' b' uB' := by
    have h := idealOf_comp_eq_of_idealOf_eq hv sbIndex
    change idealOf k (rankTwoTripleTuple s' b' uB') = M.ideal
    calc
      idealOf k (rankTwoTripleTuple s' b' uB') =
          idealOf k (v ∘ sbIndex) := by
        congr 1
        funext i
        fin_cases i
        · exact (hinput 0).symm
        · exact (hinput 1).symm
        · exact (hinput 6).symm
        · exact (hinput 7).symm
        · rfl
        · rfl
      _ = idealOf k (D.totalTuple ∘ sbIndex) := h
      _ = M.ideal := by
        simpa [RankTwoFiniteCorrespondenceMultiplication.IsRealization]
          using D.s_b_uB
  have hsAc : M.IsRealization sA' c' uB' := by
    have h := idealOf_comp_eq_of_idealOf_eq hv sAcIndex
    change idealOf k (rankTwoTripleTuple sA' c' uB') = M.ideal
    calc
      idealOf k (rankTwoTripleTuple sA' c' uB') =
          idealOf k (v ∘ sAcIndex) := by
        congr 1
        funext i
        fin_cases i <;> rfl
      _ = idealOf k (D.totalTuple ∘ sAcIndex) := h
      _ = M.ideal := by
        simpa [RankTwoFiniteCorrespondenceMultiplication.IsRealization]
          using D.sA_c_uB
  let D' : M.FourArrowDifferenceDiagram s' a' b' e' :=
    { u := u'
      sA := sA'
      uB := uB'
      c := c'
      se_u := hse
      sA_a_u := hsAa
      s_b_uB := hsb
      sA_c_uB := hsAc }
  refine ⟨D', ?_⟩
  calc
    idealOf k D'.totalTuple = idealOf k v := by
      congr 1
      funext i
      fin_cases i
      · exact (hinput 0).symm
      · exact (hinput 1).symm
      · exact (hinput 2).symm
      · exact (hinput 3).symm
      · exact (hinput 4).symm
      · exact (hinput 5).symm
      · exact (hinput 6).symm
      · exact (hinput 7).symm
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    _ = idealOf k D.totalTuple := hv

/-- The function field of the eight free input coordinates. -/
def inputField
    (_D : M.FourArrowDifferenceDiagram s a b e) : IntermediateField k K :=
  adjoin k (Set.range (rankTwoFourTuple s e a b))

/-- The function field generated by all sixteen displayed coordinates. -/
def totalField : IntermediateField k K :=
  adjoin k (Set.range D.totalTuple)

/-- The input field embeds in the total four-arrow field. -/
theorem inputField_le_totalField : D.inputField ≤ D.totalField := by
  apply adjoin.mono
  rintro z ⟨i, rfl⟩
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩

/-- The total four-arrow field as an extension of its eight-coordinate
input field. -/
def totalOverInput : IntermediateField (↥D.inputField) K :=
  extendScalars D.inputField_le_totalField

/-- The full four-arrow component is finite over its eight free input
coordinates. -/
theorem totalOverInput_finiteDimensional :
    FiniteDimensional (↥D.inputField) (↥D.totalOverInput) := by
  have key : D.totalOverInput =
      adjoin (↥D.inputField) (Set.range D.totalTuple) := by
    refine restrictScalars_injective k ?_
    unfold totalOverInput inputField totalField
    rw [adjoin_adjoin_left, extendScalars_restrictScalars, adjoin_union]
    exact (sup_eq_right.2 D.inputField_le_totalField).symm
  rw [key]
  letI : Fintype (Set.range D.totalTuple) :=
    Set.Finite.fintype (Set.finite_range D.totalTuple)
  exact finiteDimensional_adjoin fun x hx ↦ by
    obtain ⟨i, rfl⟩ := hx
    exact ((mem_racl_iff k).1 (D.totalTuple_mem_input_racl i)).isIntegral

/-- One normal closure containing the entire four-arrow component. -/
def normalCover : IntermediateField (↥D.inputField) K :=
  FiniteCover.normalClosureOver D.inputField_le_totalField

/-- The total four-arrow field embeds in its normal closure. -/
theorem totalOverInput_le_normalCover :
    D.totalOverInput ≤ D.normalCover :=
  FiniteCover.extendScalars_le_normalClosureOver D.inputField_le_totalField

/-- The normal four-arrow cover remains finite over the eight input
coordinates. -/
theorem normalCover_finiteDimensional :
    FiniteDimensional (↥D.inputField) (↥D.normalCover) :=
  FiniteCover.normalClosureOver_finiteDimensional
    D.inputField_le_totalField D.totalOverInput_finiteDimensional

/-- In an algebraically closed ambient field, the four-arrow cover is a
normal extension of the eight-coordinate input field. -/
theorem normalCover_normal [IsAlgClosed K] :
    Normal (↥D.inputField) (↥D.normalCover) := by
  letI := D.totalOverInput_finiteDimensional
  exact FiniteCover.normalClosureOver_normal D.inputField_le_totalField
    (Algebra.IsAlgebraic.of_finite (↥D.inputField) (↥D.totalOverInput))

/-- Equality of complete four-arrow loci restricts to equality of their
eight-coordinate input loci. -/
theorem inputIdeal_eq_of_totalIdeal_eq
    {s' a' b' e' : Fin 2 → K}
    (V : M.FourArrowDifferenceDiagram s' a' b' e')
    (h : idealOf k D.totalTuple = idealOf k V.totalTuple) :
    idealOf k (rankTwoFourTuple s e a b) =
      idealOf k (rankTwoFourTuple s' e' a' b') := by
  have ht := idealOf_comp_eq_of_idealOf_eq h inputIndex
  simpa using ht

/-- Equal complete loci canonically identify the eight-coordinate input
function fields. -/
def inputEquiv
    {s' a' b' e' : Fin 2 → K}
    (V : M.FourArrowDifferenceDiagram s' a' b' e')
    (h : idealOf k D.totalTuple = idealOf k V.totalTuple) :
    (↥D.inputField) ≃ₐ[k] (↥V.inputField) :=
  locusFunctionFieldEquivOfIdealEq (D.inputIdeal_eq_of_totalIdeal_eq V h)

/-- Equal complete loci canonically identify the sixteen-coordinate total
function fields. -/
def totalEquiv
    {s' a' b' e' : Fin 2 → K}
    (V : M.FourArrowDifferenceDiagram s' a' b' e')
    (h : idealOf k D.totalTuple = idealOf k V.totalTuple) :
    (↥D.totalField) ≃ₐ[k] (↥V.totalField) :=
  locusFunctionFieldEquivOfIdealEq h

/-- The input and total field equivalences form a commuting equivalence of
finite extensions. -/
def extensionEquiv
    {s' a' b' e' : Fin 2 → K}
    (V : M.FourArrowDifferenceDiagram s' a' b' e')
    (h : idealOf k D.totalTuple = idealOf k V.totalTuple) :
    FiniteCover.ExtensionEquiv D.inputField_le_totalField
      V.inputField_le_totalField where
  baseEquiv := D.inputEquiv V h
  totalEquiv := D.totalEquiv V h
  commutes := by
    apply adjoin_algHom_ext k
    rintro _ ⟨i, rfl⟩
    let xi : D.inputField :=
      ⟨rankTwoFourTuple s e a b i,
        subset_adjoin k _ (Set.mem_range_self i)⟩
    change D.totalEquiv V h
        (IntermediateField.inclusion D.inputField_le_totalField xi) =
      IntermediateField.inclusion V.inputField_le_totalField
        (D.inputEquiv V h xi)
    apply Subtype.ext
    have hsource :
        IntermediateField.inclusion D.inputField_le_totalField xi =
          ⟨D.totalTuple (inputIndex i),
            subset_adjoin k _ (Set.mem_range_self (inputIndex i))⟩ := by
      apply Subtype.ext
      exact (congrFun D.totalTuple_comp_inputIndex i).symm
    rw [hsource]
    have htotal := congrArg Subtype.val
      (locusFunctionFieldEquivOfIdealEq_apply h (inputIndex i))
    have hbase := congrArg Subtype.val
      (locusFunctionFieldEquivOfIdealEq_apply
        (D.inputIdeal_eq_of_totalIdeal_eq V h) i)
    exact htotal.trans <| (congrFun V.totalTuple_comp_inputIndex i).trans hbase.symm

/-- Equal complete loci have semilinearly equivalent concrete normal
covers. -/
noncomputable def normalCoverEquiv [IsAlgClosed K]
    {s' a' b' e' : Fin 2 → K}
    (V : M.FourArrowDifferenceDiagram s' a' b' e')
    (h : idealOf k D.totalTuple = idealOf k V.totalTuple) :
    (↥D.normalCover) ≃+* (↥V.normalCover) := by
  have hfinD := D.totalOverInput_finiteDimensional
  have hfinV := V.totalOverInput_finiteDimensional
  letI : FiniteDimensional (↥D.inputField)
      (↥(extendScalars D.inputField_le_totalField)) := by
    change FiniteDimensional (↥D.inputField) (↥D.totalOverInput)
    exact hfinD
  letI : FiniteDimensional (↥V.inputField)
      (↥(extendScalars V.inputField_le_totalField)) := by
    change FiniteDimensional (↥V.inputField) (↥V.totalOverInput)
    exact hfinV
  let cD := FiniteCover.normalClosureOverEquivCanonical
    D.inputField_le_totalField (Algebra.IsAlgebraic.of_finite _ _)
  let cV := FiniteCover.normalClosureOverEquivCanonical
    V.inputField_le_totalField (Algebra.IsAlgebraic.of_finite _ _)
  exact cD.toRingEquiv |>.trans
    (D.extensionEquiv V h).normalLift.normalEquiv |>.trans
      cV.symm.toRingEquiv

/-- Normal-cover transport is semilinear over the canonical input-field
transport. -/
@[simp] theorem normalCoverEquiv_algebraMap [IsAlgClosed K]
    {s' a' b' e' : Fin 2 → K}
    (V : M.FourArrowDifferenceDiagram s' a' b' e')
    (h : idealOf k D.totalTuple = idealOf k V.totalTuple)
    (x : D.inputField) :
    D.normalCoverEquiv V h (algebraMap (↥D.inputField) (↥D.normalCover) x) =
      algebraMap (↥V.inputField) (↥V.normalCover) (D.inputEquiv V h x) := by
  letI : FiniteDimensional (↥D.inputField)
      (↥(extendScalars D.inputField_le_totalField)) := by
    change FiniteDimensional (↥D.inputField) (↥D.totalOverInput)
    exact D.totalOverInput_finiteDimensional
  letI : FiniteDimensional (↥V.inputField)
      (↥(extendScalars V.inputField_le_totalField)) := by
    change FiniteDimensional (↥V.inputField) (↥V.totalOverInput)
    exact V.totalOverInput_finiteDimensional
  let cD := FiniteCover.normalClosureOverEquivCanonical
    D.inputField_le_totalField (Algebra.IsAlgebraic.of_finite _ _)
  let cV := FiniteCover.normalClosureOverEquivCanonical
    V.inputField_le_totalField (Algebra.IsAlgebraic.of_finite _ _)
  let n := (D.extensionEquiv V h).normalLift
  change cV.symm.toRingEquiv
      (n.normalEquiv
        (cD.toRingEquiv
          (algebraMap (↥D.inputField) (↥D.normalCover) x))) =
    algebraMap (↥V.inputField) (↥V.normalCover) (D.inputEquiv V h x)
  rw [show cD.toRingEquiv
      (algebraMap (↥D.inputField) (↥D.normalCover) x) =
        algebraMap (↥D.inputField)
          (↥(FiniteCover.canonicalNormalClosure D.inputField_le_totalField)) x
    from cD.commutes x]
  rw [n.normal_commutes_apply]
  exact cV.symm.commutes (D.inputEquiv V h x)

/-- The semilinear normal-cover comparison is a ground-field algebra
equivalence. -/
noncomputable def normalCoverAlgEquiv [IsAlgClosed K]
    {s' a' b' e' : Fin 2 → K}
    (V : M.FourArrowDifferenceDiagram s' a' b' e')
    (h : idealOf k D.totalTuple = idealOf k V.totalTuple) :
    (↥D.normalCover) ≃ₐ[k] (↥V.normalCover) :=
  { D.normalCoverEquiv V h with
    commutes' := fun r ↦ by
      rw [IsScalarTower.algebraMap_apply k (↥D.inputField) (↥D.normalCover),
        IsScalarTower.algebraMap_apply k (↥V.inputField) (↥V.normalCover)]
      calc
        _ = algebraMap (↥V.inputField) (↥V.normalCover)
              (D.inputEquiv V h (algebraMap k (↥D.inputField) r)) :=
          D.normalCoverEquiv_algebraMap V h
            (algebraMap k (↥D.inputField) r)
        _ = _ := by
          congr 1
          exact (D.inputEquiv V h).commutes r }

/-- Normalize the comparison between two complete four-arrow loci through
one fixed reference realization. -/
noncomputable def referenceNormalCoverAlgEquiv [IsAlgClosed K]
    {sr ar br er : Fin 2 → K}
    (R : M.FourArrowDifferenceDiagram sr ar br er)
    (hRD : idealOf k R.totalTuple = idealOf k D.totalTuple)
    {s' a' b' e' : Fin 2 → K}
    (V : M.FourArrowDifferenceDiagram s' a' b' e')
    (hRV : idealOf k R.totalTuple = idealOf k V.totalTuple) :
    (↥D.normalCover) ≃ₐ[k] (↥V.normalCover) :=
  (R.normalCoverAlgEquiv D hRD).symm.trans
    (R.normalCoverAlgEquiv V hRV)

/-- Reference normalization makes the self-comparison literal. -/
@[simp] theorem referenceNormalCoverAlgEquiv_self [IsAlgClosed K]
    {sr ar br er : Fin 2 → K}
    (R : M.FourArrowDifferenceDiagram sr ar br er)
    (hRD : idealOf k R.totalTuple = idealOf k D.totalTuple) :
    D.referenceNormalCoverAlgEquiv R hRD D hRD = AlgEquiv.refl := by
  unfold referenceNormalCoverAlgEquiv
  ext x
  simp

/-- Reversing a reference-normalized comparison gives the comparison in
the opposite direction. -/
@[simp] theorem referenceNormalCoverAlgEquiv_symm [IsAlgClosed K]
    {sr ar br er : Fin 2 → K}
    (R : M.FourArrowDifferenceDiagram sr ar br er)
    (hRD : idealOf k R.totalTuple = idealOf k D.totalTuple)
    {s' a' b' e' : Fin 2 → K}
    (V : M.FourArrowDifferenceDiagram s' a' b' e')
    (hRV : idealOf k R.totalTuple = idealOf k V.totalTuple) :
    (D.referenceNormalCoverAlgEquiv R hRD V hRV).symm =
      V.referenceNormalCoverAlgEquiv R hRV D hRD := by
  unfold referenceNormalCoverAlgEquiv
  ext x
  simp

/-- Reference-normalized normal-cover comparisons satisfy a strict
transitive cocycle. -/
@[simp] theorem referenceNormalCoverAlgEquiv_trans [IsAlgClosed K]
    {sr ar br er : Fin 2 → K}
    (R : M.FourArrowDifferenceDiagram sr ar br er)
    (hRD : idealOf k R.totalTuple = idealOf k D.totalTuple)
    {s' a' b' e' : Fin 2 → K}
    (V : M.FourArrowDifferenceDiagram s' a' b' e')
    (hRV : idealOf k R.totalTuple = idealOf k V.totalTuple)
    {s'' a'' b'' e'' : Fin 2 → K}
    (W : M.FourArrowDifferenceDiagram s'' a'' b'' e'')
    (hRW : idealOf k R.totalTuple = idealOf k W.totalTuple) :
    (D.referenceNormalCoverAlgEquiv R hRD V hRV).trans
        (V.referenceNormalCoverAlgEquiv R hRV W hRW) =
      D.referenceNormalCoverAlgEquiv R hRD W hRW := by
  unfold referenceNormalCoverAlgEquiv
  ext x
  simp

/-- The eight free input coordinates, lifted into their generated field. -/
abbrev inputCoordinates : Fin 8 → D.inputField :=
  FiniteExtensionChart.liftedCoordinates (k := k)
    (rankTwoFourTuple s e a b)

/-- The input coordinates generate the complete eight-coordinate function
field. -/
theorem adjoin_inputCoordinates_eq_top :
    adjoin k (Set.range D.inputCoordinates) = ⊤ :=
  FiniteExtensionChart.adjoin_liftedCoordinates_eq_top
    (k := k) (rankTwoFourTuple s e a b)

/-- The integral affine chart attached to the normalized four-arrow
component over its eight free coordinates. -/
abbrev algebraicChart : Scheme := by
  letI := D.normalCover_finiteDimensional
  exact FiniteExtensionChart.scheme (k := k)
    (K := ↥D.inputField) (L := ↥D.normalCover) D.inputCoordinates

/-- Equal complete four-arrow loci determine a dominant rational comparison
between their normalized affine charts. -/
noncomputable def transitionRationalMap [IsAlgClosed K]
    {s' a' b' e' : Fin 2 → K}
    (V : M.FourArrowDifferenceDiagram s' a' b' e')
    (h : idealOf k D.totalTuple = idealOf k V.totalTuple) :
    Scheme.RationalMap D.algebraicChart V.algebraicChart := by
  letI := D.normalCover_finiteDimensional
  letI := V.normalCover_finiteDimensional
  exact FiniteExtensionTransition.rationalMap
    D.inputCoordinates V.inputCoordinates
    D.adjoin_inputCoordinates_eq_top V.adjoin_inputCoordinates_eq_top
    (D.normalCoverAlgEquiv V h)

instance transitionRationalMap_isDominant [IsAlgClosed K]
    {s' a' b' e' : Fin 2 → K}
    (V : M.FourArrowDifferenceDiagram s' a' b' e')
    (h : idealOf k D.totalTuple = idealOf k V.totalTuple) :
    (D.transitionRationalMap V h).IsDominant := by
  letI := D.normalCover_finiteDimensional
  letI := V.normalCover_finiteDimensional
  unfold transitionRationalMap
  infer_instance

/-- Equal complete loci have isomorphic dense opens in their normalized
affine charts. -/
noncomputable def transitionPartialIso [IsAlgClosed K]
    {s' a' b' e' : Fin 2 → K}
    (V : M.FourArrowDifferenceDiagram s' a' b' e')
    (h : idealOf k D.totalTuple = idealOf k V.totalTuple) :
    D.algebraicChart.PartialIso V.algebraicChart := by
  letI := D.normalCover_finiteDimensional
  letI := V.normalCover_finiteDimensional
  exact FiniteExtensionTransition.partialIso
    D.inputCoordinates V.inputCoordinates
    D.adjoin_inputCoordinates_eq_top V.adjoin_inputCoordinates_eq_top
    (D.normalCoverAlgEquiv V h)

/-- The rational comparison of two complete-locus charts, normalized
through one fixed reference realization. -/
noncomputable def referenceTransitionRationalMap [IsAlgClosed K]
    {sr ar br er : Fin 2 → K}
    (R : M.FourArrowDifferenceDiagram sr ar br er)
    (hRD : idealOf k R.totalTuple = idealOf k D.totalTuple)
    {s' a' b' e' : Fin 2 → K}
    (V : M.FourArrowDifferenceDiagram s' a' b' e')
    (hRV : idealOf k R.totalTuple = idealOf k V.totalTuple) :
    Scheme.RationalMap D.algebraicChart V.algebraicChart := by
  letI := D.normalCover_finiteDimensional
  letI := V.normalCover_finiteDimensional
  exact FiniteExtensionTransition.rationalMap
    D.inputCoordinates V.inputCoordinates
    D.adjoin_inputCoordinates_eq_top V.adjoin_inputCoordinates_eq_top
    (D.referenceNormalCoverAlgEquiv R hRD V hRV)

instance referenceTransitionRationalMap_isDominant [IsAlgClosed K]
    {sr ar br er : Fin 2 → K}
    (R : M.FourArrowDifferenceDiagram sr ar br er)
    (hRD : idealOf k R.totalTuple = idealOf k D.totalTuple)
    {s' a' b' e' : Fin 2 → K}
    (V : M.FourArrowDifferenceDiagram s' a' b' e')
    (hRV : idealOf k R.totalTuple = idealOf k V.totalTuple) :
    (D.referenceTransitionRationalMap R hRD V hRV).IsDominant := by
  letI := D.normalCover_finiteDimensional
  letI := V.normalCover_finiteDimensional
  unfold referenceTransitionRationalMap
  infer_instance

/-- Reference-normalized chart comparisons inherit the strict transitive
cocycle from their ambient normal-cover equivalences. -/
theorem referenceTransitionRationalMap_comp [IsAlgClosed K]
    {sr ar br er : Fin 2 → K}
    (R : M.FourArrowDifferenceDiagram sr ar br er)
    (hRD : idealOf k R.totalTuple = idealOf k D.totalTuple)
    {s' a' b' e' : Fin 2 → K}
    (V : M.FourArrowDifferenceDiagram s' a' b' e')
    (hRV : idealOf k R.totalTuple = idealOf k V.totalTuple)
    {s'' a'' b'' e'' : Fin 2 → K}
    (W : M.FourArrowDifferenceDiagram s'' a'' b'' e'')
    (hRW : idealOf k R.totalTuple = idealOf k W.totalTuple) :
    (D.referenceTransitionRationalMap R hRD V hRV).comp
        (V.referenceTransitionRationalMap R hRV W hRW) =
      D.referenceTransitionRationalMap R hRD W hRW := by
  letI := D.normalCover_finiteDimensional
  letI := V.normalCover_finiteDimensional
  letI := W.normalCover_finiteDimensional
  unfold referenceTransitionRationalMap
  rw [FiniteExtensionTransition.rationalMap_comp]
  rw [referenceNormalCoverAlgEquiv_trans]

/-- The function field generated by one rank-two block. -/
def blockField (p : Fin 2 → K) : IntermediateField k K :=
  adjoin k (Set.range p)

/-- The two coordinates of a rank-two block, lifted into their generated
field. -/
abbrev blockCoordinates (p : Fin 2 → K) : Fin 2 → blockField (k := k) p :=
  FiniteExtensionChart.liftedCoordinates (k := k) p

/-- The two lifted coordinates generate the rank-two block field. -/
theorem adjoin_blockCoordinates_eq_top (p : Fin 2 → K) :
    adjoin k (Set.range (blockCoordinates (k := k) p)) = ⊤ :=
  FiniteExtensionChart.adjoin_liftedCoordinates_eq_top (k := k) p

/-- The integral affine chart of one displayed rank-two block. -/
abbrev blockAlgebraicChart (p : Fin 2 → K) : Scheme :=
  FiniteExtensionChart.scheme (k := k)
    (K := ↥(blockField (k := k) p))
    (L := ↥(blockField (k := k) p))
    (blockCoordinates (k := k) p)

/-- Any displayed block contained in the total coordinate field embeds in
the common normal four-arrow cover. -/
def blockFieldToNormalCover (p : Fin 2 → K)
    (hp : blockField (k := k) p ≤ D.totalField) :
    (↥(blockField (k := k) p)) →ₐ[k] (↥D.normalCover) := by
  let hle : (blockField (k := k) p).restrictScalars k ≤
      D.normalCover.restrictScalars k := by
    intro x hx
    apply D.totalOverInput_le_normalCover
    exact hp hx
  exact IntermediateField.inclusion hle

/-- A block projection from the normalized four-arrow component.  The
field-containment argument identifies which displayed block is selected. -/
def projectionToBlock (p : Fin 2 → K)
    (hp : blockField (k := k) p ≤ D.totalField) :
    Scheme.RationalMap D.algebraicChart (blockAlgebraicChart (k := k) p) := by
  letI := D.normalCover_finiteDimensional
  exact FiniteExtensionProjection.rationalMap
    D.inputCoordinates (blockCoordinates (k := k) p)
    D.adjoin_inputCoordinates_eq_top (D.blockFieldToNormalCover p hp)

instance projectionToBlock_isDominant (p : Fin 2 → K)
    (hp : blockField (k := k) p ≤ D.totalField) :
    (D.projectionToBlock p hp).IsDominant := by
  letI := D.normalCover_finiteDimensional
  unfold projectionToBlock
  infer_instance

/-- The `e` input block lies in the total four-arrow field. -/
theorem eBlockField_le_totalField :
    blockField (k := k) e ≤ D.totalField := by
  apply adjoin.mono
  rintro z ⟨i, rfl⟩
  fin_cases i
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

/-- The `a` input block lies in the total four-arrow field. -/
theorem aBlockField_le_totalField :
    blockField (k := k) a ≤ D.totalField := by
  apply adjoin.mono
  rintro z ⟨i, rfl⟩
  fin_cases i
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩

/-- The `b` input block lies in the total four-arrow field. -/
theorem bBlockField_le_totalField :
    blockField (k := k) b ≤ D.totalField := by
  apply adjoin.mono
  rintro z ⟨i, rfl⟩
  fin_cases i
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩

/-- The selected difference-output block lies in the total four-arrow
field. -/
theorem cBlockField_le_totalField :
    blockField (k := k) D.c ≤ D.totalField := by
  apply adjoin.mono
  rintro z ⟨i, rfl⟩
  fin_cases i
  · exact ⟨14, rfl⟩
  · exact ⟨15, rfl⟩

/-- Dominant rational projection to the first based input `e`. -/
abbrev toE : Scheme.RationalMap D.algebraicChart
    (blockAlgebraicChart (k := k) e) :=
  D.projectionToBlock e D.eBlockField_le_totalField

/-- Dominant rational projection to the inverse input `a`. -/
abbrev toA : Scheme.RationalMap D.algebraicChart
    (blockAlgebraicChart (k := k) a) :=
  D.projectionToBlock a D.aBlockField_le_totalField

/-- Dominant rational projection to the second based input `b`. -/
abbrev toB : Scheme.RationalMap D.algebraicChart
    (blockAlgebraicChart (k := k) b) :=
  D.projectionToBlock b D.bBlockField_le_totalField

/-- Dominant rational projection to the selected difference output `c`. -/
abbrev toC : Scheme.RationalMap D.algebraicChart
    (blockAlgebraicChart (k := k) D.c) :=
  D.projectionToBlock D.c D.cBlockField_le_totalField

instance toE_isDominant : D.toE.IsDominant := by infer_instance
instance toA_isDominant : D.toA.IsDominant := by infer_instance
instance toB_isDominant : D.toB.IsDominant := by infer_instance
instance toC_isDominant : D.toC.IsDominant := by infer_instance

end RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram

end

end AclGeom
