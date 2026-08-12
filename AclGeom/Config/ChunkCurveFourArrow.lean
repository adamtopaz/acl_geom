/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveRelocation
import AclGeom.Config.ChunkFourArrowReference

/-!
# Curve triangles on the four Ψ parameter edges

A rank-two four-arrow difference diagram has four parameter-composition
edges.  Starting from eight independent input coordinates, this file finds
an explicit curve source generic over each edge: an unused coordinate of
the ambient input tuple.  The complete selected Ψ curve triangle can then
be relocated over all four parameter edges.

The resulting package contains four literal finite-normal-cover
composition identities.  Its next use is to identify the repeated source,
middle, and target cover fields through common reference fields and thereby
construct a semantic `FieldEquiv.FourArrowDiagram`.
-/

namespace AclGeom

open IntermediateField

noncomputable section

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

namespace RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram

variable {M : RankTwoFiniteCorrespondenceMultiplication (k := k) (Ω := K)}
  {s a b e : Fin 2 → K}
  (D : M.FourArrowDifferenceDiagram s a b e)

/-- Replacing the first output in the independent ambient input tuple
preserves independence. -/
theorem s_u_a_b_independent
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicIndependent k (rankTwoFourTuple s D.u a b) :=
  algebraicIndependent_of_racl_range_eq hind
    (D.se_u.racl_four_leftRight_eq_leftOutput a b)

/-- Replacing the first left block by its selected quotient also preserves
the ambient eight-coordinate independence. -/
theorem s_sA_a_b_independent
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicIndependent k (rankTwoFourTuple s D.sA a b) :=
  algebraicIndependent_of_racl_range_eq (D.s_u_a_b_independent hind)
    (D.sA_a_u.racl_four_outputRight_eq_leftRight s b)

/-- Replacing the second right block by its selected output gives the
third independent ambient presentation used by the last edge. -/
theorem s_sA_a_uB_independent
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicIndependent k (rankTwoFourTuple s D.sA a D.uB) :=
  algebraicIndependent_of_racl_range_eq (D.s_sA_a_b_independent hind)
    (D.s_b_uB.racl_four_firstRight_eq_firstOutput D.sA a)

/-- Replacing the final output block by its right input gives an
independent presentation containing the fourth right-arrow label `c`.
This is the coefficient presentation needed for a semilinear chart of the
last face, rather than an automorphism fixing the original common base. -/
theorem s_sA_a_c_independent
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    AlgebraicIndependent k (rankTwoFourTuple s D.sA a D.c) := by
  apply algebraicIndependent_of_racl_range_eq
    (D.s_sA_a_uB_independent hind)
  have h := D.sA_c_uB.racl_four_firstRight_eq_firstOutput s a
  rw [rankTwoFourTuple_range, rankTwoFourTuple_range] at h ⊢
  simpa only [Set.union_assoc, Set.union_left_comm, Set.union_comm] using h.symm

/-- The original independent inputs and the algebraic-output presentation
have the same relative algebraic closure.  This records the whole
four-arrow interalgebraicity chain, not only the independence consequence
used above. -/
theorem racl_s_e_a_b_eq_s_sA_a_c :
    racl k (Set.range (rankTwoFourTuple s e a b)) =
      racl k (Set.range (rankTwoFourTuple s D.sA a D.c)) := by
  have hlast := D.sA_c_uB.racl_four_firstRight_eq_firstOutput s a
  rw [rankTwoFourTuple_range, rankTwoFourTuple_range] at hlast
  have hlast' :
      racl k (Set.range (rankTwoFourTuple s D.sA a D.uB)) =
        racl k (Set.range (rankTwoFourTuple s D.sA a D.c)) := by
    rw [rankTwoFourTuple_range, rankTwoFourTuple_range]
    simpa only [Set.union_assoc, Set.union_left_comm, Set.union_comm]
      using hlast.symm
  exact (D.se_u.racl_four_leftRight_eq_leftOutput a b).trans
    ((D.sA_a_u.racl_four_outputRight_eq_leftRight s b).trans
      ((D.s_b_uB.racl_four_firstRight_eq_firstOutput D.sA a).trans hlast'))

end RankTwoFiniteCorrespondenceMultiplication.FourArrowDifferenceDiagram

namespace QWitness

variable (w : QWitness k K)

private theorem notMem_racl_composition_of_base
    {p q r : Fin 2 → K} {base : Fin 4 → K} {x : K}
    (hx : x ∉ racl k (Set.range base))
    (hparam : ∀ i,
      compositionParameterTuple p q r i ∈ racl k (Set.range base)) :
    x ∉ racl k (Set.range (compositionParameterTuple p q r)) := by
  intro hmem
  apply hx
  exact racl_le_of_subset_racl
    (by rintro _ ⟨i, rfl⟩; exact hparam i) hmem

namespace PsiParameterFourArrowDifferenceDiagram

variable {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  (D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e)

/-- On the edge `s·e=u`, the first coordinate of the unused `a` input is
generic over all six edge parameters. -/
theorem a_zero_notMem_racl_se_parameters
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    a 0 ∉ racl k
      (Set.range (compositionParameterTuple s e D.u)) := by
  let S : Set (Fin 8) := {0, 1, 2, 3}
  have himage : rankTwoFourTuple s e a b '' S =
      Set.range (rankTwoPairTuple s e) := by
    ext z
    simp [S, rankTwoFourTuple, rankTwoPairTuple]
    tauto
  have hx := AlgebraicIndependent.notMem_racl_image hind
    (S := S) (i := (4 : Fin 8)) (by simp [S])
  rw [himage] at hx
  have hx' : a 0 ∉ racl k (Set.range (rankTwoPairTuple s e)) := by
    simpa [rankTwoFourTuple] using hx
  exact notMem_racl_composition_of_base hx' fun i ↦ by
    fin_cases i
    · exact subset_racl k _ (Set.mem_range_self 0)
    · exact subset_racl k _ (Set.mem_range_self 1)
    · exact subset_racl k _ (Set.mem_range_self 2)
    · exact subset_racl k _ (Set.mem_range_self 3)
    · exact D.se_u.output_mem_left_right 0
    · exact D.se_u.output_mem_left_right 1

/-- On the edge `sA·a=u`, the first coordinate of the unused `b` input is
generic over all six edge parameters. -/
theorem b_zero_notMem_racl_sAa_parameters
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    b 0 ∉ racl k
      (Set.range (compositionParameterTuple D.sA a D.u)) := by
  let q : Fin 8 → K := rankTwoFourTuple s D.sA a b
  let S : Set (Fin 8) := {2, 3, 4, 5}
  have hq : AlgebraicIndependent k q := D.s_sA_a_b_independent hind
  have himage : q '' S =
      Set.range (rankTwoPairTuple D.sA a) := by
    ext z
    simp [q, S, rankTwoFourTuple, rankTwoPairTuple]
    tauto
  have hx := AlgebraicIndependent.notMem_racl_image hq
    (S := S) (i := (6 : Fin 8)) (by simp [S])
  rw [himage] at hx
  have hx' : b 0 ∉ racl k (Set.range (rankTwoPairTuple D.sA a)) := by
    simpa [q, rankTwoFourTuple] using hx
  exact notMem_racl_composition_of_base hx' fun i ↦ by
    fin_cases i
    · exact subset_racl k _ (Set.mem_range_self 0)
    · exact subset_racl k _ (Set.mem_range_self 1)
    · exact subset_racl k _ (Set.mem_range_self 2)
    · exact subset_racl k _ (Set.mem_range_self 3)
    · exact D.sA_a_u.output_mem_left_right 0
    · exact D.sA_a_u.output_mem_left_right 1

/-- On the edge `s·b=uB`, the first coordinate of the unused `e` input is
generic over all six edge parameters. -/
theorem e_zero_notMem_racl_sb_parameters
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    e 0 ∉ racl k
      (Set.range (compositionParameterTuple s b D.uB)) := by
  let S : Set (Fin 8) := {0, 1, 6, 7}
  have himage : rankTwoFourTuple s e a b '' S =
      Set.range (rankTwoPairTuple s b) := by
    ext z
    simp [S, rankTwoFourTuple, rankTwoPairTuple]
    tauto
  have hx := AlgebraicIndependent.notMem_racl_image hind
    (S := S) (i := (2 : Fin 8)) (by simp [S])
  rw [himage] at hx
  have hx' : e 0 ∉ racl k (Set.range (rankTwoPairTuple s b)) := by
    simpa [rankTwoFourTuple] using hx
  exact notMem_racl_composition_of_base hx' fun i ↦ by
    fin_cases i
    · exact subset_racl k _ (Set.mem_range_self 0)
    · exact subset_racl k _ (Set.mem_range_self 1)
    · exact subset_racl k _ (Set.mem_range_self 2)
    · exact subset_racl k _ (Set.mem_range_self 3)
    · exact D.s_b_uB.output_mem_left_right 0
    · exact D.s_b_uB.output_mem_left_right 1

/-- On the last edge `sA·c=uB`, the first coordinate of the unused `s`
input is generic over all six edge parameters. -/
theorem s_zero_notMem_racl_sAc_parameters
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    s 0 ∉ racl k
      (Set.range (compositionParameterTuple D.sA D.c D.uB)) := by
  let q : Fin 8 → K := rankTwoFourTuple s D.sA a D.uB
  let base : Fin 4 → K := rankTwoPairTuple D.sA D.uB
  let S : Set (Fin 8) := {2, 3, 6, 7}
  have hq : AlgebraicIndependent k q := D.s_sA_a_uB_independent hind
  have himage : q '' S = Set.range base := by
    ext z
    simp [q, base, S, rankTwoFourTuple, rankTwoPairTuple]
    tauto
  have hx := AlgebraicIndependent.notMem_racl_image hq
    (S := S) (i := (0 : Fin 8)) (by simp [S])
  rw [himage] at hx
  have hx' : s 0 ∉ racl k (Set.range base) := by
    simpa [q, rankTwoFourTuple] using hx
  exact notMem_racl_composition_of_base hx' fun i ↦ by
    fin_cases i
    · exact subset_racl k _ (Set.mem_range_self 0)
    · exact subset_racl k _ (Set.mem_range_self 1)
    · exact D.sA_c_uB.right_mem_left_output 0
    · exact D.sA_c_uB.right_mem_left_output 1
    · exact subset_racl k _ (Set.mem_range_self 2)
    · exact subset_racl k _ (Set.mem_range_self 3)

end PsiParameterFourArrowDifferenceDiagram

/-- Curve-coordinate composition triangles above all four parameter edges
of a Ψ difference diagram.  The source equalities record the concrete
unused ambient coordinates chosen to witness edgewise genericity. -/
structure PsiCurveFourArrowRealizations
    (hψ : w.Psi) {s a b e : Fin 2 → K}
    (D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e) where
  /-- Curve triangle above `s·e=u`. -/
  se : w.PsiCurveCompositionRealization s e D.u
  /-- Its chosen source is the unused coordinate `a₀`. -/
  se_source : se.source = a 0
  /-- Curve triangle above `sA·a=u`. -/
  sAa : w.PsiCurveCompositionRealization D.sA a D.u
  /-- Its chosen source is the unused coordinate `b₀`. -/
  sAa_source : sAa.source = b 0
  /-- Curve triangle above `s·b=uB`. -/
  sb : w.PsiCurveCompositionRealization s b D.uB
  /-- Its chosen source is the unused coordinate `e₀`. -/
  sb_source : sb.source = e 0
  /-- Curve triangle above `sA·c=uB`. -/
  sAc : w.PsiCurveCompositionRealization D.sA D.c D.uB
  /-- Its chosen source is the unused coordinate `s₀`. -/
  sAc_source : sAc.source = s 0

/-- Eight independent ambient inputs supply curve-coordinate triangles on
all four parameter edges simultaneously. -/
theorem exists_psiCurveFourArrowRealizations [IsAlgClosed K]
    (hψ : w.Psi) {s a b e : Fin 2 → K}
    (D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e)
    (hind : AlgebraicIndependent k (rankTwoFourTuple s e a b)) :
    Nonempty (w.PsiCurveFourArrowRealizations hψ D) := by
  have hse : w.psiFamilyCompositionRelation s e D.u :=
    (w.psiFamilyCompositionRelation_iff_isRealization hψ s e D.u).2 D.se_u
  have hsAa : w.psiFamilyCompositionRelation D.sA a D.u :=
    (w.psiFamilyCompositionRelation_iff_isRealization
      hψ D.sA a D.u).2 D.sA_a_u
  have hsb : w.psiFamilyCompositionRelation s b D.uB :=
    (w.psiFamilyCompositionRelation_iff_isRealization hψ s b D.uB).2
      D.s_b_uB
  have hsAc : w.psiFamilyCompositionRelation D.sA D.c D.uB :=
    (w.psiFamilyCompositionRelation_iff_isRealization
      hψ D.sA D.c D.uB).2 D.sA_c_uB
  obtain ⟨Rse, hRse⟩ := w.exists_psiCurveCompositionRealization hψ hse
    (D.a_zero_notMem_racl_se_parameters hind)
  obtain ⟨RsAa, hRsAa⟩ := w.exists_psiCurveCompositionRealization hψ hsAa
    (D.b_zero_notMem_racl_sAa_parameters hind)
  obtain ⟨Rsb, hRsb⟩ := w.exists_psiCurveCompositionRealization hψ hsb
    (D.e_zero_notMem_racl_sb_parameters hind)
  obtain ⟨RsAc, hRsAc⟩ := w.exists_psiCurveCompositionRealization hψ hsAc
    (D.s_zero_notMem_racl_sAc_parameters hind)
  exact ⟨⟨Rse, hRse, RsAa, hRsAa, Rsb, hRsb, RsAc, hRsAc⟩⟩

namespace PsiCurveFourArrowRealizations

variable {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (R : w.PsiCurveFourArrowRealizations hψ D)

/-- The four relocated curve edges carry four literal finite-normal-cover
composition identities in the order of the four-arrow diagram. -/
theorem finiteCoverStrictCompositions :
    (R.se.aFiniteCoverEquiv hψ).trans
        (R.se.bFiniteCoverEquiv hψ) =
          R.se.strictCFiniteCoverEquiv hψ ∧
      (R.sAa.aFiniteCoverEquiv hψ).trans
        (R.sAa.bFiniteCoverEquiv hψ) =
          R.sAa.strictCFiniteCoverEquiv hψ ∧
      (R.sb.aFiniteCoverEquiv hψ).trans
        (R.sb.bFiniteCoverEquiv hψ) =
          R.sb.strictCFiniteCoverEquiv hψ ∧
      (R.sAc.aFiniteCoverEquiv hψ).trans
        (R.sAc.bFiniteCoverEquiv hψ) =
          R.sAc.strictCFiniteCoverEquiv hψ :=
  ⟨R.se.finiteCoverStrictComposition hψ,
    R.sAa.finiteCoverStrictComposition hψ,
    R.sb.finiteCoverStrictComposition hψ,
    R.sAc.finiteCoverStrictComposition hψ⟩

/-- Compatible reference charts for all twelve cover fields in the four
curve triangles.  The four equations retain exactly the repeated `s`,
`sA`, `u`, and `uB` arrows after conjugation; they are the coefficient-aware
coherence obligations which cannot be replaced by arbitrary abstract field
isomorphisms. -/
structure ReferenceAlignment (X Y Z : Type u)
    [Field X] [Field Y] [Field Z] where
  /-- Reference chart for the first source cover. -/
  seX : (↥(R.se.finiteSourceCover hψ).field) ≃+* X
  /-- Reference chart for the first middle cover. -/
  seY : (↥(R.se.finiteMiddleCover hψ).field) ≃+* Y
  /-- Reference chart for the first target cover. -/
  seZ : (↥(R.se.finiteTargetCover hψ).field) ≃+* Z
  /-- Reference chart for the second source cover. -/
  sAaX : (↥(R.sAa.finiteSourceCover hψ).field) ≃+* X
  /-- Reference chart for the second middle cover. -/
  sAaY : (↥(R.sAa.finiteMiddleCover hψ).field) ≃+* Y
  /-- Reference chart for the second target cover. -/
  sAaZ : (↥(R.sAa.finiteTargetCover hψ).field) ≃+* Z
  /-- Reference chart for the third source cover. -/
  sbX : (↥(R.sb.finiteSourceCover hψ).field) ≃+* X
  /-- Reference chart for the third middle cover. -/
  sbY : (↥(R.sb.finiteMiddleCover hψ).field) ≃+* Y
  /-- Reference chart for the third target cover. -/
  sbZ : (↥(R.sb.finiteTargetCover hψ).field) ≃+* Z
  /-- Reference chart for the fourth source cover. -/
  sAcX : (↥(R.sAc.finiteSourceCover hψ).field) ≃+* X
  /-- Reference chart for the fourth middle cover. -/
  sAcY : (↥(R.sAc.finiteMiddleCover hψ).field) ≃+* Y
  /-- Reference chart for the fourth target cover. -/
  sAcZ : (↥(R.sAc.finiteTargetCover hψ).field) ≃+* Z
  /-- The two occurrences of the `s` action agree on the reference
  covers. -/
  leftS :
    (R.sb.finiteCoverCompositionTriangle hψ
      |>.conjugate sbX sbY sbZ).left =
    (R.se.finiteCoverCompositionTriangle hψ
      |>.conjugate seX seY seZ).left
  /-- The two occurrences of the `sA` action agree on the reference
  covers. -/
  leftSA :
    (R.sAc.finiteCoverCompositionTriangle hψ
      |>.conjugate sAcX sAcY sAcZ).left =
    (R.sAa.finiteCoverCompositionTriangle hψ
      |>.conjugate sAaX sAaY sAaZ).left
  /-- The two occurrences of the `u` action agree on the reference
  covers. -/
  compositeU :
    (R.sAa.finiteCoverCompositionTriangle hψ
      |>.conjugate sAaX sAaY sAaZ).direct =
    (R.se.finiteCoverCompositionTriangle hψ
      |>.conjugate seX seY seZ).direct
  /-- The two occurrences of the `uB` action agree on the reference
  covers. -/
  compositeUB :
    (R.sAc.finiteCoverCompositionTriangle hψ
      |>.conjugate sAcX sAcY sAcZ).direct =
    (R.sb.finiteCoverCompositionTriangle hψ
      |>.conjugate sbX sbY sbZ).direct

namespace ReferenceAlignment

variable {X Y Z : Type u} [Field X] [Field Y] [Field Z]
  (A : R.ReferenceAlignment X Y Z)

/-- Forget the Ψ-specific origin of a compatible reference alignment. -/
def toFourTriangleReference :=
  { se := R.se.finiteCoverCompositionTriangle hψ
    sAa := R.sAa.finiteCoverCompositionTriangle hψ
    sb := R.sb.finiteCoverCompositionTriangle hψ
    sAc := R.sAc.finiteCoverCompositionTriangle hψ
    seX := A.seX
    seY := A.seY
    seZ := A.seZ
    sAaX := A.sAaX
    sAaY := A.sAaY
    sAaZ := A.sAaZ
    sbX := A.sbX
    sbY := A.sbY
    sbZ := A.sbZ
    sAcX := A.sAcX
    sAcY := A.sAcY
    sAcZ := A.sAcZ
    leftS := A.leftS
    leftSA := A.leftSA
    compositeU := A.compositeU
    compositeUB := A.compositeUB :
    FieldEquiv.FourTriangleReference X Y Z
      (↥(R.se.finiteSourceCover hψ).field)
      (↥(R.se.finiteMiddleCover hψ).field)
      (↥(R.se.finiteTargetCover hψ).field)
      (↥(R.sAa.finiteSourceCover hψ).field)
      (↥(R.sAa.finiteMiddleCover hψ).field)
      (↥(R.sAa.finiteTargetCover hψ).field)
      (↥(R.sb.finiteSourceCover hψ).field)
      (↥(R.sb.finiteMiddleCover hψ).field)
      (↥(R.sb.finiteTargetCover hψ).field)
      (↥(R.sAc.finiteSourceCover hψ).field)
      (↥(R.sAc.finiteMiddleCover hψ).field)
      (↥(R.sAc.finiteTargetCover hψ).field) }

/-- A coefficient-compatible reference alignment produces the faithful
semantic four-arrow diagram. -/
def toFourArrowDiagram : FieldEquiv.FourArrowDiagram X Y Z :=
  A.toFourTriangleReference.toFourArrowDiagram

/-- Literal semantic cancellation after the four curve triangles have been
aligned to their reference fields. -/
theorem right_cancellation :
    A.toFourArrowDiagram.rightC =
      (A.toFourArrowDiagram.rightA.trans
        A.toFourArrowDiagram.rightE.symm).trans
          A.toFourArrowDiagram.rightB :=
  A.toFourArrowDiagram.right_cancellation

end ReferenceAlignment

end PsiCurveFourArrowRealizations

end QWitness

end

end AclGeom
