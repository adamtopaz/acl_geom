/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkCurveCommonSource

/-!
# Existence of common-source realizations

Existence of the base-change and four-arrow common-source realizations, together with
the coordinate facts used only by those existence proofs. Split from
`AclGeom.Config.ChunkCurveCommonSource` (#18) so that the modules depending on
the common source do not wait for these results.
-/

namespace AclGeom

open IntermediateField

noncomputable section

universe u

variable {k K Ω : Type u} [Field k] [Field K] [Algebra k K]
  [Field Ω] [Algebra k Ω]

namespace QWitness

variable (w : QWitness k K)

/-- The six displayed parameters followed by a curve source, in an arbitrary
ambient field. -/
def psiCurveParameterSourceTupleOver (_w : QWitness k K) (a b c : Fin 2 → Ω)
    (x : Ω) : Fin 7 → Ω :=
  Fin.snoc (compositionParameterTuple a b c) x

/-- Mapping the parameter/source prefix is the same as constructing it from
the mapped coordinates. -/
@[simp] theorem psiCurveParameterSourceTupleOver_map
    (ι : K →ₐ[k] Ω) (a b c : Fin 2 → K) (x : K) :
    w.psiCurveParameterSourceTupleOver (ι ∘ a) (ι ∘ b) (ι ∘ c) (ι x) =
      ι ∘ psiCurveParameterSourceTuple a b c x := by
  funext i
  fin_cases i <;> rfl

/-- The selected Ψ curve locus relocates along any ambient embedding while
fixing mapped parameters and any source generic over those parameters. -/
theorem exists_psiCurveCompositionBaseChangeRealization [IsAlgClosed Ω]
    (ι : K →ₐ[k] Ω) (hψ : w.Psi) {a b c : Fin 2 → K}
    (hrel : w.psiFamilyCompositionRelation a b c) {x : Ω}
    (hx : x ∉ racl k
      (Set.range (ι ∘ compositionParameterTuple a b c))) :
    ∃ R : w.PsiCurveCompositionBaseChangeRealization ι
        (ι ∘ a) (ι ∘ b) (ι ∘ c),
      R.source = x := by
  have hparameter :
      idealOf k (ι ∘ compositionParameterTuple a b c) =
        idealOf k (ι ∘ w.abcReps) := by
    calc
      idealOf k (ι ∘ compositionParameterTuple a b c) =
          idealOf k (compositionParameterTuple a b c) :=
        idealOf_comp_algHom k ι _
      _ = idealOf k w.abcReps := by
        simpa [psiFamilyCompositionRelation] using hrel
      _ = idealOf k (ι ∘ w.abcReps) :=
        (idealOf_comp_algHom k ι _).symm
  have hsource :
      ι w.X.rep ∉ racl k (Set.range (ι ∘ w.abcReps)) := by
    intro hmem
    rw [Set.range_comp] at hmem
    exact w.X_rep_notMem_racl_abcReps hψ
      ((algHom_mem_racl_image_iff ι).1 hmem)
  have hfixed :
      idealOf k (w.psiCurveParameterSourceTupleOver
          (ι ∘ a) (ι ∘ b) (ι ∘ c) x) =
        idealOf k (ι ∘ psiCurveParameterSourceTuple
          w.aReps w.bReps w.cReps w.X.rep) := by
    rw [← w.psiCurveParameterSourceTupleOver_map]
    change idealOf k (Fin.snoc
        (compositionParameterTuple (ι ∘ a) (ι ∘ b) (ι ∘ c)) x) =
      idealOf k (Fin.snoc
        (compositionParameterTuple (ι ∘ w.aReps) (ι ∘ w.bReps)
          (ι ∘ w.cReps)) (ι w.X.rep))
    have hmapParameters :
        compositionParameterTuple (ι ∘ a) (ι ∘ b) (ι ∘ c) =
          ι ∘ compositionParameterTuple a b c := by
      funext i
      fin_cases i <;> rfl
    have hmapSelected :
        compositionParameterTuple (ι ∘ w.aReps) (ι ∘ w.bReps)
            (ι ∘ w.cReps) =
          ι ∘ w.abcReps := by
      funext i
      fin_cases i <;> rfl
    rw [hmapParameters, hmapSelected]
    exact idealOf_snoc_eq_of_idealOf_eq_of_generic
      hparameter hx hsource
  have hselectedAlgebraic (j : Fin 9) :
      (ι ∘ w.psiSelectedCurveCompositionTuple) j ∈ racl k
        (Set.range (ι ∘ psiCurveParameterSourceTuple
          w.aReps w.bReps w.cReps w.X.rep)) := by
    rw [Set.range_comp]
    exact (algHom_mem_racl_image_iff ι).2
      (w.psiSelectedCurveCompositionTuple_mem_parameterSource_racl hψ j)
  obtain ⟨v, hv, hfix⟩ := exists_tuple_relocation_fixing_locus
    hfixed
    (u := ι ∘ w.psiSelectedCurveCompositionTuple)
    (e := psiCurveParameterSourceIndex)
    (fun i ↦ by
      change ι (w.psiSelectedCurveCompositionTuple
          (psiCurveParameterSourceIndex i)) =
        ι (psiCurveParameterSourceTuple
          w.aReps w.bReps w.cReps w.X.rep i)
      congr 1
      exact congrFun
        (w.psiCurveCompositionTuple_comp_parameterSourceIndex
          w.aReps w.bReps w.cReps w.X.rep w.Y.rep w.Z.rep) i)
    hselectedAlgebraic
  let y : Ω := v 7
  let z : Ω := v 8
  have htotal :
      w.psiCurveCompositionTupleOver
          (ι ∘ a) (ι ∘ b) (ι ∘ c) x y z = v := by
    funext i
    fin_cases i
    · simpa [psiCurveParameterSourceIndex,
        psiCurveParameterSourceTupleOver, compositionParameterTuple,
        psiCurveCompositionTupleOver] using (hfix 0).symm
    · simpa [psiCurveParameterSourceIndex,
        psiCurveParameterSourceTupleOver, compositionParameterTuple,
        psiCurveCompositionTupleOver] using (hfix 1).symm
    · simpa [psiCurveParameterSourceIndex,
        psiCurveParameterSourceTupleOver, compositionParameterTuple,
        psiCurveCompositionTupleOver] using (hfix 2).symm
    · simpa [psiCurveParameterSourceIndex,
        psiCurveParameterSourceTupleOver, compositionParameterTuple,
        psiCurveCompositionTupleOver] using (hfix 3).symm
    · simpa [psiCurveParameterSourceIndex,
        psiCurveParameterSourceTupleOver, compositionParameterTuple,
        psiCurveCompositionTupleOver] using (hfix 4).symm
    · simpa [psiCurveParameterSourceIndex,
        psiCurveParameterSourceTupleOver, compositionParameterTuple,
        psiCurveCompositionTupleOver] using (hfix 5).symm
    · simpa [psiCurveParameterSourceIndex,
        psiCurveParameterSourceTupleOver, compositionParameterTuple,
        psiCurveCompositionTupleOver] using (hfix 6).symm
    · rfl
    · rfl
  let R : w.PsiCurveCompositionBaseChangeRealization ι
      (ι ∘ a) (ι ∘ b) (ι ∘ c) :=
    { source := x
      middle := y
      target := z
      locus := by rw [htotal]; exact hv }
  exact ⟨R, rfl⟩

namespace PsiCurveCompositionBaseChangeRealization

variable {w : QWitness k K} {ι : K →ₐ[k] Ω}
  {a b c : Fin 2 → Ω}
  (R : w.PsiCurveCompositionBaseChangeRealization ι a b c)

namespace CommonBaseData

variable {n : ℕ} {base : Fin n → Ω}
  (H : R.CommonBaseData base)

end CommonBaseData

end PsiCurveCompositionBaseChangeRealization

/-- The formal rational-function coordinate supplies a single common source
for all four edges of every Ψ parameter difference diagram. -/
theorem exists_psiCurveFourArrowCommonSourceRealizations
    (hψ : w.Psi) {s a b e : Fin 2 → K}
    (D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e) :
    Nonempty (w.PsiCurveFourArrowCommonSourceRealizations hψ D) := by
  let ι : K →ₐ[k] CommonCurveAmbient K :=
    commonCurveEmbedding (k := k) (K := K)
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
  obtain ⟨Rse, hRse⟩ :=
    w.exists_psiCurveCompositionBaseChangeRealization ι hψ hse
      (commonCurveSource_notMem_racl
        (k := k) (K := K) (compositionParameterTuple s e D.u))
  obtain ⟨RsAa, hRsAa⟩ :=
    w.exists_psiCurveCompositionBaseChangeRealization ι hψ hsAa
      (commonCurveSource_notMem_racl
        (k := k) (K := K) (compositionParameterTuple D.sA a D.u))
  obtain ⟨Rsb, hRsb⟩ :=
    w.exists_psiCurveCompositionBaseChangeRealization ι hψ hsb
      (commonCurveSource_notMem_racl
        (k := k) (K := K) (compositionParameterTuple s b D.uB))
  obtain ⟨RsAc, hRsAc⟩ :=
    w.exists_psiCurveCompositionBaseChangeRealization ι hψ hsAc
      (commonCurveSource_notMem_racl
        (k := k) (K := K) (compositionParameterTuple D.sA D.c D.uB))
  exact ⟨⟨Rse, hRse, RsAa, hRsAa, Rsb, hRsb, RsAc, hRsAc⟩⟩

namespace PsiCurveFourArrowCommonSourceRealizations

variable {w : QWitness k K} {hψ : w.Psi}
  {s a b e : Fin 2 → K}
  {D : w.PsiParameterFourArrowDifferenceDiagram hψ s a b e}
  (R : w.PsiCurveFourArrowCommonSourceRealizations hψ D)

section SourceFieldAliases

/-!
### Source-field aliases

From here on, branch fields of different correspondence pairs are compared
over source fields that agree only definitionally: for instance
`repeatedSCommonCorrespondencePair_source_eq` is `rfl`, so the source field of
the `s·e = u` pair is the source field of the `s·b = uB` pair after unfolding.
Statements such as `repeatedSCommonBranchEquiv` need the induced instances
`Algebra ↥P.sourceField ↥P'.branchOverSource` across these aliases.  Since
Lean v4.34 instance search no longer unfolds such definitions under the
default transparency, so this section restores the earlier elaboration
behaviour with `backward.isDefEq.respectTransparency false`.  The setting
affects elaboration only; the kernel still checks every declaration.  See
issues #20 (version upgrade) and #18 (build performance) for the plan to
replace these aliases with explicit presentations.
-/

set_option backward.isDefEq.respectTransparency false

/- The canonical covers and total-field embeddings below use the literal
common source over its coefficient field throughout. Mixing it with the
restriction to k caused costly kernel conversions under Lean 4.34 (#20).
The explicit carrier equivalences preserve the original finite extensions. -/

end SourceFieldAliases

end PsiCurveFourArrowCommonSourceRealizations

end QWitness

end

end AclGeom
