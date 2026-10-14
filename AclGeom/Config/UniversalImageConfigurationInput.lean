/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.UniversalConfigurationInput

/-!
# Literal image tuples in the canonical universal ambient

The actual clause-(i)–(iv) input constructs the six-point configuration on the
literal images of the original displayed representatives under the canonical
embedding. Each lifted point and its displayed image have the same relatively
algebraic closure over the algebraic base of the universal ambient. Equality
of these closures transports the configuration and its ranks.

**Status:** the literal image-tuple comparison is proved from `PsiCore` over
arbitrary original fields. Its result is in the chosen universal extension Ω,
not in the original K. Chart/action descent, group extraction/algebraization,
action classification and unconditional reconstruction remain obligations.
-/

set_option linter.mathlibStandardSet true

namespace AclGeom

open GroupConfig IntermediateField Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

private theorem single_image_lift_racl (P : Point k K) :
    racl (↥(configurationBase k K)) {(configurationEmbedding k K) P.rep} =
      racl (↥(configurationBase k K))
        {(liftPoint (fun _ hy ↦ mem_algebraicClosure_iff.1 hy)
          (configurationEmbedding k K) P).rep} := by
  have h := (liftClosed_point
    (fun _ hy ↦ mem_algebraicClosure_iff.1 hy) (configurationEmbedding k K) P.rep).symm
  rw [P.point_rep] at h
  have hpoint :
      ClosedIF.point (↥(configurationBase k K)) ((configurationEmbedding k K) P.rep) =
      (liftPoint (fun _ hy ↦ mem_algebraicClosure_iff.1 hy)
        (configurationEmbedding k K) P).1 := h
  have hr := congrArg Subtype.val hpoint
  rw [← (liftPoint (fun _ hy ↦ mem_algebraicClosure_iff.1 hy)
    (configurationEmbedding k K) P).point_rep] at hr
  exact hr

private theorem pair_image_lift_racl (P Q : Point k K) :
    racl (↥(configurationBase k K))
      (range ((configurationEmbedding k K) ∘ (![P.rep, Q.rep] : Fin 2 → K))) =
    racl (↥(configurationBase k K))
      (range (![(liftPoint (fun _ hy ↦ mem_algebraicClosure_iff.1 hy)
        (configurationEmbedding k K) P).rep,
        (liftPoint (fun _ hy ↦ mem_algebraicClosure_iff.1 hy)
          (configurationEmbedding k K) Q).rep] : Fin 2 → ConfigurationAmbient K)) := by
  have hcomp : (configurationEmbedding k K) ∘ (![P.rep, Q.rep] : Fin 2 → K) =
      ![(configurationEmbedding k K) P.rep, (configurationEmbedding k K) Q.rep] := by
    funext i
    fin_cases i <;> rfl
  rw [hcomp, Matrix.range_cons_cons_empty, Matrix.range_cons_cons_empty]
  simpa only [singleton_union] using
    racl_union_congr (single_image_lift_racl P) (single_image_lift_racl Q)

namespace QWitness

variable {w : QWitness k K}

/-- Clauses (i)–(iv) give the six-point configuration on the literal images of the
original displayed representatives in the canonical universal extension, with group
rank two and space rank one. No original-field chart or action is asserted. -/
theorem PsiCore.groupConfiguration_universalImages (hw : w.PsiCore) :
    GroupConfig.GroupConfiguration (↥(configurationBase k K))
      ((configurationEmbedding k K) ∘ w.aTuple) ((configurationEmbedding k K) ∘ w.bTuple)
      ((configurationEmbedding k K) ∘ w.cTuple) ((configurationEmbedding k K) ∘ w.xTuple)
      ((configurationEmbedding k K) ∘ w.yTuple) ((configurationEmbedding k K) ∘ w.zTuple) ∧
      erk (↥(configurationBase k K)) ∅ (range ((configurationEmbedding k K) ∘ w.aTuple)) = 2 ∧
      erk (↥(configurationBase k K)) ∅ (range ((configurationEmbedding k K) ∘ w.xTuple)) = 1 := by
  have hA : racl (↥(configurationBase k K)) (range ((configurationEmbedding k K) ∘ w.aTuple)) =
      racl (↥(configurationBase k K)) (range w.universalLift.aTuple) :=
    pair_image_lift_racl w.A₁ w.A₂
  have hB : racl (↥(configurationBase k K)) (range ((configurationEmbedding k K) ∘ w.bTuple)) =
      racl (↥(configurationBase k K)) (range w.universalLift.bTuple) :=
    pair_image_lift_racl w.B₁ w.B₂
  have hC : racl (↥(configurationBase k K)) (range ((configurationEmbedding k K) ∘ w.cTuple)) =
      racl (↥(configurationBase k K)) (range w.universalLift.cTuple) :=
    pair_image_lift_racl w.C₁ w.C₂
  have hs (P : Point k K) :
      racl (↥(configurationBase k K))
          (range ((configurationEmbedding k K) ∘ (fun _ : Fin 1 ↦ P.rep))) =
      racl (↥(configurationBase k K)) (range (fun _ : Fin 1 ↦
        (liftPoint (fun _ hy ↦ mem_algebraicClosure_iff.1 hy)
          (configurationEmbedding k K) P).rep)) := by
    simpa only [Function.comp_def, range_const] using single_image_lift_racl P
  have hX := hs w.X
  have hY := hs w.Y
  have hZ := hs w.Z
  have hc := hw.groupConfiguration_universalLift
  refine ⟨hc.1.ofRaclEq hA hB hC hX hY hZ, ?_, ?_⟩
  · exact (erk_eq_of_racl_eq hA).trans hc.2.1
  · exact (erk_eq_of_racl_eq hX).trans hc.2.2

end QWitness

end

end AclGeom
