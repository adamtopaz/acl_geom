/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ChunkFieldAction
import AclGeom.Correspondence.FieldEquivDiagram
import AclGeom.Correspondence.FiniteNormalTransport

/-!
# The selected Ψ action on one finite normal curve cover

The algebraic-closure action attached to Ψ can be restricted to finite
normal curve covers.  The source cover below is enlarged by three finite
normal pieces: the selected `A` branch, the pullback of the selected `B`
branch, and the selected composite `C` branch.  Its transported middle
and target covers therefore retain all three selected finite
correspondences.

Normality is the key stabilization input.  The vertical discrepancy
between strict `A`-then-`B` composition and the independently chosen `C`
lift fixes the target base field, hence stabilizes the transported target
cover.  Equation (8.6) consequently restricts to an exact equality of
equivalences between finite-dimensional normal fields.
-/

namespace AclGeom

open IntermediateField
open AlgebraicClosureTransport

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace QWitness

variable (w : QWitness k K)

/-- The `A` transport followed by the lifted identification of its target
coordinate field with the source coordinate field of `B`. -/
noncomputable def psiAToBSourceClosureTransport (hψ : w.Psi) :=
  (w.xyCorrespondencePair hψ).coordinateClosureTransport.trans
    ((w.xyCorrespondencePair hψ).middleClosureTransport
      (w.yzCorrespondencePair hψ) rfl)

/-- A common finite normal source cover containing the selected `A` and
`C` branch normalizations and the pullback of the selected `B` branch
normalization. -/
noncomputable def psiXFiniteNormalCover (hψ : w.Psi) :=
  (((w.xyCorrespondencePair hψ).sourceFiniteNormalCover.sup
      ((w.yzCorrespondencePair hψ).sourceFiniteNormalCover.map
        (w.psiAToBSourceClosureTransport hψ).symm)).sup
    (w.xzCorrespondencePair hψ).sourceFiniteNormalCover)

/-- The common middle cover obtained by transporting the source cover
through the selected `A` branch and the shared-coordinate identification. -/
noncomputable def psiYFiniteNormalCover (hψ : w.Psi) :=
  (w.psiXFiniteNormalCover hψ).map
    (w.psiAToBSourceClosureTransport hψ)

/-- The common source cover contains the canonical normal cover of the
selected `A` branch. -/
theorem psiA_sourceCover_le_psiXFiniteNormalCover (hψ : w.Psi) :
    (w.xyCorrespondencePair hψ).sourceFiniteNormalCover.field ≤
      (w.psiXFiniteNormalCover hψ).field := by
  change (w.xyCorrespondencePair hψ).sourceFiniteNormalCover.field ≤
    (((w.xyCorrespondencePair hψ).sourceFiniteNormalCover.field ⊔
      ((w.yzCorrespondencePair hψ).sourceFiniteNormalCover.map
        (w.psiAToBSourceClosureTransport hψ).symm).field) ⊔
      (w.xzCorrespondencePair hψ).sourceFiniteNormalCover.field)
  exact le_sup_left.trans le_sup_left

/-- The common source cover also contains the canonical normal cover of
the selected composite `C` branch. -/
theorem psiC_sourceCover_le_psiXFiniteNormalCover (hψ : w.Psi) :
    (w.xzCorrespondencePair hψ).sourceFiniteNormalCover.field ≤
      (w.psiXFiniteNormalCover hψ).field := by
  change (w.xzCorrespondencePair hψ).sourceFiniteNormalCover.field ≤
    (((w.xyCorrespondencePair hψ).sourceFiniteNormalCover.field ⊔
      ((w.yzCorrespondencePair hψ).sourceFiniteNormalCover.map
        (w.psiAToBSourceClosureTransport hψ).symm).field) ⊔
      (w.xzCorrespondencePair hψ).sourceFiniteNormalCover.field)
  exact le_sup_right

/-- After transport to the middle coordinate, the common cover contains
the canonical normal cover of the selected `B` branch. -/
theorem psiB_sourceCover_le_psiYFiniteNormalCover (hψ : w.Psi) :
    (w.yzCorrespondencePair hψ).sourceFiniteNormalCover.field ≤
      (w.psiYFiniteNormalCover hψ).field := by
  let T := w.psiAToBSourceClosureTransport hψ
  let NB := (w.yzCorrespondencePair hψ).sourceFiniteNormalCover
  have hpre : (NB.map T.symm).field ≤
      (w.psiXFiniteNormalCover hψ).field := by
    simpa [psiXFiniteNormalCover, T, NB] using
      (le_sup_right.trans le_sup_left :
        (NB.map T.symm).field ≤
          ((((w.xyCorrespondencePair hψ).sourceFiniteNormalCover.field ⊔
            (NB.map T.symm).field)) ⊔
            (w.xzCorrespondencePair hψ).sourceFiniteNormalCover.field))
  have hmap := T.mapField_mono hpre
  simpa [psiYFiniteNormalCover, T, NB] using hmap

/-- The common target cover obtained by strict `A`-then-`B` transport.
The next theorem identifies it with transport of the middle cover through
the selected `B` branch. -/
noncomputable def psiZFiniteNormalCover (hψ : w.Psi) :=
  (w.psiXFiniteNormalCover hψ).map
    (w.psiABClosureTransport hψ)

/-- Transporting the common middle cover through `B` gives the same target
field as the strict `A`-then-`B` transport of the common source cover. -/
theorem psiBFiniteNormalCover_field (hψ : w.Psi) :
    ((w.psiYFiniteNormalCover hψ).map
      (w.psiBClosureTransport hψ)).field =
        (w.psiZFiniteNormalCover hψ).field := by
  ext z
  simp [psiABClosureTransport, psiZFiniteNormalCover,
    psiYFiniteNormalCover, psiAToBSourceClosureTransport,
    psiBClosureTransport,
    FiniteCorrespondencePair.chainCoordinateClosureTransport]

/-- The selected `A` branch, including the shared-middle identification,
restricted to the common finite normal source and middle covers. -/
noncomputable def psiAFiniteCoverEquiv (hψ : w.Psi) :
    (↥(w.psiXFiniteNormalCover hψ).field) ≃+*
      (↥(w.psiYFiniteNormalCover hψ).field) :=
  (w.psiXFiniteNormalCover hψ).mapEquiv
    (w.psiAToBSourceClosureTransport hψ)

/-- The selected `B` branch restricted from the common middle cover to the
strict common target cover. -/
noncomputable def psiBFiniteCoverEquiv (hψ : w.Psi) :
    (↥(w.psiYFiniteNormalCover hψ).field) ≃+*
      (↥(w.psiZFiniteNormalCover hψ).field) :=
  ((w.psiYFiniteNormalCover hψ).mapEquiv
      (w.psiBClosureTransport hψ)).trans
    (IntermediateField.equivOfEq
      (w.psiBFiniteNormalCover_field hψ)).toRingEquiv

/-- The independently chosen composite `C` lift stabilizes exactly the
same finite normal source and target covers as strict `A`-then-`B`
composition. -/
theorem psiCFiniteNormalCover_field (hψ : w.Psi) :
    ((w.psiXFiniteNormalCover hψ).map
      (w.psiCClosureTransport hψ)).field =
        (w.psiZFiniteNormalCover hψ).field := by
  exact (w.psiXFiniteNormalCover hψ).correctedMap_field
    (w.psiABClosureTransport hψ)
    (w.psiCClosureTransport hψ)
    (w.psiClosureCompositionDefect hψ)
    (w.psiClosureComposition hψ)

/-- Strict `A`-then-`B` composition restricted to the common finite normal
source and target covers. -/
noncomputable def psiABFiniteCoverEquiv (hψ : w.Psi) :
    (↥(w.psiXFiniteNormalCover hψ).field) ≃+*
      (↥(w.psiZFiniteNormalCover hψ).field) :=
  (w.psiXFiniteNormalCover hψ).mapEquiv
    (w.psiABClosureTransport hψ)

/-- Restriction commutes with the strict `A`-then-`B` composition: the two
successive finite-cover equivalences are literally the restricted composite
transport. -/
theorem psiAFiniteCoverEquiv_trans_psiBFiniteCoverEquiv (hψ : w.Psi) :
    (w.psiAFiniteCoverEquiv hψ).trans
        (w.psiBFiniteCoverEquiv hψ) =
      w.psiABFiniteCoverEquiv hψ := by
  apply RingEquiv.ext
  intro x
  apply Subtype.ext
  rfl

/-- The independently selected `C` transport restricted to the same finite
normal source and target covers. -/
noncomputable def psiCFiniteCoverEquiv (hψ : w.Psi) :
    (↥(w.psiXFiniteNormalCover hψ).field) ≃+*
      (↥(w.psiZFiniteNormalCover hψ).field) :=
  (w.psiXFiniteNormalCover hψ).correctedMapEquiv
    (w.psiABClosureTransport hψ)
    (w.psiCClosureTransport hψ)
    (w.psiClosureCompositionDefect hψ)
    (w.psiClosureComposition hψ)

/-- The vertical composition defect restricted to the common target
finite normal cover. -/
noncomputable def psiFiniteCoverCompositionDefect (hψ : w.Psi) :
    (↥(w.psiZFiniteNormalCover hψ).field) ≃ₐ[
      ↥(w.yzCorrespondencePair hψ).targetField]
      (↥(w.psiZFiniteNormalCover hψ).field) :=
  (w.psiZFiniteNormalCover hψ).restrictAlgEquiv
    (w.psiClosureCompositionDefect hψ)

/-- Correct the independently selected `C` lift by the inverse target deck
defect.  This is the semantic `C` arrow whose composition relation is
strict on the chosen finite normal cover. -/
noncomputable def psiStrictCFiniteCoverEquiv (hψ : w.Psi) :
    (↥(w.psiXFiniteNormalCover hψ).field) ≃+*
      (↥(w.psiZFiniteNormalCover hψ).field) :=
  (w.psiCFiniteCoverEquiv hψ).trans
    (w.psiFiniteCoverCompositionDefect hψ).symm.toRingEquiv

/-- **Finite-cover form of blueprint equation (8.6).**  Strict
`A`-then-`B` composition followed by the restricted vertical deck defect
is exactly the independently selected `C` equivalence on the common finite
normal curve cover. -/
theorem psiFiniteCoverComposition (hψ : w.Psi) :
    (w.psiABFiniteCoverEquiv hψ).trans
        (w.psiFiniteCoverCompositionDefect hψ).toRingEquiv =
      w.psiCFiniteCoverEquiv hψ :=
  (w.psiXFiniteNormalCover hψ).mapEquiv_trans_restrictAlgEquiv
    (w.psiABClosureTransport hψ)
    (w.psiCClosureTransport hψ)
    (w.psiClosureCompositionDefect hψ)
    (w.psiClosureComposition hψ)

/-- After the explicit deck correction, the selected `A`, `B`, and `C`
branches form a literal composition triangle of finite normal-cover field
equivalences.  This is the semantic relation used by
`FieldEquiv.FourArrowDiagram`, not equality in a formal quotient. -/
theorem psiFiniteCoverStrictComposition (hψ : w.Psi) :
    (w.psiAFiniteCoverEquiv hψ).trans
        (w.psiBFiniteCoverEquiv hψ) =
      w.psiStrictCFiniteCoverEquiv hψ := by
  rw [w.psiAFiniteCoverEquiv_trans_psiBFiniteCoverEquiv hψ]
  exact FieldEquiv.eq_trans_symm_of_trans_eq
    (w.psiABFiniteCoverEquiv hψ)
    (w.psiCFiniteCoverEquiv hψ)
    (w.psiFiniteCoverCompositionDefect hψ).toRingEquiv
    (w.psiFiniteCoverComposition hψ)

end QWitness

end

end AclGeom
