/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ConfigurationInput
import AclGeom.Transfer.LiftConfig
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.AlgebraicClosure
import AclGeom.Geometry.CountableAmbient

/-!
# A canonical universal ambient for the actual Ψ input

Adjoin countably many independent variables to the original ambient K and
algebraically close the fraction field. The algebraic closure of k inside this
chosen Ω is an algebraically closed base. The variables remain independent
on enlarging k to that algebraic base, so Ω is a proved universal domain there.
The specific base's algebraic-closedness instance uses Mathlib's
`IsAlgClosure.isAlgClosed`; no local algebraic-closure theorem is duplicated.

The proved `QWitness.PsiCore.lift` transfers precisely clauses (i)–(iv),
including atom-freeness, along the canonical embedding. These clauses construct
a six-point configuration of group rank two and space rank one in Ω. The full
Ψ theorem remains available through its core projection. No ambient closedness
or infinitude is assumed of the original caller.

**Status:** the canonical ACF ambient, algebraically closed base, universal-
domain instance, actual witness lift and its six-point input/ranks are proved.
The literal comparison with image tuples is proved in
`Config.UniversalImageConfigurationInput`. The original-field guarded chart consumer is
`Config.GuardedAffineGrid`; it uses the original-base universal-domain instance below.
Original scheme/action descent, algebraization and unconditional reconstruction remain
separate obligations. This construction alone does not give semantic representatives.
-/

namespace AclGeom

open GroupConfig IntermediateField MvPolynomial

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A fixed algebraically closed ambient with countably many fresh variables.
Named consumer: the actual Ψ configuration lift below. -/
abbrev ConfigurationAmbient (K : Type*) [Field K] :=
  AlgebraicClosure (FractionRing (MvPolynomial ℕ K))

/-- The canonical embedding of the original field into the universal configuration ambient.
Named consumers: the witness lift and its literal six-tuple comparison. -/
def configurationEmbedding (k K : Type*) [Field k] [Field K] [Algebra k K] :
    K →ₐ[k] ConfigurationAmbient K := IsScalarTower.toAlgHom k K (ConfigurationAmbient K)

/-- The algebraic base in the canonical configuration ambient. -/
abbrev configurationBase (k K : Type*) [Field k] [Field K] [Algebra k K] :
    IntermediateField k (ConfigurationAmbient K) := algebraicClosure k (ConfigurationAmbient K)

instance configurationBase_isAlgClosed : IsAlgClosed (↥(configurationBase k K)) :=
  IsAlgClosure.isAlgClosed k

instance configurationAmbient_universalDomain :
    UniversalDomain (↥(configurationBase k K)) (ConfigurationAmbient K) := by
  have h := trdeg_add_eq k (↥(configurationBase k K)) (A := ConfigurationAmbient K)
  rw [trdeg_eq_zero, zero_add] at h
  constructor
  rw [h]
  exact aleph0_le_trdeg_algebraicClosure

/-- The chosen configuration ambient is also a universal domain over the original base.
Named consumer: guarded affine-grid extraction and original-field chart descent. -/
instance configurationAmbient_originalBase_universalDomain :
    UniversalDomain k (ConfigurationAmbient K) :=
  ⟨aleph0_le_trdeg_algebraicClosure⟩

namespace QWitness

/-- The actual witness lifted to a chosen universal ACF ambient.
Named consumer: groupConfiguration_universalLift below. -/
def universalLift (w : QWitness k K) :
    QWitness (↥(configurationBase k K)) (ConfigurationAmbient K) :=
  w.lift (fun _ hy ↦ mem_algebraicClosure_iff.1 hy)
    (configurationEmbedding k K)

variable {w : QWitness k K}

/-- Clauses (i)–(iv) in any ambient field supply a six-point configuration
in the canonical universal ACF extension, with group rank two and space rank one.
No universal-domain, configuration, group or chart input is assumed of the caller.
The finite-ambient guarded chart consumer is `Config.GuardedAffineGrid`; original
scheme/action descent remains a separate obligation. -/
theorem PsiCore.groupConfiguration_universalLift (hw : w.PsiCore) :
    GroupConfig.GroupConfiguration (↥(configurationBase k K))
      w.universalLift.aTuple w.universalLift.bTuple w.universalLift.cTuple
      w.universalLift.xTuple w.universalLift.yTuple w.universalLift.zTuple ∧
      erk (↥(configurationBase k K)) ∅ (Set.range w.universalLift.aTuple) = 2 ∧
      erk (↥(configurationBase k K)) ∅ (Set.range w.universalLift.xTuple) = 1 := by
  have hlift : w.universalLift.PsiCore := hw.lift _ _
  exact hlift.groupConfiguration_with_ranks

/-- An actual Ψ input in any ambient field supplies a six-point configuration
in the canonical universal ACF extension, with group rank two and space rank one.
No universal-domain, configuration, group or chart input is assumed of the caller.
The finite-ambient guarded chart consumer is `Config.GuardedAffineGrid`; original
scheme/action descent remains a separate obligation. -/
theorem Psi.groupConfiguration_universalLift (hw : w.Psi) :
    GroupConfig.GroupConfiguration (↥(configurationBase k K))
      w.universalLift.aTuple w.universalLift.bTuple w.universalLift.cTuple
      w.universalLift.xTuple w.universalLift.yTuple w.universalLift.zTuple ∧
      erk (↥(configurationBase k K)) ∅ (Set.range w.universalLift.aTuple) = 2 ∧
      erk (↥(configurationBase k K)) ∅ (Set.range w.universalLift.xTuple) = 1 := by
  exact hw.toCore.groupConfiguration_universalLift

end QWitness

end

end AclGeom
