/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Config.ConfigurationInput
import AclGeom.Transfer.LiftConfig
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

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
`Config.UniversalImageConfigurationInput`. Finite-ambient chart/action descent,
group extraction/algebraization, action classification and unconditional
reconstruction remain separate obligations. No original-field semantic
representatives or guarded chart are obtained by this construction alone.
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
  let Ω := ConfigurationAmbient K
  let φ : MvPolynomial ℕ K →ₐ[K] Ω := IsScalarTower.toAlgHom K (MvPolynomial ℕ K) Ω
  have hφ : Function.Injective φ := by
    change Function.Injective (algebraMap (MvPolynomial ℕ K) Ω)
    rw [IsScalarTower.algebraMap_eq (MvPolynomial ℕ K)
      (FractionRing (MvPolynomial ℕ K)) Ω]
    exact (algebraMap (FractionRing (MvPolynomial ℕ K)) Ω).injective.comp
      (IsFractionRing.injective (MvPolynomial ℕ K) (FractionRing (MvPolynomial ℕ K)))
  have hX := (MvPolynomial.algebraicIndependent_X ℕ K).map' hφ
  have hXk := AlgebraicIndependent.restrictScalars (algebraMap k K).injective hX
  have hXbase := hXk.algebraicClosure
  constructor
  simpa using hXbase.lift_cardinalMk_le_trdeg

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
Literal finite-ambient chart/action descent remains a separate obligation. -/
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
Literal finite-ambient chart/action descent remains a separate obligation. -/
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
