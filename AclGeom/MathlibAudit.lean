/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Mathlib

/-!
# Mathlib API audit (blueprint milestone M0)

One `#check` per Mathlib API name cited in the blueprint's audit table
(`sources/blueprint.tex`, §What may be taken from Mathlib), pinned against the
project's Mathlib version. Where the blueprint's guessed name differs from the
actual declaration, the actual name is used and the discrepancy noted.

This file is deliberately imported by nothing; it exists so that a Mathlib bump
that breaks an assumed API fails the build here, with a pointer back to the
blueprint item that relies on it.
-/

set_option linter.hashCommand false

/-! ## Relative algebraic closure (blueprint: F1) -/

#check @algebraicClosure
#check @mem_algebraicClosure_iff
#check @mem_algebraicClosure_iff'
#check @algebraicClosure.algebraicClosure_eq_bot
#check @algebraicClosure.map_eq_of_algebraicClosure_eq_bot

/-! ## Intermediate fields -/

#check @IntermediateField.adjoin
#check @IntermediateField.map
#check @IntermediateField.comap
#check @IntermediateField.restrictScalars
#check (inferInstance : CompleteLattice (IntermediateField ℚ ℂ))

/-! ## Algebraic independence and transcendence degree -/

#check @AlgebraicIndependent
#check @AlgebraicIndepOn
#check @Algebra.trdeg
#check @exists_isTranscendenceBasis
#check @AlgebraicIndependent.option_iff

/-! ## Perfect closures and Frobenius (blueprint: P1, P3) -/

#check @perfectClosure
#check @mem_perfectClosure_iff_pow_mem
#check @IsPerfectClosure
#check @PerfectRing.lift
#check @IsPerfectClosure.equiv
#check @iterateFrobeniusEquiv
#check @frobeniusEquiv

/-! ## Matroids (available; adopted only after the purpose-built geometry API) -/

#check @Matroid

/-! ## First-order syntax (available; deliberately not used, per blueprint) -/

#check @FirstOrder.Language

/-! ## Transfer ingredients (blueprint: T1) -/

#check @Subgroup.exists_index_le_card_of_leftCoset_cover

-- Cyclicity of the unit group of a finite field:
example (F : Type) [Field F] [Finite F] : IsCyclic Fˣ := inferInstance
