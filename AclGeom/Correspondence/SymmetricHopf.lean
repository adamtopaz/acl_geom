/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The Hopf algebra of an additive vector group

The existing Mathlib symmetric-algebra bialgebra has primitive generators. Negating those
generators gives its antipode. The named consumer is the actual additive algebraic group,
and then the affine group and regular action in blueprint equation (8.4a).

**Status:** proved; used by the concrete additive and affine group schemes.
-/

noncomputable section

namespace SymmetricAlgebra

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- The symmetric algebra is the Hopf algebra of the additive vector group. -/
instance instHopfAlgebra : HopfAlgebra R (SymmetricAlgebra R M) :=
  .ofAlgHom (lift (-ι R M))
    (by
      ext x
      simp only [LinearMap.coe_comp, LinearMap.coe_ofClass, AlgHom.coe_comp, Function.comp_apply,
        Bialgebra.comulAlgHom_apply, comul_ι, map_add, counitAlgHom_eq,
        algebraMapInv_ι, map_zero]
      change (lift (-ι R M)) (ι R M x) * (AlgHom.id R _) 1 +
        (lift (-ι R M)) 1 * (AlgHom.id R _) (ι R M x) = 0
      simp)
    (by ext x; simp [algebraMapInv_ι])

@[simp]
theorem antipode_ι (x : M) : HopfAlgebra.antipode R (ι R M x) = -ι R M x :=
  lift_ι_apply _ x

end SymmetricAlgebra
