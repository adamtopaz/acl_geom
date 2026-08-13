/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.FiniteNormalTransport

/-!
# Two-orbit stabilization of finite normal covers

A semilinear algebraic-closure transport whose base equivalence has order two
need not itself have order two: its square can be a nontrivial deck
transformation.  Normality absorbs precisely that discrepancy.  Consequently
the compositum of a finite normal cover with its first image is stable under
the transport and carries its restriction as a semilinear self-equivalence.
-/

namespace AclGeom

open IntermediateField

noncomputable section

namespace AlgebraicClosureTransport

variable {E : Type*} [Field E]

/-- The square of a semilinear closure transport becomes an algebra
automorphism when its base equivalence is involutive. -/
def squareAlgEquiv (T : AlgebraicClosureTransport E E)
    (hbase : T.baseEquiv.trans T.baseEquiv = RingEquiv.refl E) :
    AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E := by
  apply AlgEquiv.ofRingEquiv (f := T.closureEquiv.trans T.closureEquiv)
  intro x
  rw [RingEquiv.trans_apply, T.commutes_apply, T.commutes_apply]
  exact congrArg (algebraMap E (AlgebraicClosure E))
    (DFunLike.congr_fun hbase x)

namespace FiniteNormalCover

variable (N : FiniteNormalCover E)

/-- Applying an involutive-base transport twice preserves every finite normal
cover, even when the chosen ambient lift is not itself involutive. -/
theorem map_trans_self_field (T : AlgebraicClosureTransport E E)
    (hbase : T.baseEquiv.trans T.baseEquiv = RingEquiv.refl E) :
    (N.map (T.trans T)).field = N.field := by
  let σ := T.squareAlgEquiv hbase
  calc
    (N.map (T.trans T)).field =
        (N.map (ofAlgEquiv σ)).field :=
      mapField_eq_of_closureEquiv_eq
        (T.trans T) (ofAlgEquiv σ) rfl N.field
    _ = N.field := N.map_ofAlgEquiv_field σ

/-- The two-orbit compositum of a finite normal cover under a semilinear
transport. -/
def twoOrbitCover (T : AlgebraicClosureTransport E E) :
    FiniteNormalCover E :=
  N.sup (N.map T)

/-- The two-orbit compositum is stable under the original transport. -/
theorem twoOrbitCover_map_field (T : AlgebraicClosureTransport E E)
    (hbase : T.baseEquiv.trans T.baseEquiv = RingEquiv.refl E) :
    ((N.twoOrbitCover T).map T).field = (N.twoOrbitCover T).field := by
  calc
    ((N.twoOrbitCover T).map T).field =
        ((N.map T).sup ((N.map T).map T)).field :=
      N.map_sup_field (N.map T) T
    _ = (N.map T).field ⊔ ((N.map T).map T).field := rfl
    _ = (N.map T).field ⊔ (N.map (T.trans T)).field := by
      rw [N.map_trans_field T T]
    _ = (N.map T).field ⊔ N.field := by
      rw [N.map_trans_self_field T hbase]
    _ = N.field ⊔ (N.map T).field := by rw [sup_comm]
    _ = (N.twoOrbitCover T).field := rfl

/-- Restrict an involutive-base transport to its stable two-orbit cover. -/
def twoOrbitEquiv (T : AlgebraicClosureTransport E E)
    (hbase : T.baseEquiv.trans T.baseEquiv = RingEquiv.refl E) :
    (N.twoOrbitCover T).field ≃+* (N.twoOrbitCover T).field :=
  ((N.twoOrbitCover T).mapEquiv T).trans
    (IntermediateField.equivOfEq
      (N.twoOrbitCover_map_field T hbase)).toRingEquiv

/-- The restricted two-orbit chart evaluates as the original ambient
transport. -/
@[simp] theorem coe_twoOrbitEquiv_apply
    (T : AlgebraicClosureTransport E E)
    (hbase : T.baseEquiv.trans T.baseEquiv = RingEquiv.refl E)
    (x : (N.twoOrbitCover T).field) :
    ((N.twoOrbitEquiv T hbase x : (N.twoOrbitCover T).field) :
        AlgebraicClosure E) = T.closureEquiv x :=
  rfl

/-- The stable two-orbit chart remains semilinear over the displayed base
equivalence. -/
@[simp] theorem twoOrbitEquiv_algebraMap
    (T : AlgebraicClosureTransport E E)
    (hbase : T.baseEquiv.trans T.baseEquiv = RingEquiv.refl E)
    (x : E) :
    N.twoOrbitEquiv T hbase
        (algebraMap E (↥(N.twoOrbitCover T).field) x) =
      algebraMap E (↥(N.twoOrbitCover T).field) (T.baseEquiv x) := by
  apply Subtype.ext
  rw [N.coe_twoOrbitEquiv_apply]
  exact T.commutes_apply x

/-- Ring-hom form of the semilinearity square for the restricted chart. -/
theorem twoOrbitEquiv_commutes
    (T : AlgebraicClosureTransport E E)
    (hbase : T.baseEquiv.trans T.baseEquiv = RingEquiv.refl E) :
    (N.twoOrbitEquiv T hbase).toRingHom.comp
        (algebraMap E (↥(N.twoOrbitCover T).field)) =
      (algebraMap E (↥(N.twoOrbitCover T).field)).comp
        T.baseEquiv.toRingHom := by
  apply RingHom.ext
  intro x
  exact N.twoOrbitEquiv_algebraMap T hbase x

end FiniteNormalCover

end AlgebraicClosureTransport

end

end AclGeom
