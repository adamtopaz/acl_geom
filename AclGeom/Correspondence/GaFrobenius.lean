/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AdditivePolynomialMaps
import AclGeom.Correspondence.AffineTranslationSubgroup

/-!
# Relative Frobenius as an actual additive-group morphism

**Status:** T to T^(p^n), fixing the base coefficients, is an actual group morphism over
every field of exponential characteristic p, including p=1 in characteristic zero. Its
literal formula holds over every commutative coefficient algebra in the base universe,
including the zero ring. Named consumer: the group laws of the finite Ga cover of the
actual normal subgroup, without cancelling its finite beta map as a monomorphism (#21).
-/

namespace AclGeom.FiniteGaCover
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
universe u
variable (k : Type u) [Field k] (p n : ℕ)

/-- The relative Frobenius power on the additive line, including p=1 in characteristic0.
Named consumer: the finite Ga cover of the actual normal subgroup. -/
def relativeFrobenius : (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X ⟶
    (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X :=
  AffineSchemeAction.linePoint k (AffineSchemeAction.lineCoordinate k ^ p ^ n)

/-- Named consumers: the finite-cover factorization and its literal point formula. -/
theorem linePoint_comp_relativeFrobenius {C : Type u} [CommRing C] [Algebra k C]
    (c : C) : AffineSchemeAction.linePoint k c ≫ relativeFrobenius k p n =
      AffineSchemeAction.linePoint k (c ^ p ^ n) := by
  change AffineSchemeAction.linePoint k c ≫
      AffineSchemeAction.linePoint k (AffineSchemeAction.lineCoordinate k ^ p ^ n) = _
  rw [AdditiveTranslation.linePoint_comp_linePoint, map_pow,
    AffineSchemeAction.lineEval_lineCoordinate]

/-- Relative Frobenius is an actual group morphism over every field. Named consumer:
the group laws of the finite Ga cover, proved without cancelling beta as mono. -/
instance relativeFrobenius_isMonHom [ExpChar k p] : IsMonHom (relativeFrobenius k p n) := by
  let L := (AdditiveGroupScheme.algebraicGroup k 1).toGroupScheme.X
  let F := relativeFrobenius k p n
  constructor
  · have hh : (1 : (Spec (.of k)).asOver (Spec (.of k)) ⟶ L) ≫ F = 1 := by
      rw [← AdditiveTranslation.linePoint_zero k, linePoint_comp_relativeFrobenius,
        zero_pow (Nat.ne_of_gt (expChar_pow_pos k p n)), AdditiveTranslation.linePoint_zero]
    apply (cancel_epi (unitIsoSpecAsOver k).inv).mp
    rw [← Category.assoc]
    simpa only [comp_one, one_eq_one] using hh
  · have key {C : Type u} [CommRing C] [Algebra k C]
        (z : (Spec (.of C)).asOver (Spec (.of k)) ⟶ L ⊗ L) :
        z ≫ μ[L] ≫ F = z ≫ (F ⊗ₘ F) ≫ μ[L] := by
      obtain ⟨b, hb⟩ := AffineSchemeAction.exists_linePoint k (z ≫ fst L L)
      obtain ⟨c, hc⟩ := AffineSchemeAction.exists_linePoint k (z ≫ snd L L)
      have hz : lift (AffineSchemeAction.linePoint k b)
          (AffineSchemeAction.linePoint k c) = z := by
        apply CartesianMonoidalCategory.hom_ext
        · simpa only [lift_fst] using hb
        · simpa only [lift_snd] using hc
      have hsum : (b + c) ^ p ^ n = b ^ p ^ n + c ^ p ^ n := by
        by_cases hC : Nontrivial C
        · have := hC
          have : ExpChar C p := expChar_of_injective_algebraMap (algebraMap k C).injective p
          exact add_pow_expChar_pow b c p n
        · have : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
          exact Subsingleton.elim _ _
      calc
        _ = (AffineSchemeAction.linePoint k b * AffineSchemeAction.linePoint k c) ≫ F := by
          rw [← hz]
          rfl
        _ = AffineSchemeAction.linePoint k ((b + c) ^ p ^ n) := by
          rw [AdditiveTranslation.linePoint_mul, linePoint_comp_relativeFrobenius]
        _ = AffineSchemeAction.linePoint k (b ^ p ^ n + c ^ p ^ n) := congrArg _ hsum
        _ = (AffineSchemeAction.linePoint k b ≫ F) *
            (AffineSchemeAction.linePoint k c ≫ F) := by
          rw [linePoint_comp_relativeFrobenius, linePoint_comp_relativeFrobenius,
            AdditiveTranslation.linePoint_mul]
        _ = _ := by
          rw [← hz, lift_map_assoc, ← Hom.mul_def]
    let e := AffineSchemeAction.tensorSpecIso k
      (AdditiveGroupScheme.CoordinateRing k 1) (AdditiveGroupScheme.CoordinateRing k 1)
    apply (cancel_epi e.inv).mp
    exact key e.inv

end
end AclGeom.FiniteGaCover
