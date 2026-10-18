/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Normal

/-!
# Isomorphisms induced by a regular normal-subgroup conjugation lift

**Status:** proved for group objects in any cartesian monoidal category (#21). A regular
lift of conjugation through a monic group morphism restricts at every group point to an
actual group-object isomorphism. Multiplication and the inverse are proved by cancellation
through the monic inclusion. Named consumer:
`MultiplicativeRigidity.normal_multiplicativeGroup_conj`, which extracts the lift internally
from the actual normal subgroup property. No supplied action or inverse certificate is used.
-/

namespace AclGeom.NormalConjugation
noncomputable section
open CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.GrpObj CategoryTheory.MonObj

/-- A regular lift of conjugation through a monic group morphism restricts at each group
 point to an actual group-object isomorphism. No action or inverse certificate is supplied.
 Named consumer: `MultiplicativeRigidity.normal_multiplicativeGroup_conj`. -/
theorem exists_groupIso_conjugation_lift
    {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    {G N : C} [GrpObj G] [GrpObj N]
    (i : N ⟶ G) [IsMonHom i] [Mono i]
    (ψ : G ⊗ N ⟶ N) (hψ : ψ ≫ i = G ◁ i ≫ conj G)
    (q : 𝟙_ C ⟶ G) :
    ∃ e : Grp.mk N ≅ Grp.mk N,
      e.hom.hom.hom = lift (toUnit N ≫ q) (𝟙 N) ≫ ψ := by
  let c (q : 𝟙_ C ⟶ G) : N ⟶ N := lift (toUnit N ≫ q) (𝟙 N) ≫ ψ
  have hc (q : 𝟙_ C ⟶ G) {T : C} (p : T ⟶ N) :
      (p ≫ c q) ≫ i = (toUnit T ≫ q) * (p ≫ i) * (toUnit T ≫ q)⁻¹ := by
    simp only [c, Category.assoc, hψ, comp_lift_assoc,
      Category.comp_id, lift_whiskerLeft_assoc, lift_conj_eq_mul_mul_inv]
    simp only [← Category.assoc, comp_toUnit]
  have hci (q : 𝟙_ C ⟶ G) :
      c q ≫ i = (toUnit N ≫ q) * i * (toUnit N ≫ q)⁻¹ := by
    simpa only [Category.id_comp] using hc q (𝟙 N)
  have hmul (q : 𝟙_ C ⟶ G) {T : C} (p r : T ⟶ N) :
      (p * r) ≫ c q = (p ≫ c q) * (r ≫ c q) := by
    apply (cancel_mono i).mp
    rw [hc, mul_comp, mul_comp, hc, hc]
    simp only [_root_.mul_assoc, _root_.inv_mul_cancel_left]
  have hone (q : 𝟙_ C ⟶ G) {T : C} : (1 : T ⟶ N) ≫ c q = 1 := by
    apply (cancel_mono i).mp
    rw [hc, one_comp]
    simp only [_root_.mul_one, _root_.mul_inv_cancel]
  have hmon (q : 𝟙_ C ⟶ G) : IsMonHom (c q) := by
    constructor
    · simpa only [one_eq_one] using (hone q (T := 𝟙_ C))
    · simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp,
        lift_fst_comp_snd_comp] using hmul q (fst N N) (snd N N)
  have hinv (q : 𝟙_ C ⟶ G) : c q ≫ c q⁻¹ = 𝟙 N := by
    apply (cancel_mono i).mp
    rw [hc, hci, Category.id_comp, comp_inv]
    simp only [_root_.inv_inv, _root_.mul_assoc, _root_.inv_mul_cancel_left,
      _root_.inv_mul_cancel, _root_.mul_one]
  let e : N ≅ N := ⟨c q, c q⁻¹, hinv q, by simpa only [_root_.inv_inv] using hinv q⁻¹⟩
  have : IsMonHom e.hom := hmon q
  exact ⟨Grp.mkIso' e, rfl⟩
end
end AclGeom.NormalConjugation
