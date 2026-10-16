/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.StepI
import GroupConfig.StepII
import GroupConfig.Germ.BaseChangeHW
import GroupConfig.Germ.HomogeneousSpace

/-!
# The group configuration theorem

Blueprint `sources/group_configuration/08-proof.tex`, Step III and `thm:main`.

Let `(a, b, c, x, y, z)` be a group configuration over an algebraically closed field `k`.
After adjoining a finite set `E` independent from it, the configuration is realized by a
Hrushovski–Weil datum (`GroupConfiguration.exists_main`). Over `acl(k, E)` there are:

* a Hrushovski–Weil datum of bijections `f₀ : V → V'` (`thm:hw-bij`);
* members `g_a`, `g_b`, `g_c` of its difference set with `g_b = g_c g_a`;
* a generic point `y'` of `V` such that `(g_a, g_b, y')` is independent.

For these, `(code g_a, code g_b, code g_c, g_a(y'), y', g_b(y'))` is a group configuration
whose points are interalgebraic with `(a, b, c, x, y, z)`. This conclusion is the predicate
`IsMainConclusion`.

The proof follows the blueprint. Steps I and II (`GroupConfiguration.exists_stepI`,
`GroupConfiguration.exists_isHWBij`) give a configuration over `K₀ = acl(k, E₀)` whose point
`b` is the code of a Hrushovski–Weil datum `g`. Step III (`GroupConfiguration.exists_stepIII`)
then makes three replacements:

1. Over `acl(K₀, b')`, the code and the value of a difference germ `δ` replace `b` and `z`
   (III.1, `GroupConfiguration.exists_stepIII_one`).
2. Over `acl(K₀, b', c'')`, the code and the value of a conjugate `g''` of `δ` replace `a` and
   `x` (III.2).
3. The code of `δ g''⁻¹` replaces `c` (III.3).

For the last replacement, `prop:converse` makes the codes of `g''`, `δ` and `δ g''⁻¹`,
together with the values, a configuration. The third group point of a configuration is
determined up to interalgebraicity by the other points
(`GroupConfiguration.racl_range_c_eq`, by `Cb2`). This replaces the appeal to `lem:triple` in
Step III.3 of the blueprint.

The fresh five-copy construction also makes the finite parameters independent from any
prescribed finite set, retaining their rank and the actual main conclusion. This supplies both
fresh Ψ consumers in `GroupConfig.PsiFresh`; the original main theorem is its empty-set
specialization. The larger field is used for sampling, without changing the configuration base.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the precise `thm:main` of `08-proof.tex` is complete, with the identities in the
homogeneous space `S` of `thm:hw` in `Germ.IsHWBij.iota_eq_smul`. The informal statement in
`00-scope.tex` also asserts that `G` and `S` are constructible. That clause is `thm:constructible`
of `09-constructibility.tex`, proved for every Hrushovski–Weil datum of bijections in
`GroupConfig.Constructible.CanonicalPresentation`. The combined general configuration
conclusion is proved in `GroupConfig.MainConstructible`; its actual Ψ specialization is in
`GroupConfig.PsiConstructible`.
-/

namespace GroupConfig

open AclGeom IntermediateField Set Germ

noncomputable section

universe u

variable {k : Type*} {K : Type u} [Field k] [Field K] [Algebra k K]

/-! ### Closures and independence over nested bases -/

section Nested

variable (K₀ : IntermediateField k K)

/-- Closures over `K₀` are contained in closures over a larger base. -/
theorem coe_racl_subset_of_le {K₁ : IntermediateField k K} (h₀₁ : K₀ ≤ K₁) (S : Set K) :
    ((racl (↥K₀) S : IntermediateField (↥K₀) K) : Set K) ⊆ racl (↥K₁) S := by
  rw [racl_base_coe, racl_base_coe]
  exact SetLike.coe_subset_coe.2 (racl_mono (union_subset_union_left S
    (SetLike.coe_subset_coe.2 h₀₁)))

/-- Independence over `K₀` from `S`, and over `K₁ = acl(K₀, S)` from `T`, give independence
over `K₀` from `acl(K₁, T)`. -/
theorem indepOver_racl_racl {S T A : Set K} (h₁ : IndepOver (↥K₀) ∅ A S)
    (h₂ : IndepOver (↥(racl k ((K₀ : Set K) ∪ S))) ∅ A T) :
    IndepOver (↥K₀) ∅ A (racl k ((racl k ((K₀ : Set K) ∪ S) : Set K) ∪ T) : Set K) := by
  have hle : K₀ ≤ racl k ((K₀ : Set K) ∪ S) := fun w hw ↦ subset_racl k _ (Or.inl hw)
  have hcl : racl (↥K₀) ((racl k ((K₀ : Set K) ∪ S) : IntermediateField k K) : Set K) =
      racl (↥K₀) S := by
    refine SetLike.coe_injective ?_
    rw [racl_base_coe, racl_base_coe, racl_union_right, ← union_assoc, union_self]
  have h₂' : IndepOver (↥K₀) S A T :=
    (indepOver_congr_base hcl).1 ((indepOver_base_le_iff K₀ _ hle A T).1 h₂)
  have h : IndepOver (↥K₀) ∅ A (S ∪ T) :=
    indepOver_union_right_iff.2 ⟨h₁, by rwa [empty_union]⟩
  have e : ((racl k ((racl k ((K₀ : Set K) ∪ S) : Set K) ∪ T) : IntermediateField k K) :
      Set K) = ((racl (↥K₀) (∅ ∪ (S ∪ T)) : IntermediateField (↥K₀) K) : Set K) := by
    rw [empty_union, racl_base_coe, racl_union_left, union_assoc]
  rw [e]
  exact indepOver_racl_right_iff.2 h

end Nested

/-- Equal closures after adjoining `E` give equal closures over `acl(E)`. -/
theorem racl_racl_base_eq {E A B : Set K} (h : racl k (E ∪ A) = racl k (E ∪ B)) :
    racl (↥(racl k E)) A = racl (↥(racl k E)) B := by
  refine SetLike.coe_injective ?_
  rw [racl_base_coe, racl_base_coe, racl_union_left, racl_union_left, h]

/-- Two sets algebraic over each other together with `T` have the same closure with `T`. -/
theorem racl_union_eq_of_subset {A B T : Set K} (hA : A ⊆ racl k (B ∪ T))
    (hB : B ⊆ racl k (A ∪ T)) : racl k (A ∪ T) = racl k (B ∪ T) :=
  le_antisymm (racl_le_of_subset_racl (union_subset hA fun _ hw ↦ subset_racl k _ (Or.inr hw)))
    (racl_le_of_subset_racl (union_subset hB fun _ hw ↦ subset_racl k _ (Or.inr hw)))

/-! ### Codes of base changes -/

namespace Germ

variable [IsAlgClosed K] {ι κ : Type*} [Finite ι] [Finite κ] {a : ι → K} {a' : κ → K}
  (K₀ K₁ : IntermediateField k K) [IsAlgClosed (↥K₀)] [IsAlgClosed (↥K₁)]
  [UniversalDomain (↥K₀) K] [UniversalDomain (↥K₁) K] (h₀₁ : K₀ ≤ K₁)

include h₀₁ in
omit [IsAlgClosed (↥K₁)] [UniversalDomain (↥K₁) K] in
/-- The canonical base of a germ over `K₀` is algebraic over `K₁` and its code. -/
theorem cb_subset_racl_codeTuple_of_le (g : Germ (↥K₀) a a') :
    (g.cb : Set K) ⊆ racl (↥K₁) (range g.codeTuple) :=
  (cb_subset_racl_codeTuple g).trans (coe_racl_subset_of_le K₀ h₀₁ _)

variable (hK₁ : IsSmall (↥K₀) (K₁ : Set K)) (ha : IndepOver (↥K₀) ∅ (range a) (K₁ : Set K))
  (ha' : IndepOver (↥K₀) ∅ (range a') (K₁ : Set K))

/-- The code of a base change is interalgebraic over `K₁` with the original code. -/
theorem racl_codeTuple_baseChange (g : Germ (↥K₀) a a') :
    racl (↥K₁) (range (g.baseChange K₀ K₁ h₀₁ hK₁ ha ha').codeTuple) =
      racl (↥K₁) (range g.codeTuple) := by
  rw [racl_codeTuple, racl_cb_baseChange]
  refine SetLike.coe_injective ?_
  rw [coe_racl_base_eq K₀ K₁ h₀₁, coe_racl_base_eq K₀ K₁ h₀₁,
    racl_union_congr rfl (racl_codeTuple g).symm]

end Germ

/-! ### Configurations -/

namespace GroupConfiguration

variable {ι₁ ι₂ ι₃ ι₄ ι₅ ι₆ : Type*} [Finite ι₁] [Finite ι₂] [Finite ι₃] [Finite ι₄]
  [Finite ι₅] [Finite ι₆] {a : ι₁ → K} {b : ι₂ → K} {c : ι₃ → K} {x : ι₄ → K} {y : ι₅ → K}
  {z : ι₆ → K}

section Points

variable (hc : GroupConfiguration k a b c x y z)
include hc

omit [Finite ι₃] in
/-- `lem:gc-ranks`: the space point `x` is independent from the group points `a, b`. -/
theorem indepOver_x_ab : IndepOver k ∅ (range x) (range a ∪ range b) :=
  (hc.indep 0 1 3 (by decide) (by decide) (by decide) (by decide)).rotate.rotate.indepOver_union
    (finite_range x) (finite_range a) (finite_range b)

variable [IsAlgClosed K] [UniversalDomain k K]

/-- The closure of the group point `c` is the closure of the canonical base of `x, z` over
`acl(a, b)` (`Cb2`). -/
theorem racl_c_eq_canonicalBase :
    racl k (range c) =
      racl k (canonicalBase (racl k (range a ∪ range b)) (Sum.elim x z) : Set K) := by
  have _ : IsAlgClosed ↥(racl k (range c)) := isAlgClosed_racl _
  have _ : IsAlgClosed ↥(racl k (range a ∪ range b)) := isAlgClosed_racl _
  have hcab : range c ⊆ racl k (range a ∪ range b) := by
    rw [hc.racl_ab_bc]
    exact fun w hw ↦ subset_racl k _ (Or.inr hw)
  have hLM : racl k (range c) ≤ racl k (range a ∪ range b) := racl_le_of_isAlgClosed hcab
  have hzc : range z ⊆ racl k (range c ∪ range x) := by
    rw [hc.racl_cx_cz]
    exact fun w hw ↦ subset_racl k _ (Or.inr hw)
  have hzL : range z ⊆ racl k ((racl k (range c) : Set K) ∪ range x) := by
    rw [racl_union_left]
    exact hzc
  have hzM : range z ⊆ racl k ((racl k (range a ∪ range b) : Set K) ∪ range x) := by
    exact hzc.trans (SetLike.coe_subset_coe.2 (racl_mono (union_subset_union_left _ hcab)))
  have hrkL : erk k (racl k (range c) : Set K) (range x ∪ range z) = erk k ∅ (range x) := by
    rw [erk_union_eq_of_subset_racl k hzL, erk_racl_base]
    have := hc.indepOver_cx.symm (subset_refl _) (finite_range x)
    rwa [empty_union] at this
  have hrkM : erk k ((racl k (range c) : Set K) ∪ (racl k (range a ∪ range b) : Set K))
      (range x ∪ range z) = erk k ∅ (range x) := by
    rw [union_eq_right.2 (SetLike.coe_subset_coe.2 hLM), erk_union_eq_of_subset_racl k hzM,
      erk_racl_base]
    have := hc.indepOver_x_ab (subset_refl _) (finite_range x)
    rwa [empty_union] at this
  have hind : IndepOver k (racl k (range c) : Set K) (range (Sum.elim x z))
      (racl k (range a ∪ range b) : Set K) := by
    refine indepOver_of_erk_eq (finite_range _) ?_
    rw [Sum.elim_range, hrkL, hrkM]
  rw [canonicalBase_eq_of_indepOver (IsSmall.of_finite (finite_range c)).racl
    (IsSmall.of_finite ((finite_range a).union (finite_range b))).racl hLM hind]
  have _ : IsAlgClosed ↥(racl k (canonicalBase (racl k (range c)) (Sum.elim x z) : Set K)) :=
    isAlgClosed_racl _
  exact le_antisymm (racl_le_of_isAlgClosed hc.cb_c)
    (racl_le_of_isAlgClosed (SetLike.coe_subset_coe.2 (canonicalBase_le _ _)))

/-- The third group point of a configuration is determined up to interalgebraicity by the
other points. -/
theorem racl_range_c_eq {ι₃' : Type*} [Finite ι₃'] {c' : ι₃' → K}
    (hc' : GroupConfiguration k a b c' x y z) : racl k (range c) = racl k (range c') := by
  rw [hc.racl_c_eq_canonicalBase, hc'.racl_c_eq_canonicalBase]

end Points

/-- `lem:gc-invariance`(2) over the nested base `acl(K₀, S)`. -/
theorem baseChange_racl [IsAlgClosed K] (K₀ : IntermediateField k K) [UniversalDomain (↥K₀) K]
    (hc : GroupConfiguration (↥K₀) a b c x y z) {S : Set K} (hS : S.Finite)
    (h : IndepOver (↥K₀) ∅ S (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z)) :
    GroupConfiguration (↥(racl k ((K₀ : Set K) ∪ S))) a b c x y z := by
  refine ofNested K₀ S (hc.baseChange (racl (↥K₀) S) (IsSmall.of_finite hS).racl ?_)
  have h' := indepOver_racl_left_iff.2 h
  rwa [empty_union] at h'

omit [Finite ι₂] in
/-- Step III.2 of `thm:main`, the conjugation: a generic copy `c''` of `c` over a finite set `W`
is the image of `c` under an automorphism fixing `a`, `x` and `y`. -/
theorem exists_conj_c [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K]
    (hc : GroupConfiguration k a b c x y z) {W : Set K} (hW : W.Finite) :
    ∃ (c'' : ι₃ → K) (σ : K ≃ₐ[k] K), IndepOver k ∅ (range c'') W ∧ ⇑σ ∘ a = a ∧
      ⇑σ ∘ x = x ∧ ⇑σ ∘ y = y ∧ ⇑σ ∘ c = c'' := by
  have hN : (range a ∪ range x ∪ range y).Finite :=
    ((finite_range a).union (finite_range x)).union (finite_range y)
  obtain ⟨c'', hc''⟩ := exists_isGenericOver (IsSmall.of_finite (k := k) (hW.union hN)).racl c
  have hcN : IsGenericOver (racl k (range a ∪ range x ∪ range y)) c c := by
    refine isGenericOver_self_of_indepOver (IsSmall.of_finite (k := k) hN).racl ?_
    have := indepOver_racl_right_iff.2 hc.indepOver_c_axy
    rwa [empty_union] at this
  have hc''N : IsGenericOver (racl k (range a ∪ range x ∪ range y)) c c'' :=
    hc''.of_le (racl_mono (k := k) subset_union_right)
  obtain ⟨σ, hσ⟩ := hcN.exists_algEquiv hc''N
  have hfix : ∀ s ∈ range a ∪ range x ∪ range y, (σ.restrictScalars k) s = s := fun s hs ↦ by
    change σ s = s
    exact σ.commutes ⟨s, subset_racl k _ hs⟩
  refine ⟨c'', σ.restrictScalars k, ?_, ?_, ?_, ?_, funext fun i ↦ hσ i⟩
  · exact (hc''.indepOver.mono_right (subset_racl k _)).mono_right subset_union_left
  · exact funext fun i ↦ hfix _ (subset_union_left (subset_union_left (mem_range_self i)))
  · exact funext fun i ↦ hfix _ (subset_union_left (subset_union_right (mem_range_self i)))
  · exact funext fun i ↦ hfix _ (subset_union_right (mem_range_self i))

end GroupConfiguration

/-! ### The standard configuration in the homogeneous space -/

namespace Germ

variable [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] {ι κ : Type*} [Finite ι]
  [Finite κ] {a : ι → K} {a' : κ → K}

/-- `thm:main`, the identities in the homogeneous space `S` of `thm:hw`. Let `g_a`, `g_b`, `g_c`
be members of the difference set of a Hrushovski–Weil datum of bijections, with
`g_b = g_c g_a` and `g_c(g_a(y)) = g_b(y)`, whose standard tuple is a group configuration.
Then `ι(x') = g_a · ι(y)`, `ι(z') = g_b · ι(y) = g_c · ι(x')` and `g_b = g_c g_a` in the
group `G`, for `x' = g_a(y)` and `z' = g_b(y)`. -/
theorem IsHWBij.iota_eq_smul {f₀ : Germ k a a'} (hb : IsHWBij f₀) {ga gb gc : Germ k a a}
    (hga : ga ∈ diffSet f₀) (hgb : gb ∈ diffSet f₀) (hgc : gc ∈ diffSet f₀) {y : ι → K}
    (hy : IsGen k a y)
    (hc : GroupConfiguration k ga.codeTuple gb.codeTuple gc.codeTuple (ga.evalGen y) y
      (gb.evalGen y))
    (hmul : gb = gc * ga) (heval : gc.evalGen (ga.evalGen y) = gb.evalGen y) :
    ∃ (hx : IsGen k a (ga.evalGen y)) (hz : IsGen k a (gb.evalGen y))
      (ha : ga ∈ IsHW.prodSet gb) (hb' : gb ∈ IsHW.prodSet gb) (hc' : gc ∈ IsHW.prodSet gb),
      (hb.isHW hgb).iota hx = (hb.isHW hgb).ofMem ha • (hb.isHW hgb).iota hy ∧
      (hb.isHW hgb).iota hz = (hb.isHW hgb).ofMem hb' • (hb.isHW hgb).iota hy ∧
      (hb.isHW hgb).iota hz = (hb.isHW hgb).ofMem hc' • (hb.isHW hgb).iota hx ∧
      (hb.isHW hgb).ofMem hb' = (hb.isHW hgb).ofMem hc' * (hb.isHW hgb).ofMem ha := by
  have hw := hb.isHW hgb
  have horb := diffSet_eq_orbit hgb
  have ha := hw.mem_prodSet_of_mem (horb ▸ hga)
  have hb' := hw.mem_prodSet_of_mem (horb ▸ hgb)
  have hc' := hw.mem_prodSet_of_mem (horb ▸ hgc)
  have hya : IndepOver k ∅ (range y) (ga.cb : Set K) :=
    indepOver_of_subset_racl (subset_racl k _) (cb_subset_racl_codeTuple ga) hc.indepOver_ay.symm
  have hyb : IndepOver k ∅ (range y) (gb.cb : Set K) :=
    indepOver_of_subset_racl (subset_racl k _) (cb_subset_racl_codeTuple gb) hc.indepOver_by.symm
  have hxc : IndepOver k ∅ (range (ga.evalGen y)) (gc.cb : Set K) :=
    indepOver_of_subset_racl (subset_racl k _) (cb_subset_racl_codeTuple gc) hc.indepOver_cx.symm
  have hx := ga.isGen_evalGen hy hya
  refine ⟨hx, gb.isGen_evalGen hy hyb, ha, hb', hc', ((hb.isHW hgb).smul_iota ha hy hya).symm,
    ((hb.isHW hgb).smul_iota hb' hy hyb).symm, ?_, ?_⟩
  · rw [(hb.isHW hgb).smul_iota hc' hx hxc]
    exact (hb.isHW hgb).iota_congr _ _ heval.symm
  · refine (hb.isHW hgb).val_injective ?_
    rw [IsHW.val_mul, IsHW.val_ofMem, IsHW.val_ofMem, IsHW.val_ofMem]
    exact hmul

end Germ

/-! ### The conclusion of the main theorem -/

variable [IsAlgClosed K]

variable (k) in
/-- The conclusion of `thm:main` over a base `F` for tuples `(a, b, c, x, y, z)`. Over `F`
there are:

* a Hrushovski–Weil datum of bijections `f₀ : V → V'` (`thm:hw-bij`), where `V = Loc(v)` and
  `V' = Loc(v')` have the rank of `x` and the canonical base of `f₀` has the rank of `a`;
* members `g_a`, `g_b`, `g_c` of its difference set with `g_b = g_c g_a`;
* a generic point `y'` of `V` such that `(g_a, g_b, y')` is independent.

They satisfy `g_c(g_a(y')) = g_b(y')`, the tuple
`(code g_a, code g_b, code g_c, g_a(y'), y', g_b(y'))` is a group configuration over `F`, and
its points are interalgebraic over `F` with `a, b, c, x, y, z`. -/
def IsMainConclusion (F : IntermediateField k K) {ι₁ ι₂ ι₃ ι₄ ι₅ ι₆ : Type*} (a : ι₁ → K)
    (b : ι₂ → K) (c : ι₃ → K) (x : ι₄ → K) (y : ι₅ → K) (z : ι₆ → K) : Prop :=
  ∃ (_ : IsAlgClosed ↥F) (_ : UniversalDomain (↥F) K) (ν ν' : Type u) (_ : Finite ν)
    (_ : Finite ν') (v : ν → K) (v' : ν' → K) (f₀ : Germ (↥F) v v') (ga gb gc : Germ (↥F) v v)
    (y' : ν → K),
    IsHWBij f₀ ∧ ga ∈ diffSet f₀ ∧ gb ∈ diffSet f₀ ∧ gc ∈ diffSet f₀ ∧ gb = gc * ga ∧
      IsGen (↥F) v y' ∧ IndepTriple (↥F) (ga.cb : Set K) (gb.cb : Set K) (range y') ∧
      gc.evalGen (ga.evalGen y') = gb.evalGen y' ∧
      GroupConfiguration (↥F) ga.codeTuple gb.codeTuple gc.codeTuple (ga.evalGen y') y'
        (gb.evalGen y') ∧
      racl (↥F) (range a) = racl (↥F) (range ga.codeTuple) ∧
      racl (↥F) (range b) = racl (↥F) (range gb.codeTuple) ∧
      racl (↥F) (range c) = racl (↥F) (range gc.codeTuple) ∧
      racl (↥F) (range x) = racl (↥F) (range (ga.evalGen y')) ∧
      racl (↥F) (range y) = racl (↥F) (range y') ∧
      racl (↥F) (range z) = racl (↥F) (range (gb.evalGen y')) ∧
      erk (↥F) ∅ (range v) = erk (↥F) ∅ (range x) ∧
      erk (↥F) ∅ (range v') = erk (↥F) ∅ (range x) ∧
      erk (↥F) ∅ (f₀.cb : Set K) = erk (↥F) ∅ (range a)

/-! ### Step III -/

namespace GroupConfiguration

variable [IsAlgClosed k] [UniversalDomain k K]

section StepIII

variable {ι₁ ι₃ ι₄ : Type*} {ι₅ ι₆ : Type u} [Finite ι₁] [Finite ι₃] [Finite ι₄] [Finite ι₅]
  [Finite ι₆] {a : ι₁ → K} {c : ι₃ → K} {x : ι₄ → K} {y : ι₅ → K} {z : ι₆ → K}

omit [IsAlgClosed k] in
/-- Step III.1 retaining the rank of its actual generic copy of the germ code, which is chosen
independent from a prescribed finite set `W` as well as from the configuration. Named consumers:
`GroupConfiguration.exists_stepIII_one_with_parameterRank` and
`GroupConfiguration.exists_stepIII_fresh_with_parameterRank`. -/
theorem exists_stepIII_one_fresh_with_parameterRank (K₀ : IntermediateField k K)
    [IsAlgClosed (↥K₀)] [UniversalDomain (↥K₀) K] (hK₀ : IsSmall k (K₀ : Set K))
    {g : Germ (↥K₀) y z} (hc : GroupConfiguration (↥K₀) a g.codeTuple c x y z) (hg : IsHWBij g)
    (hgz : g.evalGen y = z) {W : Set K} (hW : W.Finite) :
    ∃ (b' : ↥g.codeSet → K) (δ : Germ (↥K₀) y y) (y₁ : ι₅ → K),
      erk (↥K₀) ∅ (range b') = erk (↥K₀) ∅ (range g.codeTuple) ∧
      IndepOver (↥K₀) ∅ (range b')
        (range a ∪ range g.codeTuple ∪ range c ∪ range x ∪ range y ∪ range z ∪ W) ∧
      δ ∈ diffSet g ∧ δ.evalGen y = y₁ ∧ IndepOver (↥K₀) ∅ (δ.cb : Set K) (range b') ∧
      IndepOver (↥K₀) ∅ (range y) (δ.cb : Set K) ∧
      racl (↥(racl k ((K₀ : Set K) ∪ range b'))) (range δ.codeTuple) =
        racl (↥(racl k ((K₀ : Set K) ∪ range b'))) (range g.codeTuple) ∧
      racl (↥(racl k ((K₀ : Set K) ∪ range b'))) (range y₁) =
        racl (↥(racl k ((K₀ : Set K) ∪ range b'))) (range z) ∧
      GroupConfiguration (↥(racl k ((K₀ : Set K) ∪ range b'))) a δ.codeTuple c x y y₁ := by
  obtain ⟨b', σ, δ, hb'indW, hσb, -, -, -, hc', hδmem, hδy, hδcb_le, hbsub, hδb', -, -⟩ :=
    exists_conj_diff_fresh (range_codeTuple g) hc hg.isInvertible hgz hW
  have hb'ind : IndepOver (↥K₀) ∅ (range b')
      (range a ∪ range g.codeTuple ∪ range c ∪ range x ∪ range y ∪ range z) :=
    hb'indW.mono_right subset_union_left
  have hb'rank : erk (↥K₀) ∅ (range b') = erk (↥K₀) ∅ (range g.codeTuple) := by
    rw [← hσb, range_comp]
    simpa only [image_empty] using erk_image σ (∅ : Set K) (range g.codeTuple)
  have hsub := fun i ↦ gcPoints_subset (a := a) (b := g.codeTuple) (c := c) (x := x) (y := y)
    (z := z) i
  have hK₁s : IsSmall k ((racl k ((K₀ : Set K) ∪ range b') : IntermediateField k K) : Set K) :=
    (hK₀.union (IsSmall.of_finite (finite_range b'))).racl
  have _ : IsAlgClosed ↥(racl k ((K₀ : Set K) ∪ range b')) := isAlgClosed_racl _
  have _ : UniversalDomain ↥(racl k ((K₀ : Set K) ∪ range b')) K :=
    universalDomain_of_isSmall _ hK₁s
  /- `b` and the code of `δ` are interalgebraic over `b'`. -/
  have hδcode : racl (↥K₀) (range δ.codeTuple ∪ range b') =
      racl (↥K₀) (range g.codeTuple ∪ range b') := by
    refine racl_union_eq_of_subset ?_ ?_
    · have _ : IsAlgClosed ↥(racl (↥K₀) (range g.codeTuple ∪ range b')) := isAlgClosed_racl _
      rw [range_codeTuple δ]
      exact (codeSet_subset_racl_cb δ).trans (SetLike.coe_subset_coe.2
        (racl_le_of_isAlgClosed (SetLike.coe_subset_coe.2 hδcb_le)))
    · refine hbsub.trans (SetLike.coe_subset_coe.2 (racl_le_of_subset_racl (union_subset ?_ ?_)))
      · exact fun w hw ↦ subset_racl (↥K₀) _ (Or.inr hw)
      · exact (cb_subset_racl_codeTuple δ).trans
          (SetLike.coe_subset_coe.2 (racl_mono subset_union_left))
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : ι₅ → K, y₁ = ⇑σ ∘ y := ⟨_, rfl⟩
  have hracl_z : racl (↥(racl k ((K₀ : Set K) ∪ range b'))) (range y₁) =
      racl (↥(racl k ((K₀ : Set K) ∪ range b'))) (range z) := by
    refine racl_eq_of_racl_union_eq K₀ ?_
    rw [union_comm (range y₁), hy₁, hc'.racl_by_bz, union_comm]
  have hc₁ : GroupConfiguration (↥(racl k ((K₀ : Set K) ∪ range b'))) a δ.codeTuple c x y y₁ :=
    (baseChange_racl K₀ hc (finite_range b') hb'ind).ofRaclEq rfl
      (racl_eq_of_racl_union_eq K₀ hδcode) rfl rfl rfl hracl_z
  /- `y` is independent from `δ`. -/
  have hyδ : IndepOver (↥K₀) ∅ (range y) (δ.cb : Set K) := by
    have h₁ : IndepOver (↥K₀) ∅ (range y) (range b') :=
      (hb'ind.mono_right (hsub 4)).symm
    have h₂ : IndepOver (↥(racl k ((K₀ : Set K) ∪ range b'))) ∅ (range y)
        (range δ.codeTuple) := hc₁.indepOver_by.symm
    refine (indepOver_racl_racl K₀ h₁ h₂).mono_right ((cb_subset_racl_codeTuple δ).trans ?_)
    rw [racl_base_coe]
    exact SetLike.coe_subset_coe.2 (racl_mono (union_subset_union_left _
      fun w hw ↦ subset_racl k _ (Or.inl hw)))
  exact ⟨b', δ, y₁, hb'rank, hb'indW, hδmem, hδy.trans hy₁.symm, hδb', hyδ,
    racl_eq_of_racl_union_eq K₀ hδcode, hracl_z, hc₁⟩

omit [IsAlgClosed k] in
/-- Step III.1 retaining the rank of its actual generic copy of the germ code.
Named consumer: `GroupConfiguration.exists_stepIII_one`. -/
theorem exists_stepIII_one_with_parameterRank (K₀ : IntermediateField k K) [IsAlgClosed (↥K₀)]
    [UniversalDomain (↥K₀) K] (hK₀ : IsSmall k (K₀ : Set K)) {g : Germ (↥K₀) y z}
    (hc : GroupConfiguration (↥K₀) a g.codeTuple c x y z) (hg : IsHWBij g)
    (hgz : g.evalGen y = z) :
    ∃ (b' : ↥g.codeSet → K) (δ : Germ (↥K₀) y y) (y₁ : ι₅ → K),
      erk (↥K₀) ∅ (range b') = erk (↥K₀) ∅ (range g.codeTuple) ∧
      IndepOver (↥K₀) ∅ (range b')
        (range a ∪ range g.codeTuple ∪ range c ∪ range x ∪ range y ∪ range z) ∧
      δ ∈ diffSet g ∧ δ.evalGen y = y₁ ∧ IndepOver (↥K₀) ∅ (δ.cb : Set K) (range b') ∧
      IndepOver (↥K₀) ∅ (range y) (δ.cb : Set K) ∧
      racl (↥(racl k ((K₀ : Set K) ∪ range b'))) (range δ.codeTuple) =
        racl (↥(racl k ((K₀ : Set K) ∪ range b'))) (range g.codeTuple) ∧
      racl (↥(racl k ((K₀ : Set K) ∪ range b'))) (range y₁) =
        racl (↥(racl k ((K₀ : Set K) ∪ range b'))) (range z) ∧
      GroupConfiguration (↥(racl k ((K₀ : Set K) ∪ range b'))) a δ.codeTuple c x y y₁ := by
  obtain ⟨b', δ, y₁, hrank, hb', h⟩ :=
    exists_stepIII_one_fresh_with_parameterRank K₀ hK₀ hc hg hgz finite_empty
  rw [union_empty] at hb'
  exact ⟨b', δ, y₁, hrank, hb', h⟩

omit [IsAlgClosed k] in
/-- Step III.1 of `thm:main`. Let `b'` be a generic copy of `b = code g`. Over
`K₁ = acl(K₀, b')`, the code of the difference germ `δ = g_{b'}⁻¹ g` replaces `b`, and its value
`y₁ = δ(y)` replaces `z`. -/
theorem exists_stepIII_one (K₀ : IntermediateField k K) [IsAlgClosed (↥K₀)]
    [UniversalDomain (↥K₀) K] (hK₀ : IsSmall k (K₀ : Set K)) {g : Germ (↥K₀) y z}
    (hc : GroupConfiguration (↥K₀) a g.codeTuple c x y z) (hg : IsHWBij g)
    (hgz : g.evalGen y = z) :
    ∃ (b' : ↥g.codeSet → K) (δ : Germ (↥K₀) y y) (y₁ : ι₅ → K),
      IndepOver (↥K₀) ∅ (range b')
        (range a ∪ range g.codeTuple ∪ range c ∪ range x ∪ range y ∪ range z) ∧
      δ ∈ diffSet g ∧ δ.evalGen y = y₁ ∧ IndepOver (↥K₀) ∅ (δ.cb : Set K) (range b') ∧
      IndepOver (↥K₀) ∅ (range y) (δ.cb : Set K) ∧
      racl (↥(racl k ((K₀ : Set K) ∪ range b'))) (range δ.codeTuple) =
        racl (↥(racl k ((K₀ : Set K) ∪ range b'))) (range g.codeTuple) ∧
      racl (↥(racl k ((K₀ : Set K) ∪ range b'))) (range y₁) =
        racl (↥(racl k ((K₀ : Set K) ∪ range b'))) (range z) ∧
      GroupConfiguration (↥(racl k ((K₀ : Set K) ∪ range b'))) a δ.codeTuple c x y y₁ := by
  obtain ⟨b', δ, y₁, -, h⟩ := exists_stepIII_one_with_parameterRank K₀ hK₀ hc hg hgz
  exact ⟨b', δ, y₁, h⟩

omit [IsAlgClosed k] in
/-- Step III retaining the total rank of its two actual generic copies, which are chosen
independent from a prescribed finite set `W` as well as from the configuration. Named consumers:
`GroupConfiguration.exists_stepIII_with_parameterRank` and
`GroupConfiguration.exists_main_fresh_with_parameterRank`. -/
theorem exists_stepIII_fresh_with_parameterRank (K₀ : IntermediateField k K)
    [IsAlgClosed (↥K₀)] [UniversalDomain (↥K₀) K] (hK₀ : IsSmall k (K₀ : Set K))
    {g : Germ (↥K₀) y z} (hc : GroupConfiguration (↥K₀) a g.codeTuple c x y z) (hg : IsHWBij g)
    (hgz : g.evalGen y = z) {W : Set K} (hW : W.Finite) {μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : Type*}
    {a₀ : μ₁ → K} {b₀ : μ₂ → K} {c₀ : μ₃ → K} {x₀ : μ₄ → K} {y₀ : μ₅ → K} {z₀ : μ₆ → K}
    (ha₀ : racl (↥K₀) (range a₀) = racl (↥K₀) (range a))
    (hb₀ : racl (↥K₀) (range b₀) = racl (↥K₀) (range g.codeTuple))
    (hc₀ : racl (↥K₀) (range c₀) = racl (↥K₀) (range c))
    (hx₀ : racl (↥K₀) (range x₀) = racl (↥K₀) (range x))
    (hy₀ : racl (↥K₀) (range y₀) = racl (↥K₀) (range y))
    (hz₀ : racl (↥K₀) (range z₀) = racl (↥K₀) (range z)) :
    ∃ S : Set K, S.Finite ∧ erk (↥K₀) ∅ S = 2 * erk (↥K₀) ∅ (range a) ∧
      IndepOver (↥K₀) ∅ S
        (range a ∪ range g.codeTuple ∪ range c ∪ range x ∪ range y ∪ range z ∪ W) ∧
      IsMainConclusion k (racl k ((K₀ : Set K) ∪ S)) a₀ b₀ c₀ x₀ y₀ z₀ := by
  /- Step III.1. -/
  obtain ⟨b', δ, y₁, hb'rank, hb'indW, hδmem, hδy, hδb', hyδ, hracl_b, hracl_z, hc₁⟩ :=
    exists_stepIII_one_fresh_with_parameterRank K₀ hK₀ hc hg hgz hW
  have hb'ind : IndepOver (↥K₀) ∅ (range b')
      (range a ∪ range g.codeTuple ∪ range c ∪ range x ∪ range y ∪ range z) :=
    hb'indW.mono_right subset_union_left
  have hb'rank' := hb'rank.trans hc.erk_b_eq
  have hsub := fun i ↦ gcPoints_subset (a := a) (b := g.codeTuple) (c := c) (x := x) (y := y)
    (z := z) i
  have hK₁s : IsSmall k ((racl k ((K₀ : Set K) ∪ range b') : IntermediateField k K) : Set K) :=
    (hK₀.union (IsSmall.of_finite (finite_range b'))).racl
  have i₁ : IsAlgClosed ↥(racl k ((K₀ : Set K) ∪ range b')) := isAlgClosed_racl _
  have u₁ : UniversalDomain ↥(racl k ((K₀ : Set K) ∪ range b')) K :=
    universalDomain_of_isSmall _ hK₁s
  have h₀₁ : K₀ ≤ racl k ((K₀ : Set K) ∪ range b') := fun w hw ↦ subset_racl k _ (Or.inl hw)
  have hb'K₁ : range b' ⊆ (racl k ((K₀ : Set K) ∪ range b') : Set K) :=
    fun w hw ↦ subset_racl k _ (Or.inr hw)
  have lift₁ : ∀ {A B : Set K}, racl (↥K₀) A = racl (↥K₀) B →
      racl (↥(racl k ((K₀ : Set K) ∪ range b'))) A =
        racl (↥(racl k ((K₀ : Set K) ∪ range b'))) B :=
    fun h ↦ racl_eq_of_racl_eq K₀ _ h
  have two_step : ∀ {A T : Set K}, IndepOver (↥K₀) ∅ A (range b') →
      IndepOver (↥(racl k ((K₀ : Set K) ∪ range b'))) ∅ A T →
      IndepOver (↥K₀) ∅ A (racl k ((racl k ((K₀ : Set K) ∪ range b') : Set K) ∪ T) : Set K) :=
    fun h₁ h₂ ↦ indepOver_racl_racl K₀ h₁ h₂
  have hK₂eq : ∀ T : Set K, racl k ((racl k ((K₀ : Set K) ∪ range b') : Set K) ∪ T) =
      racl k ((K₀ : Set K) ∪ (range b' ∪ T)) := fun T ↦ by
    rw [racl_union_left, union_assoc]
  revert hracl_b hracl_z hc₁ lift₁ two_step hK₂eq
  generalize hK₁ : racl k ((K₀ : Set K) ∪ range b') = K₁ at hK₁s i₁ u₁ h₀₁ hb'K₁ ⊢
  intro hracl_b hracl_z hc₁ lift₁ two_step hK₂eq
  have hK₁base : (K₁ : Set K) = (racl (↥K₀) (range b') : Set K) := by
    rw [racl_base_coe K₀, hK₁]
  have hcrank : erk (↥K₁) ∅ (range c) = erk (↥K₀) ∅ (range a) := by
    rw [erk_base_le K₀ K₁ h₀₁, hK₁base, erk_racl_base]
    simpa only [empty_union] using
      ((hb'ind.mono_right (hsub 2)).symm.erk_eq (a := range c)
        (subset_refl _) (finite_range c)).trans hc.erk_c_eq
  /- Step III.2: a generic copy `c''` of `c` and its conjugation `σ₂` over `K₁`. -/
  have hWfin : (range a ∪ range δ.codeTuple ∪ range c ∪ range x ∪ range y ∪ range y₁ ∪
      (range g.codeTuple ∪ range z)).Finite :=
    ((((((finite_range a).union (finite_range _)).union (finite_range c)).union
      (finite_range x)).union (finite_range y)).union (finite_range y₁)).union
      ((finite_range _).union (finite_range z))
  obtain ⟨c'', σ₂, hc''WW, hσ₂a, hσ₂x, hσ₂y, hσ₂c⟩ := hc₁.exists_conj_c (hWfin.union hW)
  have hc''W := hc''WW.mono_right subset_union_left
  have hc''rank : erk (↥K₁) ∅ (range c'') = erk (↥K₁) ∅ (range c) := by
    rw [← hσ₂c, range_comp]
    simpa only [image_empty] using erk_image σ₂ (∅ : Set K) (range c)
  have hSrank : erk (↥K₀) ∅ (range b' ∪ range c'') = 2 * erk (↥K₀) ∅ (range a) := by
    have hbase : erk (↥K₀) (range b') (range c'') = erk (↥K₁) ∅ (range c'') := by
      rw [erk_base_le K₀ K₁ h₀₁, hK₁base, erk_racl_base]
    rw [erk_union_eq, empty_union, hb'rank', hbase, hc''rank, hcrank]
    ring
  have hyW : range y ⊆ range a ∪ range δ.codeTuple ∪ range c ∪ range x ∪ range y ∪ range y₁ ∪
      (range g.codeTuple ∪ range z) := fun _ h ↦ Or.inl (Or.inl (Or.inr h))
  have hzW : range z ⊆ range a ∪ range δ.codeTuple ∪ range c ∪ range x ∪ range y ∪ range y₁ ∪
      (range g.codeTuple ∪ range z) := fun _ h ↦ Or.inr (Or.inr h)
  have hgW : range g.codeTuple ⊆ range a ∪ range δ.codeTuple ∪ range c ∪ range x ∪ range y ∪
      range y₁ ∪ (range g.codeTuple ∪ range z) := fun _ h ↦ Or.inr (Or.inl h)
  have hδW : range δ.codeTuple ⊆ range a ∪ range δ.codeTuple ∪ range c ∪ range x ∪ range y ∪
      range y₁ ∪ (range g.codeTuple ∪ range z) :=
    fun _ h ↦ Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  have hptsW : range a ∪ range g.codeTuple ∪ range c ∪ range x ∪ range y ∪ range z ⊆
      range a ∪ range δ.codeTuple ∪ range c ∪ range x ∪ range y ∪ range y₁ ∪
        (range g.codeTuple ∪ range z) :=
    union_subset (union_subset (union_subset (union_subset (union_subset
      (fun _ h ↦ Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))) hgW)
      (fun _ h ↦ Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
      (fun _ h ↦ Or.inl (Or.inl (Or.inl (Or.inr h))))) hyW) hzW
  obtain ⟨σ₂₀, hσ₂₀⟩ : ∃ τ : K ≃ₐ[↥K₀] K, ⇑τ = ⇑σ₂ :=
    ⟨restrictBase K₀ K₁ h₀₁ σ₂, coe_restrictBase K₀ K₁ h₀₁ σ₂⟩
  obtain ⟨g'', hg''⟩ : ∃ g'' : Germ (↥K₀) y y, g'' = δ.map σ₂₀ := ⟨_, rfl⟩
  obtain ⟨z'', hz''⟩ : ∃ z'' : ι₅ → K, z'' = ⇑σ₂ ∘ y₁ := ⟨_, rfl⟩
  have hg''mem : g'' ∈ diffSet g := by
    rw [hg'']
    exact map_mem_diffSet hδmem σ₂₀
  have hg''y : g''.evalGen y = z'' := by
    have h := evalGen_map σ₂₀ δ (rfl : IsGen (↥K₀) y y) hyδ
    have hy : ⇑σ₂₀ ∘ y = y := by
      rw [hσ₂₀]
      exact hσ₂y
    rw [hy, hδy, hσ₂₀, ← hz'', ← hg''] at h
    exact h
  /- The conjugate configuration over `K₁`. -/
  have hc₁σ : GroupConfiguration (↥K₁) a g''.codeTuple c'' x y z'' := by
    have h := hc₁.map σ₂
    rw [hσ₂a, hσ₂x, hσ₂y, hσ₂c, ← hz''] at h
    refine h.ofRaclEq rfl ?_ rfl rfl rfl rfl
    rw [← hσ₂₀]
    refine lift₁ ?_
    rw [hg'']
    exact racl_codeTuple_map σ₂₀ δ
  /- Base change to `K₂ = acl(K₁, c'')`, replacing `a` and `x`. -/
  have hK₂s : IsSmall k ((racl k ((K₁ : Set K) ∪ range c'') : IntermediateField k K) : Set K) :=
    (hK₁s.union (IsSmall.of_finite (finite_range c''))).racl
  have i₂ : IsAlgClosed ↥(racl k ((K₁ : Set K) ∪ range c'')) := isAlgClosed_racl _
  have u₂ : UniversalDomain ↥(racl k ((K₁ : Set K) ∪ range c'')) K :=
    universalDomain_of_isSmall _ hK₂s
  have hra : racl (↥(racl k ((K₁ : Set K) ∪ range c''))) (range g''.codeTuple) =
      racl (↥(racl k ((K₁ : Set K) ∪ range c''))) (range a) :=
    racl_eq_of_racl_union_eq K₁ (hc₁σ.racl_ab_bc.symm.trans hc₁σ.racl_ab_ac)
  have hrx : racl (↥(racl k ((K₁ : Set K) ∪ range c''))) (range z'') =
      racl (↥(racl k ((K₁ : Set K) ∪ range c''))) (range x) :=
    racl_eq_of_racl_union_eq K₁ (by rw [union_comm (range z''), ← hc₁σ.racl_cx_cz, union_comm])
  have hc₂ : GroupConfiguration (↥(racl k ((K₁ : Set K) ∪ range c''))) g''.codeTuple
      δ.codeTuple c z'' y y₁ :=
    (baseChange_racl K₁ hc₁ (finite_range c'') (hc''W.mono_right subset_union_left)).ofRaclEq
      hra rfl rfl hrx rfl rfl
  /- Independence from `K₂` of the reference tuples and of the germs. -/
  have hyK : IndepOver (↥K₀) ∅ (range y) (racl k ((K₁ : Set K) ∪ range c'') : Set K) :=
    two_step (hb'ind.mono_right (hsub 4)).symm (hc''W.mono_right hyW).symm
  have hzK : IndepOver (↥K₀) ∅ (range z) (racl k ((K₁ : Set K) ∪ range c'') : Set K) :=
    two_step (hb'ind.mono_right (hsub 5)).symm (hc''W.mono_right hzW).symm
  have hgK : IndepOver (↥K₀) ∅ (g.cb : Set K) (racl k ((K₁ : Set K) ∪ range c'') : Set K) :=
    two_step (indepOver_of_subset_racl (cb_subset_racl_codeTuple g) (subset_racl _ _)
        (hb'ind.mono_right (hsub 1)).symm)
      (indepOver_of_subset_racl (cb_subset_racl_codeTuple_of_le K₀ K₁ h₀₁ g) (subset_racl _ _)
        (hc''W.mono_right hgW).symm)
  have hδK : IndepOver (↥K₀) ∅ (δ.cb : Set K) (racl k ((K₁ : Set K) ∪ range c'') : Set K) :=
    two_step hδb'
      (indepOver_of_subset_racl (cb_subset_racl_codeTuple_of_le K₀ K₁ h₀₁ δ) (subset_racl _ _)
        (hc''W.mono_right hδW).symm)
  have hσ₂b' : ⇑σ₂₀ '' range b' = range b' := by
    rw [← range_comp, hσ₂₀]
    congr 1
    funext i
    change σ₂ (b' i) = b' i
    exact σ₂.commutes ⟨b' i, hb'K₁ (mem_range_self i)⟩
  have hg''b' : IndepOver (↥K₀) ∅ (g''.cb : Set K) (range b') := by
    have h := hδb'.image σ₂₀
    rwa [image_empty, hσ₂b', ← AlgEquiv.coe_toAlgHom, ← coe_map, ← cb_map, ← hg''] at h
  have hg''K : IndepOver (↥K₀) ∅ (g''.cb : Set K) (racl k ((K₁ : Set K) ∪ range c'') : Set K) :=
    two_step hg''b'
      (indepOver_of_subset_racl (cb_subset_racl_codeTuple_of_le K₀ K₁ h₀₁ g'')
        (subset_racl _ _) hc₁σ.indepOver_bc)
  have hptsK : IndepOver (↥K₀) ∅
      (range a ∪ range g.codeTuple ∪ range c ∪ range x ∪ range y ∪ range z ∪ W)
      (racl k ((K₁ : Set K) ∪ range c'') : Set K) :=
    two_step hb'indW.symm (hc''WW.mono_right (union_subset_union_left W hptsW)).symm
  have h₀₂ : K₀ ≤ racl k ((K₁ : Set K) ∪ range c'') :=
    fun w hw ↦ subset_racl k _ (Or.inl (h₀₁ hw))
  have lift₂ : ∀ {A B : Set K}, racl (↥K₁) A = racl (↥K₁) B →
      racl (↥(racl k ((K₁ : Set K) ∪ range c''))) A =
        racl (↥(racl k ((K₁ : Set K) ∪ range c''))) B :=
    fun h ↦ racl_eq_of_racl_eq K₁ _ h
  refine ⟨range b' ∪ range c'', (finite_range b').union (finite_range c''), hSrank, ?_, ?_⟩
  · refine hptsK.symm.mono_left (union_subset ?_ fun w hw ↦ subset_racl k _ (Or.inr hw))
    exact hb'K₁.trans fun w hw ↦ subset_racl k _ (Or.inl hw)
  rw [← hK₂eq (range c'')]
  revert hra hrx hc₂ hyK hzK hgK hδK hg''K lift₂
  generalize hK₂ : racl k ((K₁ : Set K) ∪ range c'') = K₂ at hK₂s i₂ u₂ h₀₂ ⊢
  intro hra hrx hc₂ hyK hzK hgK hδK hg''K lift₂
  /- Step III.3, over `K₂`: base change of the germs. -/
  have hK₂₀ : IsSmall (↥K₀) (K₂ : Set K) := isSmall_coe_of_isSmall K₀ hK₂s
  obtain ⟨F₀, hF₀⟩ : ∃ f : Germ (↥K₂) y z, f = g.baseChange K₀ K₂ h₀₂ hK₂₀ hyK hzK := ⟨_, rfl⟩
  obtain ⟨Gb, hGb⟩ : ∃ f : Germ (↥K₂) y y, f = δ.baseChange K₀ K₂ h₀₂ hK₂₀ hyK hyK := ⟨_, rfl⟩
  obtain ⟨Ga, hGa⟩ : ∃ f : Germ (↥K₂) y y, f = g''.baseChange K₀ K₂ h₀₂ hK₂₀ hyK hyK :=
    ⟨_, rfl⟩
  have hF₀b : IsHWBij F₀ := by
    rw [hF₀]
    exact IsHWBij.baseChange K₀ K₂ h₀₂ hK₂₀ hyK hzK hg hgK
  have hGbmem : Gb ∈ diffSet F₀ := by
    rw [hF₀, hGb]
    exact baseChange_mem_diffSet K₀ K₂ h₀₂ hK₂₀ hyK hzK hgK hδmem hδK
  have hGamem : Ga ∈ diffSet F₀ := by
    rw [hF₀, hGa]
    exact baseChange_mem_diffSet K₀ K₂ h₀₂ hK₂₀ hyK hzK hgK hg''mem hg''K
  have hcodeA : racl (↥K₂) (range Ga.codeTuple) = racl (↥K₂) (range g''.codeTuple) := by
    rw [hGa]
    exact racl_codeTuple_baseChange K₀ K₂ h₀₂ hK₂₀ hyK hyK g''
  have hcodeB : racl (↥K₂) (range Gb.codeTuple) = racl (↥K₂) (range δ.codeTuple) := by
    rw [hGb]
    exact racl_codeTuple_baseChange K₀ K₂ h₀₂ hK₂₀ hyK hyK δ
  have hc₃ : GroupConfiguration (↥K₂) Ga.codeTuple Gb.codeTuple c z'' y y₁ :=
    hc₂.ofRaclEq hcodeA hcodeB rfl rfl rfl rfl
  have hyGa : IndepOver (↥K₂) ∅ (range y) (Ga.cb : Set K) :=
    indepOver_of_subset_racl (subset_racl _ _) (cb_subset_racl_codeTuple Ga)
      hc₃.indepOver_ay.symm
  have hyGb : IndepOver (↥K₂) ∅ (range y) (Gb.cb : Set K) :=
    indepOver_of_subset_racl (subset_racl _ _) (cb_subset_racl_codeTuple Gb)
      hc₃.indepOver_by.symm
  have hGay : Ga.evalGen y = z'' := by
    have h := evalGen_baseChange K₀ K₂ h₀₂ hK₂₀ hyK hyK g'' (rfl : IsGen (↥K₂) y y)
      (by rw [← hGa]; exact hyGa)
    rw [← hGa, hg''y] at h
    exact h
  have hGby : Gb.evalGen y = y₁ := by
    have h := evalGen_baseChange K₀ K₂ h₀₂ hK₂₀ hyK hyK δ (rfl : IsGen (↥K₂) y y)
      (by rw [← hGb]; exact hyGb)
    rw [← hGb, hδy] at h
    exact h
  have hc₄ : GroupConfiguration (↥K₂) Ga.codeTuple Gb.codeTuple c (Ga.evalGen y) y
      (Gb.evalGen y) := by
    rw [hGay, hGby]
    exact hc₃
  /- `prop:converse` for `g_a = Ga`, `g_b = Gb`. -/
  have hw := hF₀b.isHW hGbmem
  have hGaorb : Ga ∈ orbit Gb := by
    rw [← diffSet_eq_orbit hGbmem]
    exact hGamem
  obtain ⟨Ga', hGa'⟩ := isUnit_iff.1 (hw.isUnit_of_mem hGaorb)
  have ht : IndepTriple (↥K₂) (range Ga.codeTuple) (range Gb.codeTuple) (range y) :=
    hc₄.indep 0 1 4 (by decide) (by decide) (by decide) (by decide)
  have hind₃ : IndepTriple (↥K₂) (Ga.cb : Set K) (Gb.cb : Set K) (range y) :=
    indepTriple_of_racl_eq (racl_codeTuple Ga) (racl_codeTuple Gb) rfl ht
  obtain ⟨hconv, hGcx, hGcGa⟩ := hw.groupConfiguration hGaorb (self_mem_orbit Gb)
    (rfl : IsGen (↥K₂) y y) hind₃ hc₄.one_le_erk_y hGa'
  have hGa'mem : Ga' ∈ diffSet F₀ := inv_mem_diffSet hF₀b.isInvertible hGamem hGa'
  have hGbGa' : IndepOver (↥K₂) ∅ (Gb.cb : Set K) (Ga'.cb : Set K) := by
    refine indepOver_of_subset_racl (cb_subset_racl_codeTuple Gb) ?_ hc₄.indepOver_ab.symm
    rw [racl_codeTuple]
    exact SetLike.coe_subset_coe.2 hGa'.cb_le
  have hGcmem : Gb * Ga' ∈ diffSet F₀ := hF₀b.mul_mem_diffSet hGbmem hGa'mem hGbGa'
  /- Interalgebraicity with the given tuples. -/
  have lift₀₂ : ∀ {A B : Set K}, racl (↥K₀) A = racl (↥K₀) B → racl (↥K₂) A = racl (↥K₂) B :=
    fun h ↦ lift₂ (lift₁ h)
  have hfa : racl (↥K₂) (range a₀) = racl (↥K₂) (range Ga.codeTuple) :=
    (lift₀₂ ha₀).trans (hra.symm.trans hcodeA.symm)
  have hfb : racl (↥K₂) (range b₀) = racl (↥K₂) (range Gb.codeTuple) :=
    (lift₀₂ hb₀).trans ((lift₂ hracl_b.symm).trans hcodeB.symm)
  have hfc : racl (↥K₂) (range c₀) = racl (↥K₂) (range (Gb * Ga').codeTuple) :=
    (lift₀₂ hc₀).trans (hc₄.racl_range_c_eq hconv)
  have hfx : racl (↥K₂) (range x₀) = racl (↥K₂) (range (Ga.evalGen y)) := by
    rw [hGay]
    exact (lift₀₂ hx₀).trans hrx.symm
  have hfz : racl (↥K₂) (range z₀) = racl (↥K₂) (range (Gb.evalGen y)) := by
    rw [hGby]
    exact (lift₀₂ hz₀).trans (lift₂ hracl_z.symm)
  /- Ranks. -/
  have hbase : ∀ {X : Set K}, X.Finite → IndepOver (↥K₀) ∅ X (K₂ : Set K) →
      erk (↥K₂) ∅ X = erk (↥K₀) ∅ X := fun hX h ↦ by
    rw [erk_base_le K₀ K₂ h₀₂, ← empty_union (K₂ : Set K)]
    exact h (subset_refl _) hX
  have hrkx : erk (↥K₂) ∅ (range (Ga.evalGen y)) = erk (↥K₂) ∅ (range x₀) :=
    (erk_eq_of_racl_eq hfx).symm
  have hrky : erk (↥K₂) ∅ (range y) = erk (↥K₂) ∅ (range x₀) := hc₄.erk_y_eq.trans hrkx
  have hrkz : erk (↥K₂) ∅ (range z) = erk (↥K₂) ∅ (range x₀) := by
    rw [← hrky, hbase (finite_range z) hzK, hbase (finite_range y) hyK, hc.erk_z_eq, hc.erk_y_eq]
  have hrkf : erk (↥K₂) ∅ (F₀.cb : Set K) = erk (↥K₂) ∅ (range a₀) :=
    (hF₀b.rank Ga hGamem).symm.trans ((erk_eq_of_racl_eq (racl_codeTuple Ga).symm).trans
      (erk_eq_of_racl_eq hfa).symm)
  unfold IsMainConclusion
  exact ⟨i₂, u₂, ι₅, ι₆, inferInstance, inferInstance, y, z, F₀, Ga, Gb, Gb * Ga', y, hF₀b,
    hGamem, hGbmem, hGcmem, hGcGa.symm, rfl, hind₃, hGcx, hconv, hfa, hfb, hfc, hfx,
    lift₀₂ hy₀, hfz, hrky, hrkz, hrkf⟩

omit [IsAlgClosed k] in
/-- Step III retaining the total rank of its two actual generic copies.
Named consumer: `GroupConfiguration.exists_stepIII`. -/
theorem exists_stepIII_with_parameterRank (K₀ : IntermediateField k K) [IsAlgClosed (↥K₀)]
    [UniversalDomain (↥K₀) K] (hK₀ : IsSmall k (K₀ : Set K)) {g : Germ (↥K₀) y z}
    (hc : GroupConfiguration (↥K₀) a g.codeTuple c x y z) (hg : IsHWBij g)
    (hgz : g.evalGen y = z) {μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : Type*} {a₀ : μ₁ → K} {b₀ : μ₂ → K}
    {c₀ : μ₃ → K} {x₀ : μ₄ → K} {y₀ : μ₅ → K} {z₀ : μ₆ → K}
    (ha₀ : racl (↥K₀) (range a₀) = racl (↥K₀) (range a))
    (hb₀ : racl (↥K₀) (range b₀) = racl (↥K₀) (range g.codeTuple))
    (hc₀ : racl (↥K₀) (range c₀) = racl (↥K₀) (range c))
    (hx₀ : racl (↥K₀) (range x₀) = racl (↥K₀) (range x))
    (hy₀ : racl (↥K₀) (range y₀) = racl (↥K₀) (range y))
    (hz₀ : racl (↥K₀) (range z₀) = racl (↥K₀) (range z)) :
    ∃ S : Set K, S.Finite ∧ erk (↥K₀) ∅ S = 2 * erk (↥K₀) ∅ (range a) ∧
      IndepOver (↥K₀) ∅ S (range a ∪ range g.codeTuple ∪ range c ∪ range x ∪ range y ∪ range z) ∧
      IsMainConclusion k (racl k ((K₀ : Set K) ∪ S)) a₀ b₀ c₀ x₀ y₀ z₀ := by
  obtain ⟨S, hSfin, hSrank, hS, h⟩ := exists_stepIII_fresh_with_parameterRank K₀ hK₀ hc hg hgz
    finite_empty ha₀ hb₀ hc₀ hx₀ hy₀ hz₀
  rw [union_empty] at hS
  exact ⟨S, hSfin, hSrank, hS, h⟩

omit [IsAlgClosed k] in
/-- Step III of `thm:main`. Let `(a, code g, c, x, y, z)` be a configuration over `K₀` whose
second point is the code of a Hrushovski–Weil datum of bijections `g` with `g(y) = z`. Then
there is a finite set `S`, independent over `K₀` from the configuration, such that over
`acl(K₀, S)` the conclusion of `thm:main` holds for every tuple interalgebraic over `K₀` with
the configuration. -/
theorem exists_stepIII (K₀ : IntermediateField k K) [IsAlgClosed (↥K₀)]
    [UniversalDomain (↥K₀) K] (hK₀ : IsSmall k (K₀ : Set K)) {g : Germ (↥K₀) y z}
    (hc : GroupConfiguration (↥K₀) a g.codeTuple c x y z) (hg : IsHWBij g)
    (hgz : g.evalGen y = z) {μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : Type*} {a₀ : μ₁ → K} {b₀ : μ₂ → K}
    {c₀ : μ₃ → K} {x₀ : μ₄ → K} {y₀ : μ₅ → K} {z₀ : μ₆ → K}
    (ha₀ : racl (↥K₀) (range a₀) = racl (↥K₀) (range a))
    (hb₀ : racl (↥K₀) (range b₀) = racl (↥K₀) (range g.codeTuple))
    (hc₀ : racl (↥K₀) (range c₀) = racl (↥K₀) (range c))
    (hx₀ : racl (↥K₀) (range x₀) = racl (↥K₀) (range x))
    (hy₀ : racl (↥K₀) (range y₀) = racl (↥K₀) (range y))
    (hz₀ : racl (↥K₀) (range z₀) = racl (↥K₀) (range z)) :
    ∃ S : Set K, S.Finite ∧
      IndepOver (↥K₀) ∅ S (range a ∪ range g.codeTuple ∪ range c ∪ range x ∪ range y ∪ range z) ∧
      IsMainConclusion k (racl k ((K₀ : Set K) ∪ S)) a₀ b₀ c₀ x₀ y₀ z₀ := by
  obtain ⟨S, hSfin, -, h⟩ := exists_stepIII_with_parameterRank K₀ hK₀ hc hg hgz
    ha₀ hb₀ hc₀ hx₀ hy₀ hz₀
  exact ⟨S, hSfin, h⟩

end StepIII

variable {ι₁ ι₂ ι₃ ι₄ ι₅ ι₆ : Type*} [Finite ι₁] [Finite ι₂] [Finite ι₃] [Finite ι₄]
  [Finite ι₅] [Finite ι₆] {a : ι₁ → K} {b : ι₂ → K} {c : ι₃ → K} {x : ι₄ → K} {y : ι₅ → K}
  {z : ι₆ → K}

/-- `rem:params`: the actual five-copy construction of the group configuration theorem.
The finite independent parameter set has rank five times the original group-point rank, and it
is independent from a prescribed finite set `W` as well as from the configuration. Named
consumers: `GroupConfiguration.exists_main_with_parameterRank`,
`AclGeom.QWitness.PsiCore.exists_isMainConclusion_fresh` and
`AclGeom.QWitness.Psi.exists_rankOne_isMainConclusion_fresh`. -/
theorem exists_main_fresh_with_parameterRank (hc : GroupConfiguration k a b c x y z) {W : Set K}
    (hW : W.Finite) :
    ∃ E : Set K, E.Finite ∧ erk k ∅ E = 5 * erk k ∅ (range a) ∧
      IndepOver k ∅ E (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z ∪ W) ∧
      IsMainConclusion k (racl k E) a b c x y z := by
  obtain ⟨E, hEfin, hErank, hEind, κ₁, κ₂, κ₃, κ₄, κ₅, κ₆, _, _, _, _, _, _, a₁, b₁, c₁, x₁, y₁, z₁,
    hc₁, ha₁, hb₁, hc₁', hx₁, hy₁, hz₁, hzdcl, hydcl⟩ :=
    hc.exists_stepI_fresh_with_parameterRank hW
  have hEs : IsSmall k ((racl k E : IntermediateField k K) : Set K) :=
    (IsSmall.of_finite hEfin).racl
  have _ : IsAlgClosed ↥(racl k E) := isAlgClosed_racl _
  have _ : UniversalDomain ↥(racl k E) K := universalDomain_of_isSmall _ hEs
  obtain ⟨g, hg, hgz, hc₂, hgb⟩ := hc₁.exists_isHWBij hzdcl hydcl
  have ha₀ := racl_racl_base_eq ha₁.symm
  have hb₀ : racl (↥(racl k E)) (range b) = racl (↥(racl k E)) (range g.codeTuple) :=
    (racl_racl_base_eq hb₁.symm).trans hgb.symm
  have hc₀ := racl_racl_base_eq hc₁'.symm
  have hx₀ := racl_racl_base_eq hx₁.symm
  have hy₀ := racl_racl_base_eq hy₁.symm
  have hz₀ := racl_racl_base_eq hz₁.symm
  obtain ⟨S, hSfin, hSrank, hSind, hmain⟩ :=
    exists_stepIII_fresh_with_parameterRank (racl k E) hEs hc₂ hg hgz hW ha₀ hb₀ hc₀ hx₀ hy₀ hz₀
  have harank : erk (↥(racl k E)) ∅ (range a₁) = erk k ∅ (range a) := by
    rw [← erk_eq_of_racl_eq ha₀, erk_base_empty, erk_racl_base]
    simpa only [empty_union] using hEind.symm.erk_eq
      (fun _ h ↦ Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))) (finite_range a)
  have hSrank' : erk k E S = 2 * erk k ∅ (range a) := by
    rw [← erk_racl_base k E S, ← erk_base_empty (racl k E)]
    simpa only [harank] using hSrank
  have hrank : erk k ∅ (E ∪ S) = 5 * erk k ∅ (range a) := by
    rw [erk_union_eq, empty_union, hErank, hSrank']
    ring
  refine ⟨E ∪ S, hEfin.union hSfin, hrank, ?_, ?_⟩
  · have hpts : racl (↥(racl k E))
        (range a₁ ∪ range g.codeTuple ∪ range c₁ ∪ range x₁ ∪ range y₁ ∪ range z₁ ∪ W) =
        racl (↥(racl k E)) (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z ∪ W) :=
      racl_union_congr (racl_union_congr (racl_union_congr (racl_union_congr (racl_union_congr
        (racl_union_congr ha₀.symm hb₀.symm) hc₀.symm) hx₀.symm) hy₀.symm) hz₀.symm) rfl
    have h1 : IndepOver (↥(racl k E)) ∅ S
        (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z ∪ W) :=
      (indepOver_congr₀ rfl hpts).1 hSind
    have h2 : IndepOver k E S
        (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z ∪ W) :=
      (indepOver_racl_base_iff E _ _).1 ((indepOver_base_iff (racl k E) _ _).1 h1)
    have h3 : IndepOver k ∅ (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z ∪ W)
        (E ∪ S) :=
      indepOver_union_right_iff.2 ⟨hEind.symm, by rw [empty_union]; exact h2.symm⟩
    exact h3.symm
  · rw [← racl_union_left E S]
    exact hmain

/-- `rem:params`: the actual five-copy construction of the group configuration theorem.
The finite independent parameter set has rank five times the original group-point rank. Named
consumer: `GroupConfiguration.exists_main`. -/
theorem exists_main_with_parameterRank (hc : GroupConfiguration k a b c x y z) :
    ∃ E : Set K, E.Finite ∧ erk k ∅ E = 5 * erk k ∅ (range a) ∧
      IndepOver k ∅ E (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z) ∧
      IsMainConclusion k (racl k E) a b c x y z := by
  obtain ⟨E, hEfin, hErank, hEind, h⟩ := hc.exists_main_fresh_with_parameterRank finite_empty
  rw [union_empty] at hEind
  exact ⟨E, hEfin, hErank, hEind, h⟩

/-- `thm:main`, the group configuration theorem for algebraically closed fields: a group
configuration over `k` is realized, after adjoining a finite set `E` independent from it, by the
standard configuration of a Hrushovski–Weil datum of bijections over `acl(k, E)`
(`IsMainConclusion`). The identities in the homogeneous space follow from
`Germ.IsHWBij.iota_eq_smul`. -/
theorem exists_main (hc : GroupConfiguration k a b c x y z) :
    ∃ E : Set K, E.Finite ∧
      IndepOver k ∅ E (range a ∪ range b ∪ range c ∪ range x ∪ range y ∪ range z) ∧
      IsMainConclusion k (racl k E) a b c x y z := by
  obtain ⟨E, hEfin, -, h⟩ := hc.exists_main_with_parameterRank
  exact ⟨E, hEfin, h⟩

end GroupConfiguration

end

end GroupConfig
