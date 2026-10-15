/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.PsiNonfaithful
import AclGeom.Config.ConfigurationInput
import GroupConfig.CanonicalBaseCounterexample
import GroupConfig.ConfigurationNecessity

/-!
# The nonfaithful product-group witness is not realized

Blueprint `sources/group_configuration/11-application.tex`, `rem:psi-hyp`(b), last clause: no
faithful rank-two action on a curve realizes the product-group witness
`AclGeom.QWitness.Nonfaithful.witness`, because the conclusion of `thm:main` forces the
hypothesis (GC4) for the original tuple.

* For `a = (s, u)`, `x = st`, `y = t`, the locus of `(x, y)` over `acl(s, u)` is the line
  `X = s Y`, with canonical base `k(s)`, which does not contain `u` in its algebraic closure. So
  (GC4) fails for `a` (`AclGeom.QWitness.Nonfaithful.not_cb_a`).
* Hence the tuples of the witness do not form a group configuration
  (`AclGeom.QWitness.Nonfaithful.not_groupConfiguration`).
* Hence no finite set `E` independent from them carries the conclusion of `thm:main` over
  `acl(k, E)` (`AclGeom.QWitness.Nonfaithful.not_exists_isMainConclusion`), by
  `GroupConfig.GroupConfiguration.of_isMainConclusion`.

The statement is about the precise conclusion `GroupConfig.IsMainConclusion` of `thm:main`; it
does not quantify over arbitrary algebraic actions.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the nonrealization clause of `rem:psi-hyp`(b) is complete.
-/

namespace AclGeom

open GroupConfig IntermediateField Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] [UniversalDomain k K]

namespace QWitness

namespace Nonfaithful

omit [IsAlgClosed K] [UniversalDomain k K] in
/-- The closure of the representative of a point is the closure of a generator. -/
private theorem racl_rep {P : Point k K} {x : K} (hP : P.1 = ClosedIF.point k x) :
    racl k ({P.rep} : Set K) = racl k ({x} : Set K) := by
  exact congrArg (fun E : ClosedIF k K ↦ (E.1 : IntermediateField k K))
    ((Point.point_rep P).trans hP)

omit [IsAlgClosed K] [UniversalDomain k K] in
/-- Closures of pairs are joins of closures of their entries. -/
private theorem racl_range_pair (p q : K) :
    racl k (range ![p, q]) = racl k ((racl k ({p} : Set K) : Set K) ∪ racl k ({q} : Set K)) := by
  rw [racl_union_left, racl_union_right]
  congr 1
  ext x
  simp only [mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    mem_union, mem_singleton_iff]
  tauto

variable {s s' t u u' : K} (hind : erk k ∅ ({s, s', t, u, u'} : Set K) = 5)
include hind

omit [IsAlgClosed K] [UniversalDomain k K] in
/-- `rem:psi-hyp`(b): (GC4) fails for `a = (s, u)` with `x = st`, `y = t`: the canonical base
of `(x, y)` over `acl(a)` is `k(s)`. -/
theorem not_cb_a :
    ¬ (range ![s, u] ⊆
      racl k (canonicalBase (racl k (range ![s, u])) (Sum.elim ![s * t] ![t]) : Set K)) := by
  intro h
  have hrange : range ![s, u] = ({s, u} : Set K) := by
    ext x
    simp only [mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      mem_insert_iff, mem_singleton_iff]
    tauto
  have hsL : s ∈ racl k (range ![s, u]) := subset_racl k _ ⟨0, rfl⟩
  have ht : Transcendental (↥(racl k (range ![s, u]))) t := by
    intro halg
    have h1 : t ∈ racl k ((racl k (range ![s, u]) : IntermediateField k K) : Set K) :=
      (mem_racl_iff k).2 (by rw [adjoin_self]; exact halg)
    rw [racl_racl, hrange] at h1
    have hsub : ({s, u} : Set K) ⊆ ({s, u, s', u'} : Set K) := by
      intro x hx
      simp only [mem_insert_iff, mem_singleton_iff] at hx ⊢
      tauto
    exact t_not_mem hind (racl_mono (k := k) hsub h1)
  have hpt : (Sum.elim ![s * t] ![t] : Fin 1 ⊕ Fin 1 → K) =
      ![t, s * t + 0] ∘ ((Equiv.sumComm (Fin 1) (Fin 1)).trans
        (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2)) := by
    rw [add_zero]
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  rw [hpt, canonicalBase_comp_equiv, canonicalBase_affineLine _ hsL (zero_mem _) ht] at h
  have hu : u ∈ racl k ((adjoin k ({s, 0} : Set K) : IntermediateField k K) : Set K) :=
    h ⟨1, rfl⟩
  have hle : adjoin k ({s, 0} : Set K) ≤ racl k ({s} : Set K) := by
    refine adjoin_le_iff.2 ?_
    rintro x (rfl | rfl)
    · exact subset_racl k _ (mem_singleton x)
    · exact zero_mem _
  have hu' := racl_mono (k := k) (SetLike.coe_subset_coe.2 hle) hu
  rw [racl_racl] at hu'
  exact u_not_mem hind hu'

/-- `rem:psi-hyp`(b): the tuples of the product-group witness are not a group configuration. -/
theorem not_groupConfiguration :
    ¬ GroupConfiguration k (witness hind).aTuple (witness hind).bTuple (witness hind).cTuple
      (witness hind).xTuple (witness hind).yTuple (witness hind).zTuple := by
  intro hc
  have hpair {P Q : Point k K} {p q : K} (hP : P.1 = ClosedIF.point k p)
      (hQ : Q.1 = ClosedIF.point k q) :
      racl k (range ![p, q]) = racl k (range ![P.rep, Q.rep]) := by
    rw [racl_range_pair, racl_range_pair, racl_rep hP, racl_rep hQ]
  have hsingle {P : Point k K} {p : K} (hP : P.1 = ClosedIF.point k p) :
      racl k (range ![p]) = racl k (range fun _ : Fin 1 ↦ P.rep) := by
    rw [range_const, racl_rep hP]
    congr 1
    ext x
    simp
  have hc' := hc.ofRaclEq (a' := ![s, u]) (b' := ![s', u']) (c' := ![s' / s, u' / u])
    (x' := ![s * t]) (y' := ![t]) (z' := ![s' * t]) (hpair rfl rfl) (hpair rfl rfl)
    (hpair rfl rfl) (hsingle rfl) (hsingle rfl) (hsingle rfl)
  exact not_cb_a hind hc'.cb_a

/-- `rem:psi-hyp`(b): no finite set `E` independent from the tuples of the product-group witness
carries the conclusion of `thm:main` over `acl(k, E)`; so no faithful rank-two action on a curve
realizes the witness in the sense of `thm:main`. -/
theorem not_exists_isMainConclusion :
    ¬ ∃ E : Set K, E.Finite ∧
      IndepOver k ∅ E (range (witness hind).aTuple ∪ range (witness hind).bTuple ∪
        range (witness hind).cTuple ∪ range (witness hind).xTuple ∪
        range (witness hind).yTuple ∪ range (witness hind).zTuple) ∧
      IsMainConclusion k (racl k E) (witness hind).aTuple (witness hind).bTuple
        (witness hind).cTuple (witness hind).xTuple (witness hind).yTuple (witness hind).zTuple :=
  fun ⟨_, hE, hindE, h⟩ ↦
    not_groupConfiguration hind (GroupConfiguration.of_isMainConclusion hE hindE h)

end Nonfaithful

end QWitness

end

end AclGeom
