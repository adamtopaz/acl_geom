/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Psi
import GroupConfig.Constructible.CanonicalPresentation
import GroupConfig.Germ.RelativeRank

/-!
# The constructible group and curve of the Ψ witness

Blueprint `sources/group_configuration/11-application.tex`, `cor:psi`, including its
constructibility clause: `prop:psi-gc`, `thm:main` and `thm:constructible` applied to an actual
Ψ witness.

`QWitness.PsiCore.exists_constructibleGroupSpace` starts from the witness alone. The group
configuration theorem (`QWitness.PsiCore.exists_isMainConclusion`) gives a finite set `E`
independent from the witness. Over `k' = acl(k, E)` it gives the actual Hrushovski–Weil datum of
bijections `f₀` between curves, the difference germs `g_a`, `g_b`, `g_c` and a generic point `y'`
realizing the six points up to interalgebraicity. The group `G` is the actual group
`(hb.isHW hga).prodSubgroup` of `f₀`, with group rank two and space rank one.

A generic point `y₀` of the curve over `acl(k', abcxyz)` is chosen. The canonical producer
`Germ.IsHWBij.exists_fresh_canonicalGroupSpacePresentation`, applied with the small field
`acl(k', abcxyz, y₀)`, then chooses the actual family on the canonical code and two stages of
fresh generic samples `t = (t₀, t₁)` independent from that field. Over `k'' = k'(t)` the pair
domain presents `G` as a constructible group. For every generic point, in particular `y₀`, the
stabiliser of `ι(y₀)` is constructible and the homogeneous space is a constructible `G`-set over
`k''(y₀)`. The parameters `(e, t)` are independent from the witness over the original base `k`.
Over the final base `acl(k'')`, `G` has rank two and is connected in the sense of
`rem:constr-connected`:

* every element has rank at most two;
* the elements of rank two are the generic ones independent from the base;
* every element is a product of two of them;
* any two of them are conjugate by an automorphism over the base.

The remaining structure of the source statement holds for the same actual objects:

* `S ≅ G/H` (`GroupConfig.Germ.IsHW.quotientStabilizerEquiv`, equivariant by
  `GroupConfig.Germ.IsHW.quotientStabilizerEquiv_smul`);
* faithfulness (`GroupConfig.Germ.IsHW.eq_one_of_forall_smul_eq`);
* transitivity (`GroupConfig.Germ.IsHW.exists_smul_eq`);
* `V_gen ⊆ S` (`GroupConfig.Germ.IsHW.iota_injective`).

This is a statement over the ACF universal domain. It does not algebraize the constructible
group, classify the action, or descend `e`, `t` or the chart to the original fields
(`rem:remaining`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `cor:psi` is complete, including its constructibility clause.
-/

namespace AclGeom

open GroupConfig Germ IntermediateField Set

universe u

variable {k : Type*} {K : Type u} [Field k] [Field K] [Algebra k K]

namespace QWitness

variable {w : QWitness k K}

/-- `cor:psi`: for a Ψ witness in an algebraically closed universal domain over an algebraically
closed base, there is a finite set `E` independent from the witness such that, over
`k' = acl(k, E)`, the conclusion of the group configuration theorem holds for an actual
Hrushovski–Weil datum of bijections `f₀` between curves, with group rank two and space rank one.
Moreover, for an actual generic point `y₀` of the curve over `acl(k', abcxyz)`, there are fresh
generic samples `t = (S₀, t₁)` independent from `acl(k', abcxyz, y₀)` such that:

* `(E, t)` is independent from the witness over `k`;
* over the final base `acl(k'(t))`, the group `G` of `f₀` has rank two and is connected
  (`rem:constr-connected`);
* `G` is a constructible group over `k'(t)`, presented by the pair domain of the canonical code;
* for every generic point, in particular `y₀`, the stabiliser of `ι(y₀)` is constructible and the
  homogeneous space is a constructible `G`-set over `k'(t, y₀)`. -/
theorem PsiCore.exists_constructibleGroupSpace [IsAlgClosed k] [IsAlgClosed K]
    [UniversalDomain k K] (hw : w.PsiCore) :
    ∃ E : Set K, E.Finite ∧
      IndepOver k ∅ E (range w.aTuple ∪ range w.bTuple ∪ range w.cTuple ∪ range w.xTuple ∪
        range w.yTuple ∪ range w.zTuple) ∧
      ∃ (_ : IsAlgClosed ↥(racl k E)) (_ : UniversalDomain (↥(racl k E)) K) (ν ν' : Type u)
        (_ : Fintype ν) (_ : Finite ν') (v : ν → K) (v' : ν' → K)
        (f₀ : Germ (↥(racl k E)) v v') (ga gb gc : Germ (↥(racl k E)) v v) (y' : ν → K)
        (hb : f₀.IsHWBij) (hga : ga ∈ f₀.diffSet)
        (_ : Fintype (CodeIndex (ν ⊕ ν') (genDeg f₀.graphIdeal))),
        gb ∈ f₀.diffSet ∧ gc ∈ f₀.diffSet ∧ gb = gc * ga ∧
        IsGen (↥(racl k E)) v y' ∧
        IndepTriple (↥(racl k E)) (ga.cb : Set K) (gb.cb : Set K) (range y') ∧
        gc.evalGen (ga.evalGen y') = gb.evalGen y' ∧
        GroupConfiguration (↥(racl k E)) ga.codeTuple gb.codeTuple gc.codeTuple (ga.evalGen y')
          y' (gb.evalGen y') ∧
        racl (↥(racl k E)) (range w.aTuple) = racl (↥(racl k E)) (range ga.codeTuple) ∧
        racl (↥(racl k E)) (range w.bTuple) = racl (↥(racl k E)) (range gb.codeTuple) ∧
        racl (↥(racl k E)) (range w.cTuple) = racl (↥(racl k E)) (range gc.codeTuple) ∧
        racl (↥(racl k E)) (range w.xTuple) = racl (↥(racl k E)) (range (ga.evalGen y')) ∧
        racl (↥(racl k E)) (range w.yTuple) = racl (↥(racl k E)) (range y') ∧
        racl (↥(racl k E)) (range w.zTuple) = racl (↥(racl k E)) (range (gb.evalGen y')) ∧
        erk (↥(racl k E)) ∅ (range v) = erk (↥(racl k E)) ∅ (range w.xTuple) ∧
        erk (↥(racl k E)) ∅ (range v') = erk (↥(racl k E)) ∅ (range w.xTuple) ∧
        erk (↥(racl k E)) ∅ (f₀.cb : Set K) = erk (↥(racl k E)) ∅ (range w.aTuple) ∧
        erk (↥(racl k E)) ∅ (range w.aTuple) = 2 ∧ erk (↥(racl k E)) ∅ (range w.xTuple) = 1 ∧
        ∃ y₀ : ν → K, IsGenericOver (racl (↥(racl k E)) (range w.aTuple ∪ range w.bTuple ∪
            range w.cTuple ∪ range w.xTuple ∪ range w.yTuple ∪ range w.zTuple)) v y₀ ∧
          ∃ (F : QuasiRational (↥(racl k E)) (CodeIndex (ν ⊕ ν') (genDeg f₀.graphIdeal) ⊕ ν) ν')
            (hF : ∀ σ : K ≃ₐ[↥(racl k E)] K, ∃ hu : F.IsAdmissible v v' (⇑σ ∘ f₀.code),
              F.parameterGerm hu = f₀.map σ)
            (hdim : erk (↥(racl k E)) ∅ (range v) = erk (↥(racl k E)) ∅ (range v'))
            (S₀ : Set K)
            (t₁ : Fin (2 * (6 * Fintype.card (CodeIndex (ν ⊕ ν') (genDeg f₀.graphIdeal)) +
              Fintype.card ν) + 1) → CodeIndex (ν ⊕ ν') (genDeg f₀.graphIdeal) → K),
            IndepOver k ∅ (E ∪ (S₀ ∪ ⋃ i, range (t₁ i))) (range w.aTuple ∪ range w.bTuple ∪
              range w.cTuple ∪ range w.xTuple ∪ range w.yTuple ∪ range w.zTuple) ∧
            (∀ γ ∈ IsHW.prodSet ga, erk (↥(racl k E)) (racl (↥(racl k E))
              ((adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i)) :
                IntermediateField (↥(racl k E)) K) : Set K) : Set K) (γ.cb : Set K) ≤ 2) ∧
            (∀ γ ∈ IsHW.prodSet ga, erk (↥(racl k E)) (racl (↥(racl k E))
              ((adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i)) :
                IntermediateField (↥(racl k E)) K) : Set K) : Set K) (γ.cb : Set K) = 2 ↔
              γ ∈ orbit ga ∧ IndepOver (↥(racl k E)) ∅ (γ.cb : Set K) (racl (↥(racl k E))
                ((adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i)) :
                  IntermediateField (↥(racl k E)) K) : Set K) : Set K)) ∧
            (∀ γ ∈ IsHW.prodSet ga, ∃ γ₁ ∈ IsHW.prodSet ga, ∃ γ₂ ∈ IsHW.prodSet ga, γ = γ₁ * γ₂ ∧
              erk (↥(racl k E)) (racl (↥(racl k E))
                ((adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i)) :
                  IntermediateField (↥(racl k E)) K) : Set K) : Set K) (γ₁.cb : Set K) = 2 ∧
              erk (↥(racl k E)) (racl (↥(racl k E))
                ((adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i)) :
                  IntermediateField (↥(racl k E)) K) : Set K) : Set K) (γ₂.cb : Set K) = 2) ∧
            (∀ γ ∈ IsHW.prodSet ga, ∀ γ' ∈ IsHW.prodSet ga,
              erk (↥(racl k E)) (racl (↥(racl k E))
                ((adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i)) :
                  IntermediateField (↥(racl k E)) K) : Set K) : Set K) (γ.cb : Set K) = 2 →
              erk (↥(racl k E)) (racl (↥(racl k E))
                ((adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i)) :
                  IntermediateField (↥(racl k E)) K) : Set K) : Set K) (γ'.cb : Set K) = 2 →
              ∃ σ : K ≃ₐ[↥(racl (↥(racl k E))
                ((adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i)) :
                  IntermediateField (↥(racl k E)) K) : Set K))] K,
                γ.map (σ.restrictScalars (↥(racl k E))) = γ') ∧
            S₀.Finite ∧
            IndepOver (↥(racl k E)) ∅ S₀ (racl (↥(racl k E)) (range w.aTuple ∪ range w.bTuple ∪
              range w.cTuple ∪ range w.xTuple ∪ range w.yTuple ∪ range w.zTuple ∪ range y₀) :
                Set K) ∧
            (∃ T : List (Σ τ : Type u, (τ → K) × (τ → K)),
              (∀ p ∈ T, ((⟨p.1, p.2.1⟩ : Σ τ : Type u, τ → K) = ⟨ν, v⟩ ∨
                  (⟨p.1, p.2.1⟩ : Σ τ : Type u, τ → K) = ⟨ν', v'⟩) ∧
                IsGenericOver (⊥ : IntermediateField (↥(racl k E)) K) p.2.1 p.2.2) ∧
              S₀ = (⋃ p ∈ T, range p.2.2) ∧
              erk (↥(racl k E)) ∅ S₀ = (T.map fun p ↦ erk (↥(racl k E)) ∅ (range p.2.2)).sum) ∧
            HasGenericSamples (adjoin (↥(racl k E)) S₀) v
              (8 * Fintype.card (CodeIndex (ν ⊕ ν') (genDeg f₀.graphIdeal))) ∧
            HasGenericSamples (adjoin (↥(racl k E)) S₀) v'
              (Fintype.card (CodeIndex (ν ⊕ ν') (genDeg f₀.graphIdeal))) ∧
            (∀ i, IsGenericOver (⊥ : IntermediateField (↥(racl k E)) K) f₀.code (t₁ i)) ∧
            (∀ i, IsGenericOver (adjoin (↥(racl k E)) S₀) f₀.code (t₁ i)) ∧
            erk (↥(racl k E)) (adjoin (↥(racl k E)) S₀ : Set K) (⋃ i, range (t₁ i)) =
              ∑ i, erk (↥(racl k E)) (adjoin (↥(racl k E)) S₀ : Set K) (range (t₁ i)) ∧
            IndepOver (↥(racl k E)) ∅ (S₀ ∪ ⋃ i, range (t₁ i)) (racl (↥(racl k E))
              (range w.aTuple ∪ range w.bTuple ∪ range w.cTuple ∪ range w.xTuple ∪
                range w.yTuple ∪ range w.zTuple ∪ range y₀) : Set K) ∧
            erk (↥(racl k E)) ∅ (S₀ ∪ ⋃ i, range (t₁ i)) =
              erk (↥(racl k E)) ∅ S₀ + ∑ i, erk (↥(racl k E)) ∅ (range (t₁ i)) ∧
            ∃ hL : IsSmall (↥(racl k E)) ((adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i)) :
                IntermediateField (↥(racl k E)) K) : Set K),
              ConstructibleGroupPresentation (adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i)))
                (F.pairDomain (adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i))) f₀.code v v')
                (F.pairDomainMap (adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i))) hL hb hga
                  f₀.adjoin_range_code hF hdim) ∧
              ∀ (y₁ : ν → K) (hy₁ : IsGen (↥(racl k E)) v y₁),
                IsConstructibleOver
                  (↥(adjoin (↥(racl k E)) ((S₀ ∪ ⋃ i, range (t₁ i)) ∪ range y₁)))
                  {d | ∃ hd : d ∈ F.pairDomain (adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i)))
                      f₀.code v v',
                    F.pairDomainMap (adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i))) hL hb hga
                        f₀.adjoin_range_code hF hdim ⟨d, hd⟩ • (hb.isHW hga).iota hy₁ =
                      (hb.isHW hga).iota hy₁} ∧
                ConstructibleGSetPresentation
                  (adjoin (↥(racl k E)) ((S₀ ∪ ⋃ i, range (t₁ i)) ∪ range y₁))
                  (F.pairDomain (adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i))) f₀.code v v')
                  (F.pairDomainMap (adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i))) hL hb hga
                    f₀.adjoin_range_code hF hdim)
                  (F.pairDomain (adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i))) f₀.code v v')
                  (F.pairDomainSpaceMap (adjoin (↥(racl k E)) (S₀ ∪ ⋃ i, range (t₁ i))) hL hb
                    hga f₀.adjoin_range_code hF hdim hy₁) := by
  obtain ⟨E, hEfin, hEind, hmain, hra, hrx⟩ := hw.exists_isMainConclusion
  unfold IsMainConclusion at hmain
  obtain ⟨hacl, hud, ν, ν', _, _, v, v', f₀, ga, gb, gc, y', hb, hga, hgb, hgc, hmul, hy', hind,
    heval, hconf, r₁, r₂, r₃, r₄, r₅, r₆, hv, hv', hcb⟩ := hmain
  let : Fintype ν := Fintype.ofFinite ν
  let : Fintype (CodeIndex (ν ⊕ ν') (genDeg f₀.graphIdeal)) := Fintype.ofFinite _
  have hPfin : (range w.aTuple ∪ range w.bTuple ∪ range w.cTuple ∪ range w.xTuple ∪
      range w.yTuple ∪ range w.zTuple).Finite :=
    (((((finite_range _).union (finite_range _)).union (finite_range _)).union
      (finite_range _)).union (finite_range _)).union (finite_range _)
  -- A generic point of the curve over `acl(k', abcxyz)`.
  obtain ⟨y₀, hy₀⟩ := exists_isGenericOver (IsSmall.of_finite (k := ↥(racl k E)) hPfin).racl v
  -- The canonical producer, fresh from `acl(k', abcxyz, y₀)`.
  obtain ⟨F, hF, hdim, S₀, t₁, hS₀, hS₀ind, hT, hs, hs', ht₁, ht₁', htrk, hfresh, hrk, hL,
    hpres⟩ := hb.exists_fresh_canonicalGroupSpacePresentation hga _
      (IsSmall.of_finite (k := ↥(racl k E)) (hPfin.union (finite_range y₀))).racl
  -- The rank of the group is two.
  have hn : erk (↥(racl k E)) ∅ (ga.cb : Set K) = 2 := (hb.rank ga hga).trans (hcb.trans hra)
  have hM := hL.racl
  refine ⟨E, hEfin, hEind, hacl, hud, ν, ν', inferInstance, inferInstance, v, v', f₀, ga, gb, gc,
    y', hb, hga, inferInstance, hgb, hgc, hmul, hy', hind, heval, hconf, r₁, r₂, r₃, r₄, r₅, r₆,
    hv, hv', hcb, hra, hrx, y₀, hy₀, F, hF, hdim, S₀, t₁, ?_, fun γ hγ ↦ ?_, fun γ hγ ↦ ?_,
    fun γ hγ ↦ ?_, fun γ hγ γ' hγ' hr hr' ↦ ?_, hS₀, hS₀ind, hT, hs, hs', ht₁, ht₁', htrk, hfresh,
    hrk, hL, hpres⟩
  · -- `(E, t)` is independent from the witness over `k`.
    have h₁ : IndepOver (↥(racl k E)) ∅ (S₀ ∪ ⋃ i, range (t₁ i))
        (range w.aTuple ∪ range w.bTuple ∪ range w.cTuple ∪ range w.xTuple ∪ range w.yTuple ∪
          range w.zTuple) :=
      hfresh.mono_right (subset_union_left.trans (subset_racl (↥(racl k E)) _))
    have h₂ := (indepOver_racl_base_iff E _ _).1 ((indepOver_base_iff (racl k E) _ _).1 h₁)
    exact (indepOver_union_right_iff.2 ⟨hEind.symm, by rw [empty_union]; exact h₂.symm⟩).symm
  · rw [← hn]
    exact (hb.isHW hga).erk_base_cb_le _ hγ
  · rw [← hn]
    exact (hb.isHW hga).erk_base_cb_eq_iff hγ
  · rw [← hn]
    exact (hb.isHW hga).exists_mul_eq_of_mem_prodSet hM hγ
  · exact (hb.isHW hga).exists_algEquiv_of_erk_base_eq hM hγ hγ' (hr.trans hn.symm)
      (hr'.trans hn.symm)

end QWitness

end AclGeom
