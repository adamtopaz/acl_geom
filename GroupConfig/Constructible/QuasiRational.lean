/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import GroupConfig.Constructible.Closure
import GroupConfig.QuasiRational

/-!
# Constructible domains and graphs of quasi-rational expressions

Supplemental `sources/group_configuration/09-constructibility.tex`,
`cor:constructible-closure`: the domain is given by nonvanishing denominators,
and the graph by `w_j^(p^e) Q_j(u) = P_j(u)` together with those inequations.
Finite output coordinates give finite intersections of polynomial conditions.
Input coordinates may be arbitrary. Graph evaluation uses a perfect ambient field;
domain constructibility does not need perfection or algebraic closedness.

Named consumers: the admissible-parameter and germ-word relations of Section 9.
This proves their expression-domain/graph building block, not their full
parameterization or closure under germ words.

**Status:** domains and graphs are constructible over the coefficient field.
No algebraic closedness, smallness or universal-domain hypothesis is used.
Germ-word relations are proved in `GroupConfig.Constructible.AdmissibleWords`,
with fresh fields in `GroupConfig.Constructible.WordSamples`. Group construction
and algebraization remain open.
-/

namespace GroupConfig

open MvPolynomial Set

namespace QuasiRational

variable {L K ι κ : Type*} [Field L] [Field K] [Algebra L K]

/-- A finite-output quasi-rational expression has constructible domain. This is
part of supplemental `cor:constructible-closure`. -/
theorem isConstructibleOver_domain [Finite κ] (f : QuasiRational L ι κ) :
    IsConstructibleOver L {u : ι → K | f.IsDefinedAt u} := by
  have h := IsConstructibleOver.iInter fun j ↦
    IsConstructibleOver.polynomial_ne_zero (K := K) (f.den j)
  convert h using 1
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, IsDefinedAt]

variable [PerfectField K]

-- Sole consumer: isConstructibleOver_graph below.
private theorem eval_eq_iff {f : QuasiRational L ι κ} {u : ι → K}
    (hf : f.IsDefinedAt u) (w : κ → K) :
    f.eval u = w ↔ ∀ j,
      w j ^ (ringExpChar K ^ f.e) * aeval u (f.den j) = aeval u (f.num j) := by
  constructor
  · intro h j
    rw [← congrFun h j, eval_apply, pRoot_pow]
    exact div_mul_cancel₀ _ (hf j)
  · intro h
    funext j
    exact pRoot_eq_of_pow_eq ((eq_div_iff (hf j)).2 (h j))

/-- The graph of a finite-output quasi-rational expression is constructible over
its coefficient field. Its equations are w_j^(p^e) Q_j(u)=P_j(u), with Q_j(u)≠0.
Named consumer: the admissible-parameter and germ-word relations of Section 9. -/
theorem isConstructibleOver_graph [Finite κ] (f : QuasiRational L ι κ) :
    IsConstructibleOver L {z : (ι ⊕ κ) → K |
      f.IsDefinedAt (z ∘ Sum.inl) ∧ f.eval (z ∘ Sum.inl) = z ∘ Sum.inr} := by
  let P (j : κ) : MvPolynomial (ι ⊕ κ) L :=
    X (Sum.inr j) ^ (ringExpChar K ^ f.e) * rename (Sum.inl : ι → ι ⊕ κ) (f.den j) -
      rename (Sum.inl : ι → ι ⊕ κ) (f.num j)
  have hD : IsConstructibleOver L {z : (ι ⊕ κ) → K |
      f.IsDefinedAt (z ∘ Sum.inl)} := by
    have h := IsConstructibleOver.iInter fun j ↦
      IsConstructibleOver.polynomial_ne_zero (K := K) (rename (Sum.inl : ι → ι ⊕ κ) (f.den j))
    convert h using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, IsDefinedAt, aeval_rename]
  have hP := IsConstructibleOver.iInter fun j ↦
    IsConstructibleOver.polynomial_zero (K := K) (P j)
  have h : IsConstructibleOver L {z : (ι ⊕ κ) → K |
      f.IsDefinedAt (z ∘ Sum.inl) ∧ ∀ j,
        z (Sum.inr j) ^ (ringExpChar K ^ f.e) * aeval (z ∘ Sum.inl) (f.den j) =
          aeval (z ∘ Sum.inl) (f.num j)} := by
    convert hD.inter hP using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      P, map_sub, map_mul, map_pow, aeval_X, aeval_rename, sub_eq_zero]
  convert h using 1
  ext z
  simp only [Set.mem_ofPred_eq]
  exact and_congr_right fun hf ↦ eval_eq_iff hf (z ∘ Sum.inr)

end QuasiRational

end GroupConfig
