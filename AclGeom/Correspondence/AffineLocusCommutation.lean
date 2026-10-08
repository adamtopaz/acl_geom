/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import AclGeom.Correspondence.MultiplierPrimeCurve

/-!
# Commuting affine maps that preserve a curve locus

Let `L` be an intermediate field of `K / k` and let `x` be algebraic over `L(m)`.  Consider two
affine maps `A (M, X) = (λ M, X / λ + ν)` and `B (M, X) = (ρ M, X / ρ + ω)` with coefficients in
`L` that both preserve the `L`-locus of `(m, x)`, and suppose `λ` is transcendental over `k`.

* `affine_locus_commutation_balance`: then `λ (ρ - 1) ν = ρ (λ - 1) ω` in `L`.  When `λ, ρ ≠ 1`
  this says that `A` and `B` have the same centre `λ ν / (λ - 1) = ρ ω / (ρ - 1)`.

The maps `A ∘ B` and `B ∘ A` agree up to a vertical translation by an element `d` of `L`, and
transporting along the equal loci shows that this translation preserves the locus of `(m, x)`.
The locus has finite vertical fibres (`finite_same_fibre_ideals`), conjugation by `A` multiplies
preserving translations by `λ`, and the powers of `λ` are distinct in every characteristic, so
`d = 0`.  Every step is a polynomial-image transfer of vanishing ideals; no group action,
stabilizer or commutator structure is assumed.

The named consumer is the common-centre step for same-colour relocations in the corrected
blueprint Lemma `affine-grid-extraction` (#27, L2).

**Status:** commutation balance proved (#27, B2). Selected same-colour triples and their
common centres in constructed supplied-input families are privately checked. Fresh-input
existence, ambient enlargement/descent, linearity, extraction and guarded completeness remain open.
-/

namespace AclGeom
noncomputable section
open MvPolynomial IntermediateField
variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Transcendence forces distinct powers in every characteristic. -/
private theorem pow_injective_of_transcendental {lam : K} (hlam : Transcendental k lam) :
    Function.Injective fun n : ℕ ↦ lam ^ n := by
  intro n m h
  have he : (Polynomial.X : Polynomial k) ^ n = Polynomial.X ^ m :=
    (transcendental_iff_injective.1 hlam) (by simpa only [map_pow, Polynomial.aeval_X] using h)
  have hd := congrArg Polynomial.natDegree he
  simpa only [Polynomial.natDegree_X_pow] using hd

/-- A finite set stable under multiplication by an element transcendental over `k` has no nonzero
element. The stability is an explicit hypothesis, supplied below by actual conjugation. -/
private theorem finite_stable_under_mul_eq_zero {S : Set K} {lam μ : K}
    (hS : S.Finite) (hlam : Transcendental k lam)
    (hstable : ∀ z ∈ S, z * lam ∈ S) (hμ : μ ∈ S) : μ = 0 := by
  by_contra hμ0
  have hmem : ∀ n : ℕ, μ * lam ^ n ∈ S := by
    intro n
    induction n with
    | zero => simpa only [pow_zero, mul_one] using hμ
    | succ n ih => simpa only [pow_succ, ← mul_assoc] using hstable _ ih
  have hinj : Function.Injective fun n : ℕ ↦ μ * lam ^ n := by
    intro n m h
    exact pow_injective_of_transcendental hlam (mul_left_cancel₀ hμ0 h)
  exact (Set.infinite_range_of_injective hinj) (hS.subset (Set.range_subset_iff.2 hmem))

/-- Actual polynomial-image transport proves conjugation stability of vertical translations;
the affine and translation coefficients belong to the displayed coefficient field. -/
private theorem vertical_translation_conjugation {m x : K} (lam nu mu : k) (hlam : lam ≠ 0)
    (hA : idealOf k ![algebraMap k K lam * m, x / algebraMap k K lam + algebraMap k K nu] =
      idealOf k ![m, x])
    (hT : idealOf k ![m, x + algebraMap k K mu] = idealOf k ![m, x]) :
    idealOf k ![m, x + algebraMap k K (lam * mu)] = idealOf k ![m, x] := by
  let l : K := algebraMap k K lam
  let n : K := algebraMap k K nu
  let u : K := algebraMap k K mu
  have hl : l ≠ 0 := by
    intro h
    exact hlam ((algebraMap k K).injective (h.trans (map_zero _).symm))
  change idealOf k ![l * m, x / l + n] = idealOf k ![m, x] at hA
  change idealOf k ![m, x + u] = idealOf k ![m, x] at hT
  let invA : Fin 2 → MvPolynomial (Fin 2) k :=
    ![C lam⁻¹ * X 0, C lam * (X 1 - C nu)]
  let shift : Fin 2 → MvPolynomial (Fin 2) k := ![X 0, X 1 + C mu]
  have hi (a b : K) :
      (fun j ↦ aeval ![a, b] (invA j)) = ![a / l, l * (b - n)] := by
    funext j
    fin_cases j
    · simp [invA, l, div_eq_mul_inv, mul_comm]
    · simp [invA, l, n]
  have ht (a b : K) : (fun j ↦ aeval ![a, b] (shift j)) = ![a, b + u] := by
    funext j
    fin_cases j <;> simp [shift, u]
  have hc : ![(l * m) / l, l * (x / l + n - n)] = (![m, x] : Fin 2 → K) := by
    funext j
    fin_cases j
    · simp [hl]
    · change l * (x / l + n - n) = x
      rw [add_sub_cancel_right, mul_comm l (x / l), div_mul_cancel₀ x hl]
  have hInv := idealOf_aeval_comp_eq_of_idealOf_eq hA invA
  rw [hi, hi, hc] at hInv
  have hShift := idealOf_aeval_comp_eq_of_idealOf_eq hA shift
  rw [ht, ht] at hShift
  have he := idealOf_aeval_comp_eq_of_idealOf_eq (hShift.trans hT) invA
  rw [hi, hi] at he
  have hcc : ![(l * m) / l, l * (x / l + n + u - n)] =
      (![m, x + l * u] : Fin 2 → K) := by
    funext j
    fin_cases j
    · simp [hl]
    · change l * (x / l + n + u - n) = x + l * u
      have hsum : x / l + n + u - n = x / l + u := by ring
      rw [hsum, mul_add, mul_comm l (x / l), div_mul_cancel₀ x hl]
  rw [hcc] at he
  have hfinal := he.trans hInv.symm
  simpa only [map_mul] using hfinal

/-- Actual finite fibres and actual polynomial conjugation eliminate coefficient-field vertical
translations when a preserving affine scaling is transcendental over the original base. No group
action or conjugation-stability oracle is supplied; the concrete ideal equality is explicit. -/
private theorem no_vertical_translation_of_transcendental_scaling
    {L : IntermediateField k K} {m x : K}
    (hx : x ∈ racl ↥L ({m} : Set K)) (lam nu : ↥L)
    (hLam : Transcendental k (lam : K))
    (hA : idealOf ↥L ![(lam : K) * m, x / (lam : K) + (nu : K)] =
      idealOf ↥L ![m, x]) :
    ∀ mu : ↥L, idealOf ↥L ![m, x + (mu : K)] = idealOf ↥L ![m, x] → mu = 0 := by
  let S : Set K := {z | z ∈ L ∧ idealOf ↥L ![m, x + z] = idealOf ↥L ![m, x]}
  have hfibre : {z : K | idealOf ↥L ![m, z] = idealOf ↥L ![m, x]}.Finite :=
    finite_same_fibre_ideals hx
  have hinj : Function.Injective fun z : K ↦ x + z := fun _ _ h ↦ add_left_cancel h
  have htrans : {z : K | idealOf ↥L ![m, x + z] = idealOf ↥L ![m, x]}.Finite :=
    hfibre.preimage hinj.injOn
  have hS : S.Finite := htrans.subset fun _ hz ↦ hz.2
  have hLam0 : lam ≠ 0 := by
    intro h
    exact hLam.ne_zero (by rw [h]; rfl)
  have hstable : ∀ z ∈ S, z * (lam : K) ∈ S := by
    intro z hz
    refine ⟨mul_mem hz.1 lam.property, ?_⟩
    have h := vertical_translation_conjugation (k := ↥L) (K := K) lam nu ⟨z, hz.1⟩
      hLam0 hA hz.2
    simp only [map_mul, IntermediateField.algebraMap_apply] at h
    rwa [mul_comm (lam : K) z] at h
  intro mu hmu
  have he : (mu : K) = 0 := finite_stable_under_mul_eq_zero hS hLam hstable ⟨mu.property, hmu⟩
  exact Subtype.ext he

/-- **Commutation balance for locus-preserving affine maps** (#27, B2).  Let `x` be algebraic
over `L(m)`, and let the maps `A (M, X) = (λ M, X / λ + ν)` and `B (M, X) = (ρ M, X / ρ + ω)`,
with coefficients in `L`, both preserve the `L`-locus of `(m, x)`.  If `λ` is transcendental over
`k` and `ρ ≠ 0`, then `λ (ρ - 1) ν = ρ (λ - 1) ω`: when `λ, ρ ≠ 1` the two maps have the same
centre. -/
theorem affine_locus_commutation_balance {L : IntermediateField k K} {m x : K}
    (hx : x ∈ racl ↥L ({m} : Set K)) (lam nu rho omega : ↥L)
    (hLam : Transcendental k (lam : K)) (hrho : rho ≠ 0)
    (hA : idealOf ↥L ![(lam : K) * m, x / (lam : K) + (nu : K)] = idealOf ↥L ![m, x])
    (hB : idealOf ↥L ![(rho : K) * m, x / (rho : K) + (omega : K)] = idealOf ↥L ![m, x]) :
    lam * (rho - 1) * nu = rho * (lam - 1) * omega := by
  have hA0 := hA
  let d : ↥L := nu * (1 - rho⁻¹) - omega * (1 - lam⁻¹)
  let l : K := algebraMap ↥L K lam
  let n : K := algebraMap ↥L K nu
  let r : K := algebraMap ↥L K rho
  let w : K := algebraMap ↥L K omega
  let e : K := algebraMap ↥L K d
  have hl : l ≠ 0 := hLam.ne_zero
  have hr : r ≠ 0 := by
    intro h
    exact hrho ((algebraMap ↥L K).injective (h.trans (map_zero _).symm))
  have hlam : lam ≠ 0 := fun h ↦ hl (by simp [l, h])
  change idealOf ↥L ![l * m, x / l + n] = idealOf ↥L ![m, x] at hA
  change idealOf ↥L ![r * m, x / r + w] = idealOf ↥L ![m, x] at hB
  -- The affine maps and the vertical translation as polynomial maps over `L`.
  let mapA : Fin 2 → MvPolynomial (Fin 2) ↥L := ![C lam * X 0, C lam⁻¹ * X 1 + C nu]
  let mapB : Fin 2 → MvPolynomial (Fin 2) ↥L := ![C rho * X 0, C rho⁻¹ * X 1 + C omega]
  let shift : Fin 2 → MvPolynomial (Fin 2) ↥L := ![X 0, X 1 + C d]
  have hmA (a b : K) : (fun j ↦ aeval ![a, b] (mapA j)) = ![l * a, b / l + n] := by
    funext j
    fin_cases j <;> simp [mapA, l, n, div_eq_mul_inv, mul_comm]
  have hmB (a b : K) : (fun j ↦ aeval ![a, b] (mapB j)) = ![r * a, b / r + w] := by
    funext j
    fin_cases j <;> simp [mapB, r, w, div_eq_mul_inv, mul_comm]
  have hsh (a b : K) : (fun j ↦ aeval ![a, b] (shift j)) = ![a, b + e] := by
    funext j
    fin_cases j <;> simp [shift, e]
  -- `A ∘ B` and `B ∘ A` preserve the locus, and differ by the vertical translation `d`.
  have hAB := idealOf_aeval_comp_eq_of_idealOf_eq hB mapA
  rw [hmA, hmA] at hAB
  have hBA := idealOf_aeval_comp_eq_of_idealOf_eq hA mapB
  rw [hmB, hmB] at hBA
  have hcoord : ![r * (l * m), (x / l + n) / r + w + e] =
      (![l * (r * m), (x / r + w) / l + n] : Fin 2 → K) := by
    funext j
    fin_cases j
    · change r * (l * m) = l * (r * m)
      ring
    · change (x / l + n) / r + w + e = (x / r + w) / l + n
      have he : e = n * (1 - r⁻¹) - w * (1 - l⁻¹) := by
        simp [e, d, l, n, r, w]
      rw [he]
      field_simp [hl, hr]
      ring
  have hT := idealOf_aeval_comp_eq_of_idealOf_eq (hBA.trans hB) shift
  rw [hsh, hsh, hcoord] at hT
  -- So the translation by `d` preserves the locus, and hence `d = 0`.
  have hTP : idealOf ↥L ![m, x + (d : K)] = idealOf ↥L ![m, x] := hT.symm.trans (hAB.trans hA)
  have hd : nu * (1 - rho⁻¹) - omega * (1 - lam⁻¹) = 0 :=
    no_vertical_translation_of_transcendental_scaling hx lam nu hLam hA0 d hTP
  have h1 : rho * rho⁻¹ = 1 := mul_inv_cancel₀ hrho
  have h2 : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam
  linear_combination (lam * rho) * hd + (lam * nu) * h1 - (rho * omega) * h2

end
end AclGeom
