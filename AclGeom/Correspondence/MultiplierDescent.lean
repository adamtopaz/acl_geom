/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import AclGeom.Correspondence.Specialization
import AclGeom.Closure.Basic

/-!
# Descent of simultaneous multiplication corners

Three nonzero incidence equations are specialized by one algebra homomorphism
fixing the original coordinate field. The chosen parameter avoids the finite
sets that would annihilate an equation. Independence keeps the specialized
products transcendental, so their equations recover the original algebraic
closure incidences.

`mulDiagram_coordinates` consumes this theorem to prove the full original-base
auxiliary table of blueprint Lemma `mul-diagram`.
-/

namespace AclGeom

open MvPolynomial IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A dependent triple has a nonzero polynomial relation over the original
base. Used before any specialization is chosen. -/
private theorem exists_relation_of_mem_racl_pair {t u v : K}
    (hv : v ∈ racl k {t, u}) :
    ∃ P : MvPolynomial (Fin 3) k, P ≠ 0 ∧ aeval ![t, u, v] P = 0 := by
  have hn : ¬AlgebraicIndependent k ![t, u, v] := by
    intro hi
    have hm := AlgebraicIndependent.notMem_racl_image hi
      (S := ({0, 1} : Set (Fin 3))) (i := 2) (by decide)
    apply hm
    simpa [Set.image_insert_eq, Set.image_singleton] using hv
  rw [algebraicIndependent_iff] at hn
  push Not at hn
  obtain ⟨P, hzero, hne⟩ := hn
  exact ⟨P, hne, hzero⟩

/-- A nonzero equation on a pair whose first coordinate is transcendental
puts the second coordinate in its algebraic closure. -/
private theorem mem_racl_of_relation {u v : K} (hu : Transcendental k u)
    {P : MvPolynomial (Fin 2) k} (hP : P ≠ 0) (hz : aeval ![u, v] P = 0) :
    v ∈ racl k {u} := by
  by_contra hv
  have hi : AlgebraicIndependent k ![u, v] := by
    have hsingle : AlgebraicIndependent k ![u] := algebraicIndependent_unique_type_iff.mpr hu
    have hn : v ∉ racl k (Set.range (![u] : Fin 1 → K)) := by simpa using hv
    convert algebraicIndependent_snoc hsingle hn using 1
    ext i
    fin_cases i <;> rfl
  exact hP (hi.eq_zero_of_aeval_eq_zero P hz)

/-- A single algebra homomorphism preserves a vanishing relation and its
specialization at the selected first coordinate. -/
private theorem specialize_relation {R : Type*} [CommRing R] [Algebra k R]
    (ι : R →ₐ[k] K) (hι : Function.Injective ι) (φ : R →ₐ[k] K)
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) k) (t : R) (v : Fin n → R)
    (c : k) (hc : φ t = algebraMap k K c)
    (hz : aeval (Fin.cons (ι t) (fun i ↦ ι (v i))) P = 0) :
    aeval (fun i ↦ φ (v i)) ((finSuccEquiv k n P).eval (C c)) = 0 := by
  have hzero : aeval (Fin.cons t v) P = 0 := by
    apply hι
    rw [map_zero, MvPolynomial.comp_aeval_apply]
    have heq : (fun i : Fin (n + 1) ↦ ι ((Fin.cons t v : Fin (n + 1) → R) i)) =
        Fin.cons (ι t) (fun i ↦ ι (v i)) := by
      funext i
      exact Fin.cases rfl (fun _ ↦ rfl) i
    rw [heq]
    exact hz
  rw [aeval_specialize_first]
  have heq : Fin.cons (algebraMap k K c) (fun i ↦ φ (v i)) =
      fun i : Fin (n + 1) ↦ φ ((Fin.cons t v : Fin (n + 1) → R) i) := by
    ext i
    exact Fin.cases hc.symm (fun _ ↦ rfl) i
  rw [heq, ← MvPolynomial.comp_aeval_apply, hzero, map_zero]

/-- A nonzero element in the auxiliary closure cannot make an independent
coordinate algebraic by multiplication. -/
private theorem transcendental_mul_of_mem_racl {a x β : K}
    (hx : x ∉ racl k {a}) (hβ : β ∈ racl k {a}) (hβ0 : β ≠ 0) :
    Transcendental k (β * x) := by
  intro halg
  have hm : β * x ∈ racl k {a} :=
    racl_mono (Set.empty_subset _) (mem_racl_empty_of_isAlgebraic halg)
  have hd := div_mem hm hβ
  rw [mul_div_cancel_left₀ _ hβ0] at hd
  exact hx hd

/-- Descend a simultaneous multiplication-corner normalization through one
coherent specialization of the fresh parameter. The fixed closed field
contains the original coordinates; no choice of independent branches is assumed. -/
theorem exists_multiplier_descent
    {F : Type*} [Field F] [IsAlgClosed F] [Infinite k]
    [Algebra k F] [Algebra F K] [IsScalarTower k F K]
    (a b c x y : F) {t α : K} (ht : Transcendental F t)
    (hi : AlgebraicIndependent k
      ![algebraMap F K a, algebraMap F K x, algebraMap F K y])
    (hα0 : α ≠ 0) (hα : α ∈ racl k {t, algebraMap F K a})
    (hb : algebraMap F K b ∈ racl k {t, α * algebraMap F K x})
    (hc : algebraMap F K c ∈ racl k {t, α * algebraMap F K y}) :
    ∃ β : K, β ≠ 0 ∧ β ∈ racl k {algebraMap F K a} ∧
      algebraMap F K b ∈ racl k {β * algebraMap F K x} ∧
      algebraMap F K c ∈ racl k {β * algebraMap F K y} := by
  classical
  obtain ⟨Q, hQ, hQzero⟩ := exists_relation_of_mem_racl_pair hα
  obtain ⟨P, hP, hPzero⟩ := exists_relation_of_mem_racl_pair hb
  obtain ⟨T, hT, hTzero⟩ := exists_relation_of_mem_racl_pair hc
  obtain ⟨R, htR, hsR, ℓ, φ, hφ, hgood⟩ :=
    exists_finite_specialization_preserving_polynomials ht {α, α⁻¹} {Q, P, T} (by
      intro W hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl <;> assumption)
  let tR : R := ⟨t, htR⟩
  let αR : R := ⟨α, hsR (by simp)⟩
  let αinvR : R := ⟨α⁻¹, hsR (by simp)⟩
  let ι : R →ₐ[k] K := R.val.restrictScalars k
  let ψ : R →ₐ[k] K := (IsScalarTower.toAlgHom k F K).comp (φ.restrictScalars k)
  have hι : Function.Injective ι := Subtype.val_injective
  have hψ : ψ tR = algebraMap k K ℓ := by
    change algebraMap F K (φ ⟨t, htR⟩) = _
    rw [hφ, ← IsScalarTower.algebraMap_apply k F K]
  have hfix (z : F) : ψ (algebraMap F R z) = algebraMap F K z := by
    change algebraMap F K (φ (algebraMap F R z)) = _
    rw [φ.commutes, Algebra.algebraMap_self_apply]
  let β := ψ αR
  have hβ0 : β ≠ 0 := by
    have hunit : αR * αinvR = 1 := by
      apply Subtype.ext
      exact mul_inv_cancel₀ hα0
    have heq := congrArg ψ hunit
    rw [map_mul, map_one] at heq
    exact left_ne_zero_of_mul_eq_one heq
  have hmap (f : R → K) (u v : R) : (fun i ↦ f (![u, v] i)) = ![f u, f v] := by
    funext i
    fin_cases i <;> rfl
  have hQ' := specialize_relation ι hι ψ Q tR ![algebraMap F R a, αR] ℓ hψ
    (by simpa [hmap, ι, tR, αR] using hQzero)
  have hP' := specialize_relation ι hι ψ P tR ![αR * algebraMap F R x, algebraMap F R b]
    ℓ hψ (by simpa [hmap, ι, tR, αR] using hPzero)
  have hT' := specialize_relation ι hι ψ T tR ![αR * algebraMap F R y, algebraMap F R c]
    ℓ hψ (by simpa [hmap, ι, tR, αR] using hTzero)
  have hQspec : aeval ![algebraMap F K a, β]
      ((finSuccEquiv k 2 Q).eval (C ℓ)) = 0 := by
    simpa only [hmap, hfix] using hQ'
  have hPspec : aeval ![β * algebraMap F K x, algebraMap F K b]
      ((finSuccEquiv k 2 P).eval (C ℓ)) = 0 := by
    simpa only [hmap, map_mul, hfix] using hP'
  have hTspec : aeval ![β * algebraMap F K y, algebraMap F K c]
      ((finSuccEquiv k 2 T).eval (C ℓ)) = 0 := by
    simpa only [hmap, map_mul, hfix] using hT'
  have hβ : β ∈ racl k {algebraMap F K a} :=
    mem_racl_of_relation (hi.transcendental 0) (hgood Q (by simp)) hQspec
  have hx : algebraMap F K x ∉ racl k {algebraMap F K a} :=
    AlgebraicIndependent.notMem_racl_pair
      (AlgebraicIndependent.comp_pair hi (i := 0) (j := 1) (by decide))
  have hy : algebraMap F K y ∉ racl k {algebraMap F K a} :=
    AlgebraicIndependent.notMem_racl_pair
      (AlgebraicIndependent.comp_pair hi (i := 0) (j := 2) (by decide))
  exact ⟨β, hβ0, hβ,
    mem_racl_of_relation (transcendental_mul_of_mem_racl hx hβ hβ0) (hgood P (by simp)) hPspec,
    mem_racl_of_relation (transcendental_mul_of_mem_racl hy hβ hβ0) (hgood T (by simp)) hTspec⟩

end AclGeom
