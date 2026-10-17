/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Reconstruct.Kernel
import AclGeom.Closure.FreshExtension

/-!
# The source statement of j-rigidity and its normalized exponent

The literal characteristic-zero uniqueness of an integer in blueprint `thm:jrigidity`
is false (#32): every integer Frobenius iterate is the identity. The theorem
`jTupleOf_eq_charZero_and_exponent_not_unique` retains both actual independent pairs and
their tuple equality, proves the pair equality, and refutes the unnormalized integer uniqueness.

The corrected `existsUnique_normalized_frobeniusZPow_of_jTupleOf_eq` requires the
exponent to be zero in exponential characteristic one. It needs only a perfect
ambient field and the actual tuple equality, with no ambient rank or freshness premise.
The two fresh elements used by the existing core are chosen in `FreshAmbient`;
its equalities of natural powers reflect to the original field. Exponent separation
then applies only in positive characteristic.

**Status:** the corrected normalized rigidity and characteristic-zero refutation are proved
(#32). The original unnormalized source claim retains its provenance.
-/

namespace AclGeom

open ClosedIF

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Corrected source j-rigidity**: equal actual j-tuples over a perfect ambient field
have a unique common integral Frobenius exponent when the exponent is normalized to zero
in characteristic zero. No ambient rank, fresh-element or completeness input is required. -/
theorem existsUnique_normalized_frobeniusZPow_of_jTupleOf_eq [PerfectField K]
    (q : ℕ) [ExpChar K q] {x a y b : K}
    (hxa : AlgebraicIndependent k ![x, a]) (hyb : AlgebraicIndependent k ![y, b])
    (hj : jTupleOf x a hxa = jTupleOf y b hyb) :
    ∃! n : ℤ, (q = 1 → n = 0) ∧
      y = frobeniusZPow K q n x ∧ b = frobeniusZPow K q n a := by
  classical
  have : ExpChar k q := (algebraMap k K).expChar (algebraMap k K).injective q
  have h0 : point k x = point k y := congrArg (fun t ↦ (t 0).1) hj
  have h1 : point k (x + a) = point k (y + b) := congrArg (fun t ↦ (t 1).1) hj
  have h2 : point k (x * a) = point k (y * b) := congrArg (fun t ↦ (t 2).1) hj
  have h3 : point k (x * (1 + a)) = point k (y * (1 + b)) := by
    have h := congrArg (fun t ↦ (t 3).1) hj
    change point k (x + x * a) = point k (y + y * b) at h
    simpa only [mul_add, mul_one] using h
  have h4 : point k a = point k b := congrArg (fun t ↦ (t 4).1) hj
  obtain ⟨ry, rx⟩ := point_eq_point_iff.1 h0.symm
  obtain ⟨radd, radd'⟩ := point_eq_point_iff.1 h1.symm
  obtain ⟨rmul, rmul'⟩ := point_eq_point_iff.1 h2.symm
  obtain ⟨rmix, rmix'⟩ := point_eq_point_iff.1 h3.symm
  obtain ⟨rb, ra⟩ := point_eq_point_iff.1 h4.symm
  let ι : K →ₐ[k] FreshAmbient K := IsScalarTower.toAlgHom k K (FreshAmbient K)
  have hinj : Function.Injective ι := ι.toRingHom.injective
  have hind : AlgebraicIndependent k ![ι x, ι a] := by
    convert hxa.map' hinj using 1
    funext i
    fin_cases i <;> rfl
  have tr : ∀ {z w : K}, z ∈ racl k {w} → ι z ∈ racl k {ι w} :=
    fun h ↦ (algHom_mem_racl_singleton_iff ι).2 h
  have fresh : ∀ S : Finset (FreshAmbient K), S.card ≤ 3 →
      ∃ z, z ∉ racl k (S : Set (FreshAmbient K)) :=
    exists_notMem_racl_of_card_lt_trdeg (n := 3)
      (lt_of_lt_of_le (by norm_num) (four_le_trdeg_freshAmbient k K))
  obtain ⟨s, hs⟩ := fresh {ι x, ι a} (Finset.card_le_two.trans (by decide))
  obtain ⟨s', hs'⟩ := fresh {ι x, ι a, s} Finset.card_le_three
  obtain ⟨u, v, hu, hv⟩ := j_rigidity_field q hind (tr ry) (tr rx) (tr rb) (tr ra)
    (by simpa only [map_add] using tr radd)
    (by simpa only [map_add] using tr radd')
    (by simpa only [map_mul] using tr rmul)
    (by simpa only [map_mul] using tr rmul')
    (by simpa only [map_mul, map_add, map_one] using tr rmix)
    (by simpa only [map_mul, map_add, map_one] using tr rmix')
    (by simpa using hs) (by simpa using hs')
  have hy : y ^ q ^ v = x ^ q ^ u := hinj (by simpa only [map_pow] using hu)
  have hb : b ^ q ^ v = a ^ q ^ u := hinj (by simpa only [map_pow] using hv)
  by_cases hq : q = 1
  · have hy' : y = x := by simpa [hq] using hy
    have hb' : b = a := by simpa [hq] using hb
    refine ⟨0, ⟨fun _ ↦ rfl, ?_, ?_⟩, fun n hn ↦ hn.1 hq⟩
    · rw [frobeniusZPow_eq_one_of_eq_one q hq]
      exact hy'
    · rw [frobeniusZPow_eq_one_of_eq_one q hq]
      exact hb'
  · have hn₁ := (frobeniusZPow_sub_apply_of_pow_eq q hy).symm
    have hn₂ := (frobeniusZPow_sub_apply_of_pow_eq q hb).symm
    refine ⟨(u : ℤ) - v, ⟨fun h ↦ (hq h).elim, hn₁, hn₂⟩, ?_⟩
    intro n hn
    have hp : q.Prime := (expChar_is_prime_or_one K q).resolve_right hq
    have hx : x ∉ racl k (∅ : Set K) := fun h ↦
      AlgebraicIndependent.notMem_racl_pair' hxa (racl_mono (Set.empty_subset _) h)
    exact eq_of_frobeniusZPow_apply_eq q hp.two_le hx (hn.2.1.symm.trans hn₁)

/-- **The source characteristic-zero case**: equal actual j-tuples have equal pairs, but
there is no unique integer Frobenius exponent; zero and one are distinct valid exponents. -/
theorem jTupleOf_eq_charZero_and_exponent_not_unique [CharZero K] {x a y b : K}
    (hxa : AlgebraicIndependent k ![x, a]) (hyb : AlgebraicIndependent k ![y, b])
    (hj : jTupleOf x a hxa = jTupleOf y b hyb) :
    y = x ∧ b = a ∧
      ¬ ∃! n : ℤ, y = frobeniusZPow K 1 n x ∧ b = frobeniusZPow K 1 n a := by
  obtain ⟨n, hn, _⟩ := existsUnique_normalized_frobeniusZPow_of_jTupleOf_eq 1 hxa hyb hj
  rw [frobeniusZPow_eq_one_of_eq_one 1 rfl n] at hn
  have hy : y = x := hn.2.1
  have hb : b = a := hn.2.2
  refine ⟨hy, hb, ?_⟩
  have hall (m : ℤ) : y = frobeniusZPow K 1 m x ∧ b = frobeniusZPow K 1 m a := by
    rw [frobeniusZPow_eq_one_of_eq_one 1 rfl m]
    exact ⟨hy, hb⟩
  rintro ⟨m, _, hm⟩
  exact zero_ne_one ((hm 0 (hall 0)).trans (hm 1 (hall 1)).symm)

end AclGeom
