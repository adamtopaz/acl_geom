/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Mathlib.FieldTheory.Galois.Basic
import AclGeom.Correspondence.JRigidity
import AclGeom.Closure.Ambient

/-!
# Descent of j-semantics to a perfect subfield

The `(2) ⇒ (1)` arrow of the blueprint's descent theorem (§9.1): if all
five points of a semantic `j`-tuple in `Ω` have representatives in a
perfect subfield `K`, the underlying pair `(x, a)` already lies in `K`.

The formalization replaces the blueprint's automorphism argument — extend
conjugations to `Aut(Ω/K)`, iterate, and contradict finiteness of the
orbit — by *finite* Galois theory: for `σ` of finite order `r` in the
Galois group of a normal closure, the j-rigidity output
`(σ x)^{q^v} = x^{q^u}` telescopes to `x^{q^{rv}} = x^{q^{ru}}`, so the
two Frobenius exponents already agree (`orbit_exponent_eq`), and
injectivity of Frobenius powers forces `σ x = x` on the spot
(`ringHom_fix_of_pow_orbit`). No automorphism of `Ω` is ever
constructed, and no infinitude argument is needed.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** WIP (M5 descent): the telescope kernel is complete; the
assembly with the normal closure and the perfectness endgame follows.
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

section Telescope

/-- Distinct Frobenius-power exponents separate on any element that is
transcendental over the base: `x^{q^i} = x^{q^j}` forces `i = j` when
`q ≥ 2`. -/
theorem pow_pow_sep_of_notMem_racl_empty {x : Ω}
    (hx : x ∉ racl k (∅ : Set Ω)) {q : ℕ} (hq : 2 ≤ q) {i j : ℕ}
    (h : x ^ q ^ i = x ^ q ^ j) : i = j := by
  by_contra hij
  have hne : q ^ i ≠ q ^ j := (Nat.pow_right_injective hq).ne hij
  refine hx (mem_racl_empty_of_isAlgebraic ?_)
  refine ⟨Polynomial.X ^ q ^ i - Polynomial.X ^ q ^ j, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun p ↦ Polynomial.coeff p (q ^ i)) h0
    simp [Polynomial.coeff_X_pow, hne] at h1
  · rw [map_sub, map_pow, map_pow, Polynomial.aeval_X, sub_eq_zero]
    exact h

variable {L : Type*} [Field L]

/-- **The Galois telescope** (replacing the blueprint's orbit-infinitude
argument in §9.1): if iterating `σ` returns to `x` after `r > 0` steps and
`(σ x)^{q^v} = x^{q^u}`, then telescoping through one full period gives
`x^{q^{rv}} = x^{q^{ru}}`; if Frobenius exponents separate on `x`, the two
exponents agree. -/
theorem orbit_exponent_eq {σ : L →+* L} {x : L} {r : ℕ} (hr0 : 0 < r)
    (hσ : σ^[r] x = x) {q u v : ℕ}
    (h : σ x ^ q ^ v = x ^ q ^ u)
    (hsep : ∀ i j : ℕ, x ^ q ^ i = x ^ q ^ j → i = j) : u = v := by
  have key : ∀ n : ℕ, (σ^[n] x) ^ q ^ (n * v) = x ^ q ^ (n * u) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := congrArg σ ih
      rw [map_pow, map_pow, ← Function.iterate_succ_apply' σ n x] at h1
      -- Raise the telescoped identity to the `q ^ v`-th power and chain.
      have h3 := congrArg (fun z : L ↦ z ^ q ^ v) h1
      simp only [← pow_mul, ← pow_add] at h3
      have h4 := congrArg (fun z : L ↦ z ^ q ^ (n * u)) h
      simp only [← pow_mul, ← pow_add] at h4
      calc (σ^[n + 1] x) ^ q ^ ((n + 1) * v)
          = (σ^[n + 1] x) ^ q ^ (n * v + v) := by rw [Nat.succ_mul]
        _ = (σ x) ^ q ^ (n * u + v) := h3
        _ = (σ x) ^ q ^ (v + n * u) := by rw [add_comm]
        _ = x ^ q ^ (u + n * u) := h4
        _ = x ^ q ^ ((n + 1) * u) := by rw [Nat.succ_mul, add_comm]
  have hrr := key r
  rw [hσ] at hrr
  have h5 := hsep (r * v) (r * u) hrr
  exact (Nat.eq_of_mul_eq_mul_left hr0 h5).symm

/-- **Fixing from the telescope**: a ring endomorphism of finite order on
`x` whose action on `x` is a Frobenius-power twist fixes `x`. Exponent
separation is only consulted in positive characteristic; in characteristic
zero (`q = 1`) the twist is already the identity. -/
theorem ringHom_fix_of_pow_orbit {q : ℕ} [hq : ExpChar L q]
    {σ : L →+* L} {x : L} {r : ℕ} (hr0 : 0 < r) (hσ : σ^[r] x = x)
    {u v : ℕ} (h : σ x ^ q ^ v = x ^ q ^ u)
    (hsep : 2 ≤ q → ∀ i j : ℕ, x ^ q ^ i = x ^ q ^ j → i = j) :
    σ x = x := by
  rcases hq with _ | hp
  · simpa using h
  · haveI : ExpChar L q := ExpChar.prime hp
    have huv := orbit_exponent_eq hr0 hσ h (hsep hp.two_le)
    rw [huv] at h
    exact pow_expChar_pow_injective q v h

end Telescope

section GaloisFixing

/-- **The Galois fixing brick** for descent (§9.1, `(2) ⇒ (1)`): in a
finite Galois extension `L/F`, an element on which every `F`-automorphism
acts by a Frobenius-power twist lies in the base field. Combines the
telescope with the finite order of automorphisms and the Galois
correspondence — no automorphism of any ambient field is needed. -/
theorem mem_bot_of_forall_algEquiv_frobenius {F L : Type*} [Field F]
    [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {q : ℕ} [ExpChar L q] {x : L}
    (hsep : 2 ≤ q → ∀ i j : ℕ, x ^ q ^ i = x ^ q ^ j → i = j)
    (h : ∀ σ : L ≃ₐ[F] L, ∃ u v : ℕ, σ x ^ q ^ v = x ^ q ^ u) :
    x ∈ (⊥ : IntermediateField F L) := by
  rw [IsGalois.mem_bot_iff_fixed]
  intro σ
  obtain ⟨u, v, huv⟩ := h σ
  have hfin : IsOfFinOrder σ := isOfFinOrder_of_finite σ
  have hiter : (⇑(σ : L →+* L))^[orderOf σ] x = x := by
    have h1 : ⇑(σ ^ orderOf σ) = (⇑σ)^[orderOf σ] := AlgEquiv.coe_pow σ _
    have h2 := congrFun h1 x
    rw [pow_orderOf_eq_one σ] at h2
    exact h2.symm.trans rfl
  exact ringHom_fix_of_pow_orbit hfin.orderOf_pos hiter huv hsep

end GaloisFixing

section GaloisEnvelope

open IntermediateField

/-- **The Galois envelope**: any two elements algebraic over a perfect
subfield of an algebraically closed field lie in a finite Galois
subextension — the splitting field of the product of their minimal
polynomials. Perfectness supplies separability; no purely inseparable
bookkeeping is needed. -/
theorem exists_finiteDimensional_isGalois_mem {F : Type*} [Field F]
    [Algebra F Ω] [IsAlgClosed Ω] [PerfectField F] {x a : Ω}
    (hx : IsIntegral F x) (ha : IsIntegral F a) :
    ∃ L : IntermediateField F Ω, x ∈ L ∧ a ∈ L ∧
      FiniteDimensional F L ∧ IsGalois F L := by
  classical
  set f : Polynomial F := minpoly F x * minpoly F a with hf
  have hf0 : f ≠ 0 := mul_ne_zero (minpoly.ne_zero hx) (minpoly.ne_zero ha)
  have hsplits : (f.map (algebraMap F Ω)).Splits := IsAlgClosed.splits _
  haveI hsf : Polynomial.IsSplittingField F (adjoin F (f.rootSet Ω)) f :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplits
  haveI hfd : FiniteDimensional F (adjoin F (f.rootSet Ω)) :=
    Polynomial.IsSplittingField.finiteDimensional _ f
  haveI : Normal F (adjoin F (f.rootSet Ω)) :=
    Normal.of_isSplittingField f
  haveI : Algebra.IsAlgebraic F (adjoin F (f.rootSet Ω)) :=
    Algebra.IsAlgebraic.of_finite F _
  haveI : Algebra.IsSeparable F (adjoin F (f.rootSet Ω)) := inferInstance
  refine ⟨adjoin F (f.rootSet Ω), ?_, ?_, hfd, ⟨⟩⟩
  · refine subset_adjoin F _ ?_
    rw [Polynomial.mem_rootSet]
    exact ⟨hf0, by rw [hf, map_mul, minpoly.aeval, zero_mul]⟩
  · refine subset_adjoin F _ ?_
    rw [Polynomial.mem_rootSet]
    exact ⟨hf0, by rw [hf, map_mul, minpoly.aeval, mul_zero]⟩

end GaloisEnvelope

section DescentAssembly

open IntermediateField

/-- Conjugation transport: if `σ` fixes `y` and `w` is interalgebraic with
`y` through the embedding `ι`, then `σ w` is interalgebraic with `w`. -/
theorem conj_relation_of_fixed {N : Type*} [Field N] [Algebra k N]
    (ι : N →ₐ[k] Ω) (σ : N ≃ₐ[k] N) {w y : N} (hfix : σ y = y)
    (hw : ι w ∈ racl k ({ι y} : Set Ω))
    (hw' : ι y ∈ racl k ({ι w} : Set Ω)) :
    ι (σ w) ∈ racl k ({ι w} : Set Ω) ∧
      ι w ∈ racl k ({ι (σ w)} : Set Ω) := by
  constructor
  · have h1 := algHom_mem_racl_singleton_map ι σ hw
    rw [hfix] at h1
    exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 hw') h1
  · have h2 := algHom_mem_racl_singleton_map ι σ hw'
    rw [hfix] at h2
    exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 h2) hw

/-- **Descent of a semantic j-tuple to a perfect subfield** (blueprint
Theorem j-descent, arrow (2) ⇒ (1)): if the five coordinates of the
j-value `j(x, a) = (x, x+a, xa, x+xa, a)` are each interalgebraic over
`k` with an element of a perfect subfield `K₁`, then `x` and `a` already
lie in `K₁`. The freshness oracle supplies the side elements of
j-rigidity; the blueprint sources it from `trdeg ≥ 5`. -/
theorem mem_of_j_represented [IsAlgClosed Ω] (q : ℕ) [ExpChar k q]
    {K₁ : IntermediateField k Ω} [PerfectField (↥K₁)]
    {x a : Ω} (hind : AlgebraicIndependent k ![x, a])
    {y₁ y₂ y₃ y₄ y₅ : Ω}
    (hK1 : y₁ ∈ K₁) (hK2 : y₂ ∈ K₁) (hK3 : y₃ ∈ K₁) (hK4 : y₄ ∈ K₁)
    (hK5 : y₅ ∈ K₁)
    (h₁ : x ∈ racl k ({y₁} : Set Ω)) (h₁' : y₁ ∈ racl k ({x} : Set Ω))
    (h₂ : x + a ∈ racl k ({y₂} : Set Ω))
    (h₂' : y₂ ∈ racl k ({x + a} : Set Ω))
    (h₃ : x * a ∈ racl k ({y₃} : Set Ω))
    (h₃' : y₃ ∈ racl k ({x * a} : Set Ω))
    (h₄ : x + x * a ∈ racl k ({y₄} : Set Ω))
    (h₄' : y₄ ∈ racl k ({x + x * a} : Set Ω))
    (h₅ : a ∈ racl k ({y₅} : Set Ω)) (h₅' : y₅ ∈ racl k ({a} : Set Ω))
    (hfresh : ∀ S : Finset Ω, S.card ≤ 3 → ∃ z, z ∉ racl k (↑S : Set Ω)) :
    x ∈ K₁ ∧ a ∈ K₁ := by
  classical
  -- Transcendence of the coordinates.
  have hx0 : x ∉ racl k (∅ : Set Ω) := fun h ↦
    AlgebraicIndependent.notMem_racl_pair' hind
      (racl_mono (Set.empty_subset _) h)
  have ha0 : a ∉ racl k (∅ : Set Ω) := fun h ↦
    AlgebraicIndependent.notMem_racl_pair hind
      (racl_mono (Set.empty_subset _) h)
  -- Integrality over `K₁` through the representatives.
  have hxint : IsIntegral (↥K₁) x := by
    rw [← isAlgebraic_iff_isIntegral]
    exact isAlgebraic_of_le
      (adjoin_le_iff.2 (Set.singleton_subset_iff.2 hK1))
      ((mem_racl_iff k).1 h₁)
  have haint : IsIntegral (↥K₁) a := by
    rw [← isAlgebraic_iff_isIntegral]
    exact isAlgebraic_of_le
      (adjoin_le_iff.2 (Set.singleton_subset_iff.2 hK5))
      ((mem_racl_iff k).1 h₅)
  -- The Galois envelope.
  obtain ⟨L, hxL, haL, hfd, hgal⟩ :=
    exists_finiteDimensional_isGalois_mem (F := ↥K₁) hxint haint
  haveI := hfd
  haveI := hgal
  set ι : (↥L) →ₐ[k] Ω := (L.val).restrictScalars k with hιdef
  set xL : ↥L := ⟨x, hxL⟩ with hxLdef
  set aL : ↥L := ⟨a, haL⟩ with haLdef
  have hιx : ι xL = x := rfl
  have hιa : ι aL = a := rfl
  have hιinj : Function.Injective ι.toRingHom := ι.toRingHom.injective
  -- Representatives inside `L`, fixed by the Galois action.
  set y₁L : ↥L := algebraMap (↥K₁) (↥L) ⟨y₁, hK1⟩ with hy₁Ldef
  set y₂L : ↥L := algebraMap (↥K₁) (↥L) ⟨y₂, hK2⟩ with hy₂Ldef
  set y₃L : ↥L := algebraMap (↥K₁) (↥L) ⟨y₃, hK3⟩ with hy₃Ldef
  set y₄L : ↥L := algebraMap (↥K₁) (↥L) ⟨y₄, hK4⟩ with hy₄Ldef
  set y₅L : ↥L := algebraMap (↥K₁) (↥L) ⟨y₅, hK5⟩ with hy₅Ldef
  have hιy₁ : ι y₁L = y₁ := L.val.commutes ⟨y₁, hK1⟩
  have hιy₂ : ι y₂L = y₂ := L.val.commutes ⟨y₂, hK2⟩
  have hιy₃ : ι y₃L = y₃ := L.val.commutes ⟨y₃, hK3⟩
  have hιy₄ : ι y₄L = y₄ := L.val.commutes ⟨y₄, hK4⟩
  have hιy₅ : ι y₅L = y₅ := L.val.commutes ⟨y₅, hK5⟩
  -- The relations in embedded form.
  have hιsum : ι (xL + aL) = x + a := by rw [map_add, hιx, hιa]
  have hιmul : ι (xL * aL) = x * a := by rw [map_mul, hιx, hιa]
  have hιgrid : ι (xL + xL * aL) = x + x * a := by
    rw [map_add, map_mul, hιx, hιa]
  have h₁ι : ι xL ∈ racl k ({ι y₁L} : Set Ω) := by
    rw [hιx, hιy₁]; exact h₁
  have h₁ι' : ι y₁L ∈ racl k ({ι xL} : Set Ω) := by
    rw [hιx, hιy₁]; exact h₁'
  have h₂ι : ι (xL + aL) ∈ racl k ({ι y₂L} : Set Ω) := by
    rw [hιsum, hιy₂]; exact h₂
  have h₂ι' : ι y₂L ∈ racl k ({ι (xL + aL)} : Set Ω) := by
    rw [hιsum, hιy₂]; exact h₂'
  have h₃ι : ι (xL * aL) ∈ racl k ({ι y₃L} : Set Ω) := by
    rw [hιmul, hιy₃]; exact h₃
  have h₃ι' : ι y₃L ∈ racl k ({ι (xL * aL)} : Set Ω) := by
    rw [hιmul, hιy₃]; exact h₃'
  have h₄ι : ι (xL + xL * aL) ∈ racl k ({ι y₄L} : Set Ω) := by
    rw [hιgrid, hιy₄]; exact h₄
  have h₄ι' : ι y₄L ∈ racl k ({ι (xL + xL * aL)} : Set Ω) := by
    rw [hιgrid, hιy₄]; exact h₄'
  have h₅ι : ι aL ∈ racl k ({ι y₅L} : Set Ω) := by
    rw [hιa, hιy₅]; exact h₅
  have h₅ι' : ι y₅L ∈ racl k ({ι aL} : Set Ω) := by
    rw [hιa, hιy₅]; exact h₅'
  -- The algebraically closed base for j-rigidity.
  haveI : IsAlgClosed (↥(algebraicClosure k Ω)) :=
    (algebraicClosure.isAlgClosure k Ω).isAlgClosed
  haveI : ExpChar (↥(algebraicClosure k Ω)) q :=
    expChar_of_injective_ringHom
      (algebraMap k (↥(algebraicClosure k Ω))).injective q
  have halg : ∀ y ∈ algebraicClosure k Ω, IsAlgebraic k y := fun y hy ↦
    (mem_algebraicClosure_iff (F := k)).1 hy
  have hbase : ∀ {S : Set Ω} {z : Ω},
      z ∈ racl k S ↔ z ∈ racl (↥(algebraicClosure k Ω)) S :=
    fun {S z} ↦ (mem_racl_base_iff_of_algebraic halg).symm
  have hindb : AlgebraicIndependent (↥(algebraicClosure k Ω)) ![x, a] :=
    algebraicIndependent_pair_base_of_algebraic halg hind
  -- Freshness for j-rigidity.
  obtain ⟨s, hs⟩ := hfresh {x, a}
    ((Finset.card_insert_le _ _).trans (by simp))
  have hs₂ : s ∉ racl k ({x, a} : Set Ω) := by
    have hset : ((({x, a} : Finset Ω) : Set Ω)) = ({x, a} : Set Ω) := by
      simp
    rwa [hset] at hs
  obtain ⟨s', hs'⟩ := hfresh {x, a, s}
    ((Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp))))
  have hs₂' : s' ∉ racl k ({x, a, s} : Set Ω) := by
    have hset : ((({x, a, s} : Finset Ω) : Set Ω)) = ({x, a, s} : Set Ω) := by
      simp
    rwa [hset] at hs'
  -- The Frobenius twist for every Galois automorphism, via j-rigidity.
  have hall : ∀ σ : (↥L) ≃ₐ[↥K₁] (↥L),
      ∃ u v : ℕ, σ xL ^ q ^ v = xL ^ q ^ u ∧ σ aL ^ q ^ v = aL ^ q ^ u := by
    intro σ
    set σk : (↥L) ≃ₐ[k] (↥L) := σ.restrictScalars k with hσkdef
    have hfix₁ : σk y₁L = y₁L := σ.commutes ⟨y₁, hK1⟩
    have hfix₂ : σk y₂L = y₂L := σ.commutes ⟨y₂, hK2⟩
    have hfix₃ : σk y₃L = y₃L := σ.commutes ⟨y₃, hK3⟩
    have hfix₄ : σk y₄L = y₄L := σ.commutes ⟨y₄, hK4⟩
    have hfix₅ : σk y₅L = y₅L := σ.commutes ⟨y₅, hK5⟩
    obtain ⟨r₁, r₁'⟩ := conj_relation_of_fixed ι σk hfix₁ h₁ι h₁ι'
    obtain ⟨r₂, r₂'⟩ := conj_relation_of_fixed ι σk hfix₂ h₂ι h₂ι'
    obtain ⟨r₃, r₃'⟩ := conj_relation_of_fixed ι σk hfix₃ h₃ι h₃ι'
    obtain ⟨r₄, r₄'⟩ := conj_relation_of_fixed ι σk hfix₄ h₄ι h₄ι'
    obtain ⟨r₅, r₅'⟩ := conj_relation_of_fixed ι σk hfix₅ h₅ι h₅ι'
    -- Normalize the conjugated composites.
    have hσsum : ι (σk (xL + aL)) = ι (σk xL) + ι (σk aL) := by
      rw [map_add, map_add]
    have hσmul : ι (σk (xL * aL)) = ι (σk xL) * ι (σk aL) := by
      rw [map_mul, map_mul]
    have hσgrid : ι (σk (xL + xL * aL)) =
        ι (σk xL) + ι (σk xL) * ι (σk aL) := by
      rw [map_add, map_mul, map_add, map_mul]
    rw [hιx] at r₁ r₁'
    rw [hιa] at r₅ r₅'
    rw [hιsum, hσsum] at r₂ r₂'
    rw [hιmul, hσmul] at r₃ r₃'
    rw [hιgrid, hσgrid] at r₄ r₄'
    -- Apply j-rigidity over the algebraically closed base.
    have hjr := j_rigidity (k := ↥(algebraicClosure k Ω)) q
      (x := x) (a := a) (y := ι (σk xL)) (b := ι (σk aL)) hindb
      (hbase.1 r₁) (hbase.1 r₁') (hbase.1 r₅) (hbase.1 r₅')
      (hbase.1 r₂) (hbase.1 r₂') (hbase.1 r₃) (hbase.1 r₃')
      (by
        have e₁ : ι (σk xL) * (1 + ι (σk aL)) =
            ι (σk xL) + ι (σk xL) * ι (σk aL) := by ring
        have e₂ : x * (1 + a) = x + x * a := by ring
        rw [e₁, e₂]
        exact hbase.1 r₄)
      (by
        have e₁ : ι (σk xL) * (1 + ι (σk aL)) =
            ι (σk xL) + ι (σk xL) * ι (σk aL) := by ring
        have e₂ : x * (1 + a) = x + x * a := by ring
        rw [e₁, e₂]
        exact hbase.1 r₄')
      (s := s) (s' := s') (fun h ↦ hs₂ (hbase.2 h)) (fun h ↦ hs₂' (hbase.2 h))
    obtain ⟨u, v, hxe, hae⟩ := hjr
    refine ⟨u, v, hιinj ?_, hιinj ?_⟩
    · rw [map_pow, map_pow]
      show ι (σk xL) ^ q ^ v = ι xL ^ q ^ u
      rw [hιx]
      exact hxe
    · rw [map_pow, map_pow]
      show ι (σk aL) ^ q ^ v = ι aL ^ q ^ u
      rw [hιa]
      exact hae
  -- Feed the Galois fixing brick, coordinatewise.
  haveI : ExpChar (↥K₁) q :=
    expChar_of_injective_ringHom (algebraMap k (↥K₁)).injective q
  haveI : ExpChar (↥L) q :=
    expChar_of_injective_ringHom (algebraMap (↥K₁) (↥L)).injective q
  have hsepx : 2 ≤ q → ∀ i j : ℕ, xL ^ q ^ i = xL ^ q ^ j → i = j := by
    intro hq2 i j hij
    refine pow_pow_sep_of_notMem_racl_empty hx0 hq2 (i := i) (j := j) ?_
    have h1 := congrArg ι hij
    rwa [map_pow, map_pow, hιx] at h1
  have hsepa : 2 ≤ q → ∀ i j : ℕ, aL ^ q ^ i = aL ^ q ^ j → i = j := by
    intro hq2 i j hij
    refine pow_pow_sep_of_notMem_racl_empty ha0 hq2 (i := i) (j := j) ?_
    have h1 := congrArg ι hij
    rwa [map_pow, map_pow, hιa] at h1
  have hxbot := mem_bot_of_forall_algEquiv_frobenius (F := ↥K₁) hsepx
    (fun σ ↦ by obtain ⟨u, v, h1, -⟩ := hall σ; exact ⟨u, v, h1⟩)
  have habot := mem_bot_of_forall_algEquiv_frobenius (F := ↥K₁) hsepa
    (fun σ ↦ by obtain ⟨u, v, -, h2⟩ := hall σ; exact ⟨u, v, h2⟩)
  rw [IntermediateField.mem_bot] at hxbot habot
  obtain ⟨cx, hcx⟩ := hxbot
  obtain ⟨ca, hca⟩ := habot
  constructor
  · have h1 : x = (cx : Ω) := by
      rw [← hιx, ← hcx]
      exact (L.val.commutes cx).symm ▸ rfl
    rw [h1]
    exact SetLike.coe_mem cx
  · have h1 : a = (ca : Ω) := by
      rw [← hιa, ← hca]
      exact (L.val.commutes ca).symm ▸ rfl
    rw [h1]
    exact SetLike.coe_mem ca

end DescentAssembly

end

end AclGeom
