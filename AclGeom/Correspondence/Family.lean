/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import AclGeom.Closure.Ambient
import AclGeom.Correspondence.Composition

/-!
# Generic members of finite-correspondence families

A parameterized family is represented at a generic member by a tuple
`(p, x, y)`: the parameter tuple `p` is independent, `x` is generic over
`p`, and `x,y` are interalgebraic over `k(p)`.  This is the elementwise
form of the generic graph used throughout blueprint §8.

The central relocation theorem in this module moves the independent prefix
`(p,x)` to any other independent tuple while preserving the complete
vanishing ideal of `(p,x,y)`.  Consequently the same family locus has a
member above every independent generic parameter/source pair.  Unlike an
unconstrained relocation, the new prefix is fixed literally; this is what
is needed to compose varying family members on compatible normal covers.

This module starts the positive-dimensional family layer above the finite
branch groupoids.
-/

namespace AclGeom

open IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

noncomputable section

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- Relocate a finite algebraic tuple while fixing a chosen independent
coordinate subsystem literally.  The map `e` identifies the coordinates
of `u` that equal the independent tuple `t`; every coordinate of `u` is
algebraic over `k(t)`.  Any other independent tuple `s` can therefore be
installed at those same coordinate positions without changing the complete
vanishing ideal of the full tuple. -/
theorem exists_tuple_relocation_fixing [IsAlgClosed Ω] {n m : ℕ}
    {t s : Fin n → Ω} {u : Fin m → Ω} {e : Fin n → Fin m}
    (ht : AlgebraicIndependent k t) (hs : AlgebraicIndependent k s)
    (he : ∀ i, u (e i) = t i)
    (hu : ∀ j, u j ∈ racl k (Set.range t)) :
    ∃ v : Fin m → Ω,
      idealOf k v = idealOf k u ∧ ∀ i, v (e i) = s i := by
  classical
  let E := adjoin k (Set.range t)
  let L := adjoin k (Set.range u)
  have hle : E ≤ L := by
    apply adjoin.mono
    rintro _ ⟨i, rfl⟩
    have hti : t i ∈ Set.range u := ⟨e i, he i⟩
    exact hti
  have halg : Algebra.IsAlgebraic (↥E) (↥(extendScalars hle)) := by
    apply isAlgebraic_extendScalars_adjoin hle
    rintro _ ⟨j, rfl⟩
    exact (mem_racl_iff k).1 (hu j)
  obtain ⟨ψ, hψ⟩ := exists_extension_of_isAlgebraic
    (halg := halg) hle (adjoinTranscendentalAlgHom ht hs)
  have huMem (j : Fin m) : u j ∈ L :=
    subset_adjoin k _ (Set.mem_range_self j)
  let ua : Fin m → ↥L := fun j ↦ ⟨u j, huMem j⟩
  let v : Fin m → Ω := fun j ↦ ψ (ua j)
  have hfix (i : Fin n) : v (e i) = s i := by
    have hmem : t i ∈ E := subset_adjoin k _ ⟨i, rfl⟩
    have hua : ua (e i) = ⟨t i, hle hmem⟩ := by
      apply Subtype.ext
      exact he i
    change ψ (ua (e i)) = s i
    rw [hua, hψ ⟨t i, hmem⟩]
    exact adjoinTranscendentalAlgHom_apply ht hs i
  refine ⟨v, ?_, hfix⟩
  ext f
  rw [mem_idealOf_iff, mem_idealOf_iff]
  have h1 : MvPolynomial.aeval v f =
      ψ (MvPolynomial.aeval ua f) := by
    change MvPolynomial.aeval (fun j ↦ ψ (ua j)) f = _
    rw [MvPolynomial.comp_aeval_apply]
  have h2 : MvPolynomial.aeval u f =
      L.val (MvPolynomial.aeval ua f) := by
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  rw [h1, h2]
  constructor
  · intro hz
    have ha : ψ (MvPolynomial.aeval ua f) = ψ 0 := by
      rw [map_zero]
      exact hz
    rw [ψ.injective ha, map_zero]
  · intro hz
    have ha : L.val (MvPolynomial.aeval ua f) = L.val 0 := by
      rw [map_zero]
      exact hz
    rw [L.val.injective ha, map_zero]

/-- Equality of complete tuple ideals restricts to every chosen coordinate
subtuple. -/
theorem idealOf_comp_eq_of_idealOf_eq {ι κ : Type*}
    {a b : ι → Ω} (h : idealOf k a = idealOf k b) (e : κ → ι) :
    idealOf k (a ∘ e) = idealOf k (b ∘ e) := by
  ext f
  rw [mem_idealOf_iff, mem_idealOf_iff]
  have ha : MvPolynomial.aeval (a ∘ e) f =
      MvPolynomial.aeval a (MvPolynomial.rename e f) := by
    rw [MvPolynomial.aeval_rename]
  have hb : MvPolynomial.aeval (b ∘ e) f =
      MvPolynomial.aeval b (MvPolynomial.rename e f) := by
    rw [MvPolynomial.aeval_rename]
  rw [ha, hb]
  constructor
  · intro hz
    have hm : MvPolynomial.rename e f ∈ idealOf k a :=
      (mem_idealOf_iff k).2 hz
    exact (mem_idealOf_iff k).1 (h ▸ hm)
  · intro hz
    have hm : MvPolynomial.rename e f ∈ idealOf k b :=
      (mem_idealOf_iff k).2 hz
    exact (mem_idealOf_iff k).1 (h.symm ▸ hm)

/-- Algebraic independence of a coordinate subtuple transfers across
equality of complete tuple ideals. -/
theorem algebraicIndependent_comp_of_idealOf_eq {ι κ : Type*}
    {a b : ι → Ω} (h : idealOf k a = idealOf k b) (e : κ → ι)
    (ha : AlgebraicIndependent k (a ∘ e)) :
    AlgebraicIndependent k (b ∘ e) := by
  rw [← idealOf_eq_bot_iff] at ha ⊢
  rw [← idealOf_comp_eq_of_idealOf_eq h e]
  exact ha

/-- The coordinate ring of a tuple locus is canonically the subalgebra
generated by that tuple. -/
def locusCoordinateRingEquiv {ι : Type*} (a : ι → Ω) :
    (MvPolynomial ι k ⧸ idealOf k a) ≃ₐ[k]
      Algebra.adjoin k (Set.range a) := by
  change (MvPolynomial ι k ⧸
      RingHom.ker
        (MvPolynomial.aeval a : MvPolynomial ι k →ₐ[k] Ω).toRingHom) ≃ₐ[k]
    Algebra.adjoin k (Set.range a)
  exact (Ideal.quotientKerEquivRange
      (MvPolynomial.aeval a : MvPolynomial ι k →ₐ[k] Ω)).trans
    (Subalgebra.equivOfEq _ _
      (Algebra.adjoin_range_eq_range_aeval k a).symm)

/-- Evaluation describes the coordinate-ring equivalence on polynomial
classes. -/
@[simp] theorem locusCoordinateRingEquiv_mk {ι : Type*}
    (a : ι → Ω) (p : MvPolynomial ι k) :
    locusCoordinateRingEquiv a (Ideal.Quotient.mk _ p) =
      ⟨MvPolynomial.aeval a p, by
        rw [Algebra.adjoin_range_eq_range_aeval]
        exact AlgHom.mem_range_self _ p⟩ := by
  apply Subtype.ext
  change ↑(((Ideal.quotientKerEquivRange (MvPolynomial.aeval a)).trans
    (Subalgebra.equivOfEq _ _
      (Algebra.adjoin_range_eq_range_aeval k a).symm))
        (Ideal.Quotient.mk _ p)) = MvPolynomial.aeval a p
  rw [AlgEquiv.trans_apply]
  rw [Ideal.quotientKerEquivRange]
  rw [AlgEquiv.trans_apply]
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rw [Ideal.quotientKerAlgEquivOfSurjective_mk]
  rfl

/-- Equal complete tuple ideals canonically identify the two generated
coordinate rings. -/
def locusCoordinateRingEquivOfIdealEq {ι : Type*}
    {a b : ι → Ω} (h : idealOf k a = idealOf k b) :
    Algebra.adjoin k (Set.range a) ≃ₐ[k]
      Algebra.adjoin k (Set.range b) :=
  (locusCoordinateRingEquiv a).symm |>.trans <|
    (Ideal.quotientEquivAlgOfEq k h).trans
      (locusCoordinateRingEquiv b)

/-- The coordinate-ring equivalence induced by equal loci sends every
displayed coordinate to its matching coordinate. -/
@[simp] theorem locusCoordinateRingEquivOfIdealEq_apply {ι : Type*}
    {a b : ι → Ω} (h : idealOf k a = idealOf k b) (i : ι) :
    locusCoordinateRingEquivOfIdealEq h
        ⟨a i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ =
      ⟨b i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ := by
  let qa : MvPolynomial ι k ⧸ idealOf k a :=
    Ideal.Quotient.mk _ (MvPolynomial.X i)
  let qb : MvPolynomial ι k ⧸ idealOf k b :=
    Ideal.Quotient.mk _ (MvPolynomial.X i)
  have ha : locusCoordinateRingEquiv a qa =
      ⟨a i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ := by
    simp [qa]
  have hb : locusCoordinateRingEquiv b qb =
      ⟨b i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ := by
    simp [qb]
  change locusCoordinateRingEquiv b
      ((Ideal.quotientEquivAlgOfEq k h)
        ((locusCoordinateRingEquiv a).symm
          ⟨a i, Algebra.subset_adjoin (Set.mem_range_self i)⟩)) =
    ⟨b i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  rw [← ha, AlgEquiv.symm_apply_apply, ← hb]
  apply congrArg (fun x ↦ locusCoordinateRingEquiv b x)
  dsimp [qa, qb]

/-- Equal complete tuple ideals canonically identify the generated
function fields.  This is the function-field transport used to glue
relocated members of one family locus. -/
def locusFunctionFieldEquivOfIdealEq {ι : Type*}
    {a b : ι → Ω} (h : idealOf k a = idealOf k b) :
    (↥(adjoin k (Set.range a))) ≃ₐ[k]
      (↥(adjoin k (Set.range b))) :=
  IsFractionRing.algEquivOfAlgEquiv
    (locusCoordinateRingEquivOfIdealEq h)

/-- The induced function-field equivalence sends every tuple coordinate
to the corresponding coordinate of the equal-locus realization. -/
@[simp] theorem locusFunctionFieldEquivOfIdealEq_apply {ι : Type*}
    {a b : ι → Ω} (h : idealOf k a = idealOf k b) (i : ι) :
    locusFunctionFieldEquivOfIdealEq h
        ⟨a i, subset_adjoin k _ (Set.mem_range_self i)⟩ =
      ⟨b i, subset_adjoin k _ (Set.mem_range_self i)⟩ := by
  change locusFunctionFieldEquivOfIdealEq h
      (algebraMap (Algebra.adjoin k (Set.range a))
        (↥(adjoin k (Set.range a)))
        ⟨a i, Algebra.subset_adjoin (Set.mem_range_self i)⟩) =
    algebraMap (Algebra.adjoin k (Set.range b))
      (↥(adjoin k (Set.range b)))
      ⟨b i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  rw [locusFunctionFieldEquivOfIdealEq,
    IsFractionRing.algEquivOfAlgEquiv_algebraMap,
    locusCoordinateRingEquivOfIdealEq_apply]

/-- The function-field transport attached to reflexive locus equality is
the identity. -/
@[simp] theorem locusFunctionFieldEquivOfIdealEq_refl {ι : Type*}
    (a : ι → Ω) :
    locusFunctionFieldEquivOfIdealEq
        (rfl : idealOf k a = idealOf k a) = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply adjoin_algHom_ext k
  rintro _ ⟨i, rfl⟩
  simp

/-- Reversing an equality of loci reverses its function-field transport. -/
@[simp] theorem locusFunctionFieldEquivOfIdealEq_symm {ι : Type*}
    {a b : ι → Ω} (h : idealOf k a = idealOf k b) :
    (locusFunctionFieldEquivOfIdealEq h).symm =
      locusFunctionFieldEquivOfIdealEq h.symm := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply adjoin_algHom_ext k
  rintro _ ⟨i, rfl⟩
  calc
    (locusFunctionFieldEquivOfIdealEq h).symm
        ⟨b i, subset_adjoin k _ (Set.mem_range_self i)⟩ =
        ⟨a i, subset_adjoin k _ (Set.mem_range_self i)⟩ :=
      (locusFunctionFieldEquivOfIdealEq h).symm_apply_eq.mpr
        (locusFunctionFieldEquivOfIdealEq_apply h i).symm
    _ = locusFunctionFieldEquivOfIdealEq h.symm
        ⟨b i, subset_adjoin k _ (Set.mem_range_self i)⟩ :=
      (locusFunctionFieldEquivOfIdealEq_apply h.symm i).symm

/-- Function-field transports compose coherently along consecutive
equalities of complete tuple loci. -/
@[simp] theorem locusFunctionFieldEquivOfIdealEq_trans {ι : Type*}
    {a b c : ι → Ω} (hab : idealOf k a = idealOf k b)
    (hbc : idealOf k b = idealOf k c) :
    (locusFunctionFieldEquivOfIdealEq hab).trans
        (locusFunctionFieldEquivOfIdealEq hbc) =
      locusFunctionFieldEquivOfIdealEq (hab.trans hbc) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply adjoin_algHom_ext k
  rintro _ ⟨i, rfl⟩
  calc
    ((locusFunctionFieldEquivOfIdealEq hab).trans
        (locusFunctionFieldEquivOfIdealEq hbc))
        ⟨a i, subset_adjoin k _ (Set.mem_range_self i)⟩ =
        locusFunctionFieldEquivOfIdealEq hbc
          (locusFunctionFieldEquivOfIdealEq hab
            ⟨a i, subset_adjoin k _ (Set.mem_range_self i)⟩) := rfl
    _ = locusFunctionFieldEquivOfIdealEq hbc
          ⟨b i, subset_adjoin k _ (Set.mem_range_self i)⟩ := by
      rw [locusFunctionFieldEquivOfIdealEq_apply]
    _ = ⟨c i, subset_adjoin k _ (Set.mem_range_self i)⟩ :=
      locusFunctionFieldEquivOfIdealEq_apply hbc i
    _ = locusFunctionFieldEquivOfIdealEq (hab.trans hbc)
        ⟨a i, subset_adjoin k _ (Set.mem_range_self i)⟩ :=
      (locusFunctionFieldEquivOfIdealEq_apply (hab.trans hbc) i).symm

/-- A base-field equivalence extends canonically after adjoining matching
algebraically independent tuples on both sides. -/
def adjoinIndependentEquivOfEquiv {ι : Type*}
    {E E' : IntermediateField k Ω} (e : E ≃ₐ[k] E')
    {x y : ι → Ω} (hx : AlgebraicIndependent E x)
    (hy : AlgebraicIndependent E' y) :
    (↥(adjoin E (Set.range x))) ≃ₐ[k]
      (↥(adjoin E' (Set.range y))) :=
  (hx.aevalEquivField.symm.restrictScalars k).trans
    ((IsFractionRing.algEquivOfAlgEquiv
      (MvPolynomial.mapAlgEquiv ι e)).trans
        (hy.aevalEquivField.restrictScalars k))

/-- The independent extension of a base equivalence agrees with that
equivalence on the base field. -/
theorem adjoinIndependentEquivOfEquiv_algebraMap {ι : Type*}
    {E E' : IntermediateField k Ω} (e : E ≃ₐ[k] E')
    {x y : ι → Ω} (hx : AlgebraicIndependent E x)
    (hy : AlgebraicIndependent E' y) (z : E) :
    adjoinIndependentEquivOfEquiv e hx hy
        (algebraMap E (↥(adjoin E (Set.range x))) z) =
      algebraMap E' (↥(adjoin E' (Set.range y))) (e z) := by
  change hy.aevalEquivField
      ((IsFractionRing.algEquivOfAlgEquiv
        (MvPolynomial.mapAlgEquiv ι e))
          (hx.aevalEquivField.symm
            (algebraMap E (↥(adjoin E (Set.range x))) z))) = _
  rw [hx.aevalEquivField.symm.commutes]
  have hbase :
      algebraMap E (FractionRing (MvPolynomial ι E)) z =
        algebraMap (MvPolynomial ι E)
          (FractionRing (MvPolynomial ι E)) (MvPolynomial.C z) := rfl
  rw [hbase, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  apply Subtype.ext
  rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
  simp

/-- The independent extension of a base equivalence sends every displayed
source generator to its matching target generator. -/
theorem adjoinIndependentEquivOfEquiv_generator {ι : Type*}
    {E E' : IntermediateField k Ω} (e : E ≃ₐ[k] E')
    {x y : ι → Ω} (hx : AlgebraicIndependent E x)
    (hy : AlgebraicIndependent E' y) (i : ι) :
    adjoinIndependentEquivOfEquiv e hx hy
        ⟨x i, subset_adjoin E _ (Set.mem_range_self i)⟩ =
      ⟨y i, subset_adjoin E' _ (Set.mem_range_self i)⟩ := by
  have hxgen : hx.aevalEquivField
      (algebraMap (MvPolynomial ι E)
        (FractionRing (MvPolynomial ι E)) (MvPolynomial.X i)) =
        ⟨x i, subset_adjoin E _ (Set.mem_range_self i)⟩ := by
    apply Subtype.ext
    rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
    simp
  change hy.aevalEquivField
      ((IsFractionRing.algEquivOfAlgEquiv
        (MvPolynomial.mapAlgEquiv ι e))
          (hx.aevalEquivField.symm ⟨x i, _⟩)) = _
  rw [← hxgen, hx.aevalEquivField.symm_apply_apply,
    IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  apply Subtype.ext
  rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
  simp

/-- A base-field equivalence extends canonically after adjoining one
transcendental generator on each side, sending the displayed source
generator to the displayed target generator. -/
def adjoinTranscendentalEquivOfEquiv
    {E E' : IntermediateField k Ω} (e : E ≃ₐ[k] E')
    {x y : Ω} (hx : Transcendental E x) (hy : Transcendental E' y) :
    (↥(adjoin E (Set.range (![x] : Fin 1 → Ω)))) ≃ₐ[k]
      (↥(adjoin E' (Set.range (![y] : Fin 1 → Ω)))) := by
  have hx' : AlgebraicIndependent E (![x] : Fin 1 → Ω) := by
    rw [algebraicIndependent_unique_type_iff]
    exact hx
  have hy' : AlgebraicIndependent E' (![y] : Fin 1 → Ω) := by
    rw [algebraicIndependent_unique_type_iff]
    exact hy
  exact (hx'.aevalEquivField.symm.restrictScalars k).trans
    ((IsFractionRing.algEquivOfAlgEquiv
      (MvPolynomial.mapAlgEquiv (Fin 1) e)).trans
        (hy'.aevalEquivField.restrictScalars k))

/-- The transcendental extension of a base equivalence agrees with that
equivalence on the base field. -/
theorem adjoinTranscendentalEquivOfEquiv_algebraMap
    {E E' : IntermediateField k Ω} (e : E ≃ₐ[k] E')
    {x y : Ω} (hx : Transcendental E x) (hy : Transcendental E' y)
    (z : E) :
    adjoinTranscendentalEquivOfEquiv e hx hy
        (algebraMap E
          (↥(adjoin E (Set.range (![x] : Fin 1 → Ω)))) z) =
      algebraMap E' (↥(adjoin E' (Set.range (![y] : Fin 1 → Ω)))) (e z) := by
  have hx' : AlgebraicIndependent E (![x] : Fin 1 → Ω) := by
    rw [algebraicIndependent_unique_type_iff]
    exact hx
  have hy' : AlgebraicIndependent E' (![y] : Fin 1 → Ω) := by
    rw [algebraicIndependent_unique_type_iff]
    exact hy
  change hy'.aevalEquivField
      ((IsFractionRing.algEquivOfAlgEquiv
        (MvPolynomial.mapAlgEquiv (Fin 1) e))
          (hx'.aevalEquivField.symm
            (algebraMap E
              (↥(adjoin E (Set.range (![x] : Fin 1 → Ω)))) z))) = _
  rw [hx'.aevalEquivField.symm.commutes]
  have hbase :
      algebraMap E (FractionRing (MvPolynomial (Fin 1) E)) z =
        algebraMap (MvPolynomial (Fin 1) E)
          (FractionRing (MvPolynomial (Fin 1) E)) (MvPolynomial.C z) := rfl
  rw [hbase, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  apply Subtype.ext
  rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
  simp

/-- The transcendental extension of a base equivalence sends its displayed
source generator to its displayed target generator. -/
theorem adjoinTranscendentalEquivOfEquiv_generator
    {E E' : IntermediateField k Ω} (e : E ≃ₐ[k] E')
    {x y : Ω} (hx : Transcendental E x) (hy : Transcendental E' y) :
    adjoinTranscendentalEquivOfEquiv e hx hy
        ⟨x, subset_adjoin E _ ⟨0, rfl⟩⟩ =
      ⟨y, subset_adjoin E' _ ⟨0, rfl⟩⟩ := by
  have hx' : AlgebraicIndependent E (![x] : Fin 1 → Ω) := by
    rw [algebraicIndependent_unique_type_iff]
    exact hx
  have hy' : AlgebraicIndependent E' (![y] : Fin 1 → Ω) := by
    rw [algebraicIndependent_unique_type_iff]
    exact hy
  have hxgen : hx'.aevalEquivField
      (algebraMap (MvPolynomial (Fin 1) E)
        (FractionRing (MvPolynomial (Fin 1) E)) (MvPolynomial.X 0)) =
        ⟨x, subset_adjoin E _ ⟨0, rfl⟩⟩ := by
    apply Subtype.ext
    rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
    simp
  change hy'.aevalEquivField
      ((IsFractionRing.algEquivOfAlgEquiv
        (MvPolynomial.mapAlgEquiv (Fin 1) e))
          (hx'.aevalEquivField.symm ⟨x, _⟩)) = _
  rw [← hxgen, hx'.aevalEquivField.symm_apply_apply,
    IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  apply Subtype.ext
  rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
  simp

/-- Equal tuple loci remain equal after adjoining arbitrary generators
that are generic over the respective tuple fields.  This is the exact
base-change principle needed to fix an algebraic parameter realization
first and then choose a fresh family source. -/
theorem idealOf_snoc_eq_of_idealOf_eq_of_generic
    {n : ℕ} {a b : Fin n → Ω} {x y : Ω}
    (hab : idealOf k a = idealOf k b)
    (hx : x ∉ racl k (Set.range a))
    (hy : y ∉ racl k (Set.range b)) :
    idealOf k (Fin.snoc a x) = idealOf k (Fin.snoc b y) := by
  classical
  let E := adjoin k (Set.range a)
  let E' := adjoin k (Set.range b)
  let e : E ≃ₐ[k] E' := locusFunctionFieldEquivOfIdealEq hab
  have hxT : Transcendental E x := by
    change ¬IsAlgebraic E x
    exact fun h ↦ hx ((mem_racl_iff k).2 h)
  have hyT : Transcendental E' y := by
    change ¬IsAlgebraic E' y
    exact fun h ↦ hy ((mem_racl_iff k).2 h)
  let L := adjoin E (Set.range (![x] : Fin 1 → Ω))
  let L' := adjoin E' (Set.range (![y] : Fin 1 → Ω))
  let ex : L ≃ₐ[k] L' := adjoinTranscendentalEquivOfEquiv e hxT hyT
  let ax : Fin (n + 1) → L := Fin.snoc
    (fun i ↦ algebraMap E L
      ⟨a i, subset_adjoin k _ (Set.mem_range_self i)⟩)
    ⟨x, subset_adjoin E _ ⟨0, rfl⟩⟩
  let bx : Fin (n + 1) → L' := Fin.snoc
    (fun i ↦ algebraMap E' L'
      ⟨b i, subset_adjoin k _ (Set.mem_range_self i)⟩)
    ⟨y, subset_adjoin E' _ ⟨0, rfl⟩⟩
  have hax (j : Fin (n + 1)) : (ax j : Ω) =
      (Fin.snoc a x : Fin (n + 1) → Ω) j := by
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp [ax]
    · simp [ax]
  have hbx (j : Fin (n + 1)) : (bx j : Ω) =
      (Fin.snoc b y : Fin (n + 1) → Ω) j := by
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp [bx]
    · simp [bx]
  have hcoord (j : Fin (n + 1)) : ex (ax j) = bx j := by
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simpa only [ex, ax, bx, Fin.snoc_last] using
        adjoinTranscendentalEquivOfEquiv_generator e hxT hyT
    · have hei : e ⟨a i, subset_adjoin k _ (Set.mem_range_self i)⟩ =
          ⟨b i, subset_adjoin k _ (Set.mem_range_self i)⟩ :=
        locusFunctionFieldEquivOfIdealEq_apply hab i
      have hbase := adjoinTranscendentalEquivOfEquiv_algebraMap e hxT hyT
        ⟨a i, subset_adjoin k _ (Set.mem_range_self i)⟩
      rw [hei] at hbase
      simpa only [ex, ax, bx, Fin.snoc_castSucc] using hbase
  ext p
  rw [mem_idealOf_iff, mem_idealOf_iff]
  have ha : MvPolynomial.aeval (Fin.snoc a x) p =
      L.val (MvPolynomial.aeval ax p) := by
    have hhom : (L.val.restrictScalars k).comp (MvPolynomial.aeval ax) =
        MvPolynomial.aeval (Fin.snoc a x) := by
      apply MvPolynomial.algHom_ext
      intro j
      simpa using hax j
    exact congrArg (fun q ↦ q p) hhom.symm
  have hb : MvPolynomial.aeval (Fin.snoc b y) p =
      L'.val (MvPolynomial.aeval bx p) := by
    have hhom : (L'.val.restrictScalars k).comp (MvPolynomial.aeval bx) =
        MvPolynomial.aeval (Fin.snoc b y) := by
      apply MvPolynomial.algHom_ext
      intro j
      simpa using hbx j
    exact congrArg (fun q ↦ q p) hhom.symm
  have heval : MvPolynomial.aeval bx p = ex (MvPolynomial.aeval ax p) := by
    have hhom : ex.toAlgHom.comp (MvPolynomial.aeval ax) =
        MvPolynomial.aeval bx := by
      apply MvPolynomial.algHom_ext
      intro j
      simpa using hcoord j
    exact congrArg (fun q ↦ q p) hhom.symm
  rw [ha, hb, heval]
  constructor
  · intro hz
    have hz' :
        (MvPolynomial.aeval ax :
          MvPolynomial (Fin (n + 1)) k →ₐ[k] L) p = 0 := by
      apply L.val.injective
      change L.val
          ((MvPolynomial.aeval ax :
            MvPolynomial (Fin (n + 1)) k →ₐ[k] L) p) = L.val 0
      rw [map_zero]
      exact hz
    rw [hz', map_zero]
    rfl
  · intro hz
    have hz' : ex
        ((MvPolynomial.aeval ax :
          MvPolynomial (Fin (n + 1)) k →ₐ[k] L) p) = 0 := by
      apply L'.val.injective
      change L'.val (ex
          ((MvPolynomial.aeval ax :
            MvPolynomial (Fin (n + 1)) k →ₐ[k] L) p)) = L'.val 0
      rw [map_zero]
      exact hz
    have :
        (MvPolynomial.aeval ax :
          MvPolynomial (Fin (n + 1)) k →ₐ[k] L) p = 0 :=
      ex.injective (by simpa using hz')
    rw [this]
    rfl

/-- Relocate a finite algebraic tuple while fixing an arbitrary coordinate
subtuple whose complete locus has already been relocated.  Unlike
`exists_tuple_relocation_fixing`, the fixed subtuple need not be
independent: equality of its prime ideal supplies the base-field
equivalence, which is then extended across the algebraic full tuple. -/
theorem exists_tuple_relocation_fixing_locus [IsAlgClosed Ω] {n m : ℕ}
    {t s : Fin n → Ω} {u : Fin m → Ω} {e : Fin n → Fin m}
    (hI : idealOf k s = idealOf k t)
    (he : ∀ i, u (e i) = t i)
    (hu : ∀ j, u j ∈ racl k (Set.range t)) :
    ∃ v : Fin m → Ω,
      idealOf k v = idealOf k u ∧ ∀ i, v (e i) = s i := by
  classical
  let E := adjoin k (Set.range t)
  let E' := adjoin k (Set.range u)
  let F := adjoin k (Set.range s)
  have hle : E ≤ E' := by
    apply adjoin.mono
    rintro _ ⟨i, rfl⟩
    exact ⟨e i, he i⟩
  have halg : Algebra.IsAlgebraic (↥E) (↥(extendScalars hle)) := by
    apply isAlgebraic_extendScalars_adjoin hle
    rintro _ ⟨j, rfl⟩
    exact (mem_racl_iff k).1 (hu j)
  let φ : E →ₐ[k] Ω := F.val.comp
    (locusFunctionFieldEquivOfIdealEq hI.symm).toAlgHom
  obtain ⟨ψ, hψ⟩ := exists_extension_of_isAlgebraic
    (halg := halg) hle φ
  have huMem (j : Fin m) : u j ∈ E' :=
    subset_adjoin k _ (Set.mem_range_self j)
  let ua : Fin m → E' := fun j ↦ ⟨u j, huMem j⟩
  let v : Fin m → Ω := fun j ↦ ψ (ua j)
  have hfix (i : Fin n) : v (e i) = s i := by
    have hmem : t i ∈ E := subset_adjoin k _ ⟨i, rfl⟩
    have hua : ua (e i) = ⟨t i, hle hmem⟩ := by
      apply Subtype.ext
      exact he i
    change ψ (ua (e i)) = s i
    rw [hua]
    calc
      ψ ⟨t i, hle hmem⟩ = φ ⟨t i, hmem⟩ := hψ ⟨t i, hmem⟩
      _ = s i := by
        change ↑(locusFunctionFieldEquivOfIdealEq hI.symm
          ⟨t i, subset_adjoin k _ (Set.mem_range_self i)⟩) = s i
        rw [locusFunctionFieldEquivOfIdealEq_apply]
  refine ⟨v, ?_, hfix⟩
  ext p
  rw [mem_idealOf_iff, mem_idealOf_iff]
  have h1 : MvPolynomial.aeval v p = ψ (MvPolynomial.aeval ua p) := by
    change MvPolynomial.aeval (fun j ↦ ψ (ua j)) p = _
    rw [MvPolynomial.comp_aeval_apply]
  have h2 : MvPolynomial.aeval u p = E'.val (MvPolynomial.aeval ua p) := by
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  rw [h1, h2]
  constructor
  · intro hz
    have hp : ψ (MvPolynomial.aeval ua p) = ψ 0 := by
      rw [map_zero]
      exact hz
    rw [ψ.injective hp, map_zero]
  · intro hz
    have hp : E'.val (MvPolynomial.aeval ua p) = E'.val 0 := by
      rw [map_zero]
      exact hz
    rw [E'.val.injective hp, map_zero]

/-- Relocate a one-element algebraic extension while fixing its entire
independent transcendence prefix.  If `u` is algebraic over `k(t)`, then
for every equally long independent tuple `s` there is `v` such that
`(s,v)` and `(t,u)` have the same vanishing ideal over `k`. -/
theorem exists_snoc_relocation_fixing [IsAlgClosed Ω] {n : ℕ}
    {t s : Fin n → Ω} {u : Ω}
    (ht : AlgebraicIndependent k t) (hs : AlgebraicIndependent k s)
    (hu : u ∈ racl k (Set.range t)) :
    ∃ v : Ω, idealOf k (Fin.snoc s v) = idealOf k (Fin.snoc t u) := by
  classical
  let E := adjoin k (Set.range t)
  let L := adjoin k (Set.range (Fin.snoc t u))
  have hle : E ≤ L := by
    apply adjoin.mono
    rw [Fin.range_snoc]
    exact Set.subset_insert u _
  have halg : Algebra.IsAlgebraic (↥E) (↥(extendScalars hle)) := by
    apply isAlgebraic_extendScalars_adjoin hle
    intro x hx
    rw [Fin.range_snoc] at hx
    rcases hx with rfl | hx
    · exact (mem_racl_iff k).1 hu
    · have hxE : x ∈ E := subset_adjoin k _ hx
      exact isAlgebraic_algebraMap (R := ↥E) (A := Ω) ⟨x, hxE⟩
  obtain ⟨ψ, hψ⟩ := exists_extension_of_isAlgebraic
    (halg := halg) hle (adjoinTranscendentalAlgHom ht hs)
  have htaMem (j : Fin n.succ) :
      (Fin.snoc t u : Fin n.succ → Ω) j ∈
        (adjoin k (Set.range (Fin.snoc t u : Fin n.succ → Ω)) :
          IntermediateField k Ω) :=
    subset_adjoin k _ (Set.mem_range_self j)
  let ta : Fin n.succ → ↥L :=
    fun j ↦ ⟨(Fin.snoc t u : Fin n.succ → Ω) j, htaMem j⟩
  let v : Ω := ψ (ta (Fin.last n))
  have hprefix (i : Fin n) : ψ (ta i.castSucc) = s i := by
    have hmem : t i ∈ E := subset_adjoin k _ ⟨i, rfl⟩
    have hta : ta i.castSucc = ⟨t i, hle hmem⟩ := by
      apply Subtype.ext
      simp [ta]
    rw [hta, hψ ⟨t i, hmem⟩]
    exact adjoinTranscendentalAlgHom_apply ht hs i
  have htuple : Fin.snoc s v = fun j ↦ ψ (ta j) := by
    funext j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp [v]
    · simpa using (hprefix i).symm
  refine ⟨v, ?_⟩
  rw [htuple]
  ext f
  rw [mem_idealOf_iff, mem_idealOf_iff]
  have h1 : MvPolynomial.aeval (fun j ↦ ψ (ta j)) f =
      ψ (MvPolynomial.aeval ta f) := by
    rw [MvPolynomial.comp_aeval_apply]
  have h2 : MvPolynomial.aeval (Fin.snoc t u) f =
      L.val (MvPolynomial.aeval ta f) := by
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  rw [h1, h2]
  constructor
  · intro hz
    have ha : ψ (MvPolynomial.aeval ta f) = ψ 0 := by
      rw [map_zero]
      exact hz
    rw [ψ.injective ha, map_zero]
  · intro hz
    have ha : L.val (MvPolynomial.aeval ta f) = L.val 0 := by
      rw [map_zero]
      exact hz
    rw [L.val.injective ha, map_zero]

/-- A generic member `(parameter, source, target)` of a
finite-correspondence family of parameter dimension `d`. -/
structure FiniteCorrespondenceFamilyMember (d : ℕ) where
  /-- The generic family parameter. -/
  parameter : Fin d → Ω
  /-- The source coordinate of the selected generic branch. -/
  source : Ω
  /-- The target coordinate of the selected generic branch. -/
  target : Ω
  /-- The parameter coordinates are algebraically independent. -/
  parameter_independent : AlgebraicIndependent k parameter
  /-- The source is generic over the parameter field. -/
  source_generic : source ∉ racl k (Set.range parameter)
  /-- The target is algebraic over the parameter and source. -/
  target_mem_parameter_source :
    target ∈ racl k (insert source (Set.range parameter))
  /-- The source is algebraic over the parameter and target. -/
  source_mem_parameter_target :
    source ∈ racl k (insert target (Set.range parameter))

namespace FiniteCorrespondenceFamilyMember

variable {d : ℕ} (F : FiniteCorrespondenceFamilyMember (k := k) (Ω := Ω) d)

/-- Transport a generic family member along an embedding of its ambient
field.  Algebraic independence and both relative-algebraicity conditions
are invariant under the embedding. -/
def map {Ω' : Type*} [Field Ω'] [Algebra k Ω'] (σ : Ω →ₐ[k] Ω') :
    FiniteCorrespondenceFamilyMember (k := k) (Ω := Ω') d where
  parameter := σ ∘ F.parameter
  source := σ F.source
  target := σ F.target
  parameter_independent := F.parameter_independent.map' σ.injective
  source_generic := by
    intro hmem
    rw [Set.range_comp] at hmem
    exact F.source_generic ((algHom_mem_racl_image_iff σ).1 hmem)
  target_mem_parameter_source := by
    have h := (algHom_mem_racl_image_iff σ).2
      F.target_mem_parameter_source
    rw [Set.image_insert_eq, ← Set.range_comp] at h
    exact h
  source_mem_parameter_target := by
    have h := (algHom_mem_racl_image_iff σ).2
      F.source_mem_parameter_target
    rw [Set.image_insert_eq, ← Set.range_comp] at h
    exact h

/-- The coefficient field generated by the family parameter. -/
def parameterField : IntermediateField k Ω :=
  adjoin k (Set.range F.parameter)

/-- The independent parameter/source prefix of the generic family
member. -/
def parameterSource : Fin (d + 1) → Ω :=
  Fin.snoc F.parameter F.source

/-- The full generic family tuple `(parameter, source, target)`. -/
def tuple : Fin (d + 2) → Ω :=
  Fin.snoc F.parameterSource F.target

/-- The prime ideal of the total family locus. -/
def ideal : Ideal (MvPolynomial (Fin (d + 2)) k) :=
  idealOf k F.tuple

/-- Rebuild a family member of arbitrary parameter dimension from a tuple
with the same complete family ideal and an independent parameter/source
prefix.  The two relative algebraicity conditions transfer through the
complete locus equality. -/
def ofTupleIdealEq
    (F : FiniteCorrespondenceFamilyMember (k := k) (Ω := Ω) d)
    {p : Fin d → Ω} {x y : Ω}
    (hpx : AlgebraicIndependent k (Fin.snoc p x))
    (hI : idealOf k (Fin.snoc (Fin.snoc p x) y) = F.ideal) :
    FiniteCorrespondenceFamilyMember (k := k) (Ω := Ω) d where
  parameter := p
  source := x
  target := y
  parameter_independent := by
    have h := AlgebraicIndependent.comp hpx
      (Fin.castSucc : Fin d → Fin (d + 1)) (Fin.castSucc_injective d)
    convert h using 1
    funext i
    simp
  source_generic := by
    let e : Fin d → Fin (d + 1) := Fin.castSucc
    have hnot := AlgebraicIndependent.notMem_racl_image hpx
      (S := Set.range e) (i := Fin.last d) (by
        rintro ⟨i, hi⟩
        exact Fin.castSucc_ne_last i hi)
    have himage :
        (Fin.snoc p x : Fin (d + 1) → Ω) '' Set.range e =
          Set.range p := by
      rw [← Set.range_comp]
      congr 1
      funext i
      simp [e]
    simpa [himage] using hnot
  target_mem_parameter_source := by
    let q : Fin (d + 2) → Ω := Fin.snoc (Fin.snoc p x) y
    let e : Fin (d + 1) → Fin (d + 2) := Fin.castSucc
    have hfull : idealOf k F.tuple = idealOf k q := by
      simpa [ideal, q] using hI.symm
    have himageF : F.tuple '' Set.range e =
        Set.range F.parameterSource := by
      rw [← Set.range_comp]
      congr 1
      funext i
      simp [e, tuple, parameterSource]
    have hmem : F.tuple (Fin.last (d + 1)) ∈
        racl k (F.tuple '' Set.range e) := by
      rw [himageF, parameterSource, Fin.range_snoc]
      simpa [tuple] using F.target_mem_parameter_source
    have ht := mem_racl_image_of_idealOf_eq k hfull hmem
    have himage : q '' Set.range e =
        Set.range (Fin.snoc p x) := by
      rw [← Set.range_comp]
      congr 1
      funext i
      simp [q, e]
    rw [himage, Fin.range_snoc] at ht
    simpa [q] using ht

  source_mem_parameter_target := by
    let q : Fin (d + 2) → Ω := Fin.snoc (Fin.snoc p x) y
    let e : Fin (d + 1) → Fin (d + 2) :=
      Fin.snoc (fun i : Fin d ↦ i.castSucc.castSucc) (Fin.last (d + 1))
    have hfull : idealOf k F.tuple = idealOf k q := by
      simpa [ideal, q] using hI.symm
    have hcompF : F.tuple ∘ e = Fin.snoc F.parameter F.target := by
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp [e, tuple]
      · simp [e, tuple, parameterSource]
    have himageF : F.tuple '' Set.range e =
        Set.range (Fin.snoc F.parameter F.target) := by
      rw [← Set.range_comp, hcompF]
    have hmem : F.tuple (Fin.last d).castSucc ∈
        racl k (F.tuple '' Set.range e) := by
      rw [himageF, Fin.range_snoc]
      simpa [tuple, parameterSource] using
        F.source_mem_parameter_target
    have ht := mem_racl_image_of_idealOf_eq k hfull hmem
    have hcomp : q ∘ e = Fin.snoc p y := by
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp [q, e]
      · simp [q, e]
    have himage : q '' Set.range e = Set.range (Fin.snoc p y) := by
      rw [← Set.range_comp, hcomp]
    rw [himage, Fin.range_snoc] at ht
    simpa [q] using ht

/-- Rebuild a family member from equality of the complete family locus
alone.  Independence of the parameter/source prefix is itself a property
of that locus and is therefore transferred automatically. -/
def ofTupleIdealEqOnly
    (F : FiniteCorrespondenceFamilyMember (k := k) (Ω := Ω) d)
    {p : Fin d → Ω} {x y : Ω}
    (hI : idealOf k (Fin.snoc (Fin.snoc p x) y) = F.ideal) :
    FiniteCorrespondenceFamilyMember (k := k) (Ω := Ω) d := by
  let q : Fin (d + 2) → Ω := Fin.snoc (Fin.snoc p x) y
  let eParameter : Fin d → Fin (d + 2) :=
    fun i ↦ i.castSucc.castSucc
  have hparameter : idealOf k p = idealOf k F.parameter := by
    have h := idealOf_comp_eq_of_idealOf_eq hI eParameter
    calc
      idealOf k p = idealOf k (q ∘ eParameter) := by
        congr 1
        funext i
        simp [q, eParameter]
      _ = idealOf k (F.tuple ∘ eParameter) := h
      _ = idealOf k F.parameter := by
        congr 1
        funext i
        simp [tuple, parameterSource, eParameter]
  have hp : AlgebraicIndependent k p := by
    rw [← idealOf_eq_bot_iff, hparameter, idealOf_eq_bot_iff]
    exact F.parameter_independent
  have hfull : idealOf k F.tuple = idealOf k q := by
    simpa [ideal, q] using hI.symm
  have hsourceF : F.tuple (Fin.last d).castSucc ∉
      racl k (F.tuple '' Set.range eParameter) := by
    have himage : F.tuple '' Set.range eParameter =
        Set.range F.parameter := by
      rw [← Set.range_comp]
      congr 1
      funext i
      simp [eParameter, tuple, parameterSource]
    rw [himage]
    simpa [tuple, parameterSource] using F.source_generic
  have hsourceQ := notMem_racl_image_of_idealOf_eq k hfull hsourceF
  have himageQ : q '' Set.range eParameter = Set.range p := by
    rw [← Set.range_comp]
    congr 1
    funext i
    simp [q, eParameter]
  rw [himageQ] at hsourceQ
  have hx : x ∉ racl k (Set.range p) := by
    simpa [q] using hsourceQ
  exact F.ofTupleIdealEq (algebraicIndependent_snoc hp hx) hI

/-- Rebuild a one-parameter family member from any triple with the same
complete family ideal and an independent parameter/source pair. -/
def ofOneTupleIdealEq
    (F : FiniteCorrespondenceFamilyMember (k := k) (Ω := Ω) 1)
    {p x y : Ω} (hpx : AlgebraicIndependent k ![p, x])
    (hI : idealOf k ![p, x, y] = F.ideal) :
    FiniteCorrespondenceFamilyMember (k := k) (Ω := Ω) 1 where
  parameter := ![p]
  source := x
  target := y
  parameter_independent := by
    have h := AlgebraicIndependent.comp hpx
      (![0] : Fin 1 → Fin 2) (by decide)
    simpa using h
  source_generic := by
    simpa [Matrix.range_cons, Matrix.range_empty] using
      AlgebraicIndependent.notMem_racl_pair hpx
  target_mem_parameter_source := by
    have hfull : idealOf k F.tuple = idealOf k ![p, x, y] := by
      simpa [ideal] using hI.symm
    have himage : F.tuple '' ({0, 1} : Set (Fin 3)) =
        insert F.source (Set.range F.parameter) := by
      ext z
      constructor
      · rintro ⟨i, hi, rfl⟩
        fin_cases i
        · exact Set.mem_insert_of_mem _ ⟨0, rfl⟩
        · exact Set.mem_insert _ _
        · simp at hi
      · intro hz
        rw [Set.mem_insert_iff] at hz
        rcases hz with rfl | ⟨i, rfl⟩
        · exact ⟨1, by simp, rfl⟩
        · have hi : i = 0 := Subsingleton.elim _ _
          subst i
          exact ⟨0, by simp, rfl⟩
    have hmem : F.tuple 2 ∈ racl k (F.tuple '' ({0, 1} : Set (Fin 3))) := by
      rw [himage]
      exact F.target_mem_parameter_source
    have htrans := mem_racl_image_of_idealOf_eq k hfull hmem
    have himage' : (![p, x, y] : Fin 3 → Ω) '' ({0, 1} : Set (Fin 3)) =
        ({p, x} : Set Ω) := by
      ext z
      simp
      tauto
    rw [himage'] at htrans
    simpa [Matrix.range_cons, Matrix.range_empty, Set.pair_comm] using htrans
  source_mem_parameter_target := by
    have hfull : idealOf k F.tuple = idealOf k ![p, x, y] := by
      simpa [ideal] using hI.symm
    have himage : F.tuple '' ({0, 2} : Set (Fin 3)) =
        insert F.target (Set.range F.parameter) := by
      ext z
      constructor
      · rintro ⟨i, hi, rfl⟩
        fin_cases i
        · exact Set.mem_insert_of_mem _ ⟨0, rfl⟩
        · simp at hi
        · exact Set.mem_insert _ _
      · intro hz
        rw [Set.mem_insert_iff] at hz
        rcases hz with rfl | ⟨i, rfl⟩
        · exact ⟨2, by simp, rfl⟩
        · have hi : i = 0 := Subsingleton.elim _ _
          subst i
          exact ⟨0, by simp, rfl⟩
    have hmem : F.tuple 1 ∈ racl k (F.tuple '' ({0, 2} : Set (Fin 3))) := by
      rw [himage]
      exact F.source_mem_parameter_target
    have htrans := mem_racl_image_of_idealOf_eq k hfull hmem
    have himage' : (![p, x, y] : Fin 3 → Ω) '' ({0, 2} : Set (Fin 3)) =
        ({p, y} : Set Ω) := by
      ext z
      simp
      tauto
    rw [himage'] at htrans
    simpa [Matrix.range_cons, Matrix.range_empty, Set.pair_comm] using htrans

/-- The parameter and source form an algebraically independent tuple. -/
theorem parameterSource_independent :
    AlgebraicIndependent k F.parameterSource :=
  algebraicIndependent_snoc F.parameter_independent F.source_generic

/-- A generic family member specializes to a finite-correspondence pair
over its parameter field. -/
def toPair : FiniteCorrespondencePair (↥F.parameterField) Ω where
  source := F.source
  target := F.target
  source_generic := by
    rw [parameterField, mem_racl_adjoin_base_iff, Set.union_empty]
    exact F.source_generic
  target_mem_source := by
    rw [parameterField, mem_racl_adjoin_base_iff, Set.union_singleton]
    exact F.target_mem_parameter_source
  source_mem_target := by
    rw [parameterField, mem_racl_adjoin_base_iff, Set.union_singleton]
    exact F.source_mem_parameter_target

/-- The full family tuple is algebraic over its independent
parameter/source prefix. -/
theorem target_mem_parameterSource :
    F.target ∈ racl k (Set.range F.parameterSource) := by
  rw [parameterSource, Fin.range_snoc]
  exact F.target_mem_parameter_source

/-- A family locus can be relocated above any independent generic
parameter/source prefix, while preserving its complete prime ideal. -/
theorem exists_relocation [IsAlgClosed Ω] {q : Fin d → Ω} {x : Ω}
    (hqx : AlgebraicIndependent k (Fin.snoc q x)) :
    ∃ y : Ω,
      idealOf k (Fin.snoc (Fin.snoc q x) y) = F.ideal := by
  simpa [ideal, tuple, parameterSource] using
    exists_snoc_relocation_fixing F.parameterSource_independent hqx
      F.target_mem_parameterSource

end FiniteCorrespondenceFamilyMember

/-- A generically finite ternary correspondence serving as the graph of
a multiplication law.  Every two displayed coordinates are independent,
and the remaining coordinate is algebraic over them.  Thus the same locus
can be read in all three directions: multiplication and the two division
problems.  No single-valuedness is asserted at this stage. -/
structure FiniteCorrespondenceMultiplication where
  /-- The left input of the generic multiplication relation. -/
  left : Ω
  /-- The right input of the generic multiplication relation. -/
  right : Ω
  /-- The output of the generic multiplication relation. -/
  output : Ω
  /-- The two inputs are independent generic parameters. -/
  leftRight_independent : AlgebraicIndependent k ![left, right]
  /-- The left input and output are independent generic parameters. -/
  leftOutput_independent : AlgebraicIndependent k ![left, output]
  /-- The right input and output are independent generic parameters. -/
  rightOutput_independent : AlgebraicIndependent k ![right, output]
  /-- The output is finite over the two inputs. -/
  output_mem_left_right : output ∈ racl k ({left, right} : Set Ω)
  /-- The right input is finite over the left input and output. -/
  right_mem_left_output : right ∈ racl k ({left, output} : Set Ω)
  /-- The left input is finite over the right input and output. -/
  left_mem_right_output : left ∈ racl k ({right, output} : Set Ω)

namespace FiniteCorrespondenceMultiplication

variable (M : FiniteCorrespondenceMultiplication (k := k) (Ω := Ω))

/-- The generic triple `(left, right, output)`. -/
def tuple : Fin 3 → Ω := ![M.left, M.right, M.output]

/-- The prime ideal of the ternary multiplication locus. -/
def ideal : Ideal (MvPolynomial (Fin 3) k) := idealOf k M.tuple

/-- A displayed triple lies on the ternary multiplication locus. -/
def IsRealization (a b c : Ω) : Prop :=
  idealOf k ![a, b, c] = M.ideal

namespace IsRealization

variable {M : FiniteCorrespondenceMultiplication (k := k) (Ω := Ω)}
  {a b c : Ω} (h : M.IsRealization a b c)

include h

/-- Every realization retains independence of its two inputs. -/
theorem leftRight_independent : AlgebraicIndependent k ![a, b] := by
  let e : Fin 2 → Fin 3 := ![0, 1]
  have hfull : idealOf k M.tuple = idealOf k ![a, b, c] := by
    simpa [IsRealization, ideal] using h.symm
  have hsource : AlgebraicIndependent k (M.tuple ∘ e) := by
    convert M.leftRight_independent using 1
    funext i
    fin_cases i <;> rfl
  have ht := algebraicIndependent_comp_of_idealOf_eq hfull e
    hsource
  convert ht using 1
  funext i
  fin_cases i <;> rfl

/-- Every realization retains independence of its left input and output. -/
theorem leftOutput_independent : AlgebraicIndependent k ![a, c] := by
  let e : Fin 2 → Fin 3 := ![0, 2]
  have hfull : idealOf k M.tuple = idealOf k ![a, b, c] := by
    simpa [IsRealization, ideal] using h.symm
  have hsource : AlgebraicIndependent k (M.tuple ∘ e) := by
    convert M.leftOutput_independent using 1
    funext i
    fin_cases i <;> rfl
  have ht := algebraicIndependent_comp_of_idealOf_eq hfull e
    hsource
  convert ht using 1
  funext i
  fin_cases i <;> rfl

/-- Every realization retains independence of its right input and output. -/
theorem rightOutput_independent : AlgebraicIndependent k ![b, c] := by
  let e : Fin 2 → Fin 3 := ![1, 2]
  have hfull : idealOf k M.tuple = idealOf k ![a, b, c] := by
    simpa [IsRealization, ideal] using h.symm
  have hsource : AlgebraicIndependent k (M.tuple ∘ e) := by
    convert M.rightOutput_independent using 1
    funext i
    fin_cases i <;> rfl
  have ht := algebraicIndependent_comp_of_idealOf_eq hfull e
    hsource
  convert ht using 1
  funext i
  fin_cases i <;> rfl

/-- In every realization the output is algebraic over the two inputs. -/
theorem output_mem_left_right : c ∈ racl k ({a, b} : Set Ω) := by
  have hfull : idealOf k M.tuple = idealOf k ![a, b, c] := by
    simpa [IsRealization, ideal] using h.symm
  have himageM : M.tuple '' ({0, 1} : Set (Fin 3)) =
      ({M.left, M.right} : Set Ω) := by
    ext z
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp [tuple] at hi ⊢
    · rintro (rfl | rfl)
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨1, by simp, rfl⟩
  have ho : M.tuple 2 ∈
      racl k (M.tuple '' ({0, 1} : Set (Fin 3))) := by
    rw [himageM]
    exact M.output_mem_left_right
  have ht := mem_racl_image_of_idealOf_eq k hfull ho
  have himage : (![a, b, c] : Fin 3 → Ω) '' ({0, 1} : Set (Fin 3)) =
      ({a, b} : Set Ω) := by
    ext z
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp at hi ⊢
    · rintro (rfl | rfl)
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨1, by simp, rfl⟩
  rwa [himage] at ht

/-- In every realization the right input is algebraic over the left input
and output. -/
theorem right_mem_left_output : b ∈ racl k ({a, c} : Set Ω) := by
  have hfull : idealOf k M.tuple = idealOf k ![a, b, c] := by
    simpa [IsRealization, ideal] using h.symm
  have himageM : M.tuple '' ({0, 2} : Set (Fin 3)) =
      ({M.left, M.output} : Set Ω) := by
    ext z
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp [tuple] at hi ⊢
    · rintro (rfl | rfl)
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨2, by simp, rfl⟩
  have ho : M.tuple 1 ∈
      racl k (M.tuple '' ({0, 2} : Set (Fin 3))) := by
    rw [himageM]
    exact M.right_mem_left_output
  have ht := mem_racl_image_of_idealOf_eq k hfull ho
  have himage : (![a, b, c] : Fin 3 → Ω) '' ({0, 2} : Set (Fin 3)) =
      ({a, c} : Set Ω) := by
    ext z
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp at hi ⊢
    · rintro (rfl | rfl)
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨2, by simp, rfl⟩
  rwa [himage] at ht

/-- In every realization the left input is algebraic over the right input
and output. -/
theorem left_mem_right_output : a ∈ racl k ({b, c} : Set Ω) := by
  have hfull : idealOf k M.tuple = idealOf k ![a, b, c] := by
    simpa [IsRealization, ideal] using h.symm
  have himageM : M.tuple '' ({1, 2} : Set (Fin 3)) =
      ({M.right, M.output} : Set Ω) := by
    ext z
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp [tuple] at hi ⊢
    · rintro (rfl | rfl)
      · exact ⟨1, by simp, rfl⟩
      · exact ⟨2, by simp, rfl⟩
  have ho : M.tuple 0 ∈
      racl k (M.tuple '' ({1, 2} : Set (Fin 3))) := by
    rw [himageM]
    exact M.left_mem_right_output
  have ht := mem_racl_image_of_idealOf_eq k hfull ho
  have himage : (![a, b, c] : Fin 3 → Ω) '' ({1, 2} : Set (Fin 3)) =
      ({b, c} : Set Ω) := by
    ext z
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp at hi ⊢
    · rintro (rfl | rfl)
      · exact ⟨1, by simp, rfl⟩
      · exact ⟨2, by simp, rfl⟩
  rwa [himage] at ht

/-- Any two coordinate pairs in a realization generate the same relative
algebraic closure. -/
theorem racl_leftRight_eq_leftOutput :
    racl k ({a, b} : Set Ω) = racl k ({a, c} : Set Ω) := by
  refine racl_congr_of_subset_racl ?_ ?_
  · rintro z (rfl | rfl)
    · exact subset_racl k _ (by simp)
    · exact h.right_mem_left_output
  · rintro z (rfl | rfl)
    · exact subset_racl k _ (by simp)
    · exact h.output_mem_left_right

/-- The right-input/output pair generates the same closure as the input
pair in every realization. -/
theorem racl_leftRight_eq_rightOutput :
    racl k ({a, b} : Set Ω) = racl k ({b, c} : Set Ω) := by
  refine racl_congr_of_subset_racl ?_ ?_
  · rintro z (rfl | rfl)
    · exact h.left_mem_right_output
    · exact subset_racl k _ (by simp)
  · rintro z (rfl | rfl)
    · exact subset_racl k _ (by simp)
    · exact h.output_mem_left_right

end IsRealization

/-- The multiplication locus has a point over every independent generic
pair of inputs. -/
theorem exists_output [IsAlgClosed Ω] {a b : Ω}
    (hab : AlgebraicIndependent k ![a, b]) :
    ∃ c : Ω, idealOf k ![a, b, c] = M.ideal := by
  have hrange : Set.range (![M.left, M.right] : Fin 2 → Ω) =
      ({M.left, M.right} : Set Ω) := by
    ext z
    simp
    tauto
  have hmem : M.output ∈
      racl k (Set.range (![M.left, M.right] : Fin 2 → Ω)) := by
    rw [hrange]
    exact M.output_mem_left_right
  simpa [ideal, tuple] using
    exists_snoc_relocation_fixing M.leftRight_independent hab hmem

/-- The multiplication locus has a point over every independent generic
left-input/output pair, solving the right-division problem. -/
theorem exists_right [IsAlgClosed Ω] {a c : Ω}
    (hac : AlgebraicIndependent k ![a, c]) :
    ∃ b : Ω, idealOf k ![a, b, c] = M.ideal := by
  classical
  let e : Fin 2 → Fin 3 := ![0, 2]
  have he (i : Fin 2) : M.tuple (e i) = (![M.left, M.output] : Fin 2 → Ω) i := by
    fin_cases i <;> rfl
  have hmem (j : Fin 3) :
      M.tuple j ∈ racl k (Set.range (![M.left, M.output] : Fin 2 → Ω)) := by
    have hrange : Set.range (![M.left, M.output] : Fin 2 → Ω) =
        ({M.left, M.output} : Set Ω) := by
      ext z
      simp
      tauto
    rw [hrange]
    fin_cases j
    · exact subset_racl k _ (by simp [tuple])
    · exact M.right_mem_left_output
    · exact subset_racl k _ (by simp [tuple])
  obtain ⟨v, hv, hfix⟩ := exists_tuple_relocation_fixing
    M.leftOutput_independent hac he hmem
  refine ⟨v 1, ?_⟩
  have hvtuple : v = ![a, v 1, c] := by
    funext i
    fin_cases i
    · exact hfix 0
    · rfl
    · exact hfix 1
  change idealOf k ![a, v 1, c] = idealOf k M.tuple
  rw [← hvtuple]
  exact hv

/-- The multiplication locus has a point over every independent generic
right-input/output pair, solving the left-division problem. -/
theorem exists_left [IsAlgClosed Ω] {b c : Ω}
    (hbc : AlgebraicIndependent k ![b, c]) :
    ∃ a : Ω, idealOf k ![a, b, c] = M.ideal := by
  classical
  let e : Fin 2 → Fin 3 := ![1, 2]
  have he (i : Fin 2) : M.tuple (e i) = (![M.right, M.output] : Fin 2 → Ω) i := by
    fin_cases i <;> rfl
  have hmem (j : Fin 3) :
      M.tuple j ∈ racl k (Set.range (![M.right, M.output] : Fin 2 → Ω)) := by
    have hrange : Set.range (![M.right, M.output] : Fin 2 → Ω) =
        ({M.right, M.output} : Set Ω) := by
      ext z
      simp
      tauto
    rw [hrange]
    fin_cases j
    · exact M.left_mem_right_output
    · exact subset_racl k _ (by simp [tuple])
    · exact subset_racl k _ (by simp [tuple])
  obtain ⟨v, hv, hfix⟩ := exists_tuple_relocation_fixing
    M.rightOutput_independent hbc he hmem
  refine ⟨v 0, ?_⟩
  have hvtuple : v = ![v 0, b, c] := by
    funext i
    fin_cases i
    · rfl
    · exact hfix 0
    · exact hfix 1
  change idealOf k ![v 0, b, c] = idealOf k M.tuple
  rw [← hvtuple]
  exact hv

/-- The four multiplication/division edges used by the group-configuration
difference chart.  In blueprint notation these fields satisfy the four
prime-locus relations

`u = s · e`, `sA · a = u`, `uB = s · b`, and `sA · c = uB`.

The notation is relational: a finite correspondence need not yet be a
single-valued operation. -/
structure FourArrowDifferenceDiagram (s a b e : Ω) where
  /-- A selected output of `s · e`. -/
  u : Ω
  /-- A selected left quotient solving `sA · a = u`. -/
  sA : Ω
  /-- A selected output of `s · b`. -/
  uB : Ω
  /-- The selected difference-chart output solving `sA · c = uB`. -/
  c : Ω
  /-- The edge `u = s · e`. -/
  se_u : M.IsRealization s e u
  /-- The edge `sA · a = u`. -/
  sA_a_u : M.IsRealization sA a u
  /-- The edge `uB = s · b`. -/
  s_b_uB : M.IsRealization s b uB
  /-- The edge `sA · c = uB`. -/
  sA_c_uB : M.IsRealization sA c uB

namespace FourArrowDifferenceDiagram

variable {M} {s a b e : Ω}
  (D : M.FourArrowDifferenceDiagram s a b e)

/-- The first selected product is algebraic over the four inputs. -/
theorem u_mem_inputs : D.u ∈ racl k ({s, e, a, b} : Set Ω) :=
  racl_mono (by intro z hz; simp at hz ⊢; tauto)
    D.se_u.output_mem_left_right

/-- The selected left quotient is algebraic over the four inputs. -/
theorem sA_mem_inputs : D.sA ∈ racl k ({s, e, a, b} : Set Ω) := by
  refine racl_le_of_subset_racl ?_ D.sA_a_u.left_mem_right_output
  rintro z (rfl | rfl)
  · exact subset_racl k _ (by simp)
  · exact D.u_mem_inputs

/-- The second selected product is algebraic over the four inputs. -/
theorem uB_mem_inputs : D.uB ∈ racl k ({s, e, a, b} : Set Ω) :=
  racl_mono (by intro z hz; simp at hz ⊢; tauto)
    D.s_b_uB.output_mem_left_right

/-- The difference output is algebraic over the four inputs. -/
theorem c_mem_inputs : D.c ∈ racl k ({s, e, a, b} : Set Ω) := by
  refine racl_le_of_subset_racl ?_ D.sA_c_uB.right_mem_left_output
  rintro z (rfl | rfl)
  · exact D.sA_mem_inputs
  · exact D.uB_mem_inputs

end FourArrowDifferenceDiagram

set_option maxHeartbeats 800000 in
-- The four nested closure-intersection arguments elaborate above the default budget.
/-- Four independent generic inputs admit the complete four-arrow
difference diagram on one ternary finite-correspondence locus.  The proof
derives the two intermediate independence conditions by exchange.  In
particular, independence of the last division pair is a consequence of the
four generic inputs and the three preceding finite relations; it is not an
extra hypothesis. -/
theorem exists_fourArrowDifferenceDiagram [IsAlgClosed Ω]
    {s e a b : Ω} (hind : AlgebraicIndependent k ![s, e, a, b]) :
    Nonempty (M.FourArrowDifferenceDiagram s a b e) := by
  classical
  let q : Fin 4 → Ω := ![s, e, a, b]
  have hq : AlgebraicIndependent k q := hind
  have hq01 : q '' ({0, 1} : Set (Fin 4)) = ({s, e} : Set Ω) := by
    ext z
    simp [q]
    tauto
  have hq012 : q '' ({0, 1, 2} : Set (Fin 4)) =
      ({s, e, a} : Set Ω) := by
    ext z
    simp [q]
    tauto
  have hq02 : q '' ({0, 2} : Set (Fin 4)) = ({s, a} : Set Ω) := by
    ext z
    simp [q]
    tauto
  have ha_se : a ∉ racl k ({s, e} : Set Ω) := by
    have hnot := AlgebraicIndependent.notMem_racl_image hq
      (S := ({0, 1} : Set (Fin 4))) (i := 2) (by simp)
    rw [hq01] at hnot
    simpa [q] using hnot
  have hb_sea : b ∉ racl k ({s, e, a} : Set Ω) := by
    have hnot := AlgebraicIndependent.notMem_racl_image hq
      (S := ({0, 1, 2} : Set (Fin 4))) (i := 3) (by simp)
    rw [hq012] at hnot
    simpa [q] using hnot
  have he_sa : e ∉ racl k ({s, a} : Set Ω) := by
    have hnot := AlgebraicIndependent.notMem_racl_image hq
      (S := ({0, 2} : Set (Fin 4))) (i := 1) (by simp)
    rw [hq02] at hnot
    simpa [q] using hnot
  have hb_se : b ∉ racl k ({s, e} : Set Ω) := by
    intro hmem
    exact hb_sea (racl_mono (by intro z hz; simp at hz ⊢; tauto) hmem)
  have hb_s : b ∉ racl k ({s} : Set Ω) := by
    intro hmem
    exact hb_se (racl_mono (by intro z hz; simp at hz ⊢; tauto) hmem)
  have he_s : e ∉ racl k ({s} : Set Ω) := by
    intro hmem
    exact he_sa (racl_mono (by intro z hz; simp at hz ⊢; tauto) hmem)
  have hse : AlgebraicIndependent k ![s, e] := by
    have hp := AlgebraicIndependent.comp_pair hq
      (i := 0) (j := 1) (by decide)
    simpa [q] using hp
  obtain ⟨u, hu⟩ := M.exists_output hse
  have hRu : M.IsRealization s e u := hu
  have hau : AlgebraicIndependent k ![a, u] := by
    refine algebraicIndependent_pair ?_ ?_
    · intro ha_u
      apply ha_se
      refine racl_le_of_subset_racl ?_ ha_u
      rintro z rfl
      exact hRu.output_mem_left_right
    · intro hu_a
      have hu_as : u ∈ racl k (insert a ({s} : Set Ω)) :=
        racl_mono (by intro z hz; simp at hz ⊢; tauto) hu_a
      have hu_es : u ∈ racl k (insert e ({s} : Set Ω)) := by
        have hset : insert e ({s} : Set Ω) = ({s, e} : Set Ω) := by
          ext z
          simp
          tauto
        rw [hset]
        exact hRu.output_mem_left_right
      have ha_es : a ∉ racl k (insert e ({s} : Set Ω)) := by
        have hset : insert e ({s} : Set Ω) = ({s, e} : Set Ω) := by
          ext z
          simp
          tauto
        rwa [hset]
      have hu_s : u ∈ racl k ({s} : Set Ω) :=
        mem_racl_of_mem_racl_insert hu_es hu_as ha_es
      have he_s' : e ∈ racl k ({s} : Set Ω) := by
        refine racl_le_of_subset_racl ?_ hRu.right_mem_left_output
        rintro z (rfl | rfl)
        · exact subset_racl k _ (by simp)
        · exact hu_s
      exact he_s he_s'
  obtain ⟨sA, hsA⟩ := M.exists_left hau
  have hRsA : M.IsRealization sA a u := hsA
  have hsb : AlgebraicIndependent k ![s, b] := by
    have hp := AlgebraicIndependent.comp_pair hq
      (i := 0) (j := 3) (by decide)
    simpa [q] using hp
  obtain ⟨uB, huB⟩ := M.exists_output hsb
  have hRuB : M.IsRealization s b uB := huB
  have hsa_sea : sA ∈ racl k ({s, e, a} : Set Ω) := by
    refine racl_le_of_subset_racl ?_ hRsA.left_mem_right_output
    rintro z (rfl | rfl)
    · exact subset_racl k _ (by simp)
    · exact racl_mono (by intro z hz; simp at hz ⊢; tauto)
        hRu.output_mem_left_right
  have huB_sb : uB ∈ racl k ({s, b} : Set Ω) :=
    hRuB.output_mem_left_right
  have hinsert_a_se : insert a ({s, e} : Set Ω) =
      ({s, e, a} : Set Ω) := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor <;> rintro (rfl | rfl | rfl) <;> simp
  have hinsert_e_s : insert e ({s} : Set Ω) = ({s, e} : Set Ω) := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor <;> rintro (rfl | rfl) <;> simp
  have hinsert_b_s : insert b ({s} : Set Ω) = ({s, b} : Set Ω) := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor <;> rintro (rfl | rfl) <;> simp
  have hintersection {w : Ω}
      (hw_sea : w ∈ racl k ({s, e, a} : Set Ω))
      (hw_sb : w ∈ racl k ({s, b} : Set Ω)) :
      w ∈ racl k ({s} : Set Ω) := by
    have hw_a_se : w ∈ racl k (insert a ({s, e} : Set Ω)) := by
      rwa [hinsert_a_se]
    have hw_b_se : w ∈ racl k (insert b ({s, e} : Set Ω)) :=
      racl_mono (by
        rintro z (rfl | rfl)
        · exact Set.mem_insert_of_mem _ (by simp)
        · exact Set.mem_insert _ _) hw_sb
    have hb_a_se : b ∉ racl k (insert a ({s, e} : Set Ω)) := by
      rwa [hinsert_a_se]
    have hw_se : w ∈ racl k ({s, e} : Set Ω) :=
      mem_racl_of_mem_racl_insert hw_a_se hw_b_se hb_a_se
    have hw_e_s : w ∈ racl k (insert e ({s} : Set Ω)) := by
      rwa [hinsert_e_s]
    have hw_b_s : w ∈ racl k (insert b ({s} : Set Ω)) := by
      rwa [hinsert_b_s]
    have hb_e_s : b ∉ racl k (insert e ({s} : Set Ω)) := by
      rwa [hinsert_e_s]
    exact mem_racl_of_mem_racl_insert hw_e_s hw_b_s hb_e_s
  have hsa_uB : AlgebraicIndependent k ![sA, uB] := by
    refine algebraicIndependent_pair ?_ ?_
    · intro hsa_uB
      have hsa_sb : sA ∈ racl k ({s, b} : Set Ω) := by
        refine racl_le_of_subset_racl ?_ hsa_uB
        rintro z rfl
        exact huB_sb
      have hsa_s := hintersection hsa_sea hsa_sb
      have hu_sa : u ∈ racl k ({s, a} : Set Ω) := by
        refine racl_le_of_subset_racl ?_ hRsA.output_mem_left_right
        rintro z (rfl | rfl)
        · exact racl_mono (by simp) hsa_s
        · exact subset_racl k _ (by simp)
      have he_sa' : e ∈ racl k ({s, a} : Set Ω) := by
        refine racl_le_of_subset_racl ?_ hRu.right_mem_left_output
        rintro z (rfl | rfl)
        · exact subset_racl k _ (by simp)
        · exact hu_sa
      exact he_sa he_sa'
    · intro huB_sa
      have huB_sea : uB ∈ racl k ({s, e, a} : Set Ω) := by
        refine racl_le_of_subset_racl ?_ huB_sa
        rintro z rfl
        exact hsa_sea
      have huB_s := hintersection huB_sea huB_sb
      have hb_s' : b ∈ racl k ({s} : Set Ω) := by
        refine racl_le_of_subset_racl ?_ hRuB.right_mem_left_output
        rintro z (rfl | rfl)
        · exact subset_racl k _ (by simp)
        · exact huB_s
      exact hb_s hb_s'
  obtain ⟨c, hc⟩ := M.exists_right hsa_uB
  exact ⟨{
    u := u
    sA := sA
    uB := uB
    c := c
    se_u := hRu
    sA_a_u := hRsA
    s_b_uB := hRuB
    sA_c_uB := hc }⟩

end FiniteCorrespondenceMultiplication

end

end AclGeom
