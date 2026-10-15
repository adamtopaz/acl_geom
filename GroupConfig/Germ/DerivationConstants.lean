/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import GroupConfig.Germ.Code
import GroupConfig.FodBaseChange
import AclGeom.Curves.CoefficientConnection

/-!
# Derivations and the ordinary canonical base of a germ

A coefficient-stable polynomial ideal has its ordinary field of definition in the constants
of the coefficient derivation. The proof differentiates its RREF code. Thus a derivation of
an actual germ's ordinary canonical base vanishes if it preserves the contracted graph ideal.
Zero variation supplies that stability on the formal graph; `CurveGenus` derives the actual
graph comparison internally.

**Status:** proved, with no unproved hypotheses (#21). Used by the faithful variation step of
the actual Hrushovski–Weil genus theorem.
-/

namespace GroupConfig

open AclGeom MvPolynomial Set
open scoped TensorProduct

noncomputable section

section DifferentialFieldOfDefinition

variable {k C : Type*} [CommRing k] [Field C] [Algebra k C]

/-- The constants of a coefficient derivation form an ordinary subfield. -/
private def derivationConstants' (D : Derivation k C C) : Subfield C where
  carrier := {c | D c = 0}
  zero_mem' := map_zero D
  one_mem' := D.map_one_eq_zero
  add_mem' := by
    intro a b ha hb
    change D (a + b) = 0
    rw [map_add, ha, hb, add_zero]
  mul_mem' := by
    intro a b ha hb
    change D (a * b) = 0
    rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
  neg_mem' := by
    intro a ha
    change D (-a) = 0
    rw [map_neg, ha, neg_zero]
  inv_mem' := by
    intro a ha
    change D a⁻¹ = 0
    rw [Derivation.leibniz_inv, ha, smul_zero]

/-- A coefficient-stable subspace has constant RREF coordinates: the derivative of a
normalized row lies in the subspace and has zero at every pivot. -/
private theorem rref_derivation_eq_zero' {M : Type*} [Finite M] [LinearOrder M]
    (D : Derivation k C C) (W : Submodule C (M → C))
    (hW : ∀ w ∈ W, (fun i ↦ D (w i)) ∈ W) (μ : Pivots W) (i : M) :
    D (rref W μ i) = 0 := by
  classical
  let w : W := ⟨fun j ↦ D (rref W μ j), hW _ (rref_mem W μ)⟩
  have hw : pivotProj W w = pivotProj W 0 := by
    ext ν
    change D (rref W μ ν) = 0
    rw [rref_apply_pivot]
    split_ifs <;> simp only [Derivation.map_one_eq_zero, map_zero]
  have hw0 : w = 0 := pivotProj_injective W hw
  exact congrArg (fun u : W ↦ (u : M → C) i) hw0

/-- The RREF field of definition of a coefficient-stable subspace consists of constants. -/
private theorem fod_le_derivationConstants' {M : Type*} [Finite M] [LinearOrder M]
    (D : Derivation k C C) (W : Submodule C (M → C))
    (hW : ∀ w ∈ W, (fun i ↦ D (w i)) ∈ W) : fod W ≤ derivationConstants' D := by
  apply Subfield.closure_le.mpr
  rintro _ ⟨⟨μ, i⟩, rfl⟩
  exact rref_derivation_eq_zero' D W hW μ i

/-- Apply a derivation to the coefficients of a multivariate polynomial. -/
def coefficientDerivative {ι : Type*} (D : Derivation k C C)
    (p : MvPolynomial ι C) : MvPolynomial ι C :=
  AddMonoidAlgebra.map D.toLinearMap.toAddMonoidHom p

private theorem coefficientDerivative_coeff {ι : Type*} (D : Derivation k C C)
    (p : MvPolynomial ι C) (m : ι →₀ ℕ) :
    (coefficientDerivative D p).coeff m = D (p.coeff m) := rfl

private theorem coefficientDerivative_C {ι : Type*} (D : Derivation k C C) (c : C) :
    coefficientDerivative (ι := ι) D (MvPolynomial.C c) = MvPolynomial.C (D c) := by
  classical
  ext m
  simp only [coefficientDerivative_coeff, coeff_C]
  split_ifs <;> simp only [map_zero]

private theorem coefficientDerivative_add {ι : Type*} (D : Derivation k C C)
    (p q : MvPolynomial ι C) :
    coefficientDerivative D (p + q) = coefficientDerivative D p + coefficientDerivative D q := by
  ext m
  simp only [coefficientDerivative_coeff, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, map_add]

private theorem coefficientDerivative_mul_X {ι : Type*} (D : Derivation k C C)
    (p : MvPolynomial ι C) (i : ι) :
    coefficientDerivative D (p * X i) = coefficientDerivative D p * X i := by
  classical
  ext m
  simp only [coefficientDerivative_coeff, coeff_mul_X']
  split_ifs <;> simp only [map_zero]

/-- Differentiation of a polynomial value reduces to coefficient differentiation when
all its coordinate values are horizontal for the coefficient connection. -/
private theorem derivation_aeval_of_coordinates_zero' {E ι : Type*} [CommRing E]
    [Algebra k E] [Algebra C E] (D : Derivation k C C) (D₀ : Derivation k E E)
    (hcoeff : ∀ c, D₀ (algebraMap C E c) = algebraMap C E (D c))
    (x : ι → E) (hx : ∀ i, D₀ (x i) = 0) (p : MvPolynomial ι C) :
    D₀ (aeval x p) = aeval x (coefficientDerivative D p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [aeval_C, coefficientDerivative_C] using hcoeff c
  | add p q hp hq =>
    simp only [coefficientDerivative_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Derivation.leibniz, aeval_X, hx, smul_zero, zero_add, hp,
      coefficientDerivative_mul_X, map_mul, aeval_X, smul_eq_mul]
    exact mul_comm _ _

/-- The kernel defining a graph is coefficient-stable when the connection kills its
actual coordinate tuple. -/
private theorem coefficientDerivative_mem_ker {E ι : Type*} [CommRing E]
    [Algebra k E] [Algebra C E] (D : Derivation k C C) (D₀ : Derivation k E E)
    (hcoeff : ∀ c, D₀ (algebraMap C E c) = algebraMap C E (D c))
    (x : ι → E) (hx : ∀ i, D₀ (x i) = 0) {p : MvPolynomial ι C}
    (hp : p ∈ RingHom.ker (aeval x).toRingHom) :
    coefficientDerivative D p ∈ RingHom.ker (aeval x).toRingHom := by
  change aeval x (coefficientDerivative D p) = 0
  rw [← derivation_aeval_of_coordinates_zero' D D₀ hcoeff x hx,
    show aeval x p = 0 from hp, map_zero]

private theorem coefficientDerivative_totalDegree_le {ι : Type*} (D : Derivation k C C)
    (p : MvPolynomial ι C) : (coefficientDerivative D p).totalDegree ≤ p.totalDegree := by
  classical
  apply totalDegree_le_of_support_subset
  intro m hm
  apply mem_support_iff.mpr
  intro h0
  have h := mem_support_iff.mp hm
  exact h (by rw [coefficientDerivative_coeff, h0, map_zero])

/-- Coefficient stability of an ideal forces its entire ordinary field of definition
into the constants. This will detect a zero infinitesimal variation of the actual graph. -/
private theorem idealFod_le_derivationConstants' {ι : Type*} [Finite ι]
    (D : Derivation k C C) (I : Ideal (MvPolynomial ι C))
    (hI : ∀ p ∈ I, coefficientDerivative D p ∈ I) : idealFod I ≤ derivationConstants' D := by
  apply iSup_le
  intro d
  apply fod_le_derivationConstants'
  intro w hw
  obtain ⟨p, hp, hpd, rfl⟩ := mem_degSubspace_iff.mp hw
  refine mem_degSubspace_iff.mpr ⟨coefficientDerivative D p, hI p hp,
    (coefficientDerivative_totalDegree_le D p).trans hpd, ?_⟩
  ext m
  rfl

private def derivationConstantsIntermediate' {k C : Type*} [Field k] [Field C]
    [Algebra k C] (D : Derivation k C C) : IntermediateField k C where
  __ := (derivationConstants' D).toSubring
  algebraMap_mem' := D.map_algebraMap
  inv_mem' _ h := (derivationConstants' D).inv_mem h

end DifferentialFieldOfDefinition

section VariationGraphKernel

variable {k F C ι : Type*} [Field k] [Field F] [Field C] [Algebra k F] [Algebra k C]
  [IsAlgClosed k]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance : IsDomain (C ⊗[k] F) := isDomain_tensorProduct_of_isAlgClosed

omit [IsAlgClosed k] in
/-- Zero variation makes the polynomial kernel of the formal graph coefficient-stable. -/
theorem coefficientDerivative_mem_variationGraphKernel
    (g : FractionRing (C ⊗[k] F) ≃ₐ[C] FractionRing (C ⊗[k] F))
    (D : Derivation k C C) (hD : coefficientVariation (k := k) g D = 0) (u : ι → F) :
    let x : ι → FractionRing (C ⊗[k] F) := fun i ↦ algebraMap (C ⊗[k] F) _ ((1 : C) ⊗ₜ[k] u i)
    let z := Sum.elim x (fun i ↦ g (x i))
    ∀ P ∈ RingHom.ker (aeval (R := C) z).toRingHom,
      coefficientDerivative D P ∈ RingHom.ker (aeval (R := C) z).toRingHom := by
  intro x z P hP
  let conn := coefficientConnection (F := F) D
  have hcomm := (coefficientVariation_eq_zero_iff (k := k) g D).mp hD
  have hx (i : ι) : conn (x i) = 0 := by
    change coefficientConnection D (algebraMap F (FractionRing (C ⊗[k] F)) (u i)) = 0
    exact coefficientConnection_function D _
  have hz (j : ι ⊕ ι) : conn (z j) = 0 := by
    cases j with
    | inl i => exact hx i
    | inr i =>
      change conn (g (x i)) = 0
      exact (hcomm (x i)).trans (by rw [hx, map_zero])
  exact coefficientDerivative_mem_ker D (conn.restrictScalars k)
    (fun c ↦ coefficientConnection_coeff D c) z hz hP

end VariationGraphKernel

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K] {ι : Type*} [Finite ι] {v : ι → K}

/-- A derivation preserving the actual graph ideal over its ordinary canonical base
vanishes on that base. No derivation of the ambient algebraically closed field is used. -/
theorem Germ.derivation_eq_zero_of_graph_stable (g : Germ k v v)
    (D : Derivation k g.cb g.cb)
    (hD : ∀ p ∈ g.graphIdeal.comap (MvPolynomial.map (algebraMap g.cb K)),
      coefficientDerivative D p ∈
        g.graphIdeal.comap (MvPolynomial.map (algebraMap g.cb K))) : D = 0 := by
  let J := g.graphIdeal.comap (MvPolynomial.map (algebraMap g.cb K))
  let U := derivationConstantsIntermediate' D
  have hJ : idealFod J ≤ U.toSubfield := idealFod_le_derivationConstants' D J hD
  have hdef := Germ.idealDefinedOver_graphIdeal g le_rfl
  change g.graphIdeal = J.map (MvPolynomial.map (algebraMap g.cb K)) at hdef
  have hfod : idealFod g.graphIdeal = (idealFod J).map (algebraMap g.cb K) := by
    rw [hdef, idealFod_map_algebraMap]
  have hcb : g.cb ≤ U.map g.cb.val := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro c hc
    rw [hfod] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    exact ⟨a, hJ ha, rfl⟩
  apply Derivation.ext
  intro c
  change D c = 0
  obtain ⟨a, ha, hac⟩ := hcb c.property
  have heq : a = c := Subtype.val_injective hac
  exact heq ▸ ha

end

end GroupConfig
