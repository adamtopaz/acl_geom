/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import GroupConfig.Descent
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.ModelTheory.ElementaryMaps

/-!
# Elementary embeddings of algebraically closed fields

An embedding of algebraically closed fields preserves every first-order formula in
Mathlib's language of rings. Constructibility of actual bounded formulas and density
of base-field points give the Tarski–Vaught test. This supplies the model-completeness
input in `rem:psi-hyp`(c) and `rem:finite-trdeg` of the supplemental blueprint.
The actual application formulas, independence recovery and chart/action descent remain
separate obligations.

**Status:** model completeness of algebraically closed fields is proved, using actual
Mathlib syntax. The application's fixed formulas and independence recovery remain open.
-/

namespace GroupConfig

open AclGeom MvPolynomial Set FirstOrder FirstOrder.Language

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {ι : Type*}

/-- A nonempty constructible set over an algebraically closed base has a base-field
point, even when its ambient field is not algebraically closed. The elementary-embedding
construction below consumes this fact on a fibre fixing the existing parameters. -/
theorem IsConstructibleOver.exists_kpoint [IsAlgClosed k] [Finite ι]
    {s : Set (ι → K)} (hs : IsConstructibleOver k s) (hne : s.Nonempty) :
    ∃ u : ι → k, algebraMap k K ∘ u ∈ s := by
  obtain ⟨e, he⟩ := hne
  obtain ⟨cells, hcells⟩ := isConstructibleOver_iff_exists_polynomial_data.mp hs
  obtain ⟨cell, hcell, hg, hf⟩ := (hcells e).mp he
  have hf' : map (algebraMap k K) cell.f ∉ locusIdeal k e := by
    intro h
    exact hf ((mem_idealOf_iff k).mp ((map_mem_locusIdeal_iff k).mp h))
  obtain ⟨u, hu, hnu⟩ := exists_kpoint_of_notMem_locusIdeal e hf'
  refine ⟨u, (hcells _).mpr ⟨cell, hcell, ?_, ?_⟩⟩
  · intro i
    have h := (inLocus_iff.mp hu) _ (map_mem_locusIdeal k ((mem_idealOf_iff k).mpr (hg i)))
    simpa only [aeval_map_algebraMap] using h
  · simpa only [aeval_map_algebraMap] using hnu

-- Use the canonical ring-language structures without adding a global instance loop.
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- The canonical ring-language homomorphism underlying a ring homomorphism. -/
private def ringLanguageHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    Language.ring.Hom R S where
  toFun := f
  map_fun' := by
    intro n g xs
    cases g <;> simp [Function.comp_def]
  map_rel' := by
    intro n r
    exact r.elim

/-- Terms in the actual ring language give polynomial expressions. -/
private def termPolynomial {n : ℕ} (t : Language.ring.Term (Empty ⊕ Fin n)) :
    MvPolynomial (Fin n) k :=
  t.realize (Sum.elim Empty.elim X)

/-- Polynomial evaluation agrees with the actual ring-language semantics. -/
private theorem aeval_termPolynomial {n : ℕ} (t : Language.ring.Term (Empty ⊕ Fin n))
    (x : Fin n → K) : aeval x (termPolynomial (k := k) t) =
      t.realize (Sum.elim default x) := by
  let f := ringLanguageHom (R := MvPolynomial (Fin n) k) (S := K) (aeval x).toRingHom
  have h := HomClass.realize_term f (t := t) (v := Sum.elim Empty.elim X)
  have he : f ∘ (Sum.elim Empty.elim X) = Sum.elim (default : Empty → K) x := by
    funext i
    cases i with
    | inl i => exact i.elim
    | inr i => exact aeval_X x i
  rw [he] at h
  exact h.symm

/-- The realization set of every actual bounded ring formula is constructible over the
coefficient field, in an algebraically closed ambient field. This is consumed by the
Tarski–Vaught test for a given field embedding. -/
theorem isConstructibleOver_realize [IsAlgClosed K] {n : ℕ}
    (φ : Language.ring.BoundedFormula Empty n) :
    IsConstructibleOver k {x : Fin n → K | φ.Realize default x} := by
  induction φ with
  | falsum => exact IsConstructibleOver.empty
  | equal t₁ t₂ =>
    convert IsConstructibleOver.polynomial_zero
      (termPolynomial (k := k) t₁ - termPolynomial (k := k) t₂) using 1
    ext x
    simp only [mem_ofPred_eq, map_sub, aeval_termPolynomial, sub_eq_zero,
      BoundedFormula.Realize]
  | rel R _ => exact R.elim
  | imp φ ψ hφ hψ =>
    convert hφ.compl.union hψ using 1
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, BoundedFormula.Realize,
      imp_iff_not_or]
  | @all n φ hφ =>
    let q : Fin (n + 1) → MvPolynomial (Fin n ⊕ Fin 1) k :=
      Fin.snoc (fun i ↦ X (Sum.inl i)) (X (Sum.inr 0))
    have heval (z : (Fin n ⊕ Fin 1) → K) :
        (fun i ↦ aeval z (q i)) = Fin.snoc (z ∘ Sum.inl) (z (Sum.inr 0)) := by
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [q, Function.comp_def]
    have hpre := hφ.preimage_polynomial q
    have hquant := IsConstructibleOver.forall
      (φ := fun (x : Fin n → K) (y : Fin 1 → K) ↦ φ.Realize default (Fin.snoc x (y 0)))
      (by simpa only [preimage_ofPred_eq, heval, Function.comp_def] using hpre)
    convert hquant using 1
    ext x
    change (∀ a : K, φ.Realize default (Fin.snoc x a)) ↔
      (∀ y : Fin 1 → K, φ.Realize default (Fin.snoc x (y 0)))
    exact ⟨fun h y ↦ h (y 0), fun h a ↦ h (fun _ ↦ a)⟩

variable {F E : Type*} [Field F] [Field E] [IsAlgClosed F] [IsAlgClosed E]

/-- Every embedding of algebraically closed fields is an actual elementary embedding
in Mathlib's ring language, with the prescribed underlying ring homomorphism. -/
def acfElementaryEmbedding (f : F →+* E) : F ↪ₑ[Language.ring] E := by
  letI : Algebra F E := f.toAlgebra
  let e : F ↪[Language.ring] E :=
    { toFun := f
      inj' := f.injective
      map_fun' := (ringLanguageHom f).map_fun'
      map_rel' := by intro n r; exact r.elim }
  refine e.toElementaryEmbedding ?_
  intro n φ xs a ha
  let q : Fin (n + 1) → MvPolynomial (Fin 1) F :=
    Fin.snoc (fun i ↦ C (xs i)) (X 0)
  let s : Set (Fin 1 → E) :=
    {y | φ.Realize default (Fin.snoc (f ∘ xs) (y 0))}
  have heval (y : Fin 1 → E) : (fun i ↦ aeval y (q i)) =
      Fin.snoc (f ∘ xs) (y 0) := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;>
      simp [q, Function.comp_def, RingHom.algebraMap_toAlgebra]
  have hs : IsConstructibleOver F s := by
    simpa only [s, preimage_ofPred_eq, heval] using
      (isConstructibleOver_realize (k := F) (K := E) φ).preimage_polynomial q
  have hne : s.Nonempty := ⟨fun _ ↦ a, ha⟩
  obtain ⟨u, hu⟩ := hs.exists_kpoint hne
  exact ⟨u 0, hu⟩

@[simp]
theorem acfElementaryEmbedding_apply (f : F →+* E) (x : F) :
    acfElementaryEmbedding f x = f x := rfl

/-- A prescribed algebraically closed field embedding preserves every finite-arity
first-order ring formula, including arbitrary quantifiers. -/
theorem ringHom_realize_iff (f : F →+* E) {n : ℕ} (φ : Language.ring.Formula (Fin n))
    (x : Fin n → F) : φ.Realize (f ∘ x) ↔ φ.Realize x :=
  (acfElementaryEmbedding f).map_formula' φ x

end

end GroupConfig
