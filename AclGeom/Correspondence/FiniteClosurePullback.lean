/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.FiniteNormalTransport

/-!
# Finite pullbacks of algebraic-closure comparison charts

An equivalence of algebraic closures extending a field embedding need not
restrict to an equivalence of the two displayed base fields.  It does,
however, identify the inverse image of every finite target field with that
target field.  This file packages that inverse image as an intermediate
field and proves that finiteness descends through the restricted chart.

The construction is the finite stabilization step used after rebasing
several selected correspondence covers into one common codomain: pulling
that codomain back along every selected closure equivalence produces honest
finite field charts with one literal target.
-/

namespace AclGeom

open IntermediateField

noncomputable section

namespace AlgebraicClosureTransport.EmbeddingClosureEquiv

variable {E E' : Type*} [Field E] [Field E']
  {f : E →+* E'} (C : EmbeddingClosureEquiv f)

/-- The inverse image of an intermediate field under the chosen
algebraic-closure equivalence. -/
def pullbackField (T : IntermediateField E' (AlgebraicClosure E')) :
    IntermediateField E (AlgebraicClosure E) where
  carrier := C.closureEquiv ⁻¹' T
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simpa using T.add_mem hx hy
  mul_mem' := by
    intro x y hx hy
    simpa using T.mul_mem hx hy
  algebraMap_mem' := by
    intro x
    change C.closureEquiv
        (algebraMap E (AlgebraicClosure E) x) ∈ T
    rw [C.commutes x]
    exact T.algebraMap_mem (f x)
  inv_mem' := by
    intro x hx
    simpa using T.inv_mem hx

/-- Restriction of the ambient algebraic-closure equivalence to a pullback
field and its selected target. -/
def pullbackEquiv (T : IntermediateField E' (AlgebraicClosure E')) :
    (↥(C.pullbackField T)) ≃+* (↥T) where
  toFun x := ⟨C.closureEquiv x, x.2⟩
  invFun y := ⟨C.closureEquiv.symm y, by
    change C.closureEquiv (C.closureEquiv.symm y) ∈ T
    rw [C.closureEquiv.apply_symm_apply]
    exact y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp
  map_mul' x y := by ext; simp

/-- The restricted chart evaluates as the ambient closure equivalence. -/
@[simp] theorem pullbackEquiv_val
    (T : IntermediateField E' (AlgebraicClosure E'))
    (x : C.pullbackField T) :
    ((C.pullbackEquiv T x : T) : AlgebraicClosure E') =
      C.closureEquiv (x : AlgebraicClosure E) :=
  rfl

/-- The restricted chart retains the exact selected base embedding. -/
@[simp] theorem pullbackEquiv_algebraMap
    (T : IntermediateField E' (AlgebraicClosure E')) (x : E) :
    C.pullbackEquiv T
        (algebraMap E (↥(C.pullbackField T)) x) =
      algebraMap E' (↥T) (f x) := by
  apply Subtype.ext
  exact C.commutes x

/-- Pulling back the embedded target base gives a field equivalent to that
base while retaining the prescribed embedding `f`. -/
def pullbackBaseEquiv :
    (↥(C.pullbackField (⊥ : IntermediateField E'
      (AlgebraicClosure E')))) ≃+* E' :=
  (C.pullbackEquiv ⊥).trans
    (IntermediateField.botEquiv E' (AlgebraicClosure E')).toRingEquiv

/-- The selected copy of the old base inside the finite pullback field,
written explicitly so downstream constructions do not have to synthesize a
deep intermediate-field algebra tower. -/
def pullbackBaseRingHom :
    E →+* (↥(C.pullbackField (⊥ : IntermediateField E'
      (AlgebraicClosure E')))) where
  toFun x := ⟨algebraMap E (AlgebraicClosure E) x, by
    change C.closureEquiv
        (algebraMap E (AlgebraicClosure E) x) ∈
      (⊥ : IntermediateField E' (AlgebraicClosure E'))
    rw [C.commutes x]
    exact (⊥ : IntermediateField E'
      (AlgebraicClosure E')).algebraMap_mem (f x)⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- The explicit selected base map has the same value as the canonical
algebra map into the pullback intermediate field. -/
@[simp] theorem pullbackBaseRingHom_eq_algebraMap (x : E) :
    C.pullbackBaseRingHom x =
      algebraMap E (↥(C.pullbackField (⊥ : IntermediateField E'
        (AlgebraicClosure E')))) x :=
  rfl

/-- On the whole old base field, the finite pullback chart is exactly the
embedding that the ambient closure equivalence was chosen to extend. -/
@[simp] theorem pullbackBaseEquiv_algebraMap (x : E) :
    C.pullbackBaseEquiv
        (algebraMap E (↥(C.pullbackField (⊥ : IntermediateField E'
          (AlgebraicClosure E')))) x) = f x := by
  simp [pullbackBaseEquiv]

/-- The finite chart restricts along the explicit selected base map to the
original field embedding. -/
@[simp] theorem pullbackBaseEquiv_pullbackBaseRingHom (x : E) :
    C.pullbackBaseEquiv (C.pullbackBaseRingHom x) = f x := by
  rw [C.pullbackBaseRingHom_eq_algebraMap,
    C.pullbackBaseEquiv_algebraMap]

/-- Ring-hom form of the exact selected restriction square. -/
theorem pullbackBaseEquiv_comp_pullbackBaseRingHom :
    C.pullbackBaseEquiv.toRingHom.comp C.pullbackBaseRingHom = f := by
  apply RingHom.ext
  exact C.pullbackBaseEquiv_pullbackBaseRingHom

/-- Pullback along a closure equivalence preserves finiteness after a
finite embedded base change. -/
theorem pullbackField_finiteDimensional
    [Algebra E E'] (hf : algebraMap E E' = f)
    [FiniteDimensional E E']
    (T : IntermediateField E' (AlgebraicClosure E'))
    [FiniteDimensional E' (↥T)] :
    FiniteDimensional E (↥(C.pullbackField T)) := by
  letI : IsScalarTower E E' (↥T) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : FiniteDimensional E (↥T) :=
    FiniteDimensional.trans E E' (↥T)
  apply Module.Finite.of_equiv_equiv (RingEquiv.refl E)
    (C.pullbackEquiv T).symm
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, RingEquiv.refl_apply,
    RingEquiv.coe_toRingHom]
  apply (C.pullbackEquiv T).injective
  rw [C.pullbackEquiv_algebraMap, RingEquiv.apply_symm_apply]
  rw [IsScalarTower.algebraMap_apply E E' (↥T), hf]

end AlgebraicClosureTransport.EmbeddingClosureEquiv

end

end AclGeom
