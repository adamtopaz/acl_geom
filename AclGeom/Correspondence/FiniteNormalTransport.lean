/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.AlgebraicClosureTransport
import Mathlib.FieldTheory.Normal.Closure

/-!
# Finite normal subcovers carried by algebraic-closure transports

An equivalence between algebraic closures which is semilinear over an
equivalence of their base fields transports intermediate fields.  Finite
dimensionality and normality are preserved by this operation.  Consequently
every automorphism fixing the base stabilizes every finite normal subcover.

This is the finite-stabilization mechanism needed for the curve-field action
in blueprint Theorem 8.2: a vertical composition defect may move individual
elements, but it cannot move a finite normal field as a whole.
-/

namespace AclGeom

open IntermediateField

noncomputable section

namespace AlgebraicClosureTransport

variable {E E' E'' : Type*} [Field E] [Field E'] [Field E'']

/-- Changing an intermediate-field subtype along an equality does not
change its value in the ambient field. -/
@[simp] theorem equivOfEq_val
    {L : Type*} [Field L] [Algebra E L]
    {S T : IntermediateField E L} (h : S = T) (x : S) :
    (((IntermediateField.equivOfEq h).toRingEquiv x : T) : L) = x :=
  rfl

/-- Regard an automorphism of an algebraic closure over its base as an
algebraic-closure transport with trivial base map. -/
def ofAlgEquiv
    (σ : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) :
    AlgebraicClosureTransport E E where
  baseEquiv := RingEquiv.refl E
  closureEquiv := σ.toRingEquiv
  commutes := by
    apply RingHom.ext
    intro x
    simp

/-- The image of an intermediate field under a semilinear
algebraic-closure transport. -/
def mapField (T : AlgebraicClosureTransport E E')
    (L : IntermediateField E (AlgebraicClosure E)) :
    IntermediateField E' (AlgebraicClosure E') where
  carrier := T.closureEquiv '' L
  zero_mem' := ⟨0, L.zero_mem, by simp⟩
  one_mem' := ⟨1, L.one_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, L.add_mem hx hy, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, L.mul_mem hx hy, by simp⟩
  algebraMap_mem' := fun x ↦
    ⟨algebraMap E (AlgebraicClosure E) (T.baseEquiv.symm x),
      L.algebraMap_mem _, by simp⟩
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, L.inv_mem hx, by simp⟩

/-- Membership in the transported field can be tested after applying the
inverse closure equivalence. -/
@[simp] theorem mem_mapField_iff
    (T : AlgebraicClosureTransport E E')
    (L : IntermediateField E (AlgebraicClosure E))
    (y : AlgebraicClosure E') :
    y ∈ T.mapField L ↔ T.closureEquiv.symm y ∈ L := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨T.closureEquiv.symm y, hy, by simp⟩

/-- The underlying subfield of a transported intermediate field is the
ordinary image subfield. -/
@[simp] theorem mapField_toSubfield
    (T : AlgebraicClosureTransport E E')
    (L : IntermediateField E (AlgebraicClosure E)) :
    (T.mapField L).toSubfield =
      L.toSubfield.map T.closureEquiv.toRingHom := by
  ext z
  rfl

/-- A transport restricts to a semilinear ring equivalence from an
intermediate field to its image. -/
def mapFieldEquiv (T : AlgebraicClosureTransport E E')
    (L : IntermediateField E (AlgebraicClosure E)) :
    (↥L) ≃+* (↥(T.mapField L)) where
  toFun x := ⟨T.closureEquiv x, ⟨x, x.2, rfl⟩⟩
  invFun y := ⟨T.closureEquiv.symm y, (T.mem_mapField_iff L y).1 y.2⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp

/-- The restricted field equivalence remains semilinear over the displayed
base equivalence. -/
theorem mapFieldEquiv_commutes
    (T : AlgebraicClosureTransport E E')
    (L : IntermediateField E (AlgebraicClosure E)) :
    (algebraMap E' (↥(T.mapField L))).comp T.baseEquiv.toRingHom =
      (T.mapFieldEquiv L).toRingHom.comp (algebraMap E (↥L)) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  change algebraMap E' (AlgebraicClosure E') (T.baseEquiv x) =
    T.closureEquiv (algebraMap E (AlgebraicClosure E) x)
  exact (T.commutes_apply x).symm

/-- Transporting through a composite is the same as transporting in two
successive steps. -/
theorem mapField_trans (T : AlgebraicClosureTransport E E')
    (U : AlgebraicClosureTransport E' E'')
    (L : IntermediateField E (AlgebraicClosure E)) :
    (T.trans U).mapField L = U.mapField (T.mapField L) := by
  ext z
  simp

/-- Transport commutes with composita of intermediate fields. -/
theorem mapField_sup (T : AlgebraicClosureTransport E E')
    (L M : IntermediateField E (AlgebraicClosure E)) :
    T.mapField (L ⊔ M) = T.mapField L ⊔ T.mapField M := by
  apply IntermediateField.toSubfield_injective
  rw [T.mapField_toSubfield,
    IntermediateField.sup_toSubfield L M]
  rw [IntermediateField.sup_toSubfield (T.mapField L) (T.mapField M),
    T.mapField_toSubfield, T.mapField_toSubfield, Subfield.map_sup]

/-- Transporting a field and then transporting it back recovers the
original field. -/
@[simp] theorem mapField_symm_mapField
    (T : AlgebraicClosureTransport E E')
    (L : IntermediateField E (AlgebraicClosure E)) :
    T.symm.mapField (T.mapField L) = L := by
  ext z
  simp

/-- The reverse round trip also recovers the original field. -/
@[simp] theorem mapField_mapField_symm
    (T : AlgebraicClosureTransport E E')
    (L : IntermediateField E' (AlgebraicClosure E')) :
    T.mapField (T.symm.mapField L) = L := by
  ext z
  simp

/-- The transported field depends only on the underlying equivalence of
algebraic closures. -/
theorem mapField_eq_of_closureEquiv_eq
    (T U : AlgebraicClosureTransport E E')
    (h : T.closureEquiv = U.closureEquiv)
    (L : IntermediateField E (AlgebraicClosure E)) :
    T.mapField L = U.mapField L := by
  ext z
  change z ∈ T.closureEquiv '' L ↔ z ∈ U.closureEquiv '' L
  rw [h]

/-- Transport is monotone on intermediate fields. -/
theorem mapField_mono (T : AlgebraicClosureTransport E E')
    {L M : IntermediateField E (AlgebraicClosure E)} (h : L ≤ M) :
    T.mapField L ≤ T.mapField M := by
  intro z hz
  rw [T.mem_mapField_iff] at hz ⊢
  exact h hz

/-- The identity transport fixes every intermediate field. -/
@[simp] theorem mapField_refl
    (L : IntermediateField E (AlgebraicClosure E)) :
    (refl E).mapField L = L := by
  ext z
  simp

/-- A finite normal intermediate field in an algebraic closure. -/
structure FiniteNormalCover (E : Type*) [Field E] where
  /-- The concrete intermediate field. -/
  field : IntermediateField E (AlgebraicClosure E)
  /-- The cover is finite over its curve-coordinate base field. -/
  finiteDimensional : FiniteDimensional E (↥field)
  /-- The cover is normal over its curve-coordinate base field. -/
  normal : Normal E (↥field)

namespace FiniteNormalCover

variable (N : FiniteNormalCover E)

/-- The compositum of two finite normal covers is again finite and normal. -/
def sup (N M : FiniteNormalCover E) : FiniteNormalCover E where
  field := N.field ⊔ M.field
  finiteDimensional := by
    letI := N.finiteDimensional
    letI := M.finiteDimensional
    infer_instance
  normal := by
    letI := N.normal
    letI := M.normal
    infer_instance

/-- The underlying field of a compositum cover. -/
@[simp] theorem sup_field (M : FiniteNormalCover E) :
    (N.sup M).field = N.field ⊔ M.field := rfl

/-- Transport a finite normal cover along a semilinear equivalence of
algebraic closures. -/
def map (T : AlgebraicClosureTransport E E') : FiniteNormalCover E' where
  field := T.mapField N.field
  finiteDimensional := by
    letI := N.finiteDimensional
    exact Module.Finite.of_equiv_equiv T.baseEquiv
      (T.mapFieldEquiv N.field) (T.mapFieldEquiv_commutes N.field)
  normal := by
    letI := N.normal
    exact Normal.of_equiv_equiv
      (F := E) (E := ↥N.field) (M := E')
      (N := ↥(T.mapField N.field))
      (f := T.baseEquiv) (g := T.mapFieldEquiv N.field)
      (T.mapFieldEquiv_commutes N.field)

/-- The underlying field of a transported finite normal cover. -/
@[simp] theorem map_field (T : AlgebraicClosureTransport E E') :
    (N.map T).field = T.mapField N.field := rfl

/-- Restrict an algebraic-closure transport to a finite normal cover and
its transported image. -/
def mapEquiv (T : AlgebraicClosureTransport E E') :
    (↥N.field) ≃+* (↥(N.map T).field) :=
  T.mapFieldEquiv N.field

/-- The restricted finite-cover equivalence is semilinear over the same
base equivalence as the ambient transport. -/
theorem mapEquiv_commutes (T : AlgebraicClosureTransport E E') :
    (algebraMap E' (↥(N.map T).field)).comp T.baseEquiv.toRingHom =
      (N.mapEquiv T).toRingHom.comp (algebraMap E (↥N.field)) :=
  T.mapFieldEquiv_commutes N.field

/-- Mapping a finite normal cover along two transports agrees at the field
level with mapping it along their composite. -/
theorem map_trans_field (T : AlgebraicClosureTransport E E')
    (U : AlgebraicClosureTransport E' E'') :
    (N.map (T.trans U)).field = ((N.map T).map U).field :=
  T.mapField_trans U N.field

/-- Transport distributes over the compositum of finite normal covers. -/
theorem map_sup_field (M : FiniteNormalCover E)
    (T : AlgebraicClosureTransport E E') :
    ((N.sup M).map T).field = ((N.map T).sup (M.map T)).field :=
  T.mapField_sup N.field M.field

/-- A transported finite normal cover returns to its original field after
transport along the inverse equivalence. -/
theorem map_symm_map_field (T : AlgebraicClosureTransport E E') :
    ((N.map T).map T.symm).field = N.field :=
  T.mapField_symm_mapField N.field

/-- Every automorphism of the algebraic closure fixing the base stabilizes
a finite normal cover as a set. -/
theorem map_ofAlgEquiv_field
    (σ : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) :
    (N.map (ofAlgEquiv σ)).field = N.field := by
  letI := N.normal
  have hmap : N.field.map σ.toAlgHom = N.field :=
    (normal_iff_forall_map_eq'.1 N.normal) σ
  have himage : (N.map (ofAlgEquiv σ)).field =
      N.field.map σ.toAlgHom := by
    ext z
    rfl
  exact himage.trans hmap

/-- A vertical automorphism after a transport does not change the target
finite normal field. -/
theorem map_trans_ofAlgEquiv_field
    (T : AlgebraicClosureTransport E E')
    (σ : AlgebraicClosure E' ≃ₐ[E'] AlgebraicClosure E') :
    (N.map (T.trans (ofAlgEquiv σ))).field = (N.map T).field := by
  calc
    (N.map (T.trans (ofAlgEquiv σ))).field =
        ((N.map T).map (ofAlgEquiv σ)).field :=
      N.map_trans_field T (ofAlgEquiv σ)
    _ = (N.map T).field := (N.map T).map_ofAlgEquiv_field σ

/-- If a second ambient transport is obtained from the first by a vertical
automorphism, then both carry a finite normal cover onto the same target
field. -/
theorem correctedMap_field
    (T U : AlgebraicClosureTransport E E')
    (σ : AlgebraicClosure E' ≃ₐ[E'] AlgebraicClosure E')
    (h : T.closureEquiv.trans σ.toRingEquiv = U.closureEquiv) :
    (N.map U).field = (N.map T).field := by
  calc
    (N.map U).field =
        (N.map (T.trans (ofAlgEquiv σ))).field :=
      mapField_eq_of_closureEquiv_eq U (T.trans (ofAlgEquiv σ))
        h.symm N.field
    _ = (N.map T).field := N.map_trans_ofAlgEquiv_field T σ

/-- Restrict the vertically corrected ambient transport to the same finite
normal target cover as the strict transport. -/
def correctedMapEquiv
    (T U : AlgebraicClosureTransport E E')
    (σ : AlgebraicClosure E' ≃ₐ[E'] AlgebraicClosure E')
    (h : T.closureEquiv.trans σ.toRingEquiv = U.closureEquiv) :
    (↥N.field) ≃+* (↥(N.map T).field) :=
  (N.mapEquiv U).trans
    (IntermediateField.equivOfEq (N.correctedMap_field T U σ h)).toRingEquiv

/-- Restrict a vertical algebraic-closure automorphism to the finite normal
cover which it stabilizes. -/
def restrictAlgEquiv
    (σ : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) :
    (↥N.field) ≃ₐ[E] (↥N.field) := by
  letI := N.normal
  exact σ.restrictNormal N.field

/-- Restriction evaluates as the original algebraic-closure automorphism. -/
@[simp] theorem coe_restrictAlgEquiv_apply
    (σ : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) (x : N.field) :
    ((N.restrictAlgEquiv σ x : N.field) : AlgebraicClosure E) = σ x :=
  by
    letI := N.normal
    exact AlgEquiv.restrictNormal_commutes σ N.field x

/-- The same evaluation rule through the underlying ring equivalence. -/
@[simp] theorem coe_restrictAlgEquiv_toRingEquiv_apply
    (σ : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) (x : N.field) :
    (((N.restrictAlgEquiv σ).toRingEquiv x : N.field) :
      AlgebraicClosure E) = σ x := by
    exact N.coe_restrictAlgEquiv_apply σ x

/-- The deck-corrected strict equivalence is exactly the restricted second
transport on the finite normal cover. -/
theorem mapEquiv_trans_restrictAlgEquiv
    (T U : AlgebraicClosureTransport E E')
    (σ : AlgebraicClosure E' ≃ₐ[E'] AlgebraicClosure E')
    (h : T.closureEquiv.trans σ.toRingEquiv = U.closureEquiv) :
    (N.mapEquiv T).trans ((N.map T).restrictAlgEquiv σ).toRingEquiv =
      N.correctedMapEquiv T U σ h := by
  apply RingEquiv.ext
  intro x
  apply Subtype.ext
  simp only [correctedMapEquiv, RingEquiv.trans_apply, mapEquiv,
    mapFieldEquiv, coe_restrictAlgEquiv_toRingEquiv_apply,
    AlgebraicClosureTransport.equivOfEq_val]
  exact congrArg
    (fun e : AlgebraicClosure E ≃+* AlgebraicClosure E' ↦
      e (x : AlgebraicClosure E)) h

end FiniteNormalCover

end AlgebraicClosureTransport

namespace FiniteCorrespondencePair

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
  (P : FiniteCorrespondencePair k Ω)

/-- The canonical finite normal curve cover generated by the selected
correspondence branch over its source coordinate field. -/
def sourceFiniteNormalCover :
    AlgebraicClosureTransport.FiniteNormalCover (↥P.sourceField) where
  field := FiniteCover.canonicalNormalClosure P.sourceField_le_branchField
  finiteDimensional :=
    FiniteCover.canonicalNormalClosure_finiteDimensional
      P.sourceField_le_branchField P.branchOverSource_finiteDimensional
  normal := by
    letI := P.branchOverSource_finiteDimensional
    exact FiniteCover.canonicalNormalClosure_normal
      P.sourceField_le_branchField
      (Algebra.IsAlgebraic.of_finite
        (↥P.sourceField) (↥P.branchOverSource))

end FiniteCorrespondencePair

end

end AclGeom
