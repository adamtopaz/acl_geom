/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import GroupConfig.Rref
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Basic

/-!
# Literal scalar extension of a field-defined subspace

Supplemental `def:subspace-defined`: the `F`-valued part is the actual subspace
`W ∩ F^𝓜`. Its tensor product with the ambient field maps canonically into the
coordinate space. The image is exactly the span used by `DefinedOver`, so
field-definedness is equivalent to that image being `W`. Flatness and Mathlib's
finite-product tensor equivalence give injectivity for finite coordinates.

**Status:** the literal tensor form is proved, with an actual linear equivalence
and its pure-tensor formula. Range and span statements allow arbitrary coordinate
types; the equivalence requires finite coordinates. No basis or isomorphism
certificate, order, algebraic closedness or universal domain is assumed.
-/

namespace GroupConfig

open scoped TensorProduct

noncomputable section

variable {R : Type*} [Field R] {𝓜 : Type*} (W : Submodule R (𝓜 → R)) (F : Subfield R)

/-- The `F`-subspace `W ∩ F^𝓜`, with its actual `F`-valued coordinates. -/
def coefficientFieldPart : Submodule F (𝓜 → F) :=
  (W.restrictScalars F).comap (coeVec F)

/-- The canonical scalar-extension map from `R ⊗[F] (W ∩ F^𝓜)` into the ambient space. -/
def coefficientExtension : R ⊗[F] ↥(coefficientFieldPart W F) →ₗ[R] (𝓜 → R) :=
  (TensorProduct.piScalarRightHom F R R 𝓜).comp
    ((coefficientFieldPart W F).subtype.baseChange R)

@[simp]
theorem coefficientExtension_tmul (r : R) (u : coefficientFieldPart W F) :
    coefficientExtension W F (r ⊗ₜ[F] u) = r • coeVec F (u : 𝓜 → F) := by
  ext j
  simp only [coefficientExtension, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    TensorProduct.piScalarRightHom_tmul, Pi.smul_apply, coeVec_apply]
  change (u.1 j : R) * r = r * (u.1 j : R)
  exact mul_comm _ _

/-- The literal tensor extension embeds in the ambient coordinate space. -/
theorem coefficientExtension_injective [Finite 𝓜] :
    Function.Injective (coefficientExtension W F) := by
  classical
  let _ := Fintype.ofFinite 𝓜
  exact (TensorProduct.piScalarRight F R R 𝓜).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap
      (coefficientFieldPart W F).subtype (Submodule.injective_subtype _))

/-- The image of the tensor extension is the span of the `F`-valued part. -/
theorem coefficientExtension_range :
    LinearMap.range (coefficientExtension W F) =
      Submodule.span R {v : 𝓜 → R | v ∈ W ∧ ∀ j, v j ∈ F} := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul r u =>
      rw [coefficientExtension_tmul]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨u.2, fun j ↦ (u.1 j).2⟩)
    | add z z' hz hz' => simpa only [map_add] using (Submodule.span R _).add_mem hz hz'
  · refine Submodule.span_le.2 ?_
    rintro v ⟨hv, hvF⟩
    let u : 𝓜 → F := fun j ↦ ⟨v j, hvF j⟩
    have hu : u ∈ coefficientFieldPart W F := hv
    refine ⟨1 ⊗ₜ[F] (⟨u, hu⟩ : coefficientFieldPart W F), ?_⟩
    rw [coefficientExtension_tmul, one_smul]
    rfl

/-- `def:subspace-defined`: the canonical scalar extension has range `W`
exactly when `W` is defined over `F`. -/
theorem definedOver_iff_coefficientExtension_range :
    DefinedOver W F ↔ LinearMap.range (coefficientExtension W F) = W := by
  rw [coefficientExtension_range]
  exact eq_comm

/-- `def:subspace-defined`, its literal tensor form: scalar extension of the
`F`-valued part is canonically isomorphic to the field-defined subspace. -/
theorem DefinedOver.exists_coefficientExtensionEquiv [Finite 𝓜] (h : DefinedOver W F) :
    ∃ e : R ⊗[F] ↥(coefficientFieldPart W F) ≃ₗ[R] W,
      ∀ (r : R) (u : coefficientFieldPart W F),
        (e (r ⊗ₜ[F] u) : 𝓜 → R) = r • coeVec F (u : 𝓜 → F) := by
  have hrange := (definedOver_iff_coefficientExtension_range W F).1 h
  let f := (coefficientExtension W F).codRestrict W fun z ↦ hrange.le ⟨z, rfl⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro z z' heq
      exact coefficientExtension_injective W F (congrArg Subtype.val heq)
    · intro w
      obtain ⟨z, hz⟩ : (w : 𝓜 → R) ∈ LinearMap.range (coefficientExtension W F) := by
        rw [hrange]
        exact w.2
      exact ⟨z, Subtype.ext hz⟩
  exact ⟨LinearEquiv.ofBijective f hbij, fun r u ↦ coefficientExtension_tmul W F r u⟩

end

end GroupConfig
