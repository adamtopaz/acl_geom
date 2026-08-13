/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.FiniteClosurePullback

/-!
# Composition for embedding-preserving algebraic-closure charts

An algebraic-closure equivalence extending a field embedding can be
precomposed by a field equivalence of its source.  The resulting comparison
retains an exact restriction theorem for the composite embedding.
-/

namespace AclGeom

noncomputable section

namespace AlgebraicClosureTransport.EmbeddingClosureEquiv

variable {E E' E₀ : Type*} [Field E] [Field E'] [Field E₀]
  {f : E →+* E'} (C : EmbeddingClosureEquiv f)

/-- Precompose an embedding-preserving closure equivalence with a field
equivalence of its source. -/
def precompRingEquiv (e : E₀ ≃+* E) :
    EmbeddingClosureEquiv (f.comp e.toRingHom) where
  closureEquiv :=
    (AlgebraicClosureTransport.lift e).closureEquiv.trans C.closureEquiv
  commutes x := by
    change C.closureEquiv
        ((AlgebraicClosureTransport.lift e).closureEquiv
          (algebraMap E₀ (AlgebraicClosure E₀) x)) =
      algebraMap E' (AlgebraicClosure E') (f (e x))
    rw [AlgebraicClosureTransport.commutes_apply, C.commutes]
    rfl

end AlgebraicClosureTransport.EmbeddingClosureEquiv

end


end AclGeom
