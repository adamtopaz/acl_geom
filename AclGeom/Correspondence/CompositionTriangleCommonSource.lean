/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CompositionTriangleExtension
import AclGeom.Correspondence.FiniteClosurePullback

/-!
# Extending a composition triangle to a prescribed common source chart

A source equivalence extends to algebraic closures.  Pulling a prescribed
finite target field back through that extension gives a source field on which
the equivalence restricts to an honest chart.  Extending a strict composition
triangle across that pullback therefore puts its source on the prescribed
common field without changing either semantic composition or the selected
base-field restriction.
-/

namespace AclGeom

open IntermediateField

noncomputable section

universe u

namespace AlgebraicClosureTransport.EmbeddingClosureEquiv

variable {E E' : Type*} [Field E] [Field E']

/-- Regard a field equivalence as an embedding with a chosen extension to
algebraic closures.  This is the equivalence-valued counterpart of
`EmbeddingClosureEquiv.ofAlgebraic`; it uses the semilinear closure lift and
retains its exact restriction to the source field. -/
noncomputable def ofRingEquiv (e : E ≃+* E') :
    EmbeddingClosureEquiv e.toRingHom where
  closureEquiv := (AlgebraicClosureTransport.lift e).closureEquiv
  commutes x := (AlgebraicClosureTransport.lift e).commutes_apply x

end AlgebraicClosureTransport.EmbeddingClosureEquiv

namespace FieldEquiv.CompositionTriangle

variable {X Y Z X' : Type u}
  [Field X] [Field Y] [Field Z] [Field X']
  (T : FieldEquiv.CompositionTriangle X Y Z)

/-- The inverse image of a prescribed common source field under the chosen
algebraic-closure extension of a source chart. -/
noncomputable def commonSourcePullbackField
    (sourceChart : X ≃+* X')
    (commonSource : IntermediateField X' (AlgebraicClosure X')) :
    IntermediateField X (AlgebraicClosure X) :=
  (AlgebraicClosureTransport.EmbeddingClosureEquiv.ofRingEquiv sourceChart)
    |>.pullbackField commonSource

/-- Extend a strict triangle across the finite source obtained by pulling a
prescribed common source field back through `sourceChart`. -/
noncomputable def sourceExtensionAlongChart
    (sourceChart : X ≃+* X')
    (commonSource : IntermediateField X' (AlgebraicClosure X')) :=
  T.sourceExtension (commonSourcePullbackField sourceChart commonSource)

/-- The restricted source chart from the pullback source field to the one
literal prescribed common source. -/
noncomputable def commonSourcePullbackChart
    (sourceChart : X ≃+* X')
    (commonSource : IntermediateField X' (AlgebraicClosure X')) :
    (↥(commonSourcePullbackField sourceChart commonSource)) ≃+*
      (↥commonSource) :=
  (AlgebraicClosureTransport.EmbeddingClosureEquiv.ofRingEquiv sourceChart)
    |>.pullbackEquiv commonSource

/-- On the entire original source field, the restricted common chart is the
chosen source equivalence followed by the common-field algebra map. -/
@[simp] theorem commonSourcePullbackChart_algebraMap
    (sourceChart : X ≃+* X')
    (commonSource : IntermediateField X' (AlgebraicClosure X'))
    (x : X) :
    commonSourcePullbackChart sourceChart commonSource
        (algebraMap X
          (↥(commonSourcePullbackField sourceChart commonSource)) x) =
      algebraMap X' (↥commonSource) (sourceChart x) := by
  exact
    (AlgebraicClosureTransport.EmbeddingClosureEquiv.ofRingEquiv sourceChart)
      |>.pullbackEquiv_algebraMap commonSource x

/-- Ring-hom form of `commonSourcePullbackChart_algebraMap`, already
associated with an arbitrary map into the old source field.  This avoids
unfolding a deeply nested intermediate-field tower at each concrete
application. -/
theorem commonSourcePullbackChart_comp_algebraMap_comp
    {W : Type u} [Semiring W]
    (sourceChart : X ≃+* X')
    (commonSource : IntermediateField X' (AlgebraicClosure X'))
    (g : W →+* X) :
    (commonSourcePullbackChart sourceChart commonSource).toRingHom.comp
        ((algebraMap X
          (↥(commonSourcePullbackField sourceChart commonSource))).comp g) =
      (algebraMap X' (↥commonSource)).comp
        (sourceChart.toRingHom.comp g) := by
  apply RingHom.ext
  intro x
  exact commonSourcePullbackChart_algebraMap sourceChart commonSource (g x)

/-- The right square of a source extension remains exact after precomposing
the old-middle inclusion with any selected branch map. -/
theorem sourceExtensionRightEquiv_comp_middleRingHom_comp
    {W : Type u} [Semiring W]
    (source : IntermediateField X (AlgebraicClosure X))
    (g : W →+* Y) :
    (T.sourceExtension source).right.toRingHom.comp
        ((T.sourceExtensionMiddleRingHom source).comp g) =
      (T.sourceExtensionTargetRingHom source).comp
        (T.right.toRingHom.comp g) := by
  have h := T.sourceExtensionRightEquiv_comp_middleRingHom source
  have hc := congrArg (fun f ↦ f.comp g) h
  simpa only [sourceExtension, RingHom.comp_assoc] using hc

end FieldEquiv.CompositionTriangle

end

end AclGeom
