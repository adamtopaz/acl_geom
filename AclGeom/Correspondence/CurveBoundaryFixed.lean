/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveBoundaryAction
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# The actual curve boundary is fixed jointly

**Status:** proved over an ACF base for an actual integral separated finite-type dimension-one
curve, an actual connected algebraic-group regular action and an actual equivariant nonempty
open immersion. Literal complement finiteness and closedness are internal. Each actual
boundary point has an internally constructed field-point whose orbit is a constant SCHEME
morphism; fixedness holds over every test scheme in the base universe. No affine, normal or
proper hypothesis is used.

The regular action on the ambient curve is an actual input. Projective presentation, joint
regularity of extended rational families, rational-action regularization and the full original
classifier remain owed. Original group/chunk/six-point statements, algebraization/descent and
every true bypassed auxiliary remain obligations. All eight original #21 work items and the
full durable goal remain active and incomplete.

For actual smooth integral dimension-one curves over an ACF base, SmoothCurveStalks now
derives integral closedness of every actual stalk and DVRs at closed points internally; its
actual connected-group and individual proper-smooth extension consumers have no normality
premise.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.CurveBoundary
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The literal complement of an actual nonempty curve open is finite and closed-pointed.
Noetherianity comes from actual finite type. Named consumer: joint boundary fixedness. -/
theorem finite_closed_boundary
    (V : Over (Spec (.of k))) [IsIntegral V.left] [LocallyOfFiniteType V.hom]
    [QuasiCompact V.hom] (hdim : topologicalKrullDim V.left = 1)
    (U : Over (Spec (.of k))) [Nonempty U.left] (j : U ⟶ V) [IsOpenImmersion j.left] :
    ((Set.range j.left)ᶜ).Finite ∧
      ∀ x ∈ (Set.range j.left)ᶜ, IsClosed ({x} : Set V.left) := by
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  have : CompactSpace V.left := QuasiCompact.compactSpace_of_compactSpace V.hom
  have : IsNoetherian V.left := ⟨⟩
  have : Nonempty j.left.opensRange :=
    ⟨⟨j.left (Classical.arbitrary U.left), Classical.arbitrary U.left, rfl⟩⟩
  simpa only [Scheme.Hom.coe_opensRange] using
    finite_closed_complement V.left hdim j.left.opensRange

/-- Every actual boundary orbit of an equivariant curve open is a constant SCHEME morphism.
The literal finite boundary and connectedness force topological constancy; reduced-source
closed-point detection gives the actual morphism identity. Named consumer: the full source
finite-boundary fixedness assertion, including every coefficient algebra. -/
theorem orbitMap_eq_constant
    (G : ConnectedAlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [LocallyOfFiniteType V.hom]
    [QuasiCompact V.hom] [IsSeparated V.hom] [ModObj G.toGroupScheme.X V]
    (hdim : topologicalKrullDim V.left = 1)
    (U : Over (Spec (.of k))) [Nonempty U.left] [ModObj G.toGroupScheme.X U]
    (j : U ⟶ V) [IsOpenImmersion j.left] [IsModHom G.toGroupScheme.X j]
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ V)
    (hp : p.left (IsLocalRing.closedPoint k) ∉ Set.range j.left) :
    orbitMap G.toAlgebraicGroup V p = toUnit G.toGroupScheme.X ≫ p := by
  let GX := G.toGroupScheme.X
  let f := orbitMap G.toAlgebraicGroup V p
  let B : Set V.left := (Set.range j.left)ᶜ
  obtain ⟨hfinite, hclosed⟩ := finite_closed_boundary V hdim U j
  have hB : IsClosed B := j.left.opensRange.isOpen.isClosed_compl
  have : JacobsonSpace GX.left := LocallyOfFiniteType.jacobsonSpace GX.hom
  have hpoints : closedPoints GX.left ⊆ f.left ⁻¹' B := by
    intro a ha
    let q : 𝟙_ (Over (Spec (.of k))) ⟶ GX :=
      Over.homMk (pointOfClosedPoint GX.hom a ha) (pointOfClosedPoint_comp GX.hom a ha)
    have hq : q.left (IsLocalRing.closedPoint k) = a :=
      pointOfClosedPoint_apply GX.hom a ha _
    have h := congrArg (fun z : 𝟙_ (Over (Spec (.of k))) ⟶ V ↦
      z.left (IsLocalRing.closedPoint k)) (orbitMap_point G.toAlgebraicGroup V p q)
    change f.left (q.left (IsLocalRing.closedPoint k)) =
      (ModObj.pointAct V q).left (p.left (IsLocalRing.closedPoint k)) at h
    rw [hq] at h
    change f.left a ∉ Set.range j.left
    rw [h]
    exact pointAct_mem_complement j q _ hp
  have hmem : ∀ a : GX.left, f.left a ∈ B := by
    have hc := closure_minimal hpoints (hB.preimage f.left.continuous)
    rw [closure_closedPoints] at hc
    exact fun a ↦ hc (Set.mem_univ a)
  have hconst := constant_of_finite_closed_range f.left f.left.continuous B
    hfinite hclosed hmem
  have hone : (1 : 𝟙_ (Over (Spec (.of k))) ⟶ GX) ≫ f = p := by
    rw [orbitMap_point, ModObj.pointAct_one, Category.comp_id]
  have hvalue := congrArg (fun z : 𝟙_ (Over (Spec (.of k))) ⟶ V ↦
    z.left (IsLocalRing.closedPoint k)) hone
  change f.left ((1 : 𝟙_ (Over (Spec (.of k))) ⟶ GX).left
    (IsLocalRing.closedPoint k)) = p.left (IsLocalRing.closedPoint k) at hvalue
  apply Over.OverMorphism.ext
  have : LocallyOfFiniteType (f.left ≫ V.hom) := by rw [Over.w f]; infer_instance
  refine AlgebraicGeometry.ext_of_apply_eq V.hom Set.univ isClosed_univ.isLocallyClosed
    dense_univ ?_ ((Over.w f).trans (Over.w (toUnit GX ≫ p)).symm)
  intro a _ _
  change f.left a = p.left ((toUnit GX).left a)
  exact (hconst a ((1 : 𝟙_ (Over (Spec (.of k))) ⟶ GX).left
    (IsLocalRing.closedPoint k))).trans
      (hvalue.trans (congrArg p.left
        (Subsingleton.elim (IsLocalRing.closedPoint k) ((toUnit GX).left a))))

/-- The literal finite boundary of an actual equivariant nonempty curve open is fixed
jointly. The orbit morphism identity retains fixedness on every test scheme, hence over
all coefficient algebras. No finite-boundary or fixedness certificate is a caller premise.
This proves the source boundary assertion for the GIVEN regular action; it constructs no
completion or jointly regular extension of a rational family. -/
theorem fixed_boundary
    (G : ConnectedAlgebraicGroup k)
    (V : Over (Spec (.of k))) [IsIntegral V.left] [LocallyOfFiniteType V.hom]
    [QuasiCompact V.hom] [IsSeparated V.hom] [ModObj G.toGroupScheme.X V]
    (hdim : topologicalKrullDim V.left = 1)
    (U : Over (Spec (.of k))) [Nonempty U.left] [ModObj G.toGroupScheme.X U]
    (j : U ⟶ V) [IsOpenImmersion j.left] [IsModHom G.toGroupScheme.X j] :
    ((Set.range j.left)ᶜ).Finite ∧
      (∀ x ∈ (Set.range j.left)ᶜ, IsClosed ({x} : Set V.left)) ∧
      ∀ x ∈ (Set.range j.left)ᶜ,
        ∃ p : 𝟙_ (Over (Spec (.of k))) ⟶ V,
          p.left (IsLocalRing.closedPoint k) = x ∧
          orbitMap G.toAlgebraicGroup V p = toUnit G.toGroupScheme.X ≫ p ∧
          ∀ (T : Over (Spec (.of k))) (q : T ⟶ G.toGroupScheme.X),
            q • (toUnit T ≫ p) = toUnit T ≫ p := by
  obtain ⟨hf, hc⟩ := finite_closed_boundary V hdim U j
  refine ⟨hf, hc, ?_⟩
  intro x hx
  let p : 𝟙_ (Over (Spec (.of k))) ⟶ V :=
    Over.homMk (pointOfClosedPoint V.hom x (hc x hx))
      (pointOfClosedPoint_comp V.hom x (hc x hx))
  have hp : p.left (IsLocalRing.closedPoint k) = x :=
    pointOfClosedPoint_apply V.hom x (hc x hx) _
  have hfix := orbitMap_eq_constant G V hdim U j p (hp ▸ hx)
  refine ⟨p, hp, hfix, ?_⟩
  intro T q
  have h := congrArg (fun z : G.toGroupScheme.X ⟶ V ↦ q ≫ z) hfix
  change q ≫ lift (𝟙 _) (toUnit G.toGroupScheme.X ≫ p) ≫
    γ[G.toGroupScheme.X, V] = q ≫ toUnit G.toGroupScheme.X ≫ p at h
  simpa only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc, Hom.smul_def] using h

end
end AclGeom.CurveBoundary
