/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.Bijections
import GroupConfig.Germ.HomogeneousSpace

/-!
# Transport of germs between representing tuples

Blueprint `sources/group_configuration/04-germs.tex`, `def:germ`, and
`sources/group_configuration/08-proof.tex`, the first paragraph of the proof of
`lem:hw-basechange`.

A germ is a germ between varieties: it depends on the tuples `a`, `a'` only through their loci
over `k`. If `a₁` and `a'₁` have the same vanishing ideals over `k` as `a` and `a'`, a
representative of a germ `V → V'` from the locus of `a` to the locus of `a'` is one from the
locus of `a₁` to the locus of `a'₁`, with the same field and expression
(`Representative.transport`). This gives an equivalence of germs (`Germ.transportEquiv`)
preserving graph ideals, canonical bases, values, conjugation, composition, identities and
inverses, generic sets and difference sets. Consequently it carries Hrushovski–Weil data to
Hrushovski–Weil data (`Germ.IsHWBij.transport`, `Germ.IsHW.transport`), with isomorphic groups
and equivariantly isomorphic homogeneous spaces (`Germ.IsHW.transportGroupEquiv`,
`Germ.IsHW.transportSpaceEquiv`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** complete.
-/

namespace GroupConfig

open AclGeom IntermediateField Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {ι κ μ : Type*}
  {a a₁ : ι → K} {a' a'₁ : κ → K} {a'' a''₁ : μ → K}

/-- Genericity over `M` for the locus of a tuple depends only on its vanishing ideal over `k`. -/
theorem isGenericOver_iff_of_idealOf_eq {M : IntermediateField k K}
    (h : idealOf k a₁ = idealOf k a) (y : ι → K) :
    IsGenericOver M a₁ y ↔ IsGenericOver M a y := by
  unfold IsGenericOver
  rw [h]

/-- Genericity over `k` for the locus of a tuple depends only on its vanishing ideal. -/
theorem isGen_iff_of_idealOf_eq (h : idealOf k a₁ = idealOf k a) (y : ι → K) :
    IsGen k a₁ y ↔ IsGen k a y := by
  unfold IsGen
  rw [h]

variable [IsAlgClosed K] (h : idealOf k a₁ = idealOf k a) (h' : idealOf k a'₁ = idealOf k a')
  (h'' : idealOf k a''₁ = idealOf k a'')

namespace Representative

/-- A representative between the loci of `a` and `a'` as a representative between the loci of
`a₁` and `a'₁`: the same field and expression. -/
def transport (r : Representative k K a a') : Representative k K a₁ a'₁ where
  M := r.M
  isAlgClosed := r.isAlgClosed
  isSmall := r.isSmall
  f := r.f
  isDefinedAt y hy := r.isDefinedAt y ((isGenericOver_iff_of_idealOf_eq h y).1 hy)
  isGenericOver y hy := (isGenericOver_iff_of_idealOf_eq h' _).2
    (r.isGenericOver y ((isGenericOver_iff_of_idealOf_eq h y).1 hy))

theorem equivalent_transport_iff {r r' : Representative k K a a'} :
    (r.transport h h').Equivalent (r'.transport h h') ↔ r.Equivalent r' :=
  forall_congr' fun y ↦ imp_congr_left (isGenericOver_iff_of_idealOf_eq h y)

end Representative

namespace Germ

variable [IsAlgClosed k] [UniversalDomain k K] [Finite ι] [Finite κ] [Finite μ]

/-- `def:germ`: a germ between the loci of `a` and `a'` as a germ between the loci of `a₁` and
`a'₁`. -/
def transport (g : Germ k a a') : Germ k a₁ a'₁ :=
  Quotient.map (Representative.transport h h')
    (fun _ _ hr ↦ (Representative.equivalent_transport_iff h h').2 hr) g

omit [Finite κ] in
theorem transport_mk (r : Representative k K a a') :
    transport h h' (⟦r⟧ : Germ k a a') = ⟦r.transport h h'⟧ := rfl

omit [Finite κ] in
theorem transport_transport (g : Germ k a a') :
    (g.transport h h').transport h.symm h'.symm = g :=
  Quotient.inductionOn g fun _ ↦ rfl

/-- `def:germ`: germs depend only on the loci of the representing tuples. -/
def transportEquiv : Germ k a a' ≃ Germ k a₁ a'₁ where
  toFun := transport h h'
  invFun := transport h.symm h'.symm
  left_inv := transport_transport h h'
  right_inv := transport_transport h.symm h'.symm

omit [Finite κ] in
theorem transport_injective : Function.Injective (transport h h' : Germ k a a' → _) :=
  (transportEquiv h h').injective

omit [Finite κ] in
theorem transport_surjective : Function.Surjective (transport h h' : Germ k a a' → _) :=
  (transportEquiv h h').surjective

theorem graphIdeal_transport (g : Germ k a a') : (g.transport h h').graphIdeal = g.graphIdeal := by
  induction g using Quotient.inductionOn with
  | h r =>
    obtain ⟨y, hy⟩ := exists_isGenericOver r.isSmall a
    change Representative.graphIdeal (r.transport h h') = r.graphIdeal
    rw [Representative.graphIdeal_eq (r.transport h h')
      ((isGenericOver_iff_of_idealOf_eq h y).2 hy), Representative.graphIdeal_eq r hy]
    rfl

theorem cb_transport (g : Germ k a a') : (g.transport h h').cb = g.cb := by
  unfold cb
  rw [graphIdeal_transport]

theorem eval_transport (g : Germ k a a') (F : IntermediateField k K) (y : ι → K) :
    (g.transport h h').eval F y = g.eval F y := by
  unfold eval IsGraphGeneric
  rw [graphIdeal_transport]

theorem evalGen_transport (g : Germ k a a') (y : ι → K) :
    (g.transport h h').evalGen y = g.evalGen y := by
  unfold evalGen
  rw [cb_transport, eval_transport]

omit [Finite κ] in
theorem map_transport (σ : K ≃ₐ[k] K) (g : Germ k a a') :
    (g.map σ).transport h h' = (g.transport h h').map σ :=
  -- The two representatives have the same expression; comparing them as structures is costly.
  Quotient.inductionOn g fun _ ↦ Quotient.sound fun _ _ ↦ rfl

theorem comp_transport (g' : Germ k a' a'') (g : Germ k a a') :
    (Germ.comp g' g).transport h h'' = Germ.comp (g'.transport h' h'') (g.transport h h') :=
  Quotient.inductionOn₂ g' g fun _ _ ↦ rfl

theorem id_transport : (Germ.id a).transport h h = Germ.id a₁ := rfl

theorem isInverse_transport_iff {g : Germ k a a'} {f : Germ k a' a} :
    IsInverse (f.transport h' h) (g.transport h h') ↔ IsInverse f g := by
  unfold IsInverse
  rw [← comp_transport, ← comp_transport, ← id_transport h, ← id_transport h',
    (transport_injective h h).eq_iff, (transport_injective h' h').eq_iff]

theorem isInvertible_transport_iff {g : Germ k a a'} :
    IsInvertible (g.transport h h') ↔ IsInvertible g := by
  constructor
  · rintro ⟨f, hf⟩
    rw [← transport_transport h'.symm h.symm f] at hf
    exact ⟨_, (isInverse_transport_iff h h').1 hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨_, (isInverse_transport_iff h h').2 hf⟩

omit [Finite κ] in
theorem transport_mem_orbit_iff {g₀ g : Germ k a a'} :
    g.transport h h' ∈ orbit (g₀.transport h h') ↔ g ∈ orbit g₀ := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, transport_injective h h' (((map_transport h h' σ g₀)).trans hσ)⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, (map_transport h h' σ g₀).symm⟩

omit [Finite κ] in
/-- Every member of the generic set of a transported germ is a transported member. -/
theorem exists_of_mem_orbit_transport {g₀ : Germ k a a'} {f : Germ k a₁ a'₁}
    (hf : f ∈ orbit (g₀.transport h h')) : ∃ g ∈ orbit g₀, g.transport h h' = f := by
  obtain ⟨g, rfl⟩ := transport_surjective h h' f
  exact ⟨g, (transport_mem_orbit_iff h h').1 hf, rfl⟩

theorem transport_mem_diffSet_iff {f₀ : Germ k a a'} {δ : Germ k a a} :
    δ.transport h h ∈ diffSet (f₀.transport h h') ↔ δ ∈ diffSet f₀ := by
  constructor
  · rintro ⟨e₁, he₁, e₂, he₂, d₁, hd₁, hind, hδ⟩
    obtain ⟨f₁, hf₁, rfl⟩ := exists_of_mem_orbit_transport h h' he₁
    obtain ⟨f₂, hf₂, rfl⟩ := exists_of_mem_orbit_transport h h' he₂
    obtain ⟨g₁, rfl⟩ := transport_surjective h' h d₁
    rw [cb_transport, cb_transport] at hind
    rw [← comp_transport] at hδ
    exact ⟨f₁, hf₁, f₂, hf₂, g₁, (isInverse_transport_iff h h').1 hd₁, hind,
      transport_injective h h hδ⟩
  · rintro ⟨f₁, hf₁, f₂, hf₂, g₁, hg₁, hind, rfl⟩
    refine ⟨_, (transport_mem_orbit_iff h h').2 hf₁, _, (transport_mem_orbit_iff h h').2 hf₂,
      _, (isInverse_transport_iff h h').2 hg₁, ?_, comp_transport h h' h g₁ f₂⟩
    rwa [cb_transport, cb_transport]

/-- Every difference germ of a transported germ is a transported difference germ. -/
theorem exists_of_mem_diffSet_transport {f₀ : Germ k a a'} {δ : Germ k a₁ a₁}
    (hδ : δ ∈ diffSet (f₀.transport h h')) : ∃ δ₀ ∈ diffSet f₀, δ₀.transport h h = δ := by
  obtain ⟨δ₀, rfl⟩ := transport_surjective h h δ
  exact ⟨δ₀, (transport_mem_diffSet_iff h h').1 hδ, rfl⟩

/-- The Hrushovski–Weil hypotheses for bijections do not depend on the representing tuples. -/
theorem IsHWBij.transport {f₀ : Germ k a a'} (hb : IsHWBij f₀) : IsHWBij (f₀.transport h h') := by
  refine ⟨(isInvertible_transport_iff h h').2 hb.isInvertible, fun f hf y hy hind ↦ ?_,
    fun δ hδ ↦ ?_⟩
  · obtain ⟨g, hg, rfl⟩ := exists_of_mem_orbit_transport h h' hf
    rw [cb_transport] at hind
    rw [evalGen_transport]
    exact hb.trans g hg y ((isGen_iff_of_idealOf_eq h y).1 hy) hind
  · obtain ⟨δ₀, hδ₀, rfl⟩ := exists_of_mem_diffSet_transport h h' hδ
    rw [cb_transport, cb_transport]
    exact hb.rank δ₀ hδ₀

/-! ### Germs of a locus to itself -/

/-- Transport of germs of a locus to itself, as a monoid isomorphism. -/
def transportMulEquiv : Germ k a a ≃* Germ k a₁ a₁ where
  __ := transportEquiv h h
  map_mul' g g' := comp_transport h h h g g'

theorem transportMulEquiv_apply (g : Germ k a a) : transportMulEquiv h g = g.transport h h := rfl

/-- The Hrushovski–Weil hypotheses do not depend on the representing tuple. -/
theorem IsHW.transport {g₀ : Germ k a a} (hw : IsHW g₀) : IsHW (g₀.transport h h) := by
  refine ⟨?_, fun e he y hy hind ↦ ?_, fun e he d hd ↦ ?_, fun e₁ he₁ e₂ he₂ hind ↦ ?_⟩
  · rw [← transportMulEquiv_apply]
    exact hw.isUnit.map _
  · obtain ⟨g, hg, rfl⟩ := exists_of_mem_orbit_transport h h he
    rw [cb_transport] at hind
    rw [evalGen_transport]
    exact hw.trans g hg y ((isGen_iff_of_idealOf_eq h y).1 hy) hind
  · obtain ⟨g, hg, rfl⟩ := exists_of_mem_orbit_transport h h he
    obtain ⟨f, rfl⟩ := transport_surjective h h d
    exact (transport_mem_orbit_iff h h).2
      (hw.inv g hg f ((isInverse_transport_iff h h).1 hd))
  · obtain ⟨g₁, hg₁, rfl⟩ := exists_of_mem_orbit_transport h h he₁
    obtain ⟨g₂, hg₂, rfl⟩ := exists_of_mem_orbit_transport h h he₂
    rw [cb_transport, cb_transport] at hind
    rw [mul_def, ← comp_transport]
    exact (transport_mem_orbit_iff h h).2 (hw.comp g₁ hg₁ g₂ hg₂ hind)

theorem transport_mem_prodSet_iff {g₀ γ : Germ k a a} :
    γ.transport h h ∈ IsHW.prodSet (g₀.transport h h) ↔ γ ∈ IsHW.prodSet g₀ := by
  constructor
  · rintro ⟨f₁, hf₁, f₂, hf₂, hγ⟩
    obtain ⟨g₁, hg₁, rfl⟩ := exists_of_mem_orbit_transport h h hf₁
    obtain ⟨g₂, hg₂, rfl⟩ := exists_of_mem_orbit_transport h h hf₂
    rw [mul_def, ← comp_transport] at hγ
    exact ⟨g₁, hg₁, g₂, hg₂, transport_injective h h hγ⟩
  · rintro ⟨g₁, hg₁, g₂, hg₂, rfl⟩
    exact ⟨_, (transport_mem_orbit_iff h h).2 hg₁, _, (transport_mem_orbit_iff h h).2 hg₂,
      comp_transport h h h g₁ g₂⟩

namespace IsHW

variable {g₀ : Germ k a a} (hw : IsHW g₀)
include hw

/-! ### The group -/

/-- Transport on the group generated by the generic set. -/
def transportGroupHom : ↥hw.prodSubgroup →* ↥(hw.transport h).prodSubgroup :=
  ((Units.map (transportMulEquiv h).toMonoidHom).comp hw.prodSubgroup.subtype).codRestrict _
    fun δ ↦ (transport_mem_prodSet_iff h).2 (hw.val_mem δ)

theorem val_transportGroupHom (δ : ↥hw.prodSubgroup) :
    (hw.transport h).val (hw.transportGroupHom h δ) = (hw.val δ).transport h h := rfl

theorem transportGroupHom_bijective : Function.Bijective (hw.transportGroupHom h) := by
  refine ⟨fun δ δ' hδ ↦ hw.val_injective ?_, fun ε ↦ ?_⟩
  · have e := congrArg (hw.transport h).val hδ
    rw [val_transportGroupHom, val_transportGroupHom] at e
    exact transport_injective h h e
  · obtain ⟨γ, hγ⟩ := transport_surjective h h ((hw.transport h).val ε)
    have hmem : γ ∈ prodSet g₀ := by
      rw [← transport_mem_prodSet_iff h, hγ]
      exact (hw.transport h).val_mem ε
    refine ⟨hw.ofMem hmem, (hw.transport h).val_injective ?_⟩
    rw [val_transportGroupHom, val_ofMem, hγ]

/-- The groups generated by the generic set and by its transport are isomorphic. -/
def transportGroupEquiv : ↥hw.prodSubgroup ≃* ↥(hw.transport h).prodSubgroup :=
  MulEquiv.ofBijective _ (hw.transportGroupHom_bijective h)

theorem val_transportGroupEquiv (δ : ↥hw.prodSubgroup) :
    (hw.transport h).val (hw.transportGroupEquiv h δ) = (hw.val δ).transport h h := rfl

/-! ### The homogeneous space -/

omit hw in
/-- A pair for `g₀` as a pair for its transport. -/
def transportPair (p : Pair g₀) : Pair (g₀.transport h h) :=
  ⟨p.γ.transport h h, (transport_mem_prodSet_iff h).2 p.mem, p.pt,
    (isGen_iff_of_idealOf_eq h p.pt).2 p.isGen⟩

omit hw in
theorem base_transportPair (p : Pair g₀) : (transportPair h p).base = p.base := by
  change ((p.γ.transport h h).cb : Set K) ∪ range p.pt = (p.γ.cb : Set K) ∪ range p.pt
  rw [cb_transport]

omit hw in
theorem rel_transportPair_iff {p q : Pair g₀} :
    (transportPair h p).Rel (transportPair h q) ↔ p.Rel q := by
  unfold Pair.Rel
  rw [base_transportPair, base_transportPair]
  constructor
  · intro hr f hf hind
    have e := hr (f.transport h h) ((transport_mem_orbit_iff h h).2 hf) (by rwa [cb_transport])
    change (f.transport h h * p.γ.transport h h).evalGen p.pt =
      (f.transport h h * q.γ.transport h h).evalGen q.pt at e
    rwa [mul_def, mul_def, ← comp_transport, ← comp_transport, evalGen_transport,
      evalGen_transport] at e
  · intro hr f hf hind
    obtain ⟨g, hg, rfl⟩ := exists_of_mem_orbit_transport h h hf
    rw [cb_transport] at hind
    change (g.transport h h * p.γ.transport h h).evalGen p.pt =
      (g.transport h h * q.γ.transport h h).evalGen q.pt
    rw [mul_def, mul_def, ← comp_transport, ← comp_transport, evalGen_transport,
      evalGen_transport]
    exact hr g hg hind

/-- Transport on the homogeneous space. -/
def transportSpace : hw.Space → (hw.transport h).Space :=
  Quotient.lift (fun p ↦ (hw.transport h).ofPair (transportPair h p))
    (fun _ _ hr ↦ (hw.transport h).ofPair_eq_ofPair.2 ((rel_transportPair_iff h).2 hr))

theorem transportSpace_ofPair (p : Pair g₀) :
    hw.transportSpace h (hw.ofPair p) = (hw.transport h).ofPair (transportPair h p) := rfl

theorem transportSpace_bijective : Function.Bijective (hw.transportSpace h) := by
  refine ⟨fun s t ↦ ?_, fun s ↦ ?_⟩
  · refine hw.ind (fun p ↦ ?_) s
    refine hw.ind (fun q ↦ ?_) t
    intro hst
    rw [transportSpace_ofPair, transportSpace_ofPair, ofPair_eq_ofPair] at hst
    exact hw.ofPair_eq_ofPair.2 ((rel_transportPair_iff h).1 hst)
  · refine (hw.transport h).ind (fun p ↦ ?_) s
    obtain ⟨γ, hγ⟩ := transport_surjective h h p.γ
    have hmem : γ ∈ prodSet g₀ := by
      rw [← transport_mem_prodSet_iff h, hγ]
      exact p.mem
    refine ⟨hw.ofPair ⟨γ, hmem, p.pt, (isGen_iff_of_idealOf_eq h p.pt).1 p.isGen⟩, ?_⟩
    rw [transportSpace_ofPair]
    exact congrArg (hw.transport h).ofPair (Pair.ext hγ rfl)

/-- The homogeneous spaces of the generic set and of its transport are equivalent. -/
def transportSpaceEquiv : hw.Space ≃ (hw.transport h).Space :=
  Equiv.ofBijective _ (hw.transportSpace_bijective h)

theorem transportSpaceEquiv_ofPair (p : Pair g₀) :
    hw.transportSpaceEquiv h (hw.ofPair p) = (hw.transport h).ofPair (transportPair h p) := rfl

/-- The equivalence of homogeneous spaces is equivariant along the isomorphism of groups. -/
theorem transportSpaceEquiv_smul (δ : ↥hw.prodSubgroup) (s : hw.Space) :
    hw.transportSpaceEquiv h (δ • s) = hw.transportGroupEquiv h δ • hw.transportSpaceEquiv h s := by
  refine hw.ind (fun p ↦ ?_) s
  rw [smul_ofPair, transportSpaceEquiv_ofPair, transportSpaceEquiv_ofPair, smul_ofPair]
  refine congrArg (hw.transport h).ofPair (Pair.ext ?_ rfl)
  change (hw.val δ * p.γ).transport h h = (hw.val δ).transport h h * p.γ.transport h h
  exact comp_transport h h h _ _

/-- The equivalence of homogeneous spaces is compatible with the embeddings of the generic
points. -/
theorem transportSpaceEquiv_iota {y : ι → K} (hy : IsGen k a y) :
    hw.transportSpaceEquiv h (hw.iota hy) =
      (hw.transport h).iota ((isGen_iff_of_idealOf_eq h y).2 hy) := rfl

end IsHW

end Germ

end

end GroupConfig
