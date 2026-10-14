/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import GroupConfig.Germ.Definable

/-!
# Germs from triples

Blueprint `sources/group_configuration/04-germs.tex`, `lem:triple`.

A triple `(b; y, z)` (`GroupConfig.IsTriple`) consists of a parameter tuple `b` and generic
points `y`, `z` of the loci of `a`, `a'` which are independent from `b`, with `z` definable
over `b, y`.  It determines a germ `g_b` (`IsTriple.germ`) with canonical base in `acl(b)`
sending `y` to `z`, unique with these properties (`IsTriple.eq_germ`).  Its graph ideal is
the locus of `(y, z)` over `acl(b)` (`IsTriple.germ_graphIdeal`), its canonical base is
`Cb(yz/b)` (`IsTriple.germ_cb`) and lies in `dcl(b)` (`IsTriple.germ_cb_le_dcl`); it is
invertible iff `y` is definable over `b, z` (`IsTriple.isInvertible_iff`).  The construction
is equivariant (`IsTriple.germ_map`) and depends only on the image of `b`
(`IsTriple.germ_map_eq_of_comp_eq`), it is generically transitive when `y` and `z` are
independent (`IsTriple.indepOver_evalGen`), and `b` is interalgebraic with the canonical
base iff `b ⊆ acl(Cb(yz/b))` (`IsTriple.racl_cb_eq_iff`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** `lem:triple` complete.
-/

namespace GroupConfig

open AclGeom IntermediateField MvPolynomial Set

noncomputable section

attribute [local instance] isAlgClosed_racl

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
  [UniversalDomain k K] {ι κ μ : Type*} [Finite ι] [Finite κ] [Finite μ] {a : ι → K}
  {a' : κ → K}

/-! ### Equivariance of generic points and of `dcl(L, u)` -/

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite ι] in
theorem mem_dclAdjoin_map (σ : K ≃ₐ[k] K) {L : IntermediateField k K} {u : ι → K} {x : K}
    (hx : x ∈ dclAdjoin L u) : σ x ∈ dclAdjoin (L.map σ.toAlgHom) (⇑σ ∘ u) := by
  obtain ⟨n, P, Q, hQ, hx⟩ := mem_dclAdjoin_iff.1 hx
  refine mem_dclAdjoin_iff.2 ⟨n, MvPolynomial.map (intermediateFieldMap σ L).toRingHom P,
    MvPolynomial.map (intermediateFieldMap σ L).toRingHom Q, ?_, ?_⟩
  · rw [aeval_map_intermediateFieldMap]
    exact (map_ne_zero_iff _ σ.injective).2 hQ
  · rw [aeval_map_intermediateFieldMap, aeval_map_intermediateFieldMap, ← map_div₀, ← hx,
      map_pow]

/-! ### Triples -/

variable (k a a') in
/-- `lem:triple`, hypotheses: `y`, `z` are generic points of the loci of `a`, `a'`, independent
from the parameter tuple `b`, and `z` is definable over `b, y`. -/
structure IsTriple (b : μ → K) (y : ι → K) (z : κ → K) : Prop where
  /-- `y` is a generic point of the locus of `a`. -/
  isGen_left : IsGen k a y
  /-- `z` is a generic point of the locus of `a'`. -/
  isGen_right : IsGen k a' z
  /-- `y` is independent from the parameter tuple. -/
  indep_left : IndepOver k ∅ (range y) (range b)
  /-- `z` is independent from the parameter tuple. -/
  indep_right : IndepOver k ∅ (range z) (range b)
  /-- `z` is definable over the parameter tuple and `y`. -/
  mem_dcl : ∀ j, z j ∈ dclAdjoin (adjoin k (range b)) y

namespace IsTriple

variable {b : μ → K} {y : ι → K} {z : κ → K}

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite ι] [Finite κ] in
theorem isSmall_racl (b : μ → K) :
    IsSmall k ((racl k (range b) : IntermediateField k K) : Set K) :=
  (IsSmall.of_finite (finite_range b)).racl

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite ι] [Finite κ] [Finite μ] in
theorem map_racl_eq (b : μ → K) (σ : K ≃ₐ[↥(adjoin k (range b))] K) :
    (racl k (range b)).map (σ.restrictScalars k).toAlgHom = racl k (range b) := by
  have hb : ⇑(σ.restrictScalars k) '' range b = range b := by
    rw [← range_comp]
    refine congrArg range (funext fun i ↦ ?_)
    change σ (b i) = b i
    exact σ.commutes ⟨b i, subset_adjoin k _ (mem_range_self i)⟩
  rw [racl_map, hb]

variable (h : IsTriple k a a' b y z)
include h

omit [IsAlgClosed k] [IsAlgClosed K] [UniversalDomain k K] [Finite ι] [Finite κ] [Finite μ] in
theorem map (σ : K ≃ₐ[k] K) : IsTriple k a a' (⇑σ ∘ b) (⇑σ ∘ y) (⇑σ ∘ z) where
  isGen_left := h.isGen_left.map σ
  isGen_right := h.isGen_right.map σ
  indep_left := by
    have := h.indep_left.image σ
    rwa [image_empty, ← range_comp, ← range_comp] at this
  indep_right := by
    have := h.indep_right.image σ
    rwa [image_empty, ← range_comp, ← range_comp] at this
  mem_dcl j := by
    have := mem_dclAdjoin_map σ (h.mem_dcl j)
    rwa [adjoin_map, AlgEquiv.coe_toAlgHom, ← range_comp] at this

omit [Finite κ] in
theorem isGenericOver_left : IsGenericOver (racl k (range b)) a y :=
  h.isGen_left.isGenericOver_racl (IsSmall.of_finite (finite_range b)) h.indep_left

omit [Finite ι] in
theorem isGenericOver_right : IsGenericOver (racl k (range b)) a' z :=
  h.isGen_right.isGenericOver_racl (IsSmall.of_finite (finite_range b)) h.indep_right

/-- The quasi-rational expression over `k(b)` with `f(y) = z`. -/
def qr : QuasiRational (↥(adjoin k (range b))) ι κ :=
  Classical.choose (exists_quasiRational_of_mem_dclAdjoin h.mem_dcl)

omit [IsAlgClosed k] [UniversalDomain k K] [Finite ι] [Finite μ] in
theorem qr_spec : h.qr.IsDefinedAt y ∧ h.qr.eval y = z :=
  Classical.choose_spec (exists_quasiRational_of_mem_dclAdjoin h.mem_dcl)

/-- The expression `h.qr` with coefficients viewed in `acl(b)`. -/
def qrM : QuasiRational (↥(racl k (range b))) ι κ :=
  h.qr.map (IntermediateField.inclusion (adjoin_le_racl k (range b))).toRingHom

omit [IsAlgClosed k] [UniversalDomain k K] [Finite ι] [Finite μ] in
theorem qrM_eval (u : ι → K) : h.qrM.eval u = h.qr.eval u := by
  rw [qrM, QuasiRational.eval_map]

omit [IsAlgClosed k] [UniversalDomain k K] [Finite ι] [Finite μ] in
theorem qrM_isDefinedAt : h.qrM.IsDefinedAt y :=
  (QuasiRational.isDefinedAt_map_iff _ _ _).2 h.qr_spec.1

/-- The representative of `g_b` over `acl(b)`. -/
def rep : Representative k K a a' :=
  Representative.ofQuasiRational (isAlgClosed_racl _) (isSmall_racl b) h.qrM
    h.isGenericOver_left h.qrM_isDefinedAt
    (by
      rw [h.qrM_eval, h.qr_spec.2]
      exact h.isGenericOver_right)

theorem rep_M : h.rep.M = racl k (range b) := rfl

theorem rep_f_eval : h.rep.f.eval y = z := by
  change h.qrM.eval y = z
  rw [h.qrM_eval, h.qr_spec.2]

/-- Equivariance of the representative under automorphisms over `k(b)`. -/
theorem rep_f_eval_comp (σ : K ≃ₐ[↥(adjoin k (range b))] K) :
    h.rep.f.eval (⇑(σ.restrictScalars k) ∘ y) = ⇑(σ.restrictScalars k) ∘ z := by
  change h.qrM.eval (⇑(σ.restrictScalars k) ∘ y) = _
  rw [h.qrM_eval, show ⇑(σ.restrictScalars k) ∘ y = ⇑σ ∘ y from rfl, h.qr.eval_comp σ y,
    h.qr_spec.2]
  rfl

/-- `lem:triple`: the germ `g_b` determined by the triple. -/
def germ : Germ k a a' := ⟦h.rep⟧

theorem germ_cb_le : h.germ.cb ≤ racl k (range b) := Germ.cb_mk_le h.rep

theorem indep_cb : IndepOver k ∅ (range y) (h.germ.cb : Set K) :=
  (indepOver_racl_right_iff.2 h.indep_left).mono_right (by
    rw [empty_union]
    exact h.germ_cb_le)

theorem germ_eval : h.germ.eval (racl k (range b)) y = z :=
  (Germ.eval_eq_rep h.rep (isSmall_racl b) h.germ_cb_le le_rfl h.isGenericOver_left).trans
    h.rep_f_eval

theorem germ_evalGen : h.germ.evalGen y = z :=
  (Germ.evalGen_eq h.germ (isSmall_racl b) h.germ_cb_le h.isGenericOver_left).trans h.germ_eval

/-- `lem:triple`, uniqueness: `g_b` is the only germ with canonical base in `acl(b)` sending
`y` to `z`. -/
theorem eq_germ {g : Germ k a a'} (hcb : g.cb ≤ racl k (range b)) (hg : g.evalGen y = z) :
    g = h.germ := by
  refine Germ.eq_of_eval_eq (isSmall_racl b) hcb h.germ_cb_le h.isGenericOver_left ?_
  exact ((Germ.evalGen_eq g (isSmall_racl b) hcb h.isGenericOver_left).symm.trans hg).trans
    h.germ_eval.symm

/-- `lem:triple`: the graph ideal of `g_b` is the locus of `(y, z)` over `acl(b)`. -/
theorem germ_graphIdeal :
    h.germ.graphIdeal = locusIdeal (↥(racl k (range b))) (Sum.elim y z) := by
  change Germ.graphIdeal ⟦h.rep⟧ = _
  rw [Germ.graphIdeal_mk, h.rep.graphIdeal_eq h.isGenericOver_left]
  unfold Representative.graphPoint
  rw [h.rep_f_eval]
  rfl

/-- `lem:triple`: `Cb(g_b) = Cb(yz/b)`. -/
theorem germ_cb : h.germ.cb = canonicalBase (racl k (range b)) (Sum.elim y z) := by
  change Germ.cb ⟦h.rep⟧ = _
  rw [Germ.cb_mk_eq_canonicalBase h.rep h.isGenericOver_left]
  unfold Representative.graphPoint
  rw [h.rep_f_eval]
  rfl

/-! ### Definability of the canonical base -/

/-- Automorphisms over `k(b)` fix `g_b`. -/
theorem map_germ_eq_self (σ : K ≃ₐ[↥(adjoin k (range b))] K) :
    h.germ.map (σ.restrictScalars k) = h.germ := by
  have hyσ : IsGenericOver (racl k (range b)) a (⇑(σ.restrictScalars k) ∘ y) := by
    have := (isGenericOver_map_iff (σ.restrictScalars k) _ a y).2 h.isGenericOver_left
    rwa [map_racl_eq b σ] at this
  have hcb' : (h.germ.map (σ.restrictScalars k)).cb ≤ racl k (range b) := by
    rw [Germ.cb_map]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := (IntermediateField.mem_map _).1 hx
    rw [← map_racl_eq b σ]
    exact (IntermediateField.mem_map _).2 ⟨w, h.germ_cb_le hw, rfl⟩
  have e1 : (h.germ.map (σ.restrictScalars k)).evalGen (⇑(σ.restrictScalars k) ∘ y) =
      ⇑(σ.restrictScalars k) ∘ z := by
    rw [Germ.evalGen_map _ h.germ h.isGen_left h.indep_cb, h.germ_evalGen]
  have e2 : h.germ.evalGen (⇑(σ.restrictScalars k) ∘ y) = ⇑(σ.restrictScalars k) ∘ z :=
    (Germ.evalGen_eq h.germ (isSmall_racl b) h.germ_cb_le hyσ).trans
      ((Germ.eval_eq_rep h.rep (isSmall_racl b) h.germ_cb_le le_rfl hyσ).trans
        (h.rep_f_eval_comp σ))
  refine Germ.eq_of_eval_eq (isSmall_racl b) hcb' h.germ_cb_le hyσ ?_
  exact ((Germ.evalGen_eq _ (isSmall_racl b) hcb' hyσ).symm.trans e1).trans
    (e2.symm.trans (Germ.evalGen_eq _ (isSmall_racl b) h.germ_cb_le hyσ))

/-- `lem:triple`: `Cb(g_b) ⊆ dcl(b)`. -/
theorem germ_cb_le_dcl : h.germ.cb ≤ dcl (adjoin k (range b)) :=
  Germ.cb_le_dcl_of_forall_map_eq h.germ h.map_germ_eq_self

/-! ### Invertibility -/

/-- `lem:triple`: `g_b` is invertible iff `y ∈ dcl(b, z)`. -/
theorem isInvertible_iff :
    Germ.IsInvertible h.germ ↔ ∀ i, y i ∈ dclAdjoin (adjoin k (range b)) z := by
  constructor
  · rintro ⟨g', hi⟩ i
    have hg'cb : g'.cb ≤ dcl (adjoin k (range b)) := by
      refine Germ.cb_le_dcl_of_forall_map_eq g' fun σ ↦ ?_
      have e := hi.map (σ.restrictScalars k)
      rw [h.map_germ_eq_self σ] at e
      exact e.unique hi
    have hzg' : IndepOver k ∅ (range z) (g'.cb : Set K) := by
      refine (indepOver_racl_right_iff.2 h.indep_right).mono_right ?_
      rw [empty_union]
      exact hi.cb_le.trans (racl_le_of_subset_racl h.germ_cb_le)
    have e : g'.evalGen z = y := by
      have := hi.evalGen_evalGen h.isGen_left h.indep_cb
      rwa [h.germ_evalGen] at this
    exact (congrArg (fun w ↦ w ∈ dclAdjoin (adjoin k (range b)) z) (congrFun e i)).mp
      (g'.evalGen_mem_dclAdjoin_of_cb_le_dcl hg'cb h.isGen_right hzg' i)
  · intro hdef
    refine (Germ.isInvertible_iff_mem_dclAdjoin h.germ (isSmall_racl b) h.germ_cb_le
      h.isGenericOver_left).2 fun i ↦ ?_
    rw [h.germ_eval]
    exact dclAdjoin_mono (adjoin_le_racl k _) z (hdef i)

/-! ### Equivariance and generic transitivity -/

/-- `lem:triple`(1): the construction is equivariant. -/
theorem germ_map (σ : K ≃ₐ[k] K) : h.germ.map σ = (h.map σ).germ := by
  refine (h.map σ).eq_germ ?_ ?_
  · rw [Germ.cb_map, range_comp, ← racl_map]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := (IntermediateField.mem_map _).1 hx
    exact (IntermediateField.mem_map _).2 ⟨w, h.germ_cb_le hw, rfl⟩
  · rw [Germ.evalGen_map σ h.germ h.isGen_left h.indep_cb, h.germ_evalGen]

/-- `lem:triple`(1): `σ g_b` depends only on `σ b`. -/
theorem germ_map_eq_of_comp_eq {σ τ : K ≃ₐ[k] K} (hστ : ⇑σ ∘ b = ⇑τ ∘ b) :
    h.germ.map σ = h.germ.map τ := by
  have hfix : ∀ x ∈ adjoin k (range b), (τ.trans σ.symm) x = x := by
    intro x hx
    have hle : adjoin k (range b) ≤ fixedBy (τ.trans σ.symm) := by
      refine adjoin_le_iff.2 ?_
      rintro _ ⟨i, rfl⟩
      change σ.symm (τ (b i)) = b i
      have e : τ (b i) = σ (b i) := (congrFun hστ i).symm
      rw [e]
      exact σ.symm_apply_apply _
    exact hle hx
  have h1 : h.germ.map (τ.trans σ.symm) = h.germ :=
    (Germ.map_eq_self_iff _ _).2 fun x hx ↦
      apply_eq_self_of_mem_dcl_of_fixes _ hfix (h.germ_cb_le_dcl hx)
  symm
  calc h.germ.map τ = h.germ.map ((τ.trans σ.symm).trans σ) := by
        congr 1
        exact AlgEquiv.ext fun x ↦ (σ.apply_symm_apply (τ x)).symm
    _ = (h.germ.map (τ.trans σ.symm)).map σ := (Germ.map_map _ _ _).symm
    _ = h.germ.map σ := congrArg (Germ.map σ) h1

/-- `lem:triple`(2), generic transitivity: if `y` and `z` are independent, then for every
conjugate `b' = τ b` of `b` independent from `y`, the value `g_{b'}(y)` is independent from
`y`. -/
theorem indepOver_evalGen (hyz : IndepOver k ∅ (range y) (range z)) (τ : K ≃ₐ[k] K)
    (hτ : IndepOver k ∅ (range (⇑τ ∘ b)) (range y)) :
    IndepOver k ∅ (range ((h.map τ).germ.evalGen y)) (range y) := by
  have hsmall' : IsSmall k (range (⇑τ ∘ b)) := IsSmall.of_finite (finite_range _)
  have hy1 : IsGenericOver (racl k (range (⇑τ ∘ b))) a y :=
    h.isGen_left.isGenericOver_racl hsmall' hτ.symm
  obtain ⟨ρ, hρ⟩ := (h.map τ).isGenericOver_left.exists_algEquiv hy1
  have hσb : ⇑(τ.trans (ρ.restrictScalars k)) ∘ b = ⇑τ ∘ b := funext fun i ↦ by
    change ρ (τ (b i)) = τ (b i)
    exact ρ.commutes ⟨τ (b i), subset_racl k _ (mem_range_self (f := ⇑τ ∘ b) i)⟩
  have hσy : ⇑(τ.trans (ρ.restrictScalars k)) ∘ y = y := funext fun i ↦ by
    change ρ (τ (y i)) = y i
    exact hρ i
  have hg : (h.map τ).germ = h.germ.map (τ.trans (ρ.restrictScalars k)) :=
    (h.germ_map τ).symm.trans (h.germ_map_eq_of_comp_eq hσb.symm)
  have hind := hyz.symm.image (τ.trans (ρ.restrictScalars k))
  rw [image_empty, ← range_comp, ← range_comp, hσy] at hind
  have e : (h.germ.map (τ.trans (ρ.restrictScalars k))).evalGen y =
      ⇑(τ.trans (ρ.restrictScalars k)) ∘ z := by
    have := Germ.evalGen_map (τ.trans (ρ.restrictScalars k)) h.germ h.isGen_left h.indep_cb
    rwa [hσy, h.germ_evalGen] at this
  rw [hg, e]
  exact hind

/-- `lem:triple`(3), canonicity: `b` is interalgebraic with `Cb(g_b)` iff
`b ⊆ acl(Cb(g_b))`. -/
theorem racl_cb_eq_iff :
    racl k (h.germ.cb : Set K) = racl k (range b) ↔ range b ⊆ racl k (h.germ.cb : Set K) := by
  constructor
  · intro e
    rw [e]
    exact subset_racl k _
  · intro hb
    exact le_antisymm (racl_le_of_subset_racl h.germ_cb_le) (racl_le_of_subset_racl hb)

end IsTriple

end

end GroupConfig
