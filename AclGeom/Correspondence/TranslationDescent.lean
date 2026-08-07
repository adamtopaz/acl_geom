/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.GenericPoints
import AclGeom.Correspondence.CurveIdeal

/-!
# Descent of translation invariance along the locus

Step 4d of the fused curve-coset chain: the exact translation identity
`F(X + δ₁, Y + δ₂) = F` at the *generic* point `δ` of the translation locus
descends to every point of the locus. The identity is equivalent to the
vanishing at `δ` of the finitely many universal coefficient polynomials of
`F(X + U, Y + V) − F(X, Y)`; genericity places them in the vanishing ideal
of `δ`, so they vanish at any point whose ideal contains it.

* `aevalSnd`: evaluation of the second variable block at constants;
* `coeffUV`: the universal coefficient polynomials, via `toUVPoly`;
* `translate_eq_of_idealOf_le`: the descent theorem.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M3a, checklist C6/C7).
-/

namespace AclGeom

open MvPolynomial

noncomputable section

variable {k : Type*} [Field k]

section BlockEval

variable {K : Type*} [Field K] [Algebra k K]

/-- Evaluation of the second variable block at constants: `X (inl j) ↦ X j`,
`X (inr j) ↦ C (c j)`. -/
def aevalSnd (c : Fin 2 → K) :
    MvPolynomial (Fin 2 ⊕ Fin 2) k →ₐ[k] MvPolynomial (Fin 2) K :=
  aeval (Sum.elim (fun j ↦ X j) fun j ↦ C (c j))

/-- The universal coefficient view: the second block becomes the coefficient
ring. -/
def toUVPoly :
    MvPolynomial (Fin 2 ⊕ Fin 2) k →ₐ[k]
      MvPolynomial (Fin 2) (MvPolynomial (Fin 2) k) :=
  aeval (Sum.elim (fun j ↦ X j) fun j ↦ C (X j))

/-- `aevalSnd` factors through the universal coefficient view. -/
theorem aevalSnd_eq_map_toUVPoly (c : Fin 2 → K)
    (g : MvPolynomial (Fin 2 ⊕ Fin 2) k) :
    aevalSnd (k := k) c g =
      MvPolynomial.map ((aeval c : MvPolynomial (Fin 2) k →ₐ[k] K) :
        MvPolynomial (Fin 2) k →+* K) (toUVPoly (k := k) g) := by
  have hcomp : (aevalSnd (k := k) c).toRingHom =
      ((MvPolynomial.map ((aeval c : MvPolynomial (Fin 2) k →ₐ[k] K) :
        MvPolynomial (Fin 2) k →+* K)).comp (toUVPoly (k := k)).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · simp [aevalSnd, toUVPoly, MvPolynomial.algebraMap_eq]
    · rcases i with j | j
      · simp [aevalSnd, toUVPoly]
      · simp [aevalSnd, toUVPoly]
  exact congrArg (fun (f : MvPolynomial (Fin 2 ⊕ Fin 2) k →+* _) ↦ f g) hcomp

/-- The coefficient bridge: coefficients of a block evaluation are the
evaluations of the universal coefficient polynomials. -/
theorem coeff_aevalSnd (c : Fin 2 → K) (g : MvPolynomial (Fin 2 ⊕ Fin 2) k)
    (m : Fin 2 →₀ ℕ) :
    coeff m (aevalSnd (k := k) c g) =
      aeval c (coeff m (toUVPoly (k := k) g)) := by
  rw [aevalSnd_eq_map_toUVPoly, MvPolynomial.coeff_map]
  rfl

/-- Block evaluation of the sum substitution is the translation of the
extended polynomial. -/
theorem aevalSnd_addSubst (c : Fin 2 → K) (F : MvPolynomial (Fin 2) k) :
    aevalSnd (k := k) c (addSubst (k := k) F) =
      translate c (MvPolynomial.map (algebraMap k K) F) := by
  have hcomp : ((aevalSnd (k := k) c).toRingHom.comp
      (addSubst (k := k)).toRingHom) =
      ((translate c).toRingHom.comp
        (MvPolynomial.map (algebraMap k K) :
          MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) K)) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_)
    · simp [aevalSnd, addSubst, translate, MvPolynomial.algebraMap_eq]
    · simp [aevalSnd, addSubst, translate]
  exact congrArg (fun (f : MvPolynomial (Fin 2) k →+* _) ↦ f F) hcomp

/-- Block evaluation of the first-block inclusion is coefficient
extension. -/
theorem aevalSnd_rename_inl (c : Fin 2 → K) (F : MvPolynomial (Fin 2) k) :
    aevalSnd (k := k) c (rename Sum.inl F) =
      MvPolynomial.map (algebraMap k K) F := by
  have hcomp : ((aevalSnd (k := k) c).toRingHom.comp
      (rename (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2)).toRingHom) =
      (MvPolynomial.map (algebraMap k K) :
        MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) K) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_)
    · simp [aevalSnd, MvPolynomial.algebraMap_eq]
    · simp [aevalSnd]
  exact congrArg (fun (f : MvPolynomial (Fin 2) k →+* _) ↦ f F) hcomp

end BlockEval

section JointDetermination

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra k K] [Algebra k Ω]
  [Algebra K Ω] [IsScalarTower k K Ω]

/-- Evaluation of the first variable block at constants:
`X (inl j) ↦ C (c j)`, `X (inr j) ↦ X j`. -/
def aevalFst (c : Fin 2 → K) :
    MvPolynomial (Fin 2 ⊕ Fin 2) k →ₐ[k] MvPolynomial (Fin 2) K :=
  aeval (Sum.elim (fun j ↦ C (c j)) fun j ↦ X j)

/-- Composing first-block evaluation with a point evaluation recovers the
joint evaluation. -/
theorem aeval_aevalFst (c : Fin 2 → K) (v : Fin 2 → Ω)
    (f : MvPolynomial (Fin 2 ⊕ Fin 2) k) :
    aeval v (aevalFst (k := k) c f) =
      aeval (Sum.elim (fun j ↦ algebraMap K Ω (c j)) v) f := by
  have hcomp : ((aeval v : MvPolynomial (Fin 2) K →ₐ[K] Ω) :
      MvPolynomial (Fin 2) K →+* Ω).comp (aevalFst (k := k) c).toRingHom =
      ((aeval (Sum.elim (fun j ↦ algebraMap K Ω (c j)) v) :
        MvPolynomial (Fin 2 ⊕ Fin 2) k →ₐ[k] Ω) :
        MvPolynomial (Fin 2 ⊕ Fin 2) k →+* Ω) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · simp [aevalFst, MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply]
    · rcases i with j | j
      · simp [aevalFst]
      · simp [aevalFst]
  exact congrArg (fun (g : MvPolynomial (Fin 2 ⊕ Fin 2) k →+* Ω) ↦ g f) hcomp

/-- **Joint-type determination, one direction**: if the vanishing ideal of
`q` over `K` is spanned by the extension of `G`, then any joint polynomial
vanishing at `(c, q)` vanishes at `(c, w)` for every zero `w` of `G` — the
first block evaluates into `K`, and the resulting relative polynomial is a
multiple of the extended generator. -/
theorem joint_aeval_eq_zero {c : Fin 2 → K} {q : Fin 2 → Ω}
    {G : MvPolynomial (Fin 2) k}
    (hspan : idealOf K q = Ideal.span {MvPolynomial.map (algebraMap k K) G})
    {w : Fin 2 → Ω} (hw : aeval w G = 0)
    {f : MvPolynomial (Fin 2 ⊕ Fin 2) k}
    (hf : aeval (Sum.elim (fun j ↦ algebraMap K Ω (c j)) q) f = 0) :
    aeval (Sum.elim (fun j ↦ algebraMap K Ω (c j)) w) f = 0 := by
  have hfK : aevalFst (k := k) c f ∈ idealOf K q := by
    rw [mem_idealOf_iff, aeval_aevalFst]
    exact hf
  rw [hspan, Ideal.mem_span_singleton'] at hfK
  obtain ⟨h, hh⟩ := hfK
  rw [← aeval_aevalFst, ← hh, map_mul]
  have hGw : aeval w (MvPolynomial.map (algebraMap k K) G) = (0 : Ω) := by
    rw [aeval_map_algebraMap]
    exact hw
  rw [hGw, mul_zero]

/-- First-block evaluation of the sum substitution is the translation of
the extended polynomial. -/
theorem aevalFst_addSubst (c : Fin 2 → K) (F : MvPolynomial (Fin 2) k) :
    aevalFst (k := k) c (addSubst (k := k) F) =
      translate c (MvPolynomial.map (algebraMap k K) F) := by
  have hcomp : ((aevalFst (k := k) c).toRingHom.comp
      (addSubst (k := k)).toRingHom) =
      ((translate c).toRingHom.comp
        (MvPolynomial.map (algebraMap k K) :
          MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) K)) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_)
    · simp [aevalFst, addSubst, translate, MvPolynomial.algebraMap_eq]
    · simp [aevalFst, addSubst, translate, add_comm]
  exact congrArg (fun (f : MvPolynomial (Fin 2) k →+* _) ↦ f F) hcomp

/-- First-block evaluation of the first-block inclusion is the constant of
the evaluation. -/
theorem aevalFst_rename_inl (c : Fin 2 → K) (F : MvPolynomial (Fin 2) k) :
    aevalFst (k := k) c (rename Sum.inl F) = C (aeval c F) := by
  have hcomp : ((aevalFst (k := k) c).toRingHom.comp
      (rename (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2)).toRingHom) =
      ((C : K →+* MvPolynomial (Fin 2) K).comp
        ((aeval c : MvPolynomial (Fin 2) k →ₐ[k] K) :
          MvPolynomial (Fin 2) k →+* K)) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_)
    · simp [aevalFst, MvPolynomial.algebraMap_eq]
    · simp [aevalFst]
  exact congrArg (fun (f : MvPolynomial (Fin 2) k →+* _) ↦ f F) hcomp

/-- First-block evaluation of the second-block inclusion is coefficient
extension. -/
theorem aevalFst_rename_inr (c : Fin 2 → K) (F : MvPolynomial (Fin 2) k) :
    aevalFst (k := k) c (rename Sum.inr F) =
      MvPolynomial.map (algebraMap k K) F := by
  have hcomp : ((aevalFst (k := k) c).toRingHom.comp
      (rename (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2)).toRingHom) =
      (MvPolynomial.map (algebraMap k K) :
        MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) K) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_)
    · simp [aevalFst, MvPolynomial.algebraMap_eq]
    · simp [aevalFst]
  exact congrArg (fun (f : MvPolynomial (Fin 2) k →+* _) ↦ f F) hcomp

/-- Bridged form of `joint_aeval_eq_zero`: the first block is given as an
`Ω`-tuple together with the equation identifying it as the image of a
`K`-tuple. Keeping the concrete coercion inside a hypothesis avoids
elaborating evaluation maps at concrete intermediate fields. -/
theorem joint_aeval_eq_zero' {c : Fin 2 → K} {p q : Fin 2 → Ω}
    (hp : (fun j ↦ algebraMap K Ω (c j)) = p)
    {G : MvPolynomial (Fin 2) k}
    (hspan : idealOf K q = Ideal.span {MvPolynomial.map (algebraMap k K) G})
    {w : Fin 2 → Ω} (hw : aeval w G = 0)
    {f : MvPolynomial (Fin 2 ⊕ Fin 2) k}
    (hf : aeval (Sum.elim p q) f = 0) :
    aeval (Sum.elim p w) f = 0 := by
  subst hp
  exact joint_aeval_eq_zero hspan hw hf

/-- **Joint-type determination**: two points of the same curve, each generic
over the field `K` generated by the first block, have the same joint
vanishing ideal with it. -/
theorem joint_idealOf_eq {c : Fin 2 → K} {q q' : Fin 2 → Ω}
    {G : MvPolynomial (Fin 2) k}
    (hspan : idealOf K q = Ideal.span {MvPolynomial.map (algebraMap k K) G})
    (hspan' : idealOf K q' =
      Ideal.span {MvPolynomial.map (algebraMap k K) G}) :
    idealOf k (Sum.elim (fun j ↦ algebraMap K Ω (c j)) q) =
      idealOf k (Sum.elim (fun j ↦ algebraMap K Ω (c j)) q') := by
  have hzero : ∀ {r : Fin 2 → Ω}, idealOf K r =
      Ideal.span {MvPolynomial.map (algebraMap k K) G} → aeval r G = 0 := by
    intro r hr
    have hmem : MvPolynomial.map (algebraMap k K) G ∈ idealOf K r := by
      rw [hr]
      exact Ideal.subset_span rfl
    have h := (mem_idealOf_iff K).1 hmem
    rwa [aeval_map_algebraMap] at h
  refine idealOf_eq_of_aeval_iff k fun f ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact joint_aeval_eq_zero hspan (hzero hspan') h
  · exact joint_aeval_eq_zero hspan' (hzero hspan) h

end JointDetermination

/-- **Descent of translation invariance** (step 4d): if translation by `c`
fixes the extended generator and the vanishing ideal of `c` is contained in
that of `w`, then translation by `w` fixes the extended generator as well.
Applied with `c` the generic point of the translation locus, this transports
the exact translation identity to every point of the locus. -/
theorem translate_eq_of_idealOf_le
    {K L : Type*} [Field K] [Field L] [Algebra k K] [Algebra k L]
    {c : Fin 2 → K} {F : MvPolynomial (Fin 2) k}
    (hid : translate c (MvPolynomial.map (algebraMap k K) F) =
      MvPolynomial.map (algebraMap k K) F)
    {w : Fin 2 → L} (hle : idealOf k c ≤ idealOf k w) :
    translate w (MvPolynomial.map (algebraMap k L) F) =
      MvPolynomial.map (algebraMap k L) F := by
  classical
  set D := addSubst (k := k) F - rename Sum.inl F with hD
  have hDc : aevalSnd (k := k) c D = 0 := by
    rw [hD, map_sub, aevalSnd_addSubst, aevalSnd_rename_inl, hid, sub_self]
  have hQ : ∀ m : Fin 2 →₀ ℕ,
      coeff m (toUVPoly (k := k) D) ∈ idealOf k c := by
    intro m
    rw [mem_idealOf_iff]
    have h := congrArg (fun g ↦ coeff m g) hDc
    simp only [coeff_zero] at h
    rw [coeff_aevalSnd] at h
    exact h
  have hDw : aevalSnd (k := k) w D = 0 := by
    ext m
    rw [coeff_aevalSnd, coeff_zero]
    exact (mem_idealOf_iff k).1 (hle (hQ m))
  rw [hD, map_sub, aevalSnd_addSubst, aevalSnd_rename_inl, sub_eq_zero] at hDw
  exact hDw

/-- **Properness of the stabilizer**: a translation vector fixing a prime
generator cannot be algebraically independent — otherwise evaluating the
identity at the origin makes the generator constant. Consequently the
translation locus of the curve-coset chain is at most one-dimensional. -/
theorem not_algebraicIndependent_of_translate_eq
    {K : Type*} [Field K] [Algebra k K]
    {c : Fin 2 → K} {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hid : translate c (MvPolynomial.map (algebraMap k K) F) =
      MvPolynomial.map (algebraMap k K) F)
    (hc : AlgebraicIndependent k c) : False := by
  classical
  have h0 := congrArg (aeval (fun _ : Fin 2 ↦ (0 : K))) hid
  rw [aeval_translate] at h0
  have hzero : (fun j ↦ (0 : K) + algebraMap K K (c j)) = c := by
    funext j
    simp
  rw [hzero] at h0
  -- Both sides through the coefficient extension.
  rw [MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_map_algebraMap] at h0
  -- The generator satisfies a relation at the independent point.
  have hsq : (aeval c) (C (aeval (fun _ : Fin 2 ↦ (0 : k)) F) :
      MvPolynomial (Fin 2) k) = aeval (fun _ : Fin 2 ↦ (0 : K)) F := by
    rw [aeval_C]
    have hcomp2 : ((algebraMap k K).comp
        ((aeval (fun _ : Fin 2 ↦ (0 : k))).toRingHom :
          MvPolynomial (Fin 2) k →+* k)) =
        ((aeval (fun _ : Fin 2 ↦ (0 : K))).toRingHom :
          MvPolynomial (Fin 2) k →+* K) := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_) <;> simp
    exact congrArg (fun (f : MvPolynomial (Fin 2) k →+* K) ↦ f F) hcomp2
  have hmem : F - C (aeval (fun _ : Fin 2 ↦ (0 : k)) F) ∈ idealOf k c := by
    rw [mem_idealOf_iff, map_sub, hsq, h0, sub_self]
  rw [(idealOf_eq_bot_iff k).2 hc, Ideal.mem_bot, sub_eq_zero] at hmem
  -- A constant cannot be prime.
  rcases eq_or_ne (aeval (fun _ : Fin 2 ↦ (0 : k)) F) 0 with hc0 | hc0
  · rw [hc0, map_zero] at hmem
    exact hFp.ne_zero hmem
  · exact hFp.not_unit (hmem ▸ (isUnit_iff_ne_zero.2 hc0).map
      (C : k →+* MvPolynomial (Fin 2) k))

end

end AclGeom
