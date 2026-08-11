/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.CurveEquation
import AclGeom.Correspondence.FamilyCover
import AclGeom.Correspondence.FiniteCover

/-!
# Canonical curve equations under normal-cover transport

The canonical monic equation of a finite correspondence is first moved
from its coefficient field to its source-coordinate field.  Its selected
source and target points satisfy that equation inside the branch field.
Consequently every source-linear embedding of the branch into another
field, and every subsequent source-fixing automorphism, preserves the
equation exactly.

This is the coefficient-faithfulness bridge used when strict finite-cover
composition triangles are conjugated through chosen normal-cover charts.
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

namespace FiniteCorrespondencePair

variable (P : FiniteCorrespondencePair k Ω)

/-- The selected source coordinate as an element of the branch field over
the source-coordinate field. -/
def sourceInBranchOverSource : P.branchOverSource :=
  algebraMap (↥P.sourceField) (↥P.branchOverSource)
    ⟨P.source, subset_adjoin k {P.source} (by simp)⟩

/-- The selected target coordinate as an element of the branch field over
the source-coordinate field. -/
def targetInBranchOverSource : P.branchOverSource :=
  ⟨P.target, by
    change P.target ∈ P.branchField
    exact subset_adjoin k {P.source, P.target} (by simp)⟩

/-- The canonical curve equation after extending its coefficients to the
source-coordinate field. -/
def curveEquationOverSourceField :
    MvPolynomial (Fin 2) (↥P.sourceField) :=
  MvPolynomial.map (algebraMap k (↥P.sourceField)) P.curveEquation

/-- The selected source and target coordinates satisfy the canonical
equation already inside the selected branch field. -/
theorem aeval_curveEquationOverSourceField :
    MvPolynomial.aeval
        ![P.sourceInBranchOverSource, P.targetInBranchOverSource]
        P.curveEquationOverSourceField = 0 := by
  let q : Fin 2 → P.branchOverSource :=
    ![P.sourceInBranchOverSource, P.targetInBranchOverSource]
  let v := P.branchOverSource.val
  have hq : (fun i ↦ v (q i)) = (![P.source, P.target] : Fin 2 → Ω) := by
    funext i
    fin_cases i <;> rfl
  apply v.injective
  change v (MvPolynomial.aeval q P.curveEquationOverSourceField) = v 0
  calc
    v (MvPolynomial.aeval q P.curveEquationOverSourceField) =
        MvPolynomial.aeval (fun i ↦ v (q i))
          P.curveEquationOverSourceField :=
      MvPolynomial.comp_aeval_apply (f := q) v
        P.curveEquationOverSourceField
    _ = MvPolynomial.aeval ![P.source, P.target]
        P.curveEquationOverSourceField := by rw [hq]
    _ = 0 := by
      rw [curveEquationOverSourceField,
        MvPolynomial.aeval_map_algebraMap, P.aeval_curveEquation]
    _ = v 0 := by rw [map_zero]

/-- The same selected branch point satisfies the original equation over
the coefficient field.  This formulation survives charts which fix only
the coefficients, rather than the entire source-coordinate field. -/
theorem aeval_curveEquation_inBranchOverSource :
    MvPolynomial.aeval
        ![P.sourceInBranchOverSource, P.targetInBranchOverSource]
        P.curveEquation = 0 := by
  have h := P.aeval_curveEquationOverSourceField
  rw [curveEquationOverSourceField,
    MvPolynomial.aeval_map_algebraMap] at h
  exact h

variable {N : Type*} [Field N] [Algebra (↥P.sourceField) N]

/-- Every source-linear embedding of the selected branch carries its two
distinguished coordinates to another zero of the same canonical equation. -/
theorem aeval_curveEquationOverSourceField_map
    (f : (↥P.branchOverSource) →ₐ[↥P.sourceField] N) :
    MvPolynomial.aeval
        ![f P.sourceInBranchOverSource, f P.targetInBranchOverSource]
        P.curveEquationOverSourceField = 0 := by
  let q : Fin 2 → P.branchOverSource :=
    ![P.sourceInBranchOverSource, P.targetInBranchOverSource]
  have hq : (fun i ↦ f (q i)) =
      ![f P.sourceInBranchOverSource, f P.targetInBranchOverSource] := by
    funext i
    fin_cases i <;> rfl
  rw [← hq, ← MvPolynomial.comp_aeval_apply]
  rw [P.aeval_curveEquationOverSourceField, map_zero]

/-- A source-fixing automorphism of the target normal cover preserves the
canonical equation on the transported selected branch. -/
theorem aeval_curveEquationOverSourceField_map_aut
    (f : (↥P.branchOverSource) →ₐ[↥P.sourceField] N)
    (σ : N ≃ₐ[↥P.sourceField] N) :
    MvPolynomial.aeval
        ![σ (f P.sourceInBranchOverSource),
          σ (f P.targetInBranchOverSource)]
        P.curveEquationOverSourceField = 0 := by
  exact P.aeval_curveEquationOverSourceField_map (σ.toAlgHom.comp f)

variable {M : Type*} [Field M] [Algebra k M]

/-- Every coefficient-linear realization of the selected branch carries
its two distinguished coordinates to a zero of the original canonical
equation.  In particular this applies after a coefficient-fixing chart
which need not fix the source coordinate. -/
theorem aeval_curveEquation_map
    (f : (↥P.branchOverSource) →ₐ[k] M) :
    MvPolynomial.aeval
        ![f P.sourceInBranchOverSource, f P.targetInBranchOverSource]
        P.curveEquation = 0 := by
  let q : Fin 2 → P.branchOverSource :=
    ![P.sourceInBranchOverSource, P.targetInBranchOverSource]
  have hq : (fun i ↦ f (q i)) =
      ![f P.sourceInBranchOverSource, f P.targetInBranchOverSource] := by
    funext i
    fin_cases i <;> rfl
  rw [← hq, ← MvPolynomial.comp_aeval_apply]
  rw [P.aeval_curveEquation_inBranchOverSource, map_zero]

end FiniteCorrespondencePair

namespace FiniteCorrespondenceFamilyMember

variable {d : ℕ}
  (F : FiniteCorrespondenceFamilyMember (k := k) (Ω := Ω) d)

/-- Mapping a family through an ambient embedding maps its parameter field
onto the parameter field of the mapped family. -/
theorem parameterField_map {Ω' : Type*} [Field Ω'] [Algebra k Ω']
    (σ : Ω →ₐ[k] Ω') :
    F.parameterField.map σ = (F.map σ).parameterField := by
  rw [parameterField, parameterField, IntermediateField.adjoin_map]
  congr 1
  ext z
  simp [FiniteCorrespondenceFamilyMember.map]

/-- The canonical equivalence from a family's parameter field to the
parameter field obtained after an ambient embedding. -/
noncomputable def parameterMapEquiv
    {Ω' : Type*} [Field Ω'] [Algebra k Ω'] (σ : Ω →ₐ[k] Ω') :
    (↥F.parameterField) ≃ₐ[k] (↥(F.map σ).parameterField) :=
  (F.parameterField.equivMap σ).trans
    (IntermediateField.equivOfEq (F.parameterField_map σ))

/-- The parameter-field map induced by an ambient embedding is literally
that embedding on ambient values. -/
@[simp] theorem coe_parameterMapEquiv_apply
    {Ω' : Type*} [Field Ω'] [Algebra k Ω'] (σ : Ω →ₐ[k] Ω')
    (z : F.parameterField) :
    ((F.parameterMapEquiv σ z : (F.map σ).parameterField) : Ω') = σ z := by
  rfl

/-- On displayed parameters, the ambiently induced parameter equivalence
sends each coordinate to the corresponding mapped coordinate. -/
@[simp] theorem parameterMapEquiv_apply
    {Ω' : Type*} [Field Ω'] [Algebra k Ω'] (σ : Ω →ₐ[k] Ω')
    (i : Fin d) :
    F.parameterMapEquiv σ
        ⟨F.parameter i,
          IntermediateField.subset_adjoin k _ (Set.mem_range_self i)⟩ =
      ⟨(F.map σ).parameter i,
        IntermediateField.subset_adjoin k _ (Set.mem_range_self i)⟩ := by
  apply Subtype.ext
  rfl

/-- Ambiently mapping a family transports its endpoint-pair ideal through
the induced parameter-field equivalence. -/
theorem toPair_ideal_map_parameterMapEquiv
    {Ω' : Type*} [Field Ω'] [Algebra k Ω'] (σ : Ω →ₐ[k] Ω') :
    Ideal.map
        (MvPolynomial.mapAlgEquiv (Fin 2)
          (F.parameterMapEquiv σ)).toRingEquiv
        F.toPair.ideal =
      (F.map σ).toPair.ideal := by
  classical
  let ep := F.parameterMapEquiv σ
  have heval (f : MvPolynomial (Fin 2) F.parameterField) :
      σ (MvPolynomial.aeval ![F.source, F.target] f) =
        MvPolynomial.aeval ![σ F.source, σ F.target]
          (MvPolynomial.map ep.toRingHom f) := by
    induction f using MvPolynomial.induction_on with
    | C z =>
        simp only [MvPolynomial.map_C, MvPolynomial.aeval_C]
        rfl
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f i hf =>
        simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, hf]
        fin_cases i <;> rfl
  have hmem (f : MvPolynomial (Fin 2) F.parameterField) :
      MvPolynomial.map ep.toRingHom f ∈ (F.map σ).toPair.ideal ↔
        f ∈ F.toPair.ideal := by
    change MvPolynomial.map ep.toRingHom f ∈
        idealOf (↥(F.map σ).parameterField)
          ![σ F.source, σ F.target] ↔
      f ∈ idealOf (↥F.parameterField) ![F.source, F.target]
    rw [mem_idealOf_iff, mem_idealOf_iff, ← heval]
    constructor
    · intro hz
      exact σ.injective (hz.trans (map_zero σ).symm)
    · intro hz
      rw [hz, map_zero]
  let em : MvPolynomial (Fin 2) F.parameterField ≃+*
      MvPolynomial (Fin 2) (F.map σ).parameterField :=
    (MvPolynomial.mapAlgEquiv (Fin 2) ep).toRingEquiv
  ext g
  constructor
  · intro hg
    obtain ⟨f, hf, rfl⟩ := (Ideal.mem_map_of_equiv em g).mp hg
    exact (hmem f).2 hf
  · intro hg
    refine (Ideal.mem_map_of_equiv em g).2
      ⟨em.symm g, ?_, em.apply_symm_apply g⟩
    have hm : MvPolynomial.map ep.toRingHom (em.symm g) = g :=
      em.apply_symm_apply g
    rw [← hm] at hg
    exact (hmem (em.symm g)).1 hg

/-- Ambiently mapping a family transports its canonical monic endpoint
equation coefficientwise. -/
theorem curveEquation_map_parameterMapEquiv
    {Ω' : Type*} [Field Ω'] [Algebra k Ω'] (σ : Ω →ₐ[k] Ω') :
    MvPolynomial.map (F.parameterMapEquiv σ).toRingHom
        F.toPair.curveEquation =
      (F.map σ).toPair.curveEquation := by
  let ep := F.parameterMapEquiv σ
  change MvPolynomial.map ep.toRingHom F.toPair.curveEquation =
    (F.map σ).toPair.curveEquation
  have hmonic : MonomialOrder.lex.Monic
      (MvPolynomial.map ep.toRingHom F.toPair.curveEquation) := by
    have hs :
        (MvPolynomial.map ep.toRingHom F.toPair.curveEquation).support =
          F.toPair.curveEquation.support :=
      MvPolynomial.support_map_of_injective _ ep.injective
    rw [MonomialOrder.Monic, MonomialOrder.leadingCoeff,
      MonomialOrder.degree, hs, MvPolynomial.coeff_map]
    change ep.toRingHom
        (MonomialOrder.lex.leadingCoeff F.toPair.curveEquation) = 1
    rw [F.toPair.curveEquation_monic.leadingCoeff_eq_one, map_one]
  apply FiniteCorrespondencePair.eq_of_monic_of_associated
    hmonic (F.map σ).toPair.curveEquation_monic
  rw [← Ideal.span_singleton_eq_span_singleton]
  calc
    Ideal.span {MvPolynomial.map ep.toRingHom
        F.toPair.curveEquation} =
        Ideal.map
          (MvPolynomial.mapAlgEquiv (Fin 2) ep).toRingEquiv
          (Ideal.span {F.toPair.curveEquation}) := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    _ = Ideal.map
        (MvPolynomial.mapAlgEquiv (Fin 2) ep).toRingEquiv
        F.toPair.ideal := by
      rw [F.toPair.ideal_eq_span_curveEquation]
    _ = (F.map σ).toPair.ideal := by
      exact F.toPair_ideal_map_parameterMapEquiv σ
    _ = Ideal.span {(F.map σ).toPair.curveEquation} :=
      (F.map σ).toPair.ideal_eq_span_curveEquation

/-- The canonical parameter-field equivalence induced by equality of two
complete family loci transports the endpoint-pair ideal exactly. -/
theorem toPair_ideal_map_parameterEquivOfIdealEq
    (G : FiniteCorrespondenceFamilyMember (k := k) (Ω := Ω) d)
    (h : F.ideal = G.ideal) :
    Ideal.map
        (MvPolynomial.mapAlgEquiv (Fin 2)
          (F.parameterEquivOfIdealEq G h)).toRingEquiv
        F.toPair.ideal =
      G.toPair.ideal := by
  classical
  let E := F.parameterField
  let E' := G.parameterField
  let L := F.familyField
  let L' := G.familyField
  let ep : E ≃ₐ[k] E' := F.parameterEquivOfIdealEq G h
  let et : L ≃ₐ[k] L' := locusFunctionFieldEquivOfIdealEq h
  have hEL : E ≤ L := by
    apply IntermediateField.adjoin.mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i.castSucc.castSucc, by simp [tuple, parameterSource]⟩
  have hEL' : E' ≤ L' := by
    apply IntermediateField.adjoin.mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i.castSucc.castSucc, by simp [tuple, parameterSource]⟩
  let iEL : E →ₐ[k] L := IntermediateField.inclusion hEL
  let iEL' : E' →ₐ[k] L' := IntermediateField.inclusion hEL'
  letI : Algebra E L := iEL.toRingHom.toAlgebra
  letI : Algebra E' L' := iEL'.toRingHom.toAlgebra
  have het_parameter : et.toAlgHom.comp iEL = iEL'.comp ep.toAlgHom := by
    apply IntermediateField.adjoin_algHom_ext k
    rintro _ ⟨i, rfl⟩
    change et ⟨F.parameter i, _⟩ =
      iEL' (ep ⟨F.parameter i, _⟩)
    rw [F.parameterEquivOfIdealEq_apply G h i]
    change et ⟨F.parameter i, _⟩ = ⟨G.parameter i, _⟩
    have hin :
        (⟨F.parameter i,
          hEL (IntermediateField.subset_adjoin k _
            (Set.mem_range_self i))⟩ : L) =
        ⟨F.tuple i.castSucc.castSucc,
          IntermediateField.subset_adjoin k _
            (Set.mem_range_self i.castSucc.castSucc)⟩ := by
      apply Subtype.ext
      simp [tuple, parameterSource]
    rw [hin]
    apply Subtype.ext
    change ((et ⟨F.tuple i.castSucc.castSucc, _⟩ : L') : Ω) =
      G.parameter i
    dsimp only [et, L, L', familyField]
    convert congrArg Subtype.val
      (locusFunctionFieldEquivOfIdealEq_apply h
        i.castSucc.castSucc) using 1
    · congr 1
    · simp [tuple, parameterSource]
  let q : Fin 2 → L :=
    ![⟨F.source, IntermediateField.subset_adjoin k _
        ⟨(Fin.last d).castSucc, by simp [tuple, parameterSource]⟩⟩,
      ⟨F.target, IntermediateField.subset_adjoin k _
        ⟨Fin.last (d + 1), by simp [tuple]⟩⟩]
  let q' : Fin 2 → L' :=
    ![⟨G.source, IntermediateField.subset_adjoin k _
        ⟨(Fin.last d).castSucc, by simp [tuple, parameterSource]⟩⟩,
      ⟨G.target, IntermediateField.subset_adjoin k _
        ⟨Fin.last (d + 1), by simp [tuple]⟩⟩]
  have het_q (i : Fin 2) : et (q i) = q' i := by
    fin_cases i
    · change et ⟨F.source, _⟩ = ⟨G.source, _⟩
      have hin :
          (⟨F.source, IntermediateField.subset_adjoin k _
            ⟨(Fin.last d).castSucc,
              by simp [tuple, parameterSource]⟩⟩ : L) =
          ⟨F.tuple (Fin.last d).castSucc,
            IntermediateField.subset_adjoin k _
              (Set.mem_range_self (Fin.last d).castSucc)⟩ := by
        apply Subtype.ext
        simp [tuple, parameterSource]
      rw [hin]
      apply Subtype.ext
      change ((et ⟨F.tuple (Fin.last d).castSucc, _⟩ : L') : Ω) =
        G.source
      dsimp only [et, L, L', familyField]
      convert congrArg Subtype.val
        (locusFunctionFieldEquivOfIdealEq_apply h
          (Fin.last d).castSucc) using 1
      · congr 1
      · simp [tuple, parameterSource]
    · change et ⟨F.target, _⟩ = ⟨G.target, _⟩
      have hin :
          (⟨F.target, IntermediateField.subset_adjoin k _
            ⟨Fin.last (d + 1), by simp [tuple]⟩⟩ : L) =
          ⟨F.tuple (Fin.last (d + 1)),
            IntermediateField.subset_adjoin k _
              (Set.mem_range_self (Fin.last (d + 1)))⟩ := by
        apply Subtype.ext
        simp [tuple]
      rw [hin]
      apply Subtype.ext
      change ((et ⟨F.tuple (Fin.last (d + 1)), _⟩ : L') : Ω) =
        G.target
      dsimp only [et, L, L', familyField]
      convert congrArg Subtype.val
        (locusFunctionFieldEquivOfIdealEq_apply h
          (Fin.last (d + 1))) using 1
      · congr 1
      · simp [tuple]
  have het_eval (f : MvPolynomial (Fin 2) E) :
      et (MvPolynomial.aeval q f) =
        MvPolynomial.aeval q' (MvPolynomial.map ep.toRingHom f) := by
    induction f using MvPolynomial.induction_on with
    | C z =>
        simp only [MvPolynomial.map_C, MvPolynomial.aeval_C]
        change et (iEL z) = iEL' (ep z)
        exact DFunLike.congr_fun het_parameter z
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f i hf =>
        simp only [map_mul, MvPolynomial.map_X, hf,
          MvPolynomial.aeval_X, het_q]
  have hval (f : MvPolynomial (Fin 2) E) :
      MvPolynomial.aeval ![F.source, F.target] f =
        L.val (MvPolynomial.aeval q f) := by
    let vL : L →ₐ[E] Ω :=
      { L.val.toRingHom with commutes' := fun _ => rfl }
    have hqval : (fun i => vL (q i)) =
        (![F.source, F.target] : Fin 2 → Ω) := by
      funext i
      fin_cases i <;> rfl
    calc
      MvPolynomial.aeval ![F.source, F.target] f =
          MvPolynomial.aeval (fun i => vL (q i)) f := by rw [hqval]
      _ = vL (MvPolynomial.aeval q f) :=
        (MvPolynomial.comp_aeval_apply (f := q) vL f).symm
      _ = L.val (MvPolynomial.aeval q f) := rfl
  have hval' (f : MvPolynomial (Fin 2) E') :
      MvPolynomial.aeval ![G.source, G.target] f =
        L'.val (MvPolynomial.aeval q' f) := by
    let vL' : L' →ₐ[E'] Ω :=
      { L'.val.toRingHom with commutes' := fun _ => rfl }
    have hqval : (fun i => vL' (q' i)) =
        (![G.source, G.target] : Fin 2 → Ω) := by
      funext i
      fin_cases i <;> rfl
    calc
      MvPolynomial.aeval ![G.source, G.target] f =
          MvPolynomial.aeval (fun i => vL' (q' i)) f := by rw [hqval]
      _ = vL' (MvPolynomial.aeval q' f) :=
        (MvPolynomial.comp_aeval_apply (f := q') vL' f).symm
      _ = L'.val (MvPolynomial.aeval q' f) := rfl
  have hmem (f : MvPolynomial (Fin 2) E) :
      MvPolynomial.map ep.toRingHom f ∈ G.toPair.ideal ↔
        f ∈ F.toPair.ideal := by
    change MvPolynomial.map ep.toRingHom f ∈
        idealOf (↥E') ![G.source, G.target] ↔
      f ∈ idealOf (↥E) ![F.source, F.target]
    rw [mem_idealOf_iff, mem_idealOf_iff, hval, hval', ← het_eval]
    constructor
    · intro hz
      have hzero : et (MvPolynomial.aeval q f) = 0 :=
        L'.val.injective hz
      have hzero' : MvPolynomial.aeval q f = 0 :=
        et.injective (by simpa using hzero)
      simpa using congrArg L.val hzero'
    · intro hz
      have hzero : MvPolynomial.aeval q f = 0 := L.val.injective hz
      rw [hzero, map_zero]
      rfl
  let em : MvPolynomial (Fin 2) E ≃+*
      MvPolynomial (Fin 2) E' :=
    (MvPolynomial.mapAlgEquiv (Fin 2) ep).toRingEquiv
  ext g
  constructor
  · intro hg
    obtain ⟨f, hf, rfl⟩ := (Ideal.mem_map_of_equiv em g).mp hg
    exact (hmem f).2 hf
  · intro hg
    refine (Ideal.mem_map_of_equiv em g).2
      ⟨em.symm g, ?_, em.apply_symm_apply g⟩
    have hm : MvPolynomial.map ep.toRingHom (em.symm g) = g :=
      em.apply_symm_apply g
    rw [← hm] at hg
    exact (hmem (em.symm g)).1 hg

/-- Equality of complete family loci transports the canonical monic
endpoint equation coefficientwise across the induced parameter-field
equivalence. -/
theorem curveEquation_map_parameterEquivOfIdealEq
    (G : FiniteCorrespondenceFamilyMember (k := k) (Ω := Ω) d)
    (h : F.ideal = G.ideal) :
    MvPolynomial.map (F.parameterEquivOfIdealEq G h).toRingHom
        F.toPair.curveEquation =
      G.toPair.curveEquation := by
  let ep := F.parameterEquivOfIdealEq G h
  change MvPolynomial.map ep.toRingHom F.toPair.curveEquation =
    G.toPair.curveEquation
  have hmonic : MonomialOrder.lex.Monic
      (MvPolynomial.map ep.toRingHom F.toPair.curveEquation) := by
    have hs :
        (MvPolynomial.map ep.toRingHom F.toPair.curveEquation).support =
          F.toPair.curveEquation.support :=
      MvPolynomial.support_map_of_injective _ ep.injective
    rw [MonomialOrder.Monic, MonomialOrder.leadingCoeff,
      MonomialOrder.degree, hs, MvPolynomial.coeff_map]
    change ep.toRingHom
        (MonomialOrder.lex.leadingCoeff F.toPair.curveEquation) = 1
    rw [F.toPair.curveEquation_monic.leadingCoeff_eq_one, map_one]
  apply FiniteCorrespondencePair.eq_of_monic_of_associated
    hmonic G.toPair.curveEquation_monic
  rw [← Ideal.span_singleton_eq_span_singleton]
  calc
    Ideal.span {MvPolynomial.map ep.toRingHom
        F.toPair.curveEquation} =
        Ideal.map
          (MvPolynomial.mapAlgEquiv (Fin 2) ep).toRingEquiv
          (Ideal.span {F.toPair.curveEquation}) := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    _ = Ideal.map
        (MvPolynomial.mapAlgEquiv (Fin 2) ep).toRingEquiv
        F.toPair.ideal := by
      rw [F.toPair.ideal_eq_span_curveEquation]
    _ = G.toPair.ideal := by
      exact F.toPair_ideal_map_parameterEquivOfIdealEq G h
    _ = Ideal.span {G.toPair.curveEquation} :=
      G.toPair.ideal_eq_span_curveEquation

end FiniteCorrespondenceFamilyMember

end

end AclGeom
