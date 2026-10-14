/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import AclGeom.Correspondence.Composition
import AclGeom.Correspondence.AmbientAutomorphism
import AclGeom.Closure.Ambient

/-!
# Associativity of relational correspondence composition

Finite correspondences can have several composite components. Associativity
means equality of the possible final germs under the two parenthesizations.
The endpoint-pair isomorphism extends to an ambient automorphism, which aligns
the selected presentations into a common chain of four generic coordinates.
No single-valued selection of components is used.
-/

namespace AclGeom

noncomputable section

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- Transport a selected finite branch through an ambient automorphism. -/
private def transportPair (σ : Ω ≃ₐ[k] Ω) (P : FiniteCorrespondencePair k Ω) :
    FiniteCorrespondencePair k Ω where
  source := σ P.source
  target := σ P.target
  source_generic := (algHom_mem_racl_empty_iff σ.toAlgHom).not.mpr P.source_generic
  target_mem_source := (algHom_mem_racl_singleton_iff σ.toAlgHom).mpr P.target_mem_source
  source_mem_target := (algHom_mem_racl_singleton_iff σ.toAlgHom).mpr P.source_mem_target

/-- The transported branch presents the same correspondence germ. -/
private theorem transportPair_ideal (σ : Ω ≃ₐ[k] Ω) (P : FiniteCorrespondencePair k Ω) :
    (transportPair σ P).ideal = P.ideal := by
  have h : (![σ P.source, σ P.target] : Fin 2 → Ω) = σ ∘ ![P.source, P.target] := by
    funext i
    fin_cases i <;> rfl
  change idealOf k ![σ P.source, σ P.target] = idealOf k ![P.source, P.target]
  rw [h]
  exact idealOf_comp_algHom k σ.toAlgHom _

/-- Relational finite-correspondence composition is associative over any
base field in an algebraically closed ambient. Both sides retain every
possible composite component, rather than choosing a binary operation. -/
theorem FiniteCorrespondenceGerm.composes_assoc [IsAlgClosed Ω]
    (A B C D : FiniteCorrespondenceGerm k Ω) :
    (∃ E, Composes A B E ∧ Composes E C D) ↔
      ∃ F, Composes B C F ∧ Composes A F D := by
  constructor
  · rintro ⟨E, ⟨P, Q, hPQ, hA, hB, hE⟩, ⟨R, S, hRS, hE', hC, hD⟩⟩
    have hI : idealOf k ![P.source, Q.target] = idealOf k ![R.source, R.target] :=
      hE.symm.trans hE'
    obtain ⟨σ, -, hσ⟩ := exists_ambientAutomorphism_of_idealOf_eq hI
    have hσx : σ P.source = R.source := hσ 0
    have hσz : σ Q.target = R.target := hσ 1
    let P' := transportPair σ P
    let Q' := transportPair σ Q
    have hPQ' : P'.target = Q'.source := congrArg σ hPQ
    have hQS : Q'.target = S.source := hσz.trans hRS
    refine ⟨ofPair (Q'.comp S hQS), ⟨Q', S, hQS, ?_, hC, rfl⟩,
      ⟨P', Q'.comp S hQS, hPQ', ?_, rfl, ?_⟩⟩
    · exact hB.trans (transportPair_ideal σ Q).symm
    · exact hA.trans (transportPair_ideal σ P).symm
    · rw [hD]
      change idealOf k ![R.source, S.target] = idealOf k ![σ P.source, S.target]
      rw [hσx]
  · rintro ⟨F, ⟨P, Q, hPQ, hB, hC, hF⟩, ⟨R, S, hRS, hA, hF', hD⟩⟩
    have hI : idealOf k ![P.source, Q.target] = idealOf k ![S.source, S.target] :=
      hF.symm.trans hF'
    obtain ⟨σ, -, hσ⟩ := exists_ambientAutomorphism_of_idealOf_eq hI
    have hσy : σ P.source = S.source := hσ 0
    have hσw : σ Q.target = S.target := hσ 1
    let P' := transportPair σ P
    let Q' := transportPair σ Q
    have hRP : R.target = P'.source := hRS.trans hσy.symm
    have hPQ' : P'.target = Q'.source := congrArg σ hPQ
    refine ⟨ofPair (R.comp P' hRP), ⟨R, P', hRP, hA, ?_, rfl⟩,
      ⟨R.comp P' hRP, Q', hPQ', rfl, ?_, ?_⟩⟩
    · exact hB.trans (transportPair_ideal σ P).symm
    · exact hC.trans (transportPair_ideal σ Q).symm
    · rw [hD]
      change idealOf k ![R.source, S.target] = idealOf k ![R.source, σ Q.target]
      rw [hσw]

end

end AclGeom
