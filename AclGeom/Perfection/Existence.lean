/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import AclGeom.Perfection.Subfield
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Existence of a chosen perfection in every characteristic

The relative perfect closure of K inside an algebraic closure supplies a chosen Perfection K
for every exponential characteristic. This proves the existence required by blueprint
Foundation III (#24). The bundle and perfected-subfield interface stay in Subfield, so their
users do not need to import the algebraic-closure construction.

**Status:** the all-characteristic constructor and nonempty instance are proved.
Compatible transport and change of choice are in Perfection/Naturality.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is sources/blueprint.tex.
-/

namespace AclGeom

noncomputable section

universe u

namespace Perfection

/-- A chosen perfection in any exponential characteristic, obtained as the
relative perfect closure inside an algebraic closure. This supplies the
existence required by blueprint Foundation III and the chosen-perfection
parameter used by `Perfection.Lattice`. -/
def ofExpChar (K : Type u) [Field K] (q : ℕ) [ExpChar K q] :
    Perfection K where
  carrier := perfectClosure K (AlgebraicClosure K)
  p := q
  incl := algebraMap K (perfectClosure K (AlgebraicClosure K))

/-- Every field has a chosen perfection (blueprint Foundation III). -/
instance instNonempty (K : Type u) [Field K] : Nonempty (Perfection K) :=
  ⟨ofExpChar K (ringExpChar K)⟩

end Perfection

end

end AclGeom
