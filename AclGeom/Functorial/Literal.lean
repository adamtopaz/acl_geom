/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import AclGeom.Main
import Mathlib.CategoryTheory.Core
import Mathlib.Order.Category.PartOrd

/-!
# The literal geometry functor and its Hom-set fibres

Blueprint §20. An object of `Ext^i` (`PerfExt`) is a relatively algebraically closed
extension `K/k` with a chosen perfection of `K`. The perfected base `k^i` of (20.1) is
`perf.basePerf base`. An arrow (`PerfExt.Hom`, the blueprint's `PairPerfIso`) is an isomorphism
of the chosen perfections carrying `k^i` onto `l^i`. These form a groupoid.

The geometry side is the groupoid `Core PartOrd` of partial orders and order isomorphisms,
in the closed-lattice presentation the blueprint allows after (20.3). The literal functor
`geomLit` sends `K/k` to its lattice `𝒢(K/k)` of closed intermediate fields, and an arrow `Φ` to
the transported lattice isomorphism `T_Φ(M) = Φ(M^i) ∩ L` of (20.6). Its functor laws are
(20.9) and (20.11).

* `geomLit_map_frobHom`: integral Frobenius powers act trivially, (20.12);
* `frobHom_naturality`: Frobenius commutes with every arrow, (20.14);
* `geomLit_map_surjective`: the functor is full on objects of transcendence degree at least
  five, (20.15);
* `geomLit_map_eq_iff`: its fibres are the integral Frobenius orbits, (20.16) (blueprint
  Prop `hom-fibres`). The exponent is unique in positive characteristic
  (`frobHom_comp_injective`), and Frobenius is the identity in characteristic zero
  (`frobHom_eq_id`).

**Status:** proved.
-/

namespace AclGeom

open CategoryTheory

noncomputable section

universe u v

/-- **An object of `Ext^i`** (blueprint §20.1): a relatively algebraically closed extension
together with a chosen perfection of the extension field. The perfected base `k^i` of (20.1) is
`perf.basePerf base`. -/
structure PerfExt : Type (max u v + 1) where
  /-- The base field `k`. -/
  base : Type u
  /-- The extension field `K`. -/
  ext : Type v
  /-- The field structure on the base. -/
  [fieldBase : Field base]
  /-- The field structure on the extension. -/
  [fieldExt : Field ext]
  /-- The embedding of the base field into the extension. -/
  [algebra : Algebra base ext]
  /-- The base is relatively algebraically closed in the extension. -/
  isRAC : IsRAC (⊥ : IntermediateField base ext)
  /-- The chosen perfection `K^i` of the extension field. -/
  perf : Perfection ext

attribute [instance] PerfExt.fieldBase PerfExt.fieldExt PerfExt.algebra

variable {A B C : PerfExt.{u, v}}

namespace PerfExt

/-- **An arrow of `Ext^i`** (the blueprint's `PairPerfIso`): an isomorphism of the chosen
perfections carrying the perfected base onto the perfected base. -/
@[ext]
structure Hom (A B : PerfExt.{u, v}) where
  /-- The isomorphism of chosen perfections. -/
  toRingEquiv : A.perf.carrier ≃+* B.perf.carrier
  /-- It carries `k^i` onto `l^i`. -/
  compatible : CrossBase.Compatible (k := A.perf.basePerf A.base)
    (l := B.perf.basePerf B.base) toRingEquiv

/-- `Ext^i` is a groupoid (blueprint §20.1): composition, identities and inverses are those of
field isomorphisms. -/
instance : Groupoid PerfExt.{u, v} where
  Hom := Hom
  id _ := ⟨RingEquiv.refl _, CrossBase.compatible_refl⟩
  comp f g := ⟨f.toRingEquiv.trans g.toRingEquiv, f.compatible.trans g.compatible⟩
  inv f := ⟨f.toRingEquiv.symm, f.compatible.symm⟩
  id_comp _ := Hom.ext (RingEquiv.ext fun _ ↦ rfl)
  comp_id _ := Hom.ext (RingEquiv.ext fun _ ↦ rfl)
  assoc _ _ _ := Hom.ext (RingEquiv.ext fun _ ↦ rfl)
  inv_comp f := Hom.ext (RingEquiv.ext fun x ↦ f.toRingEquiv.apply_symm_apply x)
  comp_inv f := Hom.ext (RingEquiv.ext fun x ↦ f.toRingEquiv.symm_apply_apply x)

@[ext]
theorem hom_ext {f g : A ⟶ B} (h : f.toRingEquiv = g.toRingEquiv) : f = g :=
  Hom.ext h

@[simp]
theorem id_toRingEquiv (A : PerfExt.{u, v}) : (𝟙 A : A ⟶ A).toRingEquiv = RingEquiv.refl _ :=
  rfl

@[simp]
theorem comp_toRingEquiv (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).toRingEquiv = f.toRingEquiv.trans g.toRingEquiv :=
  rfl

/-- The closed-subfield lattice `𝒢(K/k)` of an object, in the groupoid of partial orders and
order isomorphisms. -/
abbrev geom (A : PerfExt.{u, v}) : Core PartOrd.{v} :=
  ⟨PartOrd.of (ClosedIF A.base A.ext)⟩

end PerfExt

/-- An isomorphism of partial orders is an order isomorphism. -/
def orderIsoOfPartOrdIso {X Y : PartOrd.{v}} (e : X ≅ Y) : X ≃o Y :=
  OrderIso.ofHomInv e.hom.hom e.inv.hom (OrderHom.ext _ _ (funext (PartOrd.hom_inv_apply e)))
    (OrderHom.ext _ _ (funext (PartOrd.inv_hom_apply e)))

@[simp]
theorem orderIsoOfPartOrdIso_apply {X Y : PartOrd.{v}} (e : X ≅ Y) (x : X) :
    orderIsoOfPartOrdIso e x = e.hom x :=
  rfl

open PerfExt

/-- **The literal geometry functor** `𝔾_lit` (blueprint (20.6)): an arrow `Φ` goes to its
transported lattice isomorphism `T_Φ(M) = Φ(M^i) ∩ L`. The functor laws are (20.9) and
(20.11) (blueprint Prop: the literal construction is a functor). -/
def geomLit : PerfExt.{u, v} ⥤ Core PartOrd.{v} where
  obj := geom
  map {A B} Φ := ⟨PartOrd.Iso.mk (A.perf.inducedIso B.perf Φ.compatible)⟩
  map_id A := Core.hom_ext <| PartOrd.ext fun M ↦
    congrArg (· M) (A.perf.inducedIso_refl (k := A.base))
  map_comp f g := Core.hom_ext <| PartOrd.ext fun M ↦
    congrArg (· M) (Perfection.inducedIso_trans f.compatible g.compatible)

theorem geomLit_map_iso_hom_apply (Φ : A ⟶ B) (M : ClosedIF A.base A.ext) :
    (geomLit.map Φ).iso.hom M = A.perf.inducedIso B.perf Φ.compatible M :=
  rfl

/-- The order isomorphism of closed lattices underlying the image of an arrow is `T_Φ`. -/
theorem orderIsoOfPartOrdIso_geomLit_map (Φ : A ⟶ B) :
    orderIsoOfPartOrdIso (geomLit.map Φ).iso = A.perf.inducedIso B.perf Φ.compatible :=
  rfl

namespace PerfExt

/-- **The integral Frobenius automorphism** `F_A^n` of an object (blueprint §20.4). -/
def frobHom (A : PerfExt.{u, v}) (n : ℤ) : A ⟶ A :=
  ⟨A.perf.frobZPow n, A.perf.compatible_frobZPow A.isRAC n⟩

@[simp]
theorem frobHom_toRingEquiv (A : PerfExt.{u, v}) (n : ℤ) :
    (A.frobHom n).toRingEquiv = A.perf.frobZPow n :=
  rfl

theorem frobHom_zero (A : PerfExt.{u, v}) : A.frobHom 0 = 𝟙 A :=
  hom_ext (RingEquiv.ext fun _ ↦ rfl)

theorem frobHom_add (A : PerfExt.{u, v}) (m n : ℤ) :
    A.frobHom m ≫ A.frobHom n = A.frobHom (m + n) := by
  ext x
  rw [comp_toRingEquiv, frobHom_toRingEquiv, frobHom_toRingEquiv, frobHom_toRingEquiv,
    RingEquiv.trans_apply, add_comm, Perfection.frobZPow_add]
  rfl

/-- **Frobenius acts trivially on the geometry** (blueprint (20.12)). -/
theorem geomLit_map_frobHom (A : PerfExt.{u, v}) (n : ℤ) :
    geomLit.map (A.frobHom n) = 𝟙 (geomLit.obj A) :=
  Core.hom_ext <| PartOrd.ext fun M ↦
    congrArg (· M) (A.perf.inducedIso_frobZPow A.isRAC n)

/-- Conjugating the Frobenius powers of `A` by an arrow gives those of `B`. In particular the
two characteristic exponents agree. -/
private theorem frobZPow_conj (Φ : A ⟶ B) (n : ℤ) (x : A.perf.carrier) :
    Φ.toRingEquiv (A.perf.frobZPow n x) = B.perf.frobZPow n (Φ.toRingEquiv x) := by
  have hp : A.perf.p = B.perf.p := by
    have := expChar_of_injective_ringHom (f := Φ.toRingEquiv.toRingHom) Φ.toRingEquiv.injective
      A.perf.p
    exact ExpChar.eq this inferInstance
  let c : RingAut A.perf.carrier →* RingAut B.perf.carrier :=
    MonoidHom.mk' (fun ψ ↦ Φ.toRingEquiv.symm.trans (ψ.trans Φ.toRingEquiv)) fun a b ↦
      RingEquiv.ext fun y ↦ by simp only [RingAut.mul_apply, RingEquiv.trans_apply,
        RingEquiv.symm_apply_apply]
  have h1 :
      c (frobeniusEquiv A.perf.carrier A.perf.p) = frobeniusEquiv B.perf.carrier B.perf.p := by
    ext y
    change Φ.toRingEquiv ((Φ.toRingEquiv.symm y) ^ A.perf.p) = y ^ B.perf.p
    rw [map_pow, RingEquiv.apply_symm_apply, hp]
  have h := congrArg (fun ψ : RingAut B.perf.carrier ↦ ψ (Φ.toRingEquiv x))
    ((map_zpow c (frobeniusEquiv A.perf.carrier A.perf.p) n).trans (by rw [h1]))
  simpa [c, Perfection.frobZPow, frobeniusZPow] using h

/-- **Frobenius naturality** (blueprint (20.14)): `Φ ∘ F_A^n = F_B^n ∘ Φ`. The two
characteristic exponents are not assumed equal; they agree because `Φ` is a field
isomorphism. -/
theorem frobHom_naturality (Φ : A ⟶ B) (n : ℤ) : A.frobHom n ≫ Φ = Φ ≫ B.frobHom n := by
  ext x
  exact frobZPow_conj Φ n x

/-- In characteristic zero every integral Frobenius power is the identity. -/
theorem frobHom_eq_id (A : PerfExt.{u, v}) (hp : A.perf.p = 1) (n : ℤ) : A.frobHom n = 𝟙 A := by
  ext x
  rw [frobHom_toRingEquiv, Perfection.frobZPow,
    frobeniusZPow_eq_one_of_eq_one (K := A.perf.carrier) A.perf.p hp n]
  rfl

/-- In positive characteristic the integral Frobenius exponent of an arrow is unique (blueprint
Prop `hom-fibres`). -/
theorem frobHom_comp_injective (htr : (5 : Cardinal) ≤ Algebra.trdeg A.base A.ext)
    (hp : B.perf.p ≠ 1) (Φ : A ⟶ B) : Function.Injective fun n : ℤ ↦ Φ ≫ B.frobHom n := by
  intro m n h
  exact Perfection.trans_frobZPow_injective (A.perf.inducedIso B.perf Φ.compatible) htr hp
    Φ.toRingEquiv (congrArg Hom.toRingEquiv h)

end PerfExt

/-- **Fullness** (blueprint (20.15)): for an object of transcendence degree at least five,
every order isomorphism of closed lattices is the image of an arrow. -/
theorem geomLit_map_surjective {A B : PerfExt.{u, v}}
    (htr : (5 : Cardinal) ≤ Algebra.trdeg A.base A.ext) :
    Function.Surjective (geomLit.map : (A ⟶ B) → (geomLit.obj A ⟶ geomLit.obj B)) := by
  intro f
  obtain ⟨-, Φ, hΦ, h, -⟩ := reconstruction_target A.perf B.perf A.isRAC B.isRAC htr
    (orderIsoOfPartOrdIso f.iso)
  refine ⟨⟨Φ, hΦ⟩, Core.hom_ext <| PartOrd.ext fun M ↦ ?_⟩
  have heq := (Perfection.induces_iff_eq_inducedIso hΦ).1 h
  exact (congrArg (fun e : ClosedIF A.base A.ext ≃o ClosedIF B.base B.ext ↦ e M) heq).symm

/-- **The Hom-set fibres** (blueprint (20.16), Prop `hom-fibres`): for an object of
transcendence degree at least five, two arrows have the same image exactly when they differ by
an integral Frobenius power of the target. -/
theorem geomLit_map_eq_iff {A B : PerfExt.{u, v}}
    (htr : (5 : Cardinal) ≤ Algebra.trdeg A.base A.ext) (Φ₁ Φ₂ : A ⟶ B) :
    geomLit.map Φ₁ = geomLit.map Φ₂ ↔ ∃ n : ℤ, Φ₂ = Φ₁ ≫ B.frobHom n := by
  constructor
  · intro h
    have he : A.perf.inducedIso B.perf Φ₁.compatible = A.perf.inducedIso B.perf Φ₂.compatible := by
      rw [← orderIsoOfPartOrdIso_geomLit_map, ← orderIsoOfPartOrdIso_geomLit_map, h]
    have h₂ := Perfection.induces_inducedIso Φ₂.compatible
    rw [← he] at h₂
    obtain ⟨n, hn⟩ :=
      ((Perfection.induces_inducedIso Φ₁.compatible).iff_exists_eq_trans_frobZPow htr).1 h₂
    exact ⟨n, hom_ext hn⟩
  · rintro ⟨n, rfl⟩
    rw [Functor.map_comp, geomLit_map_frobHom, Category.comp_id]

end

end AclGeom
