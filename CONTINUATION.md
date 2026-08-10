# Continuation guide

This document lets a fresh agent (or human) pick up the formalization
with no prior context and carry it to completion. Read this file, then
the issue tracker, then start working.

## What this project is

A Lean 4 formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem. The mathematical source of truth is
`sources/blueprint.tex`. The library lives in `AclGeom/`, a Verso book
documenting it lives in `AclGeomBook/` (built with `lake exe book`).
Toolchain: see `lean-toolchain`; verso is pinned to the nearest minor
tag of the toolchain (currently v4.32.0 for toolchain v4.32.2).

## How work is coordinated

- **All coordination happens on GitHub issues** of `adamtopaz/acl_geom`.
  Adam reads the issues, the code, and the generated Verso page; he
  steers by commenting on issues. Check for new comments from Adam at
  the start of every work session and treat them as top priority.
- Issue map: #1 coordination, #2–#10 milestones M0–M8, #11 M3a
  regularity brick, **#12 M4a design — the active issue**, and #13
  M4b function-field curve theory (completed).
- Do not add a Claude signature or Claude attribution to issue comments.
  Current Codex progress comments are left unsigned.
- Post a progress comment on the relevant milestone issue after each
  substantive push.

## Hard policies

- **Never leave `sorry` on `main`** outside files whose module
  docstring marks them WIP. (Currently no file contains sorries.)
- **Never axiomatize blueprint theorems.** Everything is proved.
- Verify with `lake build` (or `lake build <module>`); never trust
  `lake env lean` alone. Run a full `lake build` before every commit.
- Keep `lake exe book` building; grow the book alongside the code.
- Never `cd` into `.lake/packages/*` — lake builds whatever package
  the cwd is in.
- Commit and push in small verifiable increments, always green.

## State of the library (all built, CI green)

### Foundations (earlier milestones)
- M0 skeleton/CI done; M1–M3 lattice/pregeometry layers done through
  the "hard kernel" (see issues #3–#5, #11); M4 partially done (#6).
  The curve theory below is M4b (#13), the completeness half of the
  configuration layer, targeting blueprint Lemma 8.4.

### Curve theory (`AclGeom/Curves/`, Stichtenoth-style, no schemes;
### base field algebraically closed, all places degree one)
- `Places.lean` — places are DVRs (Stichtenoth 1.1.6, self-contained).
- `Divisors.lean` — ord calculus, divisors, `deg div f = 0` support.
- `Residues.lean`, `DegreeBound.lean` — residue fields, pole-degree =
  `[F : k(f)]` (1.4.11).
- `RiemannRoch.lean` — `L(D)`, one-point decomposition, `ℓ ≤ deg + 1`.
- `Genus.lean` — defect, genus, Riemann's inequality.
- `Rational.lean` — genus 0 ⟺ rational (`genus_eq_zero_iff_exists_generator`).
- `Adeles.lean` — adele space, monomials, one-point steps, stabilized
  Riemann, 1.5.8 (`adeleSubmodule_eq_sup_of_defect_eq_genus`).
- `Specialty.lean` — index of specialty, full Riemann–Roch
  `ℓ(D) = deg D + 1 − g + i(D)`.
- `Differentials.lean` — Weil differentials, levels, proportionality
  (dim_F Ω = 1), max level exists.
- `Canonical.lean` — duality `i(D) = ℓ(W−D)`, canonical divisor with
  `deg W = 2g−2`, `ℓ(W) = g`.

### Tate residue theory
- `Tate/FinitePotent.lean` — finite-potent operators, cores, the Tate
  trace, squared-range trace calculus (symmetry, additivity,
  finite-sum additivity, traceless commutators), commensurability
  (`AlmostLE`), trace class, the abstract projection-comparison
  theorem (`tateTrace_commutator_eq_of_projection`), compatible
  projection pairs (`exists_projection_pair`), abstract trace-class
  certificates (`isTraceClass_commutator_of_comm`).
- `Curves/TateResidue.lean` — valuation-ring filtration and
  commensurability; the residue
  `P.residue f g := tateTrace [ε∘m_f, m_g]` (morally `res_P(f dg)`)
  with: trace-class certificate; **bilinearity** (`residue_add_left/
  right`, `residue_smul_left/right`, `residue_zero_left/right`);
  **R2** (`residue_eq_zero_of_mem`: vanishing for integral pairs);
  **ord-link** (`residue_inv_self : res(g⁻¹dg) = ord g` for
  `ord g ≥ 0`); **threshold** (`residue_eq_zero_of_ord_ge`:
  `res(f dg) = 0` for `ord f ≥ m+1`, `ord g ≥ −m`, char-free
  nilpotency proof); **projection independence** (`residue_eq_of_
  projection`, and `residue_eq_of_projection_filtration` for
  filtration stages); **Leibniz** (`residue_mul_right`:
  `res(x d(gh)) = res(xg dh) + res(xh dg)`); the principal-part
  decomposition (`isCompl_principalSpan`) and the **monomial table**:
  `residue_zpow_pi_base` (`res(π^c dπ) = 0`, `c ≤ −2`),
  `residue_one_right`, `residue_zpow_pi_self`
  (`res(π^{−b}d(π^b)) = b`), `residue_zpow_flip`,
  `residue_zpow_pi_zpow_eq_zero` (`res(π^a d(π^b)) = 0` for
  `a+b ≠ 0`).
- `Curves/GlobalResidue.lean` — bounded adele spaces inside the adele
  module are pairwise commensurable; adelic multiplication
  almost-stabilizes them; global trace-class; the diagonal;
  **`tateTrace_adeleSMul_commutator_eq_zero`** (global trace
  vanishes, via the triple decomposition from 1.5.8);
  the componentwise projection (`adeleProj`) acting blockwise;
  single-place inclusions (`adeleSingle`); block operators with
  vanishing cross-products; **`tateTrace_adeleProj_commutator`**
  (localization: global trace = Σ local traces); **the residue
  theorem `sum_residue_eq_zero` : `Σ_{P∈S} res_P(f dg) = 0`** for any
  finite S outside which f, g are integral; the residue functional
  `residueFunctional g : Dual k 𝔸` (`ω_g`), which kills the diagonal
  and the bounded space at level `−2·poleDivisor(g)`
  (`residueFunctional_mem_weilDifferentialsAt`) and is **nonzero at
  uniformizers** (`residueFunctional_pi_ne_zero`, value 1 on the
  single-place adele `π⁻¹`).

## THE ACTIVE TASK: M4a — finite-cover field action and algebraization

P6 and P7 are complete in the library: regular-derivation rigidity,
infinitesimal automorphisms, genus-zero rationality, rational-function-field
automorphisms, Möbius normalization, and the algebraic affine-action
endgame all compile and are documented.  Issue #12 is active again.

The current boundary is blueprint Theorem 8.2 applied to equation (8.6):

1. The rank-two `A/B/C` parameter multiplication and the rank-one
   `S/T/U` quotient are genuine presented groupoids; the induced vertex
   homomorphism has a normal categorical kernel with the expected rank-one
   fiber count.
2. Every joint parameter edge is a finite cover.  Its conjugate branches
   and deck group are normalized against one reference edge with strict
   cocycle laws, and the full finite branch/deck bundles are globally
   trivialized without collapsing their positive-dimensional base.
3. `AlgebraicClosureTransport.lean` now gives each selected finite
   correspondence a semilinear equivalence between the algebraic closures
   of its source and target curve fields.  Independent lifts are not
   declared coherent: their composition discrepancy is an explicit deck
   automorphism fixing the target curve field.
4. `Config/ChunkFieldAction.lean` instantiates this for Ψ.  Over the field
   generated by the two independent rank-two parameters, the selected
   `A` transport sends `X` to `Y`, the `B` transport sends `Y` to `Z`, and
   strict composition followed by the vertical deck defect is exactly the
   selected `C` transport.  This is the field-action form of (8.6).
5. `FiniteNormalTransport.lean` proves that semilinear algebraic-closure
   transport preserves finite normal subcovers and that every vertical
   base-fixing automorphism stabilizes such a cover.  The corrected ambient
   composition law therefore restricts exactly.
6. `Config/ChunkFiniteFieldAction.lean` chooses the Ψ source cover as the
   finite normal compositum of the selected `A` branch cover, the pullback
   of the selected `B` branch cover, and the selected composite `C` branch
   cover.  Its middle and target transports contain all three branches,
   and the deck-corrected `A · B = C` equality now holds on these
   finite-dimensional normal fields.
7. `Correspondence/AlgebraicGroup.lean` fixes the honest target of the
   algebraization step: separated finite-type group schemes over the base
   field, with the connected version geometrically integral.  It constructs
   scheme-theoretic kernels in the internal group category, proves that the
   kernel is a closed finite-type separated subgroup scheme, and proves its
   inclusion normal by identifying the kernel square with pullback along the
   unit section.
8. `Correspondence/WeilGluing.lean` begins the actual scheme-gluing layer.
   Compatible maps on open charts descend to Mathlib's explicit glued
   scheme; local finite type descends from all charts; a finite atlas of
   quasi-compact chart maps is quasi-compact; and integral charts with
   nonempty pairwise overlaps glue to an integral scheme.  These discharge
   the abstract descent and irreducibility consequences needed once the
   normalized chunk supplies its concrete transition charts.
9. `Correspondence/FiniteExtensionChart.lean` turns a finite extension of a
   finitely generated parameter field into an integral separated affine
   scheme of finite type over the ground field, with the prescribed extension
   as its fraction field.  `Config/ChunkAlgebraicChart.lean` applies this
   construction to the normalized `A/S`, `B/T`, and `C/U` scalar covers.  The
   two displayed parameter coordinates still generate their base fields and
   are algebraically independent, so these are genuine rank-two scheme charts
   rather than finite deck groups.
10. `Correspondence/BirationalGluing.lean` converts mutually inverse dominant
    partial maps into an isomorphism between explicit dense open subschemes.
    Its rational-map form applies this to inverse dominant rational maps
    between integral separated schemes.  Together with the direct
    `IsFractionRing` realization of every finite-extension chart inside its
    selected ambient cover field, this supplies the generic birational-to-open
    bridge needed by the normalized transition maps.

**Next exact step:** clear the finitely many coordinate-ring denominators of
the normalized field equivalences, producing dominant rational maps between
the concrete affine models.  Apply the dense-open bridge above, package the
resulting transition isomorphisms as `Scheme.GlueData`, then glue
multiplication and inverse on the resulting integral locally finite-type
scheme.  Prove separatedness and extract the finite atlas to package the
result in the new scheme-level algebraic-group target.  Then identify the
already constructed categorical rank-one normal kernel with the connected
component of its scheme-theoretic kernel, apply the completed affine-action
classification, and finish affine-grid extraction (8.5) and Q correctness.

Do not substitute the finite deck group for the parameter group.  The deck
group only records the vertical ambiguity of chosen lifts; the parameter
base still has two independent rank-two inputs.

## Historical handoff: P6 automorphism rigidity (completed)

**Statement to prove (core)**: for genus `g ≥ 2`, every k-derivation
`D : F → F` (k-linear + Leibniz `D(ab) = aD(b) + bD(a)`, `D` kills k)
that is *regular everywhere* (`∀ P, D(O_P) ⊆ O_P`) is zero. Then a
`g = 1` variant: a regular derivation vanishing at one place (image in
the maximal ideal there) is zero. These feed the blueprint's argument
that no positive-dimensional connected automorphism group exists for
`g ≥ 1` (blueprint §8, around lines 1430–1470 of blueprint.tex), which
combines with the genus-0 endgame (`P⁴`-checkpoint, Möbius bricks) in
P7.

**The settled design (fully elementary — no chain rule, no
separability theory, no completions).** All residue ingredients are
already formalized except items (a)–(e) below.

1. Fix a derivation `D`, regular everywhere, `D ≠ 0`; pick `u₀` with
   `Du₀ ≠ 0`. Fix any place `P₀`, let `π := P₀.pi`.
2. `t := π + c • u₀` for a good `c ∈ k`: since `g ↦ ω_g :=
   residueFunctional g` is k-linear in g (residue bilinearity in the
   second slot — the linear-map packaging of `g ↦ ω_g` is a small
   missing lemma) and `ω_π ≠ 0`, at most one `c` kills
   `ω_t = ω_π + c·ω_{u₀}`; since k is infinite, choose `c ≠ 0` with
   `ω_t ≠ 0`. Then `Dt = c·Du₀ ≠ 0`.
3. `ω_t` is a nonzero Weil differential; let `W_t` be its divisor
   (its greatest level — machinery in `Differentials.lean`:
   `exists_isGreatest_level`; the pointwise value `w_P := (W_t) P` is
   characterized by: `ω_t` kills all single-place adeles at `P` of
   order `≥ −w_P`, and there is a single-place adele of order
   `−w_P − 1` not killed — from the one-point step
   `adeleSpace_add_single` and maximality; this "local level"
   extraction is missing lemma (c) below).
4. **Local bound at places where `t ∈ O_P`**: Taylor-expand
   (`Place.exists_taylor`) `t = Σ_{i<n} c_i π_P^i + π_P^n b` with
   `n > w_P + 1`. Single-place evaluation of `ω_t` (missing lemma (b))
   plus bilinearity plus the monomial table give
   `res_P(π^{−i}, t) = (i:k)·c_i` for `i < n` — the tail term dies by
   the *mirror threshold* (missing lemma (a)). Level-vanishing then
   forces `(i:k)·c_i = 0` for all `i ≤ w_P`. Now apply `D` to the
   Taylor expansion using only Leibniz on finite sums:
   `Dt = Σ_i c_i·(i·π^{i−1})·Dπ_P + n π^{n−1} b Dπ_P + π^n Db`
   (note `D(c_i • π^i) = c_i • (i:k)-scaled…`; the terms with
   `i ≤ w_P` vanish because the scalar `(i:k)c_i = 0`); every
   surviving term has `ord_P ≥ w_P` using regularity
   (`ord(Dπ_P) ≥ 0`, `ord(Db) ≥ 0`). Hence `ord_P(Dt) ≥ w_P`.
5. **At poles of `t`** (finitely many): `t⁻¹ ∈ O_P`; from Leibniz on
   `1 = t·t⁻¹`: `Dt = −t²·D(t⁻¹)`; and from the residue Leibniz rule
   the levels of `ω_t` and `ω_{t⁻¹}` at `P` differ by `2·ord_P(t)`
   (`res(f, t) = −res(f·t², t⁻¹)` — derive from `residue_mul_right`
   applied twice, e.g. via `0 = res(f·t, t·t⁻¹·…)`-style
   manipulations). Then the step-4 bound at `t⁻¹` transports to `t`.
   (Missing lemma (d); do the bookkeeping carefully on paper first.)
6. Conclusion: `div(Dt) ≥ W_t` pointwise, i.e. `Dt ∈ L(−W_t)`. Since
   `deg W_t = 2g−2` (proportionality `exists_eq_comp_adeleSMul` +
   level-shift `isGreatest_level_comp` transport the degree from the
   canonical divisor of `exists_canonicalDivisor`; small missing lemma
   (e)), `deg(−W_t) = 2−2g < 0`, so `L(−W_t) = 0`
   (`riemannSpace_eq_bot_of_deg_neg`), so `Dt = 0`, contradicting
   `Dt = c·Du₀ ≠ 0`. ∎

**Missing lemmas, in recommended order:**

(a) **Mirror threshold**: `res_P(f, g) = 0` when `ord f ≥ −m` and
    `ord g ≥ m + 1` (`m : ℕ`). Proof pattern: mirror of
    `residue_eq_zero_of_ord_ge` (same z-iteration nilpotency; now the
    commutator kills `π^m O_P` — for `x` there, `fx ∈ O` and
    `fgx ∈ πO ⊆ O` so both projections fix — lands in `O`, and the
    depth-gain via `ord(fg) ≥ 1` runs the same way; design notes in
    the m3a memory file if available, else re-derive: it is the same
    five-have skeleton: `hδO`, `hsub_ord`, `hfy`, `hstep`, `hrange`,
    `hpow` induction, `hnil`).
    Needed for the Taylor tail `res(π^{−i}, π^n b) = 0` for `n ≥ i+1`:
    apply with `f := π^{−i}` (`ord = −i ≥ −m` with `m := i`) and
    `g := π^n b` (`ord ≥ n ≥ i + 1 = m + 1`). ✓ exactly fits.

(b) **Single-place evaluation**:
    `residueFunctional g (adeleSingle P f) = P.residue f g` — via
    `residueFunctional_eq_sum` with `S := {P}` (other coordinates are
    0, `residue_zero_left`), `Finset.sum_singleton`,
    `adeleSinglePi_apply_self`. Trivial with existing pieces.

(c) **Local level extraction**: package, for a nonzero Weil
    differential `ω` with greatest level `W`
    (`exists_isGreatest_level`), the two facts
    (i) `∀ f, ord_P f ≥ −(W P) → ω (adeleSingle P f) = 0`
    (single-place adeles of bounded order lie in `boundedSubmodule W`;
    memberships are straightforward) and
    (ii) `∃ f, ω (adeleSingle P f) ≠ 0 ∧ ord_P f = −(W P) − 1`
    (maximality: `ω ∉ Ω(W + single P 1)`; use
    `adeleSpace_add_single` to decompose a witness into an `A(W)`
    part, killed, plus a monomial multiple — the monomial
    `adeleMonomial P (−(W P) − 1)` is essentially `adeleSingle P
    (π^{−W P −1})`, compare the two constructions, they agree
    definitionally at the coordinate level).

(d) **Pole-place transport** (step 5 above), and

(e) **Degree of the divisor of any nonzero differential = 2g−2**:
    from `exists_canonicalDivisor`'s `W₀` and proportionality: any
    nonzero `ω = ω₀ ∘ (mult by h)` (`exists_eq_comp_adeleSMul`), and
    `isGreatest_level_comp` says levels shift by `div h`;
    `deg div h = 0` finishes. Check exact statement shapes in
    `Differentials.lean` / `Canonical.lean`.

Then assemble the core theorem, state the `g = 1` variant (same
argument, but the vector field additionally vanishes at the fixed
place, giving `Dt ∈ L(−W_t − P)` of degree `−1 < 0` when `2g−2 = 0`),
and post on #13.

## Remaining project roadmap

- **M4** (#6, #12): algebraize the finite-normal-cover rank-two group and
  its rank-one normal kernel; apply affine-action classification; prove
  affine-grid extraction and both directions of Q/Q'/J correctness.
- **M5** (#7): T1--T3 and the main descent direction are present.  Finish
  the four-way T4 wiring after M4 supplies the ACF correctness theorems.
- **M6–M8** (#8--#10): Frobenius classes and generic arithmetic, ratio
  field interpretation, base/point recovery, Frobenius kernel, public
  theorem variants, and the functorial quotient formulation.
- **Book**: the curves chapter covers P1--P7 through infinitesimal
  rigidity, and the configurations chapter follows the current M4a
  boundary.  Keep both synchronized.  Verso requires docstrings on every
  referenced declaration *and its structure fields*.

## Lean gotchas (hard-won; read before writing proofs)

- Bare `LinearMap.id - P.conjProj g` (or any operator-subtraction)
  *applied to an argument* gives "Function expected ?m" — type-ascribe
  `(… : F →ₗ[k] F)` at every application site.
- `set`-bound operators don't pattern-match in *freshly created*
  goals; unfold the *hypotheses* (`rw [hdef] at h`) rather than trying
  to fold the goal.
- Dot-notation on type-ascribed terms fails
  (`(x : Divisor k F).deg` looks up `Finsupp.deg`) — use qualified
  names.
- `rw [h] at hyp` where `h : D P = 0` splits `ord`-atoms containing
  `(D P).toNat` — omega understands `toNat` natively, so don't rewrite.
- `Finset.sum_eq_single` as a rewrite mis-infers the function from
  side-condition lambdas (defeq-not-syntactic) — state it as a typed
  `have` first.
- `congr 1` on `zpow`-exponent goals is unreliable (`a + -b` is defeq
  to `a - b` in ℤ, so congr may close everything and orphan the next
  tactic); use explicit exponent `have`s + `rw`.
- `← zpow_one x` rewrites `x` inside *other* zpow bases; use
  `zpow_add_one₀` directly.
- `linarith` fails over an unordered field — use
  `linear_combination`.
- `rw [map_zero]` rewrites *all* instances of the instantiated
  pattern at once; count remaining occurrences.
- Membership goals of the form `x ∈ ↑S` (set-coe of a submodule) need
  `change P.val.valuation x ≤ 1`-style, not `rw [mem_iff]`.
- `push Not` normalizes `¬(1 < v)` directly to `v ≤ 1`.
- `omega` handles `Int.toNat`, `min`/`max`; give it product-atoms via
  `have`-equations (`ord_mul` etc.) first.
- Coordinate goals under `Subtype.mk` need `change` before `rw
  [map_zero]` (motive failures otherwise).
- `Submodule.finiteDimensional_of_le`'s named argument is `S₂`.
- `Submodule.map_comap_subtype` yields `p ⊓ q` in that order.
- When python-rewriting file spans, anchor on unique full lines —
  substring anchors have silently eaten declarations before.
- `Submonoid.closure_induction` uses `| mem | one | mul` cases.
- `pow_succ'` (not `pow_succ`) for `C^{n+1} x = C (C^n x)`.
- Verso `{docstring X}` requires docstrings on structure fields too.

## Session mechanics for an agent

If running as a self-paced loop: each iteration (1) check
`gh issue list` / recent comments on adamtopaz/acl_geom for steering,
(2) do one small verifiable increment, (3) full `lake build`, commit,
push, (4) leave an unsigned progress comment on the active issue, (5)
keep the book building. CI runs on push (build + Pages deploy;
back-to-back pushes can race the Pages deployment — harmless, next
push redeploys).
