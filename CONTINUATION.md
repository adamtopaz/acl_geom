# Continuation guide

This document lets a fresh agent (or human) pick up the formalization
with no prior context. Read the **Current status** section first, then the
open GitHub issues, then start working.

## What this project is

A Lean 4 formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem. The mathematical source of truth is
`sources/blueprint.tex`. The library lives in `AclGeom/`, a Verso book
documenting it lives in `AclGeomBook/` (built with `lake exe book`).
Toolchain: see `lean-toolchain`. The upgrade to Lean/Mathlib v4.34.1 (Verso
v4.34.0) was committed and pushed as `8a54b54` (#20, closed). The complete
local build and rendered book pass; reproduction and measurements appear at
the end of this guide. Verso uses the compatible stable tag for the toolchain.

## Current status (2026-10-07; audit #19, performance #18 and carryovers #24)

Read the audit on #19 before starting new work. The accepted checkpoints
include the target repairs and refutations, generic arithmetic, transfer and
semantic consumers, and the foundational transport/existence/naturality
carryovers. Full-build/book and compiled-axiom evidence is recorded at the end
of this guide. The current mathematical boundaries are:

- **No `sorry`, `admit` or project `axiom` in the sources.** The latest CI run
  at the start of the audit was on `ee31244` (run 31712093484), cancelled after about six hours (job
  time 6h 0m 16s), and the latest
  successful run at that point was for the older `7f572e4`. Historical
  "CI green" reports are therefore not current evidence. The v4.34.1 upgrade `8a54b54` (#20) supplies fresh local
  full-build/book, hygiene and compiled-axiom evidence. Its full Lean Action CI
  run [37575646876](https://github.com/adamtopaz/acl_geom/actions/runs/37575646876)
  subsequently passed. The audit head `f6964f0` also passed the full build/book
  and deployment in run
  [37580135219](https://github.com/adamtopaz/acl_geom/actions/runs/37580135219),
  completed on 2026-10-07 at 07:16 UTC. The focused-module code checkpoint
  `31864cd` also passed full CI in run
  [37591789192](https://github.com/adamtopaz/acl_geom/actions/runs/37591789192),
  completed at 08:27 UTC. These are current CI evidence; the separate release
  workflow is not a full build.
  The later documentation-only head `842976b` also has a cancelled CI run
  (37533928699, completed 2026-10-07 03:27:14 UTC after 6h 0m 30s);
  deployment was skipped. It is not successful-build evidence.
  Build latency and memory are tracked in #18. The focused core/leaf and
  configuration-book refactor is recorded below; it preserves the audited
  mathematical targets. Paired project-clean measurements now pass, and the
  #18 acceptance evidence is recorded below.
- **The old M4 completeness target was false.** `AffineGridExtraction`
  required equality with the table witness in all 21 fields, but `Psi` sees
  the generators `A₁, A₂` (likewise `B`, `C`) only through their joins.
  Exchanging `A₁` and `A₂` preserves `Psi`, so the conditional
  `QGeom ↔ QSem` held only vacuously. Blueprint table (8.5) has the same
  imprecision. This checkpoint retains the literal-target refutation and
  corrects the interface to three joins and fifteen points (#22). The ACF
  unguarded extraction and Q completeness were subsequently refuted even over ACF pairs
  (#27); the corrected candidate requires I≠D and I≠P and remains open.
- **The M4a group-chunk chain (historical items 1–117 below) is frozen.** It
  did not converge toward a blueprint statement: no `Config/Chunk*` module is
  upstream of `AffineGrid`, `Correctness` or `Main`, and several headline
  "composition" theorems hold by construction (#19, finding A2). M4 is being
  re-planned against the corrected target (#12, #21, #22).
- **The arbitrary-field Q/Q′ consequences are false.** In the rank-five
  extension ℚ(s,t,e₁,e₂,e₃), geometric Q and Q′ can hold without K-valued
  semantic representatives. Both mathematical counterexamples were independently
  checked; both are now refuted in Lean over every characteristic-zero
  rational function field in five variables (#25), with explicit geometric
  witness reflection and a semantic square obstruction. The four-way J target is
  separate. The source withdraws the invalid projection consequence.
- **The Frobenius-class, generic-arithmetic and ratio sections need a correction.** `SumPoint` and `MulPoint` allow
  independent changes of representatives. The literal JAdd/JMul definitions
  are nonfunctional even over algebraically closed fields: they accept
  j(κx+y,a) and j(κxy,a) for κ ∈ k×, κ ≠ 1. This refutes the original
  generic-arithmetic equivalences (#23), rather than only exposing a proof gap.
  The FrobEq converse reuses one multiplier representative across three
  existential clauses without proving that choice. EH95's route supplies a
  partial-quadrangle coupling by specialization. Concurrence has an independently
  checked Lean proof in `Interpretation/FrobLinkIncidence` (five public
  declarations, standard axioms); an algebraic converse from this concurrence
  now yields exact parameter twists from supplied semantic endpoint witnesses,
  over arbitrary base fields. The two-link implication keeps semantic bridge
  completeness explicit; its canonical form uses perfect K, rank at least
  five and the still-open ACF JCompletenessACF input. The original
  common-representative calculation and unconditional bridge completeness
  remain obligations. The natural/integral FrobEq semantic equivalences and
  fixed-class description are proved under explicit perfection, rank-five and
  ACF J-completeness inputs, over any base field. The coordinate bijection
  is proved under the same explicit inputs. Corrected generic fixed-class
  arithmetic and corrected geometric ratio semantics are proved under these
  inputs. The corrected geometric ratio setoid/quotient and bijective nonzero
  decoding are proved under the same inputs. Adjoining zero yields the full
  carrier decoding equivalence. The corrected two-addition negation detour
  and corrected total nonzero addition are proved under the same inputs.
  Corrected total geometric graphs on the full ratio carrier are proved
  under the same inputs. The named transported field structure, actual decoding ring
  equivalence and geometric graph/operation characterizations are proved under the same
  inputs. Pure geometric Q/Q′/J configuration and J-locus/Frobenius-link/bridge
  transport, coupled meet/join arithmetic and corrected total/ratio transport are
  proved across arbitrary bases/universes, with no completeness or perfection input.
  Conditional class/carrier maps and graph transport are proved given the
  canonical image-base equality and explicit carrier inputs. The same geometric
  map is bundled as an actual RingEquiv and composed with both decodings.
  Canonical image-base existence and conditional field-isomorphism existence are
  also proved under explicit ACF completeness; general inducing reconstruction
  remains open (#23).
  The JAdd, JMul and full-class RatioEq refutations have an
  independently checked Lean proof in `Counterexamples/GenericArithmetic`;
  all 26 public declarations use standard axioms. They record the literal
  predicates for provenance and explicitly prove membership of every witness
  in the encoded class relation.
  EH95 Lemma 2.11 and Figures 4–5 use meets of joins of the given coordinates
  for subtraction/division, preserving the coupling lost in the blueprint's
  existential projections. `Interpretation/JArith` and `JArithSem` now prove
  the generic meet identities, Point-valued JSem bridge and derived generic
  negation/inverse/addition/multiplication over arbitrary relative fields.
  All 89 authored public declarations have standard-axiom checks. Inputs
  share a literal parameter and are independent. Geometric membership
  follows from rank-five soundness without an infinite-base binder.
  Generic fixed-class correctness and corrected ratio semantics are proved
  under explicit completeness, as is bijective nonzero quotient decoding.
  Corrected negation and nonzero addition detours and full-carrier geometric graphs
  are proved under the same inputs, with a named reducible field structure and
  actual decoding RingEquiv. Conditional carrier/graph transport is proved
  with the canonical image-base equality and carrier inputs explicit; its
  induced RingEquiv and composition with both decodings are proved.
  The canonical image base and conditional field-isomorphism endpoint are proved
  under explicit ACF completeness. Public original-field existence and the assembled lattice-form target are proved
  conditionally with both exact perfected completeness inputs explicit (#9/#10).
- **The base-ratio corollary prerequisite is complete (#5/#9, R1a/C7b).**
  `Reconstruct/Base` proves ratio algebraicity over arbitrary relative fields
  with no rank, fresh-witness, perfection, completeness or characteristic
  input. Adjoining a rational-function variable supplies freshness. The
  original ratio-in-base orientation is proved with explicit `IsRAC` for the
  base. Actual corrected conditional base recovery and Compatible assembly
  for `interpretedRingEquiv` are proved under explicit carrier/completeness
  and both RAC inputs. Corrected conditional scalar one and outside-point
  recovery for the same map are proved without RAC under its explicit
  carrier/completeness inputs. Actual inducing equality and compatible
  inducing existence for perfect fields are proved with RAC/completeness
  explicit. Original-field inducing existence through arbitrary chosen perfections
  is proved with original RAC and both perfected completeness inputs explicit.
  The public conditional target is assembled in Main. General unconditional R1/R2
  and full reconstruction remain open. The original
  source proof’s incorrect correspondence-pair ordering is reported on #5
  and preserved; the corrected formal proof uses `(u₁,u₂)` and `(b,b)`.
- **Lemma 8.4 (affine action) has no Lean statement.** #13's curve
  prerequisites are proved: places, divisors, Riemann–Roch, genus, rationality
  in genus 0, Tate residues, rigidity of regular derivations in genus ≥ 1, and
  Möbius normalization. #13's final step (P7, assembling Lemma 8.4) is absent,
  and so are the group-action model and the bridge from actions to the curve
  library (#21). No module outside `Curves`/`Tate` uses the curve library
  yet.

Coverage at a glance (details and file:line references on #19):

| Layer | Status |
|---|---|
| Foundations, perfection | Lattice, atoms, point geometry, finite representative calculus, all-characteristic perfection existence, compatible cross-base transport, point/lattice round trips, independence/rank/trdeg transport and chosen-perfection naturality proved. The explicit `Induces` relation, intersection formula, compatible induced-map converse and the Frobenius fibre/uniqueness for supplied inducing maps are proved (#24/#9). The public lattice-form target is assembled conditionally with both exact perfected completeness inputs explicit. Unconditional reconstruction and literal/quotient functors remain open (#8–#10) |
| Configurations | Soundness of Q, Q′, J proved over any base field with rank-five freshness. Partial quadrangles, all 24 Ψ clauses, multiplication diagrams and geometric Q/Q′/J transport across arbitrary closed-lattice order isomorphisms, bases and universes (#23/#8 I6b1). Semantic J assembly is proved; geometric J completeness reduces to explicit, still-open ACF Q/Q′ completeness inputs (#6/#22). Arbitrary-field Q/Q′ equivalence has concrete Lean refutations over characteristic-zero rational function fields in five variables (#25); general witness descent remains open |
| Hard kernel | `j_rigidity` and the two-pair correspondence theorems proved. The no-fresh relative base-ratio corollary and its actual base-membership form under explicit IsRAC are proved. The literal three-pair additive statement and group/action construction remain open; the corrected affine-grid coordinate interface is stated but extraction is open |
| Transfer | T1–T3 and full one-quantifier transfer proved. Algebraic-base lattice/point/rank and configuration lifts, point-level J (1)⇔(2), (4)⇒(3), and rank-five (1)⇒(4) are proved. J equivalence over perfect fields remains conditional on explicit ACF completeness; no infinite-base assumption remains on these arrows (#7) |
| Interpretation, reconstruction, functorial | Frobenius-link language, soundness helpers, incidence reduction, literal arithmetic/ratio refutations and coupled generic meet/join arithmetic are proved. The rank-five Frobenius kernel, characteristic-zero identity, exponent separation and two-generic intersection are proved, with a concrete rank-free refutation (#9). Conditional all-point/lattice propagation from explicit base recovery and outside-point agreement is proved. Fixed-class correctness, corrected ratio quotient/full decoding, total geometric operation graphs, named field structure and actual decoding RingEquiv are proved under explicit perfection/rank-five/ACF completeness. Geometric J-locus, directed Frobenius-link/bridge, coupled meet/join arithmetic and corrected total/ratio invariance need no such input. Conditional class/carrier maps and graph transport are proved with a supplied canonical image-base equality and explicit carrier inputs. The same geometric map gives the induced RingEquiv and its actual K-to-L composite under those inputs. Canonical image-base and conditional field-isomorphism existence are proved with both ACF-completeness hypotheses explicit; source pair and target rank are derived inline. Actual conditional base-range compatibility and inverse naturality are proved under explicit carrier/completeness and RAC inputs. Corrected conditional scalar one and outside-point recovery for the same map need no RAC. Actual compatible inducing equality and existence are proved in perfect fields under explicit RAC/completeness inputs, with no supplied pair or target rank. Original-field chosen-perfection inducing existence is proved with original RAC and both perfected completeness inputs explicit. The public target is assembled conditionally with both perfected completeness inputs explicit. Unconditional recovery and functorial theorems remain open |

Immediate priorities, in order:

1. complete the remaining geometric and transfer completeness obligations
   (#6/#7), with a full library build and rendered book; the measured #18
   build gate is satisfied by the focused-module checkpoint;
2. keep the corrected extraction and withdrawn Q/Q′ consequences explicit
   (#22/#25); the public conditional target now assembles original-field
   chosen-perfection existence, rank, base/intersection, Frobenius uniqueness
   and converse. Next bounded public variants are assessed after that checkpoint (#9/#10);
3. reassess the arbitrary-field Q/Q′ and §10 semantics using the proved #25
   refutations; retain the explicit-instance boundary and general descent obligation;
4. re-plan M4 (#12, #21), keeping the old M4a bookkeeping chain frozen;
5. continue recovery and the literal/quotient functorial definitions using the
   proved kernel, intersection, conditional point propagation and supplied-endpoint Induces fibre APIs;
   keep both perfected completeness hypotheses explicit for every public variant (#8–#10).

## How work is coordinated

- **All communication with Adam happens on GitHub issues** of
  `adamtopaz/acl_geom`, and only there. Nothing else on Adam's GitHub
  account may be changed. Check for new comments from Adam at the start of
  every work session and treat them as top priority. Questions for Adam use
  the `question-for-adam` label.
- Two agents work on the project: `aclgeom.claude` and `aclgeom.codex`.
  They coordinate through chit direct messages. File ownership is divided
  explicitly before editing. In the shared checkout only one Lake build
  family runs at a time, and builds stop if available memory drops below
  30 GiB.
- Issue map: #1 coordination; #2–#10 milestones M0–M8; #11 M3a regularity
  brick (open, off the critical path); #12 M4a design; #13 M4b curve
  library; #14–#16 historical M4a sub-steps; #18 build performance;
  #19 audit; #20 upgrade (closed, 8a54b54); #21 Lemma 8.4 action bridge; #22 extraction
  target repair; #23 representative alignment and refuted generic arithmetic
  in §10–12; #24 foundational carryovers from #3/#4; #25 false arbitrary-field
  Q/Q′ consequences; #26 source-paper request fulfilled (PDFs outside git).
- Issue comments are posted through Adam's `gh` account. Do not append
  signature lines. When it matters which agent did the work, say so in the
  body.
- Post a progress comment on the relevant issue after each substantive push.
- Blueprint statements that the Lean route bypasses (for example the
  three-pair additive correspondence or general `E ⊗ F` regularity) remain
  tracked obligations; do not close them merely because nothing uses them.

## Hard policies

`AGENTS.md` is authoritative. In particular:

- **Never leave `sorry` or `admit` on `main`**, including WIP files.
- **Never axiomatize blueprint theorems.** Every Lean declaration must be
  kernel checked; explicitly named unproved hypotheses remain obligations.
- Use focused `lake build <module>` checks during development; never trust
  `lake env lean` alone. Run a full `lake build` before every commit.
- Keep `lake exe book` building; grow the book alongside the code.
- Never `cd` into `.lake/packages/*` — lake builds whatever package
  the cwd is in.
- Commit and push at every natural checkpoint, in small verifiable
  increments, always green (Adam's standing instruction).

## State of the library (descriptive; see #19 for the audited coverage)

### Foundations (earlier milestones)
- M0 skeleton/CI done. M1–M2: the lattice, atoms, point geometry and
  perfection isomorphism are proved. The carryovers from closed #3/#4 are
  proved for compatible cross-base transport, point/lattice round trips,
  independence/rank/trdeg transport, all-characteristic perfection existence
  and chosen-perfection naturality. The explicit `Induces` relation,
  intersection formula and compatible induced-map converse are also proved
  (#24). Full reconstruction and functorial constructions remain open
  (#8–#10). The finite
  representative calculus (Lemma 4.2) is proved in `Geometry/Representatives`;
  it is used by the arithmetic refutations. M3: `j_rigidity` and the
  correspondence theorems are proved (two-pair additive form; the general
  `E ⊗ F` regularity of #11 is open). M4: soundness and semantic J assembly
  are proved; geometric completeness remains open (#6).
  The curve theory below is M4b (#13), built as the input to blueprint
  Lemma 8.4. The lemma itself and the bridge from group actions to the
  curve library are not formalized yet (#21).

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

## Historical log: M4a finite-cover field action (items 1–117; frozen)

The numbered historical items are preserved as a record. They are **not** the
current plan. The
2026-10-06 audit (#19) found that the chain was aimed at a false target (#22)
and was not converging. Several statements described below as
"strict composition" or "cancellation" hold by construction. Re-check any
item before relying on it.

The P6 prerequisites are proved in the library: regular-derivation
rigidity, infinitesimal automorphisms, genus-zero rationality,
rational-function-field automorphisms, and Möbius normalization. P7, the
assembly of Lemma 8.4 from them, has not been done. Only the abstract
`kˣ ⋉ k` bookkeeping of the affine-action endgame exists (#21).

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
11. `Correspondence/PrincipalLocalization.lean` clears the finitely many
    denominators of an injective map from a finitely generated algebra to a
    fraction field.  Their nonzero product gives one explicit dense principal
    open `D(d)` and a dominant partial map from it.  The wrapper in
    `Correspondence/FiniteExtensionTransition.lean` applies this construction
    contravariantly to any field equivalence between two finite-extension
    charts.  `Config/ChunkAlgebraicTransition.lean` upgrades the normalized
    scalar-cover equivalence to a ground-field equivalence and instantiates
    the construction at all four repeated blocks `s`, `u`, `sA`, and `uB` of
    a lifted Ψ four-arrow diagram.  Thus every branch comparison used by the
    chunk now has a concrete dominant principal-open representative.
12. `Correspondence/FunctionFieldEquivalence.lean` proves the generic-point
    composition law for dominant partial and rational maps, recovers the
    induced field homomorphism, and proves that a function-field equivalence
    and its inverse give mutually inverse dominant rational maps.  Every
    finite-extension chart now carries its canonical ground-field function
    field, identified with the selected ambient cover field.
    `Correspondence/FiniteExtensionTransition.lean` conjugates an ambient
    equivalence through those identifications, spreads the resulting map over
    `Spec k`, proves both rational composites are identities, and extracts an
    explicit isomorphism between dense open chart subschemes via
    `BirationalGluing`.  `Config/ChunkAlgebraicTransition.lean` instantiates
    this dense-open isomorphism on all four normalized `s`, `u`, `sA`, and
    `uB` branch comparisons, alongside their principal-open representatives.
13. The generic-point lift through a principal open is now identified with
    the canonical localization map into the source function field.
    Consequently, the denominator-cleared finite-extension partial map is
    proved to induce exactly the conjugated ambient field equivalence, and
    its rational-map class is the canonical rational transition used by the
    dense-open isomorphism extractor.  Thus the explicit principal-open and
    function-field descriptions of every normalized transition agree.
14. Reference-normalized scalar-cover equivalences are now defined by going
    through one fixed branch.  They satisfy identity, symmetry, and strict
    transitive cocycle laws.  Conjugated finite-extension chart rational maps
    preserve transitive composition, so the normalized dense rational
    transitions inherit the strict cocycle.  Independently,
    `BirationalGluing.partialIsoGlueData` packages any dense-open partial
    isomorphism as an actual two-chart `Scheme.GlueData`; all four repeated
    blocks `s`, `u`, `sA`, and `uB` expose such normalized gluing data.
15. `WeilGluing.commonOverlapGlueData` packages an arbitrary family of open
    immersions from one fixed overlap as full scheme gluing data with literal
    identity triple cocycles.  `BirationalGluing.partialIsoFamilyGlueData`
    applies this to a finite family of partial isomorphisms from one reference
    chart: their finitely many dense source opens are intersected once, every
    partial isomorphism is restricted to that common dense source, and all
    target charts are glued simultaneously.  The reference-normalized scalar
    transitions instantiate this as `rankTwoScalarReferenceAtlasGlueData` for
    an arbitrary finite branch family on one rank-two locus, with
    `rankTwoScalarReferenceAtlas` the resulting actual scheme.  The extracted
    dense-open transitions are now proved to commute with their chart
    structure maps to `Spec k`; those maps descend to
    `rankTwoScalarReferenceAtlasToSpec`.  The full atlas is integral (for a
    nonempty branch family), locally of finite type, and quasi-compact, so the
    finite-type and irreducibility parts of the Weil construction are now
    discharged.  Separatedness remains tied to the group law rather than to
    the common-open gluing alone.
16. `GroupScheme.diagonal_isPullback_unit` identifies the diagonal of any
    group scheme over `k` as the pullback of its closed unit section along the
    difference morphism.  Hence every group scheme over the field is
    separated, and `AlgebraicGroup.ofGroupScheme` packages a locally
    finite-type, quasi-compact group scheme without a separate separatedness
    proof.  The existing finite reference-normalized scalar atlas should now
    be understood precisely as the branch-normalization input to Weil's
    theorem, not as the translation-indexed group atlas itself.
17. Equality of full rank-two/scalar graph loci now restricts to equality of
    their rank-two parameter loci.  The induced equivalences of the two base
    function fields and scalar extensions lift semilinearly to the normal
    covers, even when the displayed generic rank-two tuples are different.
    Normalizing these equivalences through one selected realization gives
    strict identity, inverse, and transitive laws, dominant rational chart
    comparisons, and dense-open isomorphisms over `Spec k`.  For the actual
    Ψ cancellation family, `psiBProjectionReferenceRationalMap` specializes
    this construction to arbitrary generic realizations of the `B/T` graph,
    all represented by one fixed positive-dimensional affine normal-cover
    model.  This is the model-comparison prerequisite for spreading the
    four-arrow difference product; it does not yet construct that product.
18. `Correspondence/CurveEquation.lean` removes the remaining scalar
    ambiguity from an irreducible finite-correspondence germ.  Its prime
    planar ideal now has a canonical lexicographically monic generator,
    proved to depend only on the ideal.  The coefficients generate an
    intrinsic intermediate field contained in every chosen field of
    definition, and the canonical equation descends nontrivially to that
    field while still vanishing on the selected generic endpoint pair.  This
    supplies faithful, scaling-independent coordinates for the next
    multiplication-graph normalization; arbitrary unnormalized generators
    cannot be used because rescaling them would change their coefficient
    fields.
19. The descended canonical equation now proves that the target is
    algebraic over the intrinsic coefficient field and the source.
    `RankEq.eq_of_le_of_not_le_point` supplies the corresponding rank-two
    lattice principle: a closed subfield of a rank-two flat which is not
    contained in any point is the whole flat.  Applying the Ψ minimality
    clauses in `Config/ChunkGermCoordinates.lean` shows that the canonical
    coefficient closures of the inverse-oriented `A` germ, the `B` germ,
    and the output `C` germ are exactly `A`, `B`, and `C`.  Thus the germ
    coefficients are faithful rank-two coordinates up to finite algebraic
    extension, rather than merely fields contained in the displayed
    parameter fields.
20. `finiteDimensional_extendScalars_adjoin_of_close_eq` turns equality of
    relative closures into the required finiteness statement for any
    finitely displayed parameter tuple.  Consequently the selected displayed
    `A`, `B`, and `C` parameter fields are finite over their intrinsic germ
    coefficient fields.  The compositum of the inverse-`A` and forward-`B`
    coefficient fields has relative closure exactly `A ⊔ B`; the entire
    displayed `A,B,C` multiplication component is finite over this intrinsic
    independent-input field.  `germMultiplicationNormalCover` is its one
    common normal closure in the ambient algebraically closed field, proved
    finite and normal over the intrinsic two-input base.
21. The canonical coefficient set is now proved finite, and its tautological
    lifts generate the whole intrinsic coefficient field.  The inverse-`A`
    and forward-`B` families combine to a finite coordinate family for their
    intrinsic compositum.  `FiniteExtensionProjection` spreads any embedding
    of finite-extension function fields to an explicit dominant
    principal-open rational map.  Applying it in
    `Config/ChunkGermChart.lean` produces honest integral affine charts for
    the selected intrinsic `A`, `B`, and `C` germs and for the common normal
    multiplication graph, together with dominant rational projections from
    that graph to all three parameter charts.
22. `Correspondence/FourArrowNormalization.lean` normalizes the complete
    four-arrow difference component over its actual eight free coordinates.
    The four multiplication/division edges prove successively that the
    selected blocks `u`, `sA`, `uB`, and `c` are algebraic over the input
    tuple `(s,e,a,b)`.  Hence the sixteen-coordinate total field is finite
    over the eight-coordinate input field and lies in one finite normal
    cover.  `FourArrowDifferenceDiagram.algebraicChart` realizes that cover
    as an integral affine chart, with dominant rational projections to the
    displayed `e`, inverse-`a`, `b`, and output-`c` rank-two block charts.
    This is the normalized relational difference-product component; it does
    not assert single-valuedness after forgetting the auxiliary `s` block.
23. The chosen sixteen-coordinate prime component now spreads over every
    independent eight-coordinate input tuple.  `exists_relocation` relocates
    all sixteen coordinates at once while fixing `(s,e,a,b)` literally; the
    four six-coordinate restrictions remain realizations of the original
    multiplication locus, and the full prime ideal is preserved.  Equal
    complete loci canonically identify their input fields and total fields,
    these equivalences commute as a finite-extension square, and they lift
    semilinearly to the concrete normal covers.  After upgrading to
    ground-field algebra equivalences, the affine charts have dominant
    rational comparisons and dense-open isomorphisms.  Normalizing all such
    comparisons through one reference component gives literal identity,
    inverse, and transitive laws on the cover equivalences and a strict
    transitive cocycle on the rational chart comparisons.  Thus the selected
    branch is now a genuine generically spread component, not one isolated
    tuple.
24. `Config/ChunkFourArrowNormalization.lean` retains the complete scalar
    information on that component.  Its twenty-eight-coordinate tuple is
    the sixteen ambient coordinates followed by the three independently
    selected scalar branches on each of the four edges.  Restriction to each
    nine-coordinate edge is literally the selected complete joint
    rank-two/scalar projection locus.  All twelve scalar coordinates are
    algebraic over their displayed rank-two blocks, hence all twenty-eight
    coordinates are algebraic over the same eight independent ambient
    inputs.  Their field is finite over that input field and lies in one
    finite normal cover with an integral affine chart.  The four displayed
    `e`, inverse-`a`, `b`, and output-`c` `B/T` branch fields embed in this
    cover, producing dominant rational projections to their raw finite
    scalar-branch charts.  The targets are intentionally not yet their
    individual normal closures, so this step records all finite branch data
    without claiming a comparison with the selected reference model.
25. `Correspondence/FiniteExtensionCompositum.lean` gives the required
    finite-basis base-change lemma: if `F ≤ E` and `N/F` is finite, adjoining
    the values of a finite `F`-basis of `N` to `E` contains all of `N` and is
    finite over `E`.  `Config/ChunkFourArrowReference.lean` iterates this
    construction for the `e`, inverse-`a`, `b`, and output-`c` `B/T` normal
    fields.  The resulting common field is still finite over the original
    eight inputs and literally contains every individual normal field.  One
    final normal closure gives an integral affine source chart with dominant
    rational projections `toNormalizedE/A/B/C`.  Composing each with
    `psiBProjectionReferenceRationalMap` yields four dominant maps
    `toReferenceE/A/B/C` to the exact same selected `(B,T)` affine normal
    model.  Thus the reference-model comparison requested after item 24 is
    now concrete; equality of the output map with the categorical
    difference product of the three input maps remains to be proved.
26. `Correspondence/FunctionFieldEquivalence.lean` now treats arbitrary
    embeddings, not only equivalences: it constructs their generic-point
    morphisms, recovers the embedding from any dominant representative, and
    proves that successive rational maps induce the literal contravariant
    composite.  `Correspondence/FiniteExtensionProjection.lean` identifies
    the denominator-cleared projection with the embedding obtained by
    conjugating its ambient field inclusion through the two canonical chart
    function-field identifications.  The scalar-chart reference transition
    exposes its exact function-field equivalence as well.  Consequently
    `ChunkFourArrowReference.lean` gives exact generic-point formulas for
    `toNormalizedE/A/B/C` and, after reference transport, for all four
    `toReferenceE/A/B/C`: each is attached to a displayed composite field
    embedding from the selected `(B,T)` function field into the common
    eight-input cover field.  The remaining comparison with the presented
    family is therefore an equality of explicit field maps, rather than an
    implicit appeal to dominance or birational equivalence.
27. The normalized intrinsic multiplication graph now carries the same
    exact generic-point data as the four-arrow reference chart.  The three
    projections in `Config/ChunkGermChart.lean` expose explicit
    contravariant function-field embeddings for inverse-`A`, input-`B`, and
    output-`C`; conjugating each through the canonical chart identifications
    recovers the literal inclusion of its displayed parameter field into the
    common normal multiplication field.  Each dominant rational projection
    is proved to induce exactly that embedding.  Thus a future descent from
    the eight-input four-arrow source to this intrinsic two-input graph can
    be stated and checked entirely as equality of concrete field maps.
28. `Correspondence/FieldEquivDiagram.lean` supplies the faithful semantic
    target that the formal presented family lacked.  Field equivalences can
    be conjugated to fixed reference charts while preserving composition,
    inverse, and equality, and a four-arrow diagram of four literal
    composition triangles satisfies the exact map identity
    `c = a ≫ e⁻¹ ≫ b`.  `Config/ChunkFiniteFieldAction.lean` now exposes the
    selected `A` and `B` restrictions separately, proves that they compose
    to the strict `AB` restriction, and corrects the independently selected
    `C` restriction by the inverse vertical deck defect.  The result is a
    literal finite-normal-cover composition triangle suitable for assembly
    into that semantic four-arrow diagram; no equality in the formal
    presented quotient is used as equality of field maps.
29. `Config/ChunkCurveRelocation.lean` lifts an arbitrary realization
    `(a,b,c)` of the rank-two Ψ multiplication locus to the actual curve
    coordinates on which its correspondence branches act.  Given one
    source generic over the six parameters, it relocates the complete
    nine-coordinate `(a,b,c,x,y,z)` selected prime locus while fixing
    `(a,b,c,x)` literally.  Restricting this single relocated component
    recovers exactly the selected `A` family locus on `(a,x,y)`, the `B`
    family locus on `(b,y,z)`, and the `C` family locus on `(c,x,z)`.
    Thus each parameter edge now has a coherent curve-coordinate
    composition triangle rather than three independently chosen family
    members.
30. `Correspondence/Family.lean` now rebuilds a generic family member of
    arbitrary parameter dimension from equality of its complete tuple
    ideal and independence of its parameter/source prefix.  Applying this
    to item 29 packages the relocated `A`, `B`, and `C` restrictions as
    genuine rank-two family members and as finite-correspondence pairs over
    the common field generated by all six parameters.  The reusable module
    `Correspondence/FiniteCompositionTriangle.lean` puts any two pairs with
    a literal shared middle on one common finite normal source/middle/target
    cover, restricts the vertical deck defect, and produces a strict
    equality `A ≫ B = C`.  Consequently every relocated Ψ parameter edge
    now carries its own literal finite-cover composition triangle.
31. `Config/ChunkCurveFourArrow.lean` instantiates item 30 on all four
    edges `s·e=u`, `sA·a=u`, `s·b=uB`, and `sA·c=uB` of an ambient
    rank-two difference diagram.  From independence of the original eight
    input coordinates it proves independence of the three successive
    tuples obtained by finite parameter replacement.  An unused ambient
    coordinate is therefore generic over each six-parameter edge, giving
    a package of four curve-coordinate realizations and four literal
    finite-normal-cover composition identities.
32. `Correspondence/FieldEquivDiagram.lean` now packages one strict
    `CompositionTriangle` and a `FourTriangleReference`: twelve explicit
    equivalences from four independently typed triangles to three reference
    fields, together with the four compatibility equations for repeated
    `s`, `sA`, `u`, and `uB` arrows.  Its constructor produces a literal
    `FieldEquiv.FourArrowDiagram`.  The Ψ-specific `ReferenceAlignment` in
    `Config/ChunkCurveFourArrow.lean` specializes this interface to the four
    finite-cover triangles from item 31 and exposes faithful right-arrow
    cancellation.  Thus the remaining obligation is exactly to construct
    the coefficient-compatible reference equivalences; arbitrary abstract
    field isomorphisms are insufficient.
33. `Config/ChunkCurveCommonSource.lean` removes the first obstruction to
    those coefficient-compatible equivalences.  It embeds the original
    ambient field `K` into the algebraic closure of `K(X)` and proves that
    the image of the formal variable is transcendental over all of `K`,
    hence generic over every embedded finite parameter tuple.  Ambient
    invariance transports the selected nine-coordinate Ψ locus and its
    algebraicity data along the embedding.  The tuple-relocation theorem can
    therefore be applied to all four parameter edges while fixing the same
    formal source literally.  The resulting four complete curve triangles
    now have a common source over the full eight-input coefficient field;
    their middle and target normal covers still have to be normalized over
    that common base.
34. `FiniteCorrespondenceFamilyMember.map` transports a generic family
    member along an ambient embedding, and `ofTupleIdealEqOnly` now recovers
    the independent parameter/source prefix directly from equality of the
    complete family locus.  The embedded restrictions from item 33 are
    therefore genuine generic members of the mapped selected A/B/C
    families.  `CommonBaseData` then rebases each branch to the field
    generated by the mapped eight-input tuple: the selected auxiliary
    parameter blocks need only be algebraic over this field.  Genericity of
    each B-source middle coordinate follows from its interalgebraicity with
    the one formal source.  Consequently all four faces now have strict
    deck-corrected finite-normal-cover composition triangles over the same
    coefficient field and with the same literal source coordinate.
35. `FiniteCoverTriangle.OnSourceCover` proves that the strict
    deck-corrected composition construction works on any caller-supplied
    finite normal source cover, not only the branch-generated cover chosen
    internally by one face.  The four facewise source covers are therefore
    joined by `FiniteNormalCover.sup` into
    `PsiCurveFourArrowCommonSourceRealizations.commonFiniteSourceCover`.
    Each original source normalization is proved to lie in this finite
    normal compositum, and all four faces are transported through it to
    literal strict composition triangles with exactly the same source
    field.  The remaining alignment problem is now confined to the four
    transported middle and target fields.
36. `Correspondence/FamilyCover.lean` packages the complete field of a
    generic family member as a finite extension of its independent
    parameter/source field.  Equality of complete family loci gives an
    `ExtensionEquiv` that sends every displayed coordinate to its matching
    coordinate, a semilinear equivalence of the concrete normal closures,
    and a deck-corrected `FiniteCoverBasedBranchEquiv` which preserves the
    literal selected branch.  The four repeated labels `s`, `sA`, `u`, and
    `uB` in the fresh-source diagram have equal complete family loci, so
    they now carry four such coefficient-aware based comparisons.  These
    comparisons currently live over their rank-two-parameter/source fields;
    they still have to be extended across the other six independent inputs
    to the common coefficient field of item 35.
37. Complete family-locus equality now also descends to equality of the
    endpoint-pair ideals over the field generated by the common literal
    parameter tuple.  The proof constructs the complete-locus function-field
    equivalence, proves generator by generator that it fixes the parameter
    field, and transports every two-variable polynomial evaluation.  Applied
    to the fresh-source four-arrow diagram, the two occurrences of each of
    `s`, `sA`, `u`, and `uB` therefore define the same selected curve relation
    over their exact rank-two parameter field.  This is the coefficient-
    faithful scalar-extension input: the remaining task is to preserve these
    four equal pair ideals while adjoining the other six independent input
    coordinates and then pass their selected normal branches to the common
    coefficient field of item 35.
38. Independent scalar extension is now proved without an irreducibility
    shortcut.  A base-field equivalence extends canonically after adjoining
    matching algebraically independent tuples, fixing every new generator.
    Consequently equal endpoint-pair ideals remain equal after adjoining an
    auxiliary tuple independent over both complete endpoint fields.  A
    separate tower lemma shows that six coordinates jointly independent from
    the parameter/source prefix stay independent after adjoining the
    algebraic family target.  The alternative independent presentations
    `(s,e,a,b)`, `(s,sA,a,b)`, `(s,u,a,b)`, and `(s,sA,a,uB)` supply the four
    required six-coordinate complements, so all four repeated curve ideals
    are now equal over full transcendence-degree-eight input fields.  For the
    repeated `s` block this field is literally the common input field from
    item 35, yielding the first exact common-base repeated-arrow equality.
    The other three full input fields have the same relative algebraic
    closure as the original input field but are not definitionally equal;
    their finite algebraic coefficient changes must still be normalized
    before transporting the selected branches to the common covers.
39. Equality of a selected two-variable curve ideal now canonically
    identifies the finite extension from the source-coordinate field to the
    complete branch field.  The comparison lifts semilinearly to the
    concrete normal closures and a deck correction makes it preserve the
    literal selected branch.  The exact common-input `s` relation from item
    38 instantiates this construction on the actual common-base
    finite-correspondence pairs, producing the first faithful selected-normal-
    cover anchor for the reference alignment.  This is stronger than an
    arbitrary equivalence between transported middle fields: it remembers
    which normal subcover and selected branch encode the repeated curve.
40. The remaining finite algebraic coefficient changes are now packaged in
    one field obtained by adjoining the actual `sA`, `u`, and `uB` blocks to
    the common eight inputs.  This extension is finite; its normal closure
    is finite and normal over the common input field and contains each of
    the three named alternative full input fields.  A generic family member
    plus an auxiliary tuple jointly independent from its parameter/source
    prefix now becomes a finite-correspondence pair over the enlarged
    coefficient field.  Applying this to both occurrences of `sA`, `u`, and
    `uB` turns their alternative-field ideal equalities into three genuine
    `FiniteCoverBasedBranchEquiv`s, each proved to preserve the literal
    selected branch.  The remaining bridge is to transport these three
    based comparisons through their embeddings into the common coefficient
    normal field and then into the simultaneous common source cover.
41. The common coefficient comparison field is now proved finite over all
    three alternative eight-input fields, not merely over the original
    common input field.  A reusable ambient-invariance lemma shows that
    equality of relative algebraic closures survives an embedding into a
    larger ambient field.  The diagram's successive interalgebraic block
    replacements therefore identify the closures of the original input
    tuple with `(s,sA,a,b)`, `(s,u,a,b)`, and `(s,sA,a,uB)` after embedding.
    Every common or replacement coefficient is algebraic over each named
    alternative field, so the explicit coefficient enlargement is finite
    over each; finiteness then ascends to its common normal closure by the
    finite-extension tower law.  Thus the next transport may take finite
    pairwise normal closures after adjoining the formal source and the
    simultaneous source cover.  No unsupported assertion that curve ideals
    remain prime after algebraic base change is used.
42. `FiniteCoefficientBranchCompositum` now performs the next pairwise
    normalization without tensoring curve ideals.  Given a finite coefficient
    extension and two finite correspondences with the same literal source,
    it successively adjoins the coefficient field, the first selected branch,
    and the second selected branch.  Each step is finite over the preceding
    field, so the joint field is finite over the source-coordinate field;
    its ambient normal closure is finite and normal and contains the
    coefficient extension and both selected branches literally.  The `sA`,
    `u`, and `uB` alternative pairs now instantiate this construction using
    the common coefficient normalization from items 40--41.  Thus each
    comparison has a concrete pairwise normal source field on which its
    branch equivalence can be extended.
43. Equality of the selected pair ideals with a literally common source now
    gives an equivalence of the two branch fields over that source, with an
    explicit theorem carrying the first displayed target to the second.
    Composing this equivalence with inclusion of the second branch into the
    pairwise normal field gives an embedding of the first branch; normality
    extends it to an automorphism of the whole joint field.  The extension is
    proved to restrict to the prescribed branch equivalence and hence to
    carry the first literal target to the second.  The `sA`, `u`, and `uB`
    comparisons now each expose such an automorphism.
44. The pairwise fields are now rebased honestly to the literal common
    coefficient/source field.  The alternative and common coefficient bases
    are not treated as nested: a finite-basis compositum first proves the
    pairwise normal field finite over the common field with the same formal
    source adjoined, and a second ambient normal closure handles the possible
    loss of normality between incomparable bases.  Its canonical model lives
    in the exact algebraic closure used by the four strict triangles, and
    both literal target branches embed in it.  The three canonical rebased
    covers are joined to the earlier simultaneous four-face source cover as
    `branchComparisonSourceCover`; all four composition triangles have been
    rebuilt with literal strict composition on this enlarged source.  The
    remaining local step is to compare the two induced transported
    middle/target embeddings inside that cover and use the canonical curve
    coefficients to prove coefficient-compatible equality, rather than only
    existence of the two branch embeddings.
45. Canonical normal closures now retain a distinguished branch: the
    literal ambient extension is first included in its concrete normal
    closure and then transported through the chosen concrete-to-canonical
    equivalence.  Returning along that equivalence recovers the literal
    inclusion.  The composition source cover now exposes its left,
    pulled-right, and direct canonical subcovers, and any larger source cover
    containing it inherits distinguished left and direct branch embeddings.
    For each of the four Ψ faces, both selected embeddings have been placed
    in `branchComparisonSourceCover`.  Thus the next comparison can refer to
    the actual selected `s`, `sA`, `u`, and `uB` branches of the four strict
    triangles, rather than merely to abstract isomorphic normal fields.  The
    generic ideal-induced generator theorems were also made explicit enough
    for clean dependency rebuilds, and the finite coefficient compositum now
    imports and instantiates its normal-cover prerequisites directly.
46. Branch-domain equivalences can now reparametrize a selected embedding,
    after which a distinguished deck automorphism aligns it with any other
    embedding in the same normal cover.  The construction anchors the
    temporary algebra structure at the first embedding, so it does not
    silently use an unrelated inclusion of the branch field.  The exact
    common-base repeated `s` ideal identifies its two literal branch fields;
    the induced automorphism of `branchComparisonSourceCover` fixes the full
    common coefficient/source field, carries the first selected `s` branch
    to the reparametrized second branch, and sends the first displayed middle
    coordinate to the second.  A rebased comparison branch can also be
    inherited by any larger canonical normal cover.  Thus the `s` coherence
    is now coefficient-faithful; the same domain comparison over the literal
    common base remains to be proved for `sA`, `u`, and `uB`.
47. The repeated `sA` coefficient comparison is now transported through an
    explicit semilinear rebase instead of an equality cast.  The raw rebased
    source presentation is identified with the literal common source, that
    equivalence is extended to the two algebraic closures, and both raw
    selected branches are identified carrier-faithfully with the literal
    branch fields of the `sA·a=u` and `sA·c=uB` common-base faces.  Transport
    by the same source/closure equivalence puts both branch embeddings in the
    named rebased cover and then in `branchComparisonSourceCover`.  The face
    source fields reduce to the same literal common-base type, so two chosen
    deck transformations now carry the actual selected `sA` face embeddings
    to these coefficient-comparison copies, with exact `smul` equations.
    Thus the closure choices for both occurrences of `sA` are aligned while
    retaining the algebraic coefficient transport.  The analogous explicit
    transports for the repeated direct `u` and `uB` branches remain next.
48. The repeated direct `u` comparison now has the same explicit semilinear
    transport and selected-branch alignment.  The strict composite pairs of
    the `s·e=u` and `sA·a=u` faces name the two literal direct branches.  A
    reusable carrier lemma shows that adjoining an equal ambient generator
    to equal intermediate-field carriers produces the same field carrier;
    this identifies both raw comparison branches with those strict direct
    branch fields.  The raw common-source equivalence and its algebraic-
    closure lift transport both embeddings into the named rebased cover and
    then into `branchComparisonSourceCover`.  Two chosen deck transformations
    carry the actual selected direct face embeddings to the transported
    comparison copies, with exact `smul` equations.  Thus `s`, `sA`, and `u`
    are now coefficient-faithfully aligned in the common source cover; only
    the symmetric direct `uB` transport remains before constructing the
    coefficient-compatible reference charts.
49. The symmetric direct `uB` transport and alignment are now complete.  The
    strict composite pairs of the `s·b=uB` and `sA·c=uB` faces identify the
    literal direct branch domains.  Their raw comparison branches are
    carried through the explicit common-source equivalence and its
    algebraic-closure lift, included in `branchComparisonSourceCover`, and
    aligned with the two actual selected face embeddings by distinguished
    deck transformations.  Both exact `smul` equations are proved over the
    full common coefficient/source field.  Consequently all four repeated
    labels `s`, `sA`, `u`, and `uB` now have coefficient-faithful selected-
    branch comparisons in one finite normal source cover.  The next step is
    to transport these four equations through the strict face triangles,
    choose coefficient-compatible middle and target reference charts, and
    instantiate the Ψ-specific `ReferenceAlignment`.
50. The alternative-base comparisons are now exposed with their correct
    semilinear source data.  Their branch automorphisms are linear over the
    alternative `sA`, `u`, and `uB` source-coordinate fields, but need not
    fix every coefficient of the literal eight-input common source field.
    The literal common source is therefore included in each pairwise normal
    field as a ground-field algebra, its image under the corresponding
    restricted automorphism is retained as an actual intermediate field,
    and an explicit algebra equivalence identifies the original source with
    that image.  A reusable scalar-fixity lemma proves that all three image
    equivalences fix the common formal curve generator while faithfully
    recording the potentially moved coefficient presentation.  Thus the
    next middle/target charts can be induced from genuine semilinear source
    charts; no false common-base deck-transformation assertion is needed.
51. The semilinear source charts have now been lifted to the chosen
    algebraic closures and restricted to the full enlarged common finite
    source cover.  Their restriction squares are explicit pointwise, and
    the formal curve generator is still carried by the corresponding
    source-image algebra map.  For branch faithfulness, each moved source
    field is also mapped back into the original common curve ambient.  It
    and the original source then form two bases of the same pairwise normal
    total field, and the actual alternative-base branch automorphism gives
    an equivalence of those nested extensions.  Lifting this complete
    extension equivalence to canonical normal closures retains both the
    source movement and the total-field automorphism; it does not replace
    the latter by an unrelated lift of the source equivalence.  The next
    local step is the target deck correction which makes this semilinear
    normal-closure equivalence preserve the literal selected total branch,
    followed by its inclusion in the simultaneous source cover.
52. The branch-faithful semilinear normal-cover comparisons are now
    complete for `sA`, `u`, and `uB`.  Finiteness of the pairwise total
    field over the literal common source is proved explicitly and
    transported across each moved-base extension square.  The resulting
    canonical normal-closure equivalence is returned to the concrete
    normal closures, then corrected by a target deck transformation.  This
    correction is packaged by the existing based finite-cover interface and
    proves that the literal selected embedding of the entire pairwise total
    field is carried to the literal selected embedding over the moved
    source image.  Thus both the coefficient movement and the actual branch
    automorphism survive normalization.  The next step is to compare these
    corrected concrete normal covers with the already embedded canonical
    rebased comparison covers, include the corrected charts in
    `branchComparisonSourceCover`, and induce the middle/target charts.
53. The source-chart layer has also been re-elaborated from source rather
    than accepted from replayed build hashes.  This exposed and repaired
    three presentation-level defects in items 50--52: inferred automorphism
    types did not retain the named normal-field algebra structures,
    dependent rewriting through `extendScalars` was unstable, and the
    finite-cover generator statements asked typeclass search to reconstruct
    an ambiguous scalar presentation.  The branch automorphisms now have
    explicit named-field types, equality-based finite-dimensional transport
    is packaged by `FiniteCover.finiteDimensional_of_eq`, and the generator
    equations use their literal algebraic-closure representatives.  A
    direct compilation of `ChunkCurveCommonSource.lean`, the full build,
    and the book generator all pass.  Keep direct compilation of a changed
    leaf module in the validation loop whenever only `.olean.hash` artifacts
    are initially present.  The mathematical next step remains the
    corrected concrete-to-canonical cover comparison from item 52.
54. The corrected concrete normal-cover comparisons now meet the canonical
    comparison covers already present in `branchComparisonSourceCover`.
    For each of `sA`, direct `u`, and direct `uB`, equality of the literal
    common source with the raw rebased source is packaged together with
    equality of the named pairwise total field as an extension
    equivalence.  Its canonical normal lift is composed with the same
    raw-to-common algebraic-closure transport used to define the rebased
    cover.  The result is an explicit ring equivalence from the canonical
    normal closure of the literal-common-source pairwise extension to the
    named rebased canonical cover already embedded in the simultaneous
    compositum.  The next local step is to record the base-compatibility of
    these three bridges, transport the selected whole-total-field branches
    through them, and include those embeddings into
    `branchComparisonSourceCover`.
55. The three concrete-to-canonical bridges are now algebra equivalences
    over the literal common source.  Equality-induced extension
    equivalences expose their canonical base map, and a reusable mapped
    normal-lift API proves that composing this base map with the chosen
    raw-to-common algebraic-closure transport is the identity.  This upgrades
    the `sA`, direct-`u`, and direct-`uB` canonical-cover ring equivalences to
    common-base algebra equivalences.  Each upgrade carries the canonical
    selected embedding of the entire pairwise total field into the named
    rebased cover and then, through the established containment, into
    `branchComparisonSourceCover`.  A generic algebra-map equation records
    that these whole-total-field embeddings fix the common source exactly.
    The next local step is to use these three coefficient-faithful total-field
    embeddings with the semilinear source-image charts and the four existing
    face-to-copy alignment equations to induce compatible middle and target
    reference charts.
56. The coefficient-faithful whole-total-field embeddings now supply
    coherent anchors for all six alternative selected face branches.  A
    carrier-transport lemma moves containments across two changes of scalar
    presentation, and the rebased first and second branches are proved to
    lie already in their original pairwise normal total field.  Restricting
    each of the three whole-total-field embeddings therefore places both
    occurrences of `sA`, both direct occurrences of `u`, and both direct
    occurrences of `uB` in `branchComparisonSourceCover` through one shared
    embedding for each repeated label.  Six chosen common-source deck
    transformations carry the actual selected face branches to these
    coherent anchors, with exact whole-branch `smul` equations.  Separately,
    a strict composition triangle now exposes the canonical middle and
    target charts induced by any source chart, and four source charts package
    into a literal four-triangle reference.  The next local step is to choose
    the four source charts so that the two anchor corrections attached to
    each face are jointly compatible; their induced middle and target charts
    can then be proved coefficient-faithful and fed to four-arrow
    cancellation.
57. The four coefficient/source charts are now chosen and the enlarged
    strict triangles have been assembled into an actual semantic
    four-triangle reference.  On the two `u` faces the source charts are the
    two coherent direct-`u` anchor corrections; on the two `uB` faces they
    are the corresponding direct-`uB` corrections.  All four are algebra
    automorphisms over the literal common coefficient/source field, so they
    fix every canonical curve coefficient even when they move a selected
    left branch to another conjugate.  The induced middle-chart restriction
    formula is proved on the entire selected `s` or `sA` branch, and the
    induced target chart is proved pointwise to recover the appropriate
    shared whole-total-field `u` or `uB` anchor.  These charts instantiate
    `FourTriangleReference.ofSourceCharts`, produce a literal semantic
    four-arrow diagram, and satisfy exact right-arrow cancellation.  The
    next local step is to apply canonical-curve-equation faithfulness to
    these restriction formulas and identify the four displayed parameter
    field embeddings occurring in the normalized reference projections.
58. Canonical-curve-equation faithfulness now survives the actual
    finite-cover charts.  A selected correspondence branch is represented
    inside its source-based branch field by explicit source and target
    elements; both satisfy the original canonical equation, and every
    coefficient-linear embedding carries them to another zero.  The strict
    finite composition cover now contains the literal selected right branch
    in its transported middle field.  Its left and deck-corrected direct
    equivalences fix the original coefficient field, and any
    coefficient-linear middle chart therefore preserves the right branch's
    equation.  All four `e`, `a`, `b`, and `c` right branches are embedded in
    their enlarged middle covers.  The induced middle and target charts are
    proved to fix the literal common coefficient field, and the two charted
    coordinates of every selected right branch are proved to satisfy its
    original canonical curve equation.  Thus semantic four-arrow
    cancellation is now coefficient-faithful on the actual selected
    branches, not only an identity of abstract cover equivalences.  The next
    local step is to combine these four equation identities with intrinsic
    germ coefficient-field faithfulness and identify the explicit
    function-field embeddings underlying `toReferenceE/A/B/C`.
59. The explicit normalized `B/T` reference cover and the semantic curve
    action now have one literal codomain.  The canonical embedding
    `K → AlgebraicClosure K(X)` maps the eight-input field exactly onto the
    common curve coefficient field and transports the finite normalized
    reference cover without changing its degree.  After base change across
    the formal curve source, its canonical normal closure is joined with
    `branchComparisonSourceCover`; the resulting finite normal cover
    contains both constructions.  An explicit coefficient-linear embedding
    from the original reference cover into this combined source sends every
    free input through the same semantic coefficient algebra map.  The four
    displayed contravariant embeddings underlying `toReferenceE/A/B/C` have
    been postcomposed with this embedding and are now literal ring maps into
    the semantic source cover.  The remaining local comparison is therefore
    an equality of maps with the same domain and codomain: identify their
    restrictions on intrinsic germ coefficients, then align the finite
    scalar branches inside the common normal cover.
60. The four explicit reference maps now have exact restrictions to the
    intrinsic selected-`B` germ coefficient field.  The selected coefficient
    field is included first in `k(B₁,B₂)` and then in the selected
    normalized `B/T` cover.  For every relocated projection `(p,x)`, the
    normalized selected-to-projection equivalence is proved semilinear over
    the canonical function-field equivalence induced by equality of the
    two parameter loci.  Consequently its restriction to an intrinsic germ
    coefficient is exactly that coefficient transported to `k(p₁,p₂)`,
    followed by the literal algebra map to the scalar normal cover.  This
    formula is pushed through the original reference cover and the combined
    semantic/reference source, and is instantiated as four named maps
    `toReferenceE/A/B/COnBGermCoefficientRingHom`.  Their simultaneous
    restriction theorem removes all chart-conjugation choices from the
    coefficient layer.  Direct leaf compilation also exposed and repaired
    an old stale-artifact defect in the preceding common-codomain theorem:
    its dependencies are now explicit and its large opaque composite is
    factored into small maps with a fast direct proof.  The next local step
    is to identify these canonical parameter transports with the
    coefficients of the four relocated right-branch curve equations, then
    align the remaining finite scalar-normal branches.
61. Canonical curve equations now transport coefficientwise across both
    operations used in the four-face comparison.  Ambiently embedding a
    family maps its parameter field, endpoint ideal, and lexicographically
    monic curve equation exactly; equality of two complete family loci then
    maps the endpoint ideal and canonical equation through the induced
    parameter-field equivalence.  These reusable results identify the
    selected `B` equation with every relocated right-branch equation.  The
    parameter equivalence obtained from each full relocated family locus is
    proved generator-by-generator to equal the normalized equivalence
    obtained from its `B/T` scalar locus.  Consequently, for every monomial
    index, all four canonical transports from item 60 send the corresponding
    intrinsic selected-`B` coefficient to the coefficient with that same
    index in the relocated `e`, `a`, `b`, or `c` right-branch equation.  The
    four formulas are packaged simultaneously.  Thus the coefficient layer
    of the normalized reference charts is now identified with the semantic
    curve layer without any choice of equation generator or parameter-field
    isomorphism.  The next local step is to align the remaining finite
    scalar-normal branches in the combined cover and use the resulting
    whole-branch equality to factor the four explicit reference maps.
62. The deck correction used to base a transported finite normal cover is
    now retained as an explicit semilinear field equivalence.  The generic
    `FiniteCoverBasedNormalEquiv` records both its base-field square and an
    exact whole-selected-branch square, and recovers the existing based
    branch-groupoid equivalence without making a second choice.  Applied to
    the complete nine-coordinate joint chunk edges, the corrected normal-
    cover equivalence sends every selected coordinate positionwise.  Four
    named equivalences based at the `s·e=u` edge therefore send its selected
    `B/T` scalar at coordinate `7` exactly to the `e`, `a`, `b`, and `c`
    scalar branches used by the normalized reference maps.  Their induced
    reference-based field transitions satisfy a strict cocycle, and the
    four-edge field-level holonomy is literally the identity.  Thus the
    scalar alignment is no longer only an equality in an abstract branch
    groupoid: it is carried by selected-branch-preserving field
    equivalences with exact coordinate formulas.  The next local step is to
    base-change these four corrected edge equivalences to the common eight-
    input/formal-source field and include their selected scalar branches in
    `referenceSemanticSourceCover`; there they can be compared pointwise
    with the four promoted `toReference` embeddings and the semantic curve
    charts from items 58--61.
63. The four complete selected edges have now been scalar-extended from
    their different six-coordinate ambient fields to the single
    sixteen-coordinate coefficient field of the four-arrow diagram.  A
    reusable `TotalBaseChangedEdge` records the literal ambient and selected
    inclusions.  Its finite-basis compositum is finite over the common
    coefficient field, contains the full selected nine-coordinate edge, and
    remains a subfield of the twenty-eight-coordinate joint field.  Hence
    all four such fields embed literally in `referenceNormalCover`, and
    their selected coordinate `7` elements are exactly the `e`, `a`, `b`,
    and `c` scalar branches already used by the explicit normalized
    projections.  Composing these inclusions with the canonical transport
    to `referenceSemanticSourceCover` places all nine coordinates of all
    four scalar-extended edges in the common formal-source normal cover and
    preserves them exactly.  No additional scalar branch has been chosen.
    The remaining half of the base-change step is to extend the four
    corrected complete-edge normal-cover equivalences across this common
    coefficient field and the formal source, using the coefficient-
    semilinear source charts.  Their coordinate-`7` formulas can then be
    compared pointwise with the promoted `toReferenceE/A/B/C` maps.
64. The normalized scalar-reference transitions now retain the based
    normal-cover correction instead of reverting to an arbitrary lift after
    strict reference normalization.  They therefore still satisfy strict
    identity, inverse, and transitive laws while also carrying the literal
    selected scalar branch to the literal selected target branch.  The
    selected normalized `B/T` chart has a named intrinsic function-field
    scalar generator, and every promoted projection sends it to the selected
    scalar in that projection's concrete normal field.  After inclusion in
    `referenceSemanticSourceCover`, the four named `toReferenceE/A/B/C`
    embeddings agree pointwise on this generator with coordinate `7` of the
    four literal scalar-extended complete edges from item 63.  The four named
    intrinsic-`B`-germ maps are also proved to be literally the restrictions
    of those promoted embeddings.  Thus both the coefficient layer and the
    distinguished finite scalar branch now meet the semantic construction in
    the same codomain.  The remaining local step is to extend this equality
    from the coefficient field plus selected scalar to the whole relevant
    branch/function-field comparison and derive the auxiliary-`s`-independent
    three-input factorization.
65. The pointwise selected-scalar comparison now extends to every element of
    the selected nonnormal `B/T` scalar extension.  Each scalar-extended
    complete edge contains its entire three-coordinate right branch
    literally, and the direct inclusion of that branch in
    `referenceNormalCover` is proved equal to the route through the complete
    edge.  Canonical total-field equivalences transport the intrinsic
    selected branch to each of the `e`, `a`, `b`, and `c` branches, while the
    based normal-cover transitions agree with those equivalences on the
    whole extension.  After promotion to `referenceSemanticSourceCover`, all
    four `toReferenceE/A/B/C` embeddings therefore restrict as ring
    homomorphisms to the corresponding literal complete-edge inclusions;
    the four equalities are packaged simultaneously.  The next local step
    is to extend this exact comparison from the nonnormal scalar extensions
    across the full selected normalized function field and the four complete
    curve-branch fields.  That whole-function-field equality should then
    identify the explicit reference embeddings with the semantic curve
    arrows and yield the auxiliary-`s`-independent three-input
    factorization.
66. The explicit comparison now extends across the entire selected
    normalized `B/T` function field.  A generic ambient ring homomorphism
    applies the based selected-to-projection normal-cover equivalence and
    then the literal inclusions into `referenceNormalCover` and
    `referenceSemanticSourceCover`.  Pulling that map back through the
    selected chart's generic-point equivalence is proved equal, as a ring
    homomorphism on every function-field element, to the promoted reference
    projection.  The equality is specialized and packaged simultaneously
    for `toReferenceE/A/B/C`; thus no normal-closure element remains outside
    the exact comparison.  The remaining half of the local step is to
    identify these four whole-field maps with the four complete semantic
    curve-branch embeddings and then apply literal four-arrow cancellation.
67. The four complete semantic right-branch maps now have the same literal
    codomain as the promoted normalized reference maps.  The reusable
    finite-cover triangle API proves that its right equivalence fixes the
    original coefficient field, and the four-triangle API gives exact
    pointwise formulas expressing every charted right arrow as the original
    complete right-arrow transport followed by its target chart.  The
    branch-comparison cover has a named literal inclusion in
    `referenceSemanticSourceCover`; composing it with the selected complete
    `e`, `a`, `b`, and `c` branch embeddings, the four middle charts, and the
    semantic right arrows yields four ring homomorphisms defined on the
    entire curve-branch fields.  The remaining comparison is now an equality
    between named maps with a common codomain: prove that their intrinsic
    parameter restrictions are the four whole normalized maps from item 66,
    then descend four-arrow cancellation to the `B` germ chart.
68. The coordinatewise comparison with the relocated right-branch equations
    is now promoted to maps on the whole intrinsic selected-`B` coefficient
    field.  A reusable extensionality theorem says that two coefficient-linear
    maps out of this field agree once they agree on every canonical curve
    coefficient.  Four named algebra homomorphisms land in the complete
    relocated `e`, `a`, `b`, and `c` family parameter fields and send each
    canonical generator to the coefficient with the same monomial index.
    The codomains are deliberately kept separate: in particular, the
    relocated `c` parameter field is algebraic over, not a literal subfield
    of, the common eight-input coefficient field.  Each promoted intrinsic
    `toReferenceE/A/B/C` map is proved on the entire field to factor through
    the corresponding relocated parameter map and then the normalized
    scalar-cover inclusion.  Thus the remaining equality with the complete
    semantic branch maps is reduced rigorously to their action on the named
    canonical coefficients; no invalid inclusion of the output parameter
    field into the common coefficient base is required.  The next local step
    is to construct those four coefficient embeddings into the complete
    right branches, identify their charted semantic images generator by
    generator with the factorizations above, and apply intrinsic-field
    extensionality before four-arrow cancellation.
69. The four relocated parameter-field maps now factor through precisely the
    intrinsic coefficient fields of their canonical curve equations.  For an
    arbitrary relocated member on the selected complete family locus, the
    ambient image of the selected germ coefficient field is proved equal to
    the field generated by the relocated equation's coefficients.  This gives
    a canonical algebra equivalence between the two intrinsic coefficient
    fields, sends every selected coefficient to the same-index relocated
    coefficient, and recovers the previous full parameter transport after the
    literal coefficient-field inclusion.  Four named equivalences and one
    simultaneous factorization theorem specialize the construction to the
    `e`, `a`, `b`, and `c` right families.  Consequently, the remaining
    semantic comparison is confined to actual curve-equation data rather than
    unrelated displayed parameter coordinates.  The next local step is to
    embed these four relocated coefficient fields in their complete branch
    fields, compare their semantic images with the normalized reference maps,
    and then use coefficient-field extensionality and four-arrow cancellation.
70. A chart-gauge audit has isolated an important boundary in the existing
    semantic comparison.  For every composition triangle, choosing both the
    middle and target charts by transport from a source chart conjugates not
    only the left and direct arrows but also the right arrow to the identity.
    This is now a proved reusable theorem, and its four-face specialization
    states explicitly that all four right arrows in
    `coefficientFourArrowDiagram` are `RingEquiv.refl`.  The diagram still
    organizes coefficient-faithful selected graph embeddings, but its abstract
    cancellation theorem alone is therefore gauge-trivial and cannot justify
    intrinsic parameter factorization.  GitHub issue #16 tracks the corrective
    construction: put the transported normalized reference cover and the four
    selected semantic branches in one coherent normal model, then choose
    non-induced middle/target charts (or equivalent graph-faithful data) whose
    restriction theorems retain the `e/a/b/c` coefficient embeddings.
71. Each relocated intrinsic curve-coefficient field now has a literal ring
    embedding in its complete selected right-branch field.  Composing the four
    coefficient equivalences from item 69 with these inclusions gives named
    whole-field embeddings of the intrinsic selected-`B` germ into the
    complete `e`, `a`, `b`, and `c` curve branches, and a simultaneous theorem
    identifies every canonical generator with the same-index relocated curve
    coefficient.  This closes the first unchecked task of issue #14.  The
    codomains intentionally remain the four original complete branches: the
    next issue-#16 step is the honest scalar extension/joint normal-cover
    comparison that places them beside the common-base semantic branches
    without assuming, especially for `c`, that the full relocated parameter
    field lies in the eight-input coefficient field.
72. The selected semantic/reference comparison now has a concrete joint
    field before canonicalization.  Starting from the transported reference
    compositum over the literal common curve source, it adjoins the two
    algebraic `c` coordinates and the source/target pair of each of the four
    selected semantic right branches.  All ten generators are proved
    algebraic over the common source, so the joint field is finite there and
    one ambient normal closure is both finite and normal.  Literal containment
    theorems place the transported normalized reference field, all four
    common-base semantic right branches, and all four original relocated
    complete right branches in that same normal field.  In particular, the
    `c` parameter presentation is handled by honest finite adjunction rather
    than a false inclusion in the original eight-input field.  This completes
    the concrete-joint-field and single-normal-closure tasks of issue #16.
    The next issue-#16 checkpoint is to expose selected whole-branch embeddings
    into this normal field, canonicalize it once, and prove that the resulting
    comparison maps preserve the four intrinsic coefficient embeddings.
73. The concrete selected semantic/reference normal field is now
    canonicalized exactly once, with an explicit algebra equivalence over the
    full common coefficient/source field.  A reusable cross-base branch
    inclusion sends a complete selected correspondence branch into any
    intermediate field containing its ambient branch carrier.  It supplies
    eight named literal inclusions—four common-base semantic right branches
    and four original relocated right branches—into the concrete normal field,
    followed by eight maps through the same canonicalization equivalence.
    The four intrinsic selected-`B` coefficient embeddings from item 71 now
    compose with those relocated whole-branch maps into one selected canonical
    cover.  A simultaneous generator theorem proves that all four still send
    every canonical germ coefficient to the corresponding literal relocated
    curve coefficient before the shared canonicalization.  This completes the
    selected-embedding/canonical-comparison task of issue #16.  The remaining
    issue-#16 work is to construct common graph-faithful source/middle/target
    charts from this selected model, prove repeated-arrow coherence, and expose
    the resulting non-vacuous four-arrow coefficient restrictions for #14.
74. The generic non-induced chart interface required by issue #16 is now
    explicit.  Given four strict composition triangles, four source charts,
    two independently selected common left arrows, and two independently
    selected common direct arrows, `FourTriangleReference.ofCommonLeftDirect`
    constructs all middle and target charts and proves the four repeated-arrow
    coherence equations.  The conjugated right arrows are computed exactly as
    `left⁻¹ ≫ direct`; unlike `ofSourceCharts`, they are not forced to be
    identities.  The next local step is to instantiate those four common
    arrows from the selected semantic/reference normal model of items 72--73
    and prove that the resulting graph restrictions recover the four named
    intrinsic coefficient embeddings.
75. The coherent semantic branch cover and the once-canonicalized selected
    semantic/reference cover now sit in one literal finite normal source,
    `selectedGraphSourceCover`, formed by a single supremum over their common
    source field.  Literal inclusions put all eight selected semantic and
    relocated whole-branch maps in this source, and the four intrinsic germ
    coefficient maps retain their exact same-index generator formulas there.
    The four charted semantic right-branch maps have also been duplicated
    with this precise codomain.  Thus the final issue-#16 chart step no longer
    involves incomparable canonical closures: it is the construction of
    non-induced charts in this one source whose charted semantic maps agree
    with the named selected graph embeddings (first on canonical
    coefficients, then on the whole intrinsic field).
76. A reusable normal-cover extension operation now promotes any prescribed
    automorphism of an embedded finite subcover to an automorphism of the
    ambient normal cover, with an exact restriction formula on the whole
    embedded field.  It extends each of the four established semantic source
    charts to `selectedGraphSourceCover`; the new charts agree there with the
    old `se`, `sAa`, `sb`, and `sAc` charts on all of
    `branchComparisonSourceCover`.  Four strict composition triangles now act
    on this one unified source.  This completes the source-chart half of the
    final issue-#16 construction without imposing any gauge-trivial target
    chart: the remaining step is to select compatible common middle and
    target charts and prove that their right arrows restrict to the named
    intrinsic `e`, `a`, `b`, and `c` coefficient embeddings.
77. The four complete normalized reference edges now enter
    `selectedGraphSourceCover` through the same transported concrete normal
    field and the same single canonicalization as the selected semantic and
    relocated branches.  Every one of their nine selected coordinates has an
    exact preservation formula in that codomain.  More strongly, the four
    promoted reference maps agree with their literal complete-edge routes on
    the entire selected nonnormal `B/T` scalar branch; composing with the
    intrinsic germ-field inclusion gives four equalities on the whole
    selected-`B` coefficient field, including the algebraic output `c` edge.
    The remaining issue-#16 comparison is therefore internal to one selected
    graph cover: identify these whole-field reference restrictions with the
    charted semantic right arrows while choosing common middle/target charts
    compatible with the already lifted source charts.
78. The normalized-reference restrictions of item 77 are now identified
    pointwise with the four named selected relocated intrinsic coefficient
    maps in `selectedGraphSourceCover`.  The proof works on an arbitrary
    element of the intrinsic germ field: the relocated coefficient-field
    factorization recovers its full relocated parameter transport, while the
    scalar-extension equivalence's base square shows that the complete-edge
    route transports the same element before the common curve embedding.
    Thus the simultaneous theorem is a whole-field equality for `e/a/b/c`,
    not a generator-only comparison, and it includes the algebraic `c`
    parameter field.  The remaining issue-#16 step is now specifically to
    choose the non-induced common middle/target charts whose semantic
    right-arrow restrictions are these already-identified maps.
79. The non-vacuity condition for the final charts is now a first-class
    semantic interface rather than prose.  A `FourArrowDiagram.RightRestriction`
    consists of one literal intrinsic coefficient embedding in the common
    middle field, its four named images in the common target field, and proofs
    that all four are restrictions of the corresponding semantic right
    arrows.  Its `mapC_factorization` theorem descends faithful four-arrow
    cancellation to that one coefficient field, retaining the inverse `e`
    arrow in the middle chart.  In particular, four unrelated maps with the
    right codomain cannot satisfy the interface merely because a source-induced
    diagram is gauge-trivial.  The remaining issue-#16 construction must now
    produce this restriction package with `mapE/mapA/mapB/mapC` equal to the
    four whole-field selected/reference maps from item 78.
80. The complete semantic right branches now share one anchor before any
    chart choice.  The finite extension generated by all selected semantic
    face coordinates contains the whole common-base `e`, `a`, `b`, and `c`
    branch fields.  Its one embedding into `selectedGraphSourceCover` uses
    the existing concrete normal model and its single canonicalization.
    Transitivity of literal intermediate-field inclusions then proves,
    simultaneously, that all four semantic graph maps are restrictions of
    this one whole-face embedding.  In particular, the remaining middle and
    target charts can be aligned against one coherent map rather than four
    independently canonicalized branch embeddings.  The next issue-#16 step
    is to transport the middle/target covers to this anchor and package their
    restrictions as the `RightRestriction` of item 79.
81. Equality of complete family loci now reaches the actual complete branch
    types used by the four semantic triangles.  A reusable bridge identifies
    the family-field presentation with `toPair.branchOverSource`, transports
    equal loci to a full branch ring equivalence, and proves that this
    equivalence restricts to the canonical parameter-field transport.  The
    mapped selected `B` family therefore supplies one common complete middle
    branch, with four full equivalences to the relocated `e`, `a`, `b`, and
    `c` branches.  A simultaneous factorization theorem proves that the one
    intrinsic germ embedding in this common branch becomes exactly the four
    named complete-branch coefficient embeddings.  The remaining issue-#16
    step is to extend these branch equivalences to compatible common finite
    normal middle/target covers, join them with the selected graph source,
    and package the resulting four restrictions as item 79's
    `RightRestriction`.
82. The common complete-branch comparison now survives canonical normal
    closure without losing its selected branch.  The family-locus API
    exposes the deck-corrected `FiniteCoverBasedNormalEquiv`, embeds the
    actual `toPair.branchOverSource` as the literal selected branch of that
    normal cover, and proves that the corrected normal equivalence restricts
    on the whole branch to `completeBranchRingEquivOfIdealEq`.  Specializing
    this once gives four normal-cover equivalences from one mapped
    selected-`B` normal cover to the relocated `e`, `a`, `b`, and `c` normal
    covers, with one simultaneous full-branch restriction theorem.  These
    covers still have their separate parameter/source bases.  The remaining
    issue-#16 step is their honest scalar extension into compatible common
    semantic middle/target covers, followed by the selected-graph join and
    item 79's `RightRestriction`.
83. Finite-basis scalar extension now packages the branch-preserving normal
    cover needed by that next step.  Given a finite field `N/F` and a larger
    base `F ≤ E` in one algebraically closed ambient field, the concrete
    compositum has a finite normal closure over `E` and a canonical finite
    normal-cover model.  The original `N` remains literally contained in the
    ambient normal field, and its named map to the canonical cover factors
    through the literal compositum inclusion and the canonical selected
    normal-closure embedding.  Thus rebasing one of the four separately based
    selected-`B` normal covers no longer discards its distinguished branch.
    The next issue-#16 step is to instantiate this construction on the four
    facewise middle covers and transport their based equivalences through the
    common semantic bases.
84. The branch-preserving scalar rebase is now instantiated on all four
    relocated right-family normal covers.  Their complete parameter/source
    fields, including the algebraic `c` face, embed in the one selected
    semantic/reference joint field.  Rebasing over that field and taking a
    supremum gives `fourRelocatedRightRebasedCover`, a literal common finite
    normal codomain.  Four named maps from the one mapped selected-`B`
    complete branch enter this cover through the full family-locus
    equivalences, while four companion maps carry the entire mapped native
    normal cover through the selected-branch-corrected normal equivalences
    before scalar rebase.  The next issue-#16 step is to transport this
    common right cover from the finite selected joint base back to the
    literal semantic common source (using algebraicity of the joint field),
    adjoin it to the selected graph source, and extend the four maps to the
    independent common middle/target charts required by `RightRestriction`.
85. The common four-face right cover has now been transported from the
    finite selected joint base back to the literal semantic common source.
    The chosen algebraic-closure equivalence is proved to preserve that
    smaller source, the transported field is finite by the two-stage
    source/joint/right-cover tower, and its normal closure is joined with
    `selectedGraphSourceCover` to form `selectedGraphRightSourceCover`.
    Consequently one finite normal source now contains both all established
    repeated-coordinate graph coherence and all four selected right-family
    normal covers.  The four established source-chart automorphisms extend
    across the enlargement, the four strict composition triangles are
    available on it, and the selected complete-branch and native-normal
    maps all land in it.  The next issue-#16 step is to turn those four
    right embeddings into independent common middle/target charts whose
    restrictions are the semantic right arrows, then package the resulting
    non-vacuous `RightRestriction` for issue #14.
86. The coefficient-moving source charts needed for that construction are
    now explicit.  Besides the original independent `(s,e,a,b)` tuple, the
    fourth right label admits the independent presentation `(s,sA,a,c)`.
    Reordering these presentations gives four nine-coordinate rational
    sources whose one distinguished rank-two block is literally `e`, `a`,
    `b`, or `c`, while their last coordinate is the same formal curve
    source.  All four tuples are algebraically independent, so equality of
    their zero locus ideals gives canonical ground-field function-field
    equivalences with exact coordinate formulas.  The `e`-ordered source is
    proved to be the existing semantic common source itself; hence the
    resulting maps are genuine semilinear base changes that move the
    coefficient presentation, not deck transformations linear over the old
    source.  The next issue-#16 step is to lift these three base equivalences
    to compatible finite normal source covers and use their distinguished
    `e/a/b/c` coordinate formulas to choose independent common middle and
    target charts with the required normalized right restrictions.
87. The `a`- and `b`-ordered source presentations have now been closed back
    into the literal semantic common source.  They are permutations of the
    original nine displayed generators, so their intermediate fields are
    proved equal to the `e` source and the two coordinatewise equivalences
    become ground-field automorphisms of that one source.  Both
    automorphisms retain exact same-position formulas on named semantic
    source coordinates.  Their chosen algebraic-closure lifts now transport
    `selectedGraphRightSourceCover` to finite normal `a` and `b` source
    covers, and the restricted finite-cover equivalences have exact
    coordinate formulas.  The remaining source-level case is deliberately
    different: the independent `(s,sA,a,c)` field is not identified with the
    original ambient source by a permutation.  It must be joined through the
    selected semantic/reference finite field and normalized over a compatible
    common base before the middle/target charts and `RightRestriction` are
    assembled.
88. The genuine algebraic-output source has now been lifted without making
    that false identification.  Composing the four interalgebraicity faces
    gives the explicit closure equality
    `racl(s,e,a,b) = racl(s,sA,a,c)`; after embedding and adjoining the
    common formal curve coordinate, the two concrete nine-coordinate source
    presentations still have equal relative algebraic closures.  The exact
    `e→c` source equivalence consequently lifts to algebraic closures, maps
    `selectedGraphRightSourceCover` to a finite normal cover over the literal
    `c` source, and retains its same-position coordinate formula on the
    restricted finite cover.  For the compatibility step the two embedded
    sources are retained in the literal compositum
    `rightSourceJointField = S ⊔ Sc`; both inclusions are named, and the
    compositum is proved finite over both `S` and `Sc`.  The next issue-#16
    step is to normalize the selected graph covers over this joint source,
    select the common semilinear middle/target charts, and prove their four
    whole-field normalized coefficient restrictions before constructing
    `RightRestriction`.
89. The four semilinear source covers now have one honest finite normal
    codomain over that joint source.  A reusable finite-base rebase takes a
    chosen algebraic-closure equivalence extending an embedding `E → E'`,
    adjoins the transported values of a finite basis, normalizes over `E'`,
    and retains a selected map from the entire original cover with an exact
    base-element formula.  Applying it to the inclusions `S → S ⊔ Sc` and
    `Sc → S ⊔ Sc` rebases the `e`, `a`, `b`, and genuine `c` selected graph
    covers; their supremum is `fourSelectedGraphJointCover`.  Four named maps
    from the original selected graph/right source enter this one codomain,
    and all nine displayed coordinates land exactly on their same-position
    `e/a/b/c` coordinates through the appropriate literal inclusion in the
    joint base.  The remaining issue-#16 work is no longer a base/codomain
    compatibility problem: extend/select these four embeddings as compatible
    common middle/target equivalences, prove the repeated-arrow equations and
    whole intrinsic coefficient restrictions, and package the resulting
    non-vacuous `RightRestriction`.
90. The four selected embeddings into `fourSelectedGraphJointCover` now
    agree with their coefficient-moving base maps on the entire semantic
    source field, not only on its nine displayed generators.  Twisting the
    source algebra structure by the `a` and `b` automorphisms, and by the
    genuine `S ≃ Sc` chart for `c`, preserves finiteness of the joint source.
    Since the joint cover is finite over that source, each selected embedding
    makes its target algebraic over the original selected graph/right source.
    A reusable `EmbeddingClosureEquiv` API extends such an embedding to an
    equivalence of algebraic closures while retaining its exact restriction;
    all four `e/a/b/c` extensions are instantiated.  These closure
    equivalences are comparison data, not finite-cover charts themselves.
    The next step must use them to construct a finite common chart stable
    under the necessary comparisons, then prove the repeated arrows and the
    whole intrinsic coefficient-field `RightRestriction` on that chart.
91. The semilinear source charts now restrict to the whole intrinsic
    selected-`B` germ coefficient field before any finite-cover descent.  The
    relocated `e`, `a`, and `b` parameter fields are included literally in
    the semantic common source, while the relocated algebraic-output `c`
    parameter field is included in its genuine independent source.  Composing
    the intrinsic germ map with those inclusions gives four named whole-field
    embeddings.  The common-source `a` and `b` automorphisms, and the genuine
    `e→c` source equivalence, carry the `e` embedding exactly to the `a`, `b`,
    and `c` embeddings.  Thus the required coefficient square is no longer a
    generator-level or gauge-trivial statement.  It remains to close these
    source identities under a finite stable common chart, prove the repeated
    middle/target-arrow equations there, and expose the resulting non-vacuous
    four-arrow `RightRestriction` required by issues #16 and #14.
92. The four chosen algebraic-closure comparisons now restrict to honest
    finite charts with one literal codomain.  A reusable pullback construction
    takes the inverse image of any target intermediate field under an
    embedding-preserving closure equivalence, restricts the equivalence to
    that inverse image, and proves finiteness after a finite embedded base
    change.  Pulling back the base field of `fourSelectedGraphJointCover`
    along the `e/a/b/c` extensions gives four finite source fields, each
    finite over `selectedGraphRightSourceCover`, and four field equivalences
    onto the same joint cover.  On the entire old source cover each chart is
    exactly its originally selected embedding; on the whole intrinsic germ
    field the four charts give the normalized `e`, `a`, `b`, and genuine `c`
    target maps.  Thus the comparison data are no longer merely equivalences
    of infinite algebraic closures.  It remains to transport the four strict
    composition triangles to these finite pullback sources, choose compatible
    common middle and target charts, prove the repeated `s/sA/u/uB` equations,
    and package the resulting non-vacuous `RightRestriction`.
93. Strict semantic composition now extends across those four finite
    pullback sources without an unsupported normality change of base.  A
    generic source-extension construction lifts the left and right arrows of
    any literal `CompositionTriangle` to algebraic closures, defines the new
    direct arrow as their composite, and restricts all three arrows to the
    transported intermediate fields.  The enlarged arrows recover the old
    left, right, and direct equivalences on the entire original fields.
    Instantiating it gives strict finite `s·e=u`, `sA·a=u`, `s·b=uB`, and
    `sA·c=uB` triangles on the four semilinear pullback fields, while their
    source charts still restrict to the selected whole-source `e/a/b/c`
    embeddings into the literal joint cover.  It remains to select the
    independent common middle and target charts that identify the repeated
    `s/sA/u/uB` branches and whose four right arrows have the whole intrinsic
    germ restrictions required by `RightRestriction`.
94. The four selected complete right branches now enter the middle and target
    fields of those finite extended triangles with exact whole-field
    commuting squares.  Generically, the old middle and target fields embed
    literally into a source-extended triangle, and its new right equivalence
    composed with the old-middle embedding equals the old right equivalence
    followed by the old-target embedding.  Applying this to the selected
    `e/a/b/c` complete branches gives named middle maps, named target maps,
    and four exact restriction theorems.  This is stronger than a coordinate
    or curve-generator calculation and fixes the concrete anchors that the
    remaining common middle/target equivalences must preserve.  Issue #16 is
    still open: those four middle embeddings must be identified with one
    common intrinsic embedding, the repeated `s/sA/u/uB` arrows must be made
    literal, and the normalized whole-germ target restrictions must be
    packaged as the non-vacuous `RightRestriction`.
95. The semilinear source charts are now reoriented in the direction needed
    by a faithful common middle.  The forward `e→a`, `e→b`, and genuine
    `e→c` finite-cover equivalences carry the whole intrinsic `e` germ to the
    corresponding intrinsic target germ.  Conjugating the three semantic
    triangles onto those transported source covers and then using the inverse
    equivalences as their common-source charts sends the entire `a`, `b`, and
    `c` germs back to the one literal `e` embedding in
    `selectedGraphRightSourceCover`; the `e` chart is the identity.  A single
    four-way theorem records these ring-hom equalities.  This orientation is
    essential: the old forward charts sent the same `e` source to four
    distinct images and therefore could not be followed by one injective
    repeated-left chart.  The next step is to extend these inverse-oriented
    triangles to compatible finite common middle/target covers, preserve the
    complete-branch squares of item 94, and construct `RightRestriction`.
96. A reusable source-square constructor now isolates the exact data needed
    for the final non-vacuous restriction.  Two coefficient embeddings in the
    common source chart—one for the repeated `s` faces and one for the repeated
    `sA` faces—must have one literal image in the common middle chart, while
    the repeated `u` and `uB` composites must carry them to the four prescribed
    target embeddings.  The four semantic face identities then produce a
    `FourArrowDiagram.RightRestriction` automatically.  Thus the remaining
    issue-#16 work is reduced to six named whole-field source squares, with no
    possibility of closing the obligation by a source-induced identity gauge.
97. The four inverse-oriented semantic triangles now extend across finite
    pullbacks of one prescribed common source.  The `e` pullback supplies the
    literal finite common field; the `a`, `b`, and genuine `c` sources are
    pulled back through their inverse semilinear charts before the strict
    triangles are extended.  The resulting four restricted charts have that
    one literal codomain and carry the entire intrinsic germ to one shared
    embedding there.  Thus the source side of the final reference diagram is
    finite and literally common, rather than only semilinearly identified.
    Issue #16 is now confined to compatible common middle/target charts and
    the six whole-field squares required by item 96.
98. The whole selected complete right branches now survive those
    inverse-oriented common-source extensions.  For each `e/a/b/c` face, the
    old middle branch is included in the new middle field, its image is named
    in the new target field, and the extended right equivalence satisfies an
    exact ring-hom square on the entire branch.  These four branch anchors are
    the preservation conditions for the independent common middle and target
    charts; issue #16 still requires constructing those charts, identifying
    the repeated `s/sA/u/uB` arrows, and discharging the six source squares.
99. The based `e` face now exposes a complete intrinsic-germ restriction
    through its inverse-oriented common-source triangle.  The relocated `e`
    parameter field is included in the common eight-input coefficient field,
    and the resulting germ maps in the finite source, selected middle branch,
    and selected target are named explicitly.  Exact left, right, and strict
    direct squares are proved on the whole intrinsic field.  A reusable
    `CompositionTriangle.direct_comp_of_left_right` derives the direct square
    from the adjacent two without unfolding deeply nested cover types.  This
    supplies the prototype for the remaining `a/b/c` face squares; those must
    retain inverse semilinear source charts before repeated `s/sA/u/uB`
    middle/target maps can be identified.
100. The inverse-oriented `a`, direct `b`, and inverse-oriented `c` faces now
    carry the same complete intrinsic-germ restriction package as the based
    `e` face.  In each case the source chart returns the intrinsic germ to the
    selected `e` source embedding, the finite left arrow sends it to a named
    common-coefficient anchor in that face's middle cover, and source
    extension preserves exact left, right, and strict direct squares.  A
    reusable finite-cover lemma records that every left arrow fixes an
    arbitrary map into its coefficient field.  The four middle anchors are
    still separately typed and are intentionally not equated with the four
    preserved selected branches: compatible common middle/target charts must
    identify both embeddings, after which the repeated `s/sA/u/uB` maps and
    the non-vacuous `RightRestriction` can be assembled.
101. The common-coefficient middle and target anchors on all four faces now
    factor through the preserved complete right branches on the entire
    intrinsic germ.  For `a/b/c`, named maps first include the based germ in
    each selected semantic right branch; the selected-branch embedding into
    the old middle cover is proved equal to the common-coefficient anchor,
    and the equality is transported pointwise to the extended middle and
    target fields.  The `e` factorization is definitional and is recorded by
    the same interface.  Pointwise extended statements are intentional: an
    equivalent ring-hom equality makes Lean normalize the full nested-cover
    types and exceeded the 30 GiB memory safety floor.  The remaining
    issue-#16 step is therefore purely cross-face: construct common middle
    and target charts retaining these now-unified anchors, identify repeated
    `s/sA/u/uB`, and instantiate the non-vacuous `RightRestriction`.
102. The literal finite common source now lies in one finite stable source
    on which all four selected graph/right charts act.  Concretely, its
    normal closure over the semantic common source is formed inside the
    algebraic closure of the selected graph/right source.  It is proved
    finite and normal over the semantic source, and the old graph/right
    source and finite common source both embed literally in it.  Each of the
    four generally nontrivial selected source automorphisms extends across
    this normal field with an exact restriction theorem on the entire old
    source.  The next issue-#16 increment is to extend/pull back the four
    inverse-oriented triangles to this stable field, use these four extended
    automorphisms as their source charts, and then construct compatible
    common middle and target charts.
103. The four inverse-oriented semantic triangles now extend over the stable
    source with one literal source-chart codomain and nontrivial selected
    graph actions.  The `e` triangle extends directly; the `a/b/c` triangles
    extend over the pullbacks of the stable source through their inverse
    semilinear charts.  Each restricted pullback chart is postcomposed with
    the corresponding stable selected-graph automorphism.  A generic
    pullback restriction lemma proves that this composite acts on any
    whole-field source embedding by the prescribed old chart followed by
    the stable correction.  Specializing it gives exact intrinsic-germ
    restrictions for all four faces, including genuine algebraic-output
    `c`.  The remaining issue-#16 construction is now the independent common
    middle and target chart layer: choose its repeated `s/sA/u/uB` arrows,
    prove the four semantic right restrictions, and instantiate the
    non-vacuous `RightRestriction`.
104. The source embeddings are now grouped correctly for that final
    restriction.  A reusable closure-comparison constructor precomposes an
    embedding-preserving algebraic-closure equivalence by a source field
    equivalence while retaining the exact composite embedding.  Applying it
    to the selected joint cover gives four finite pullback sources and four
    strict extended triangles with one literal chart codomain.  On the whole
    intrinsic germ, the `e/b` charts restrict to one selected source
    embedding and the `a/c` charts restrict to a second selected source
    embedding, exactly matching the two repeated left labels.  Finiteness of
    all four pullbacks is proved, including transport through the three
    nontrivial source equivalences.  Pointwise restriction statements are
    intentional because normalization of the equivalent deeply nested
    ring-hom equality crossed the 30 GiB memory safety floor.  Issue #16 now
    requires the analogous grouped common middle and target charts, followed
    by the four semantic right squares and the non-vacuous
    `RightRestriction` package.
105. The grouped finite triangles now retain the full intrinsic restriction
    package.  For each `e/a/b/c` face, the old selected-branch middle anchor
    and its target image are included into the new source extension, and
    exact whole-germ squares are proved for the left, right, and strict
    direct arrows.  Consequently the future cross-face middle and target
    charts have explicit preservation obligations on all four faces; they
    cannot satisfy coherence by discarding the chosen normalized branch
    embeddings.  The remaining issue-#16 construction is to place those
    four preserved middle anchors in one common middle chart, place their
    four target images in one common target chart, identify the repeated
    `s/sA/u/uB` maps, and instantiate the non-vacuous `RightRestriction`.
106. The entire selected `e/a/b/c` right branches now survive in the grouped
    middle and target fields, not just their intrinsic germ points.  Each
    grouped right arrow forms an exact ring-hom square with its complete
    selected branch embedding, and pointwise factorization theorems identify
    the intrinsic middle and target anchors of item 105 with the restrictions
    of those branch embeddings.  This includes the genuine algebraic-output
    `c` branch.  The remaining issue-#16 construction is cross-face only:
    build common middle and target charts preserving these four concrete
    normalized branches, identify the repeated `s/sA/u/uB` arrows, and use
    the six source/direct squares to construct `RightRestriction`.
107. The build graph is reorganized for the remaining issue-#16 work.  The
    four grouped selected-branch families now live in independent `E/A/B/C`
    sibling modules behind a thin compatibility aggregator, and their large
    expanded coherence equalities have named proposition interfaces so
    downstream artifacts stay compact.  The same declarations serialize in
    parallel in roughly 140 seconds instead of the former 1,592-second
    monolithic checkpoint.  Each Verso chapter now imports only the layers
    and stable compatibility endpoints that it documents rather than the
    whole-project umbrella.  A representative new module after the grouped
    checkpoint therefore completes the default build in roughly ten seconds
    without rebuilding any chapter.  New four-face constructions should
    retain this sibling-plus-thin-aggregator layout, and the configurations
    chapter should remain pinned to the stable grouped checkpoint until it
    is intentionally extended.
108. The remaining cross-face obligation is now isolated as the finite
    `GroupedCommonChartData` interface.  It asks for one common middle field,
    one common target field, the repeated `s/sA/u/uB` equivalences, the five
    intrinsic coefficient embeddings, and exactly the six whole-germ squares
    relating them to the two grouped source embeddings.  Any inhabitant
    canonically produces the non-induced four-triangle reference, its
    faithful four-arrow diagram, and the non-vacuous intrinsic
    `RightRestriction`; the resulting `c = b e⁻¹ a` factorization is exposed
    directly.  This keeps the next construction focused on common-chart
    existence while preventing a source-induced gauge choice from satisfying
    the semantic endpoint vacuously.
109. The repeated-`s` common-middle alignment now survives both finite source
    enlargements.  Its established deck transformation on the comparison
    cover extends first to the selected graph source and then to the
    right-enlarged selected graph source, with an exact restriction theorem
    at each boundary.  The restrictions intentionally remain two composable
    lemmas: forcing Lean to normalize both nested inclusions in one theorem is
    a slow elaboration boundary and adds no mathematical content.  Construct
    the repeated-`sA` sibling in the same way, then transport the resulting
    source-cover alignments through the joint-base rebase into a finite stable
    common middle chart.
110. Both coherent repeated-`sA` total-anchor corrections now survive the same
    two finite source enlargements, again with exact restriction equations at
    each boundary.  They live in a sibling leaf to the repeated-`s` lift and
    are collected only by a thin grouped-middle compatibility module, so the
    three normal-cover extension families serialize in parallel.  The next
    mathematical boundary is no longer branch alignment over the literal
    common source: it is transporting these source-linear alignments through
    the semilinear joint-base rebase and extending them to one finite stable
    middle cover.
111. The semilinear joint-base obstruction is now handled by a finite stable
    cover with the correct base of normality.  The complete four-face joint
    cover is finite over the original semantic source; its normal closure over
    that source is finite, contains the joint cover, and is normal over the
    field fixed by all established repeated-arrow alignments.  The whole
    selected graph/right source embeds into this cover through the selected
    `e` leg, and every semantic-source-linear deck transformation extends with
    an exact whole-cover restriction.  In particular, the repeated-`s` and
    both coherent repeated-`sA` anchor corrections now act on this one stable
    finite cover.  The stable cover, generic extension mechanism, and `s`/`sA`
    families remain parallel leaves behind a thin compatibility module.  Next
    pull all four grouped triangles back to this stable source and orient the
    three corrections into the two common left-arrow charts.
112. All four grouped triangles now live on finite pullback sources charted to
    the one stable grouped cover.  The `e/a/b/c` faces are independent sibling
    leaves, each with its exact intrinsic germ restriction; after charting,
    `e,b` share the literal stable `groupedStableSourceS` embedding and `a,c`
    share `groupedStableSourceSA`.  The pullback leaves take roughly three to
    four seconds apiece to elaborate and serialize independently behind a
    thin compatibility module.  The next step is to orient the stable
    repeated-`s` and two `sA` anchor automorphisms into common left charts and
    prove their two common-middle coefficient squares.
113. The coefficient-moving `e→a` automorphism of the whole semantic source
    is now proved involutive, not merely on the distinguished rank-two block.
    The proof uses the literal nine-coordinate generating presentation and
    checks the `e/a` block transposition coordinate by coordinate; this avoids
    an expensive definitional-equality search through the nested source-field
    presentation.  Next use this finite-order base chart to form the
    two-orbit finite normal cover stable under its algebraic-closure lift, then
    restrict the lift to the common left chart and combine it with the stable
    repeated-`s` and `sA` corrections.
114. The `e→a` lift now acts on one finite normal grouped source.  The previous
    stable cover is transported from the algebraic closure of the joint cover
    to the canonical algebraic closure of the semantic source, then enlarged
    by the two-element orbit of the lifted base chart.  A reusable
    `FiniteNormalOrbit` layer proves that the possible non-functorial defect
    in the square of the chosen lift is source-linear and hence stabilizes
    every finite normal cover.  The resulting restricted ring equivalence has
    its exact semilinearity square, contains the whole joint cover, and is
    finite over it.  The repeated-`s` and both coherent repeated-`sA`
    corrections have also been extended to this final orbit cover with exact
    restriction to the preceding stable source.  Next extend the four grouped
    triangles across finite pullbacks charted to this orbit cover, keeping the
    four constructions in independent sibling leaves.
115. The `e`, `a`, `b`, and `c` grouped triangles now extend across four
    finite pullback sources charted to the literal `e/a`-stable orbit cover.
    Each leaf constructs its explicit embedding through the old joint-source
    chart, transports finiteness from the joint cover, extends that embedding
    to algebraic closures, and proves the exact intrinsic restriction to
    `groupedStableAOrbitSourceS` or `groupedStableAOrbitSourceSA`.  The four
    leaves remain independent behind thin triangle and compatibility
    aggregators.  Next orient their extended left arrows with the stable
    repeated-`s`, repeated-`sA`, and semilinear `e→a` charts to obtain one
    common middle field and its two exact coefficient squares.
116. The final orbit source now carries two explicitly oriented candidate
    left maps with one literal ambient codomain.  The repeated-`s` map
    uses the exact whole-branch `e/b` correction followed by the restricted
    finite `e→a` semilinear chart; the repeated-`sA` map is the relative
    correction between the two selected `sA` branches through their coherent
    total-field anchor.  The semilinear chart is proved on the entire
    intrinsic germ field to carry `groupedStableAOrbitSourceS` to
    `groupedStableAOrbitSourceSA`, while source-linearity proves that every
    branch correction fixes the applicable source embedding.  Consequently
    both candidate maps have the same exact whole-germ coefficient
    restriction.  This coefficient-square leaf and the four triangle leaves
    elaborate independently behind the thin final compatibility module.  It
    is not yet a common middle chart for the four selected branches: an
    injective common postcomposition cannot make distinct face embeddings
    equal.  Next construct face-specific source charts on a finite compositum
    which align each selected left and direct branch simultaneously; only then
    use the candidate maps to obtain common middle and target charts and prove
    the four normalized `e/a/b/c` restrictions.
117. The simultaneous-alignment domain is now isolated explicitly.  A
    reusable `selectedWholeFaceField` adjoins a composition face's middle and
    target coordinates to its literal source; both the complete selected left
    branch and the complete selected direct branch are proved literal
    subextensions of this one finite field.  The four semantic faces now have
    named whole-face extensions inside the common ten-coordinate
    `selectedSemanticBranchExtension`; the genuine `c` field additionally
    retains both algebraic output parameters.  All four are finite over the
    common semantic source and map to `selectedGraphSourceCover` by restriction
    of the single coherent ten-coordinate embedding.  Thus the next
    normal-branch alignment can be selected on one whole-face domain per face,
    rather than composing unrelated left-only and direct-only corrections.
    This is the precise mechanism needed to make each future source chart
    preserve both branches simultaneously.

**Historical next step (superseded by the audit, #19):** turn the selected relational multiplication and inverse
into dominant rational maps on one common positive-dimensional normalized
parameter cover.  Items 25--27 put the four normalized based projections on
one literal source and target and identify every generic-point map with an
explicit field embedding.  Item 28 provides the faithful semantic
field-equivalence target and one strict selected composition triangle.
Items 29--40 give four strict finite-normal-cover curve triangles, the exact
semantic target for aligning them, and one formal curve source shared by all
four embedded loci over one eight-input coefficient field; item 35 also
places all four actions on one literal finite normal source compositum, and
items 36--54 supply selected-branch-preserving comparisons, equality of the
curve relations, and source-level re-elaboration integrity after the honest
independent scalar extensions.  The
repeated `s` relation already lives over the literal common input field, and
the repeated `sA`, direct `u`, and direct `uB` comparisons have now been
transported explicitly into that base.  Each alternative comparison has a
finite pairwise normal source extension containing both literal branches;
all three comparison covers have been rebased and adjoined to the common
source cover, and their actual selected branches have been aligned there.
The four direct-anchor corrections now provide the coefficient/source
charts, the induced middle and target charts have exact selected-branch
restriction formulas, and the resulting common-cover reference already
carries literal semantic cancellation.  The selected right `e`, `a`, `b`,
and `c` branches have also been embedded in the transported middle covers;
their charted endpoints satisfy the original canonical equations, while all
middle and target charts fix the common coefficient field.  The original
normalized reference cover has now been transported into the same canonical
source algebraic closure and joined with the semantic branch cover; the four
explicit `toReference` field maps therefore have the same literal codomain
as the semantic action, their eight-input coefficient square commutes, and
their restrictions to the intrinsic `B` germ coefficient field are the
canonical transports to the four displayed parameter fields.  Those
transports are now proved to be exactly the coefficients of the four
relocated right-branch curve equations.  The four complete selected edges
have also been scalar-extended to the common sixteen-coordinate field and
embedded, coordinate-for-coordinate, into the common formal-source cover.
The promoted reference embeddings now agree there with the literal
complete-edge inclusions on every element of all four selected nonnormal
`B/T` scalar extensions, and their intrinsic-germ restrictions are the
named coefficient transports.  Their action on the entire selected
normalized function field is also exactly the based ambient normal-cover
transport.  The complete semantic curve-branch maps have now been named in
the same final cover with exact charted-arrow formulas.  The intrinsic germ
maps into all four relocated parameter fields are also defined on the whole
field, are characterized by canonical curve coefficients, and factor the
the four normalized reference restrictions.  Those complete-branch
embeddings and their whole intrinsic-field reference identifications are now
established, and the four semantic branches factor through one coherent
whole-face anchor.  The mapped selected `B` family is also now one common
complete middle branch whose four full branch equivalences recover the
relocated `e/a/b/c` intrinsic maps exactly.  Its one canonical normal cover
now has four selected-branch-preserving equivalences to the relocated normal
covers.  Scalar-extend these separately based covers into compatible common
semantic middle and target covers, join them to the selected graph source,
construct the resulting `RightRestriction`, and use its faithful
cancellation theorem to prove that `toReferenceC` factors through
`toReferenceE`, `toReferenceA`, and `toReferenceB`.  This is the precise
auxiliary-`s` independence statement: the factorization must descend to the
intrinsic two-input germ chart, not merely hold on the eight-input relational
source.  Then extract multiplication and inverse on that single chart with
strict rational identities.
Use the resulting maps to construct the translation-indexed Weil atlas and
glue its multiplication, unit, and inverse with the strict field/rational
cocycle.  The resulting group scheme is automatically separated by item 16;
then extract a finite subatlas and package it in the scheme-level
algebraic-group target.  After that, identify the already constructed
categorical rank-one normal kernel with the connected component of its
scheme-theoretic kernel, apply the completed affine-action classification,
and finish affine-grid extraction (8.5) and Q correctness.

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

- **M4** (#6, #12, #21, #22): repair the extraction target, state and prove
  Lemma 8.4 (action bridge), re-plan the group-chunk step (8.2/8.3) from the
  corrected target, then prove Q, Q′ and J completeness over algebraically
  closed fields.
- **M5** (#7): T1–T3, algebraic-base lattice/point/rank and configuration
  lifts, point-level (1)⇔(2), (4)⇒(3), semantic J assembly and finite-base
  soundness are on main. Conditional four-way packaging names the open
  ACF completeness (3)⇒(2) input, which still needs M4. The old
  arbitrary-field Q/Q′ consequences have concrete Lean refutations over
  characteristic-zero rational function fields in five variables (#25).
- **M6–M8** (#8–#10, #23): Frobenius classes and generic arithmetic (after
  corrected §10–12 operation predicates), ratio-field interpretation, base/point
  recovery, public theorem variants and the functorial quotient formulation.
  The rank-five kernel, two-generic intersection, trdeg transport and compatible
  induced-map converse and supplied-endpoint uniqueness/Frobenius fibre are
  proved. Full functorial definitions and assembly remain open.
- **Book**: keep each chapter synchronized with the library and free of
  overclaims. Verso requires docstrings on every referenced declaration *and
  its structure fields*.

## Lean gotchas (hard-won; read before writing proofs)

- (v4.34.1) `MvPolynomial.coeff` is gone: write `p.coeff m`. The lemmas
  `MvPolynomial.coeff_add` and `MvPolynomial.coeff_zero` are protected.
- (v4.34.1) `rw` and `simp` unify only up to instance transparency. A
  rewrite through a `def` such as `Point` or a local `Field` instance can
  fail; use `exact`/`refine` with the lemma, which checks definitional
  equality.
- (v4.34.1) `Function.Injective.encard_range` is now an equality, and
  `TrivSqZeroExt` pair literals no longer simp-normalize their `fst`/`snd`.
- Check single files with the toolchain `lean` and the lakefile options
  (`-DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false`); without them,
  instance search behaves differently.
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

Each work session: (1) check the issues on adamtopaz/acl_geom for Adam's
steering and `chit inbox` for the peer agent; (2) agree on file ownership;
(3) do one small verifiable increment; (4) validate with a full `lake build`
and `lake exe book` (one build family at a time in a shared checkout);
(5) commit and push; (6) leave a progress comment on the relevant issue.
CI runs on push (build + Pages deploy). Until a fresh run on the current
`main` succeeds, local validation is the authoritative evidence.

## Lean/Mathlib 4.34.1 compatibility checkpoint (#20)

The direct pins are Lean/Mathlib v4.34.1 and Verso v4.34.0. Mathlib's resolved
revision is recorded in `lake-manifest.json`; Verso v4.34.0 is the compatible
stable tag for this Lean minor version. These were the latest stable releases
verified against the upstream release pages on 2026-10-06/07.

Reproduce with the toolchain's available C compiler on `PATH`, then run:

```sh
LEAN_NUM_THREADS=2 lake exe cache get
LEAN_NUM_THREADS=2 lake build
LEAN_NUM_THREADS=2 lake exe book
```

The host's previous compiler wrapper referenced a removed Nix path. For the
migration measurements, GCC was supplied from
`/nix/store/79mr0jw3qccq7hhf1hh62knxd88dwazc-gcc-wrapper-15.3.0/bin` on `PATH`.
That path is a local workaround; another machine should use its installed
compiler. The build monitor samples `MemAvailable` and process-family RSS
every two seconds and interrupts only its own family below 30 GiB available.

The compatibility changes update Mathlib lattice/rank, polynomial and
category APIs, replace deprecated declarations, and expose scalar inclusions
through the correct restricted intermediate fields. The largest repair is
`ChunkCurveCommonSource`: canonical closure transport is now over the native
source field before restricting the whole-total map to each preserved branch.
This retains a single map on the complete source and its coefficient action,
rather than constructing unrelated branch maps. The book documents the new
presentation. Abstract coefficient/composition lemmas are reused downstream.
Commented local elaboration settings unfold transparent field aliases; the
Lean kernel still checks all resulting terms.

The final transport modules exposed a separate export bottleneck: Lean's optional
symbol-frequency index traverses their deeply nested theorem signatures without
a heartbeat bound. The original 115-line orbit-triangle E module checked in 6.03
seconds without artifact emission but exceeded a 180-second compiled-output probe.
An extension-by-extension diagnostic isolated `symbolFrequency` preprocessing.
The documented `nameDenyListExt` entry excludes the exact frozen technical
namespace `PsiCurveFourArrowCommonSourceRealizations` from the optional premise
selectors and frequency statistics. It preserves every declaration, proof term,
kernel check, direct reference, simp/instance attribute and book docstring. The
private emitted-module probe then passed in 6.03 seconds, with all eight public
declarations using standard axioms. The full shared build and book also passed,
as recorded below; this is not a clean-build speed claim.

Validation on 2026-10-07 (two Lean threads):

| check | elapsed | sampled peak family RSS | minimum available RAM |
|---|---:|---:|---:|
| Full default `lake build`, pass 16 | 876.62 s | 12.46 GiB | 35.71 GiB |
| `lake exe book` | 12.08 s | 1.55 GiB | 40.67 GiB |

Both exited successfully, with no memory safety stop. The full pass rebuilt the
common-source family after the metadata entry, using dependency artifacts prepared
by earlier migration passes; it is not a clean-build measurement. Book generation
writes the multi-page HTML to `_out/html-multi`.

The compiled root axiom check covers seven representative declarations, including
all three native raw roundtrips, whole-source branch composition, soundness and
j-rigidity. Each uses only `propext`, `Classical.choice` and `Quot.sound`. Earlier
focused axiom checks cover the 68 native-source declarations, 428 reference-bridge
declarations, 34 middle-field declarations and the alignment repair. A lexical
scan of all 196 library/root files finds no proof placeholders or project axioms.
`git diff --check` passes, and the final logs have no deprecation warnings in the
changed files. Existing style suggestions and warnings in untouched files remain.

The upgrade does not close the performance gate #18. The final pass measured
`ChunkCurveCommonSource` at 209 seconds, `ChunkCurveReferenceBridge` at 129 seconds,
the four common-middle modules at 5.3–6.1 seconds, grouped restriction at 10 seconds,
and orbit-triangle E at 4.4 seconds. Earlier migration passes took 596/304 seconds
for CommonSource/ReferenceBridge, hundreds of seconds for small middle modules,
and 1439 seconds for grouped restriction; the original orbit-triangle compiled
probe exceeded its 180-second cap. These observations separate the optional export
bottleneck from kernel work; they are not controlled clean-build speed ratios.
Focused dependency cuts and the remaining native instance-path/kernel costs are
still tracked under #18.

## Audit cleanup checkpoint (#19/#22/#23/#24/#25)

This checkpoint builds on the pushed v4.34.1 migration `8a54b54` and retains
all existing proved mathematics. The 117-step M4a record remains frozen.

- `Geometry/Representatives` proves the finite representative calculus
  (12 public theorems), consumed by the arithmetic refutations. The other
  foundational carryovers in #24 remain open or privately reviewed.
- `Config/AffineGrid` retains the literal-target refutation and constrains
  only three joins and fifteen points in the corrected target. Extraction
  and `QCompletenessACF` were subsequently refuted by an actual degenerate witness (#27).
  Guarded extraction/completeness require I≠D and I≠P and remain open; current
  conditional correctness uses the guarded input over algebraically closed fields.
- `Counterexamples/GenericArithmetic` records the literal JAdd/JMul and
  full-class RatioEq refutations (26 public theorems), with every witness's
  geometric class membership proved. Corrected class operations, totalization
  and ratio decoding remain open.
- `Interpretation/FrobLinkIncidence` gives the geometric concurrence
  reduction (five public theorems) without configuration completeness.
  Direct-link semantics and the two-hop bridge are separate obligations.
- The source retains the original wording's provenance, withdraws the false
  arbitrary-field Q/Q′ consequences and marks their mathematical
  counterexamples as not yet formalized. It also withdraws the invalid
  common-representative proof and the refuted literal arithmetic/ratio claims.
  Module status, book exposition and the current issue map match these limits.

Validation on 2026-10-07 used the same GCC path, two Lean threads and owned
process-family 30 GiB available-memory guard documented above:

| check | elapsed | sampled peak family RSS | minimum available RAM |
|---|---:|---:|---:|
| Full default `lake build` | 1085.79 s | 10.18 GiB | 35.09 GiB |
| `lake exe book` | 10.08 s | 1.43 GiB | 41.44 GiB |

Both exit successfully with no memory safety stop. This is an incremental
full gate following the audit's upstream documentation/interface changes; it
is not a clean-cache benchmark. It rebuilt the frozen configuration chain.
CommonSource/ReferenceBridge took 210/131 seconds, intrinsic source
restriction 51 seconds, grouped restriction 11 seconds, orbit-triangle E
4.5 seconds, and the root library 4.2 seconds.

The configuration book module took 300 seconds in Lean, then 131 seconds
for its roughly 60 MiB generated C object; executable linking took 8.8 seconds.
That chapter contains 1152 docstring references and is a concrete remaining
#18 target for focused book sections and reduced incremental rebuild costs.
The rendered multi-page HTML contains the new calculus/refutation sections.

All 64 expected public theorem axiom reports for representative calculus,
corrected extraction/refutation, rank-five correctness, concurrence and
literal arithmetic/ratio refutations use exactly `propext`, `Classical.choice`
and `Quot.sound`; none is missing. The lexical audit covers all 199
library/root files and finds no placeholders or project axioms.
`git diff --check` passes. The changed files have no deprecation warnings;
existing warnings in untouched files are separate.

The revised TeX builds to 54 pages without undefined references or overfull
boxes. The title/provenance, corrected grid, Q/Q′ counterexamples,
Frobenius-proof audit, generic-operation audit and ratio warning were visually
checked in scratch renders. These PDFs and the supplied primary-source papers
remain outside git.

At this audit checkpoint, #18 was next: strict compiled-declaration/body and
metadata preservation, paired emitted-module timings and isolated Lake
measurements. The focused-module checkpoint below records those results and
its remaining measurements. The historical M4a work remains frozen.


## Focused module checkpoint (#18)

This refactor starts from the audited `f6964f0` sources on Lean/Mathlib 4.34.1.
It preserves all 1082 exported signatures and 1073 definition/theorem bodies
of the two oversized configuration modules, subject only to the reviewed
proof changes listed below. It does not prove an additional blueprint target
or restart the frozen M4a program.

### Dependency organization

The existing CommonSource and ReferenceBridge module names remain the cores,
so the 76 downstream library importers keep their imports. Seven leaves are
explicitly imported by `AclGeom.lean` and only the relevant book sections:

| module suffix | source lines | direct split dependencies |
|---|---:|---|
| `ChunkCurveCommonSource` | 3848 | existing upstream chain |
| `ChunkCurveCommonSourceComparison` | 1036 | CommonSource |
| `ChunkCurveCommonSourceExistence` | 251 | CommonSource |
| `ChunkCurveCommonSourceRebasing` | 2004 | CommonSource |
| `ChunkCurveReferenceBridge` | 2830 | CommonSource |
| `ChunkCurveReferenceBridgeBGermComplete` | 1396 | ReferenceBridge |
| `ChunkCurveReferenceBridgeSelectedBScalar` | 2433 | ReferenceBridge |
| `ChunkCurveReferenceBridgeSemanticBranches` | 720 | ReferenceBridge, Comparison |
| `ChunkCurveReferenceBridgeFinal` | 306 | ReferenceBridge, BGermComplete, SelectedBScalar |

The two original sources had 6942 and 7493 lines. The remaining CommonSource
core is still large because its live families form one connected dependency
component; no independent parallel cut was found. Book-only existence,
comparison and rebasing results now elaborate independently of the downstream
library chain. Nothing was discarded as unused.

`AclGeomBook/Configurations` now contains six focused sections:
CorrespondenceFields, ParameterTransport, CommonSourceCovers,
ReferenceBranches, SemilinearCommonFields and AlgebraizationPrerequisites.
A small GroupChunkRecord wrapper preserves the old group-record section and
frozen-work notice. Each section imports its declaration providers rather
than all configuration modules. The original 1152 docstring references and
nine tags remain in exactly their original order; six unique subsection tags
are added. Generated HTML retains all 64 page paths, the old section 6.8 and
its ordered subsections 6.8.1–6.8.6. Three prose corrections remove residual
by-construction claims about equation (8.6) and describe the chosen
coordinate-field equivalence accurately.

### Mathematical and artifact checks

The split preserves names, statements, attributes, reducibility and
noncomputability. `curveEmbedding` becomes a documented public abbreviation
because SelectedBScalar consumes it. This is the sole intended privacy and
documentation change among the original constants.

Six membership proofs use the inclusion supplied by an equality instead of
transporting membership with `Eq.rec`. Six later duplicate branch-inclusion
proofs alias the already proved native statements. The three
`commonSourceToRight{A,B,C}SourceEquiv_apply` type hashes change only in their
membership proof arguments, which are equal by proof irrelevance. Exactly
eleven normalized bodies change: the six aliases, those three apply lemmas
and `commonSourceRight{A,B}Aut_apply`. All changes were reviewed; the coordinate
definitions themselves have unchanged raw values.

Independent dumps from the actual isolated Lake artifacts match the frozen
1082-signature/1073-body baseline with no missing or new constants, unexpected
changes or nonstandard axioms. The exported premise-index deny entry has the
same module, kind and string. Differences caused by renamed compiler-generated
`_proof_N` theorem references are normalized only by their recursively
normalized statements; other constants and bodies are compared strictly.
All seven structural mutation checks and all 22 saved-dump comparator controls
and mutations behave as required. The existing metadata workaround remains
in CommonSource once; it does not weaken Lean kernel checking.

### Controlled measurements

Both private worktrees start at `f6964f0`, with separate regular project build
outputs and the same isolated, pinned dependency/cache snapshot. Only Codex's
one build family runs during each measured interval. All runs use two Lean
threads, the GCC path recorded above and the 30 GiB available-memory guard.
The OS cache is warm; the following are component or incremental measurements,
not whole-project clean-build ratios.

| check | elapsed | sampled peak family RSS | minimum available RAM |
|---|---:|---:|---:|
| Original six-target component rebuild | 560.85 s | 8.00 GiB | 39.05 GiB |
| Refactored six-target component rebuild | 331.76 s | 7.74 GiB | 41.09 GiB |
| Original monolithic book native-object control | 134.66 s | 5.36 GiB | 36.14 GiB |
| Focused book full build, library outputs cached | 221.09 s | 10.85 GiB | 38.53 GiB |
| Focused HTML generation | 8.05 s | 1.42 GiB | 41.02 GiB |
| Full build after one leaf docstring edit | 84.41 s | 8.81 GiB | 38.22 GiB |
| Canonical full build after reverting that fixture | 84.44 s | 8.59 GiB | 38.15 GiB |
| Canonical HTML generation | 8.04 s | 1.53 GiB | 39.75 GiB |
| Warm no-change full build | 4.02 s | 0.96 GiB | 40.28 GiB |
| Warm no-change HTML generation | 8.04 s | 1.51 GiB | 39.91 GiB |

The paired six-target experiment rebuilds exactly the same 54 library modules
in both worktrees; upstream and package outputs are reused. Targets are
IntrinsicSourceRestriction, SelectedWholeFace, SemilinearGroupedMiddleS,
SemilinearGroupedMiddleSA, SemilinearGroupedRestriction and
SemilinearGroupedStableOrbitATriangleE (each prefixed by `AclGeom.Config.ChunkCurve`).
CommonSource takes 208 → 98 seconds, ReferenceBridge 129 → 33, intrinsic
restriction 52 → 25, grouped restriction 10 → 10 and orbit-triangle E
4.2 → 4.2. The 41% wall-time reduction applies only to that component rebuild.

The original staged full build reused its unchanged book C object whereas
the math-only variant regenerated it; their raw full-build times are not a
fair speed ratio. A separately forced original native-object control takes
130 seconds in C. An earlier control overlapped a short peer Lean run and
was discarded for timing; the reported rerun has no such overlap. The original
monolithic book takes 299 seconds in Lean. The six focused sections take
28/26/51/53/73/33 seconds in Lean and 14/13/22/21/29/15 seconds in C, with the
full focused build above including their wrapper, parents and executable.
No memory guard stopped any reported run.

The temporary documentation edit was in
`QWitness.exists_psiCurveCompositionBaseChangeRealization`, cited only by
CommonSourceCovers. The full build rebuilt only Existence and the library
root, then that book section, its parents, its native object and the executable.
None of the 54 measured heavy library consumers rebuilt, and no other book
section rebuilt. The fixture was reverted before the canonical signatures,
bodies and full/book gates. A mathematical proof edit still needs its own
full gate; these measurements show the improved import fan-out.

Shared-checkout validation on 2026-10-07, with the same flags and guard:

| check | elapsed | sampled peak family RSS | minimum available RAM |
|---|---:|---:|---:|
| Full default `lake build` after source integration | 581.07 s | 12.00 GiB | 37.81 GiB |
| `lake exe book` | 14.08 s | 1.47 GiB | 39.91 GiB |
| Final full gate after book EOF whitespace cleanup | 132.71 s | 10.66 GiB | 36.52 GiB |
| Final `lake exe book` | 8.04 s | 1.55 GiB | 39.88 GiB |

All pass without a memory stop. The first full gate rebuilds the affected library
chain and all six new book sections; it is incremental, not project-clean.
The final gate follows removal of trailing blank lines in six new book sources;
no mathematical source changes in that cleanup. Fresh dumps from the shared artifacts repeat the 1082/1073 signature/body and
standard-axiom checks with exactly the reviewed exceptions and no additions.
The rendered shared book has the same 64 page paths as both private variants
and preserves the frozen notice. The 206-file library/root lexical audit
finds no placeholders or project axioms; `git diff --check` passes and no touched
file emits a deprecation warning. Only the nineteen reviewed source/doc paths
changed; no generated artifacts were copied to the shared build.

The green focused-module code checkpoint was committed and pushed as
`31864cd2c70831ebe70df9bffb98ead19dd30499` before the longer project-clean
experiment. Its full CI run also passes, as recorded above. Three native
round-trip kernel checks remain potential optimization work; they were not
claimed as completed kernel fixes. The measured gate below allows the next
mathematical checkpoints, with M4 re-planned against #12/#21 and the corrected
configuration targets.

### Project-clean measurements and gate acceptance

Both isolated worktrees use the `f6964f0` base. The candidate has exactly the
reviewed nine math modules, seven root imports and eight focused book sources
(including final EOF whitespace cleanup). Each regular `.lake/build` directory
was moved aside before its full default build. The same pinned dependency
snapshot remained populated: **neither run built any package output**. These
are whole-project clean-output builds with cached dependencies and warm OS
caches, not fresh-machine or dependency-clean benchmarks. The runs are
sequential, with no other Lean family, two Lean threads and the same 30 GiB
available-memory guard. This is one measured pair, not a statistical study.

| check | elapsed | sampled peak family RSS | minimum available RAM |
|---|---:|---:|---:|
| Original project-clean full build | 1131.89 s | 11.73 GiB | 34.93 GiB |
| Original HTML generation | 8.04 s | 1.56 GiB | 40.00 GiB |
| Refactored project-clean full build | 792.14 s | 12.27 GiB | 37.77 GiB |
| Refactored HTML generation | 8.04 s | 1.52 GiB | 40.33 GiB |

All four commands pass without a memory stop. Whole-project wall time falls
by 30.02% in this pair. Sampled family peak RSS is slightly higher with the
parallel leaves/book sections; the resource acceptance is the safe host
envelope, rather than a claim that every peak is lower.

The original run actually builds all 199 library/root modules and 417 project
tasks including native objects and the executable. The candidate builds all
206 library/root modules and 445 project tasks. Their task-set difference is
exactly the fourteen new math/book modules and their fourteen native objects;
no original task is missing or reused and no dependency task is rebuilt.
CommonSource/ReferenceBridge take 206/128 seconds originally and 98/33 seconds
in the candidate. Intrinsic restriction takes 48/26 seconds. The original
monolithic book takes 294 seconds in Lean and 131 seconds in C; the focused
sections and their native objects are all regenerated in the candidate.
Both rendered books retain the same 64 page paths and the candidate preserves
the six ordered subsections and frozen-work notice.

Fresh dumps from the project-clean candidate again match all 1082 signatures
and 1073 bodies with exactly the reviewed type/body and helper documentation/
privacy exceptions, no missing or additional constants or nonstandard axioms,
and equal exported metadata. Source hashes match the reviewed canonical
candidate; no generated artifacts are injected into the shared checkout.

The #18 acceptance criteria are met: warm full/book gates are 4.02/8.04 s,
the changed-leaf full gate is 84.41 s and avoids every unrelated heavy library
consumer and book section, reported resource measurements stay above the
30 GiB guard, and the module organization/timing/artifact/hygiene evidence is
recorded here. A core or genuinely upstream change can still require the
whole dependency chain; the measurement does not promise instant builds for
those edits. The old M4a route stays frozen.

Final shared gates for this measurement-documentation checkpoint pass:
`lake build` takes 12.10 s (sampled family peak 1.11 GiB, minimum available
40.84 GiB) and `lake exe book` takes 8.05 s (1.51 GiB, 40.52 GiB), with no
memory stop. The 206-file hygiene audit and final staged diff check also pass.
Only this continuation guide changes in the measurement checkpoint.

## Finite-base soundness checkpoint (#24)

The atom-clause specialization argument now works over any base field. It
specializes the zero substitution polynomial at two distinct elements of
`racl k {t}`, which is infinite because `t` is transcendental over `k`.
Both values and their nonzero difference lie in that closure, so division
recovers the line coefficients there. This contradicts their independence.
The new `infinite_racl_singleton` has the named consumer
`exists_two_specializations`; no new freshness assumption enters the
configuration soundness statements.

The witness proof, semantic Q/Q′/J soundness, their rank-five wrappers,
affine-grid-to-Psi implication and geometric sum/product wrappers no longer
require `[Infinite k]`. The audited three-join/fifteen-point extraction
interface and literal-table refutation remain intact. ACF completeness
still requires the explicit unproved hypothesis, the arbitrary-field
Q/Q′ Lean refutations in #25 remain open, and the blueprint derivation
calculation remains a separate obligation. The book describes the actual
specialization field.

Claude supplied the original private repair. Codex rebased it onto the
audited targets, independently compiled the exact 17-module reverse
chain with Mathlib standard linters (20.11 s, peak 2.65 GiB, minimum
available 40.71 GiB), checked all 22 selected strengthened/boundary
theorems for standard axioms, and compiled the revised book module
without warnings (10.05 s, peak 4.01 GiB, minimum available 40.36 GiB).
The integrated full `lake build` passed in 52.29 s (peak family RSS
8.35 GiB, minimum available 38.34 GiB), and `lake exe book` passed in
8.04 s (peak 1.55 GiB, minimum available 40.13 GiB). A fresh shared
probe checks all 22 theorem axioms and public statements; it finds only
standard axioms and no infinite-base binder. All 206 library/root Lean
files pass the placeholder/project-axiom scan. All 64 rendered HTML page
paths are preserved, the specialization prose is checked, and the frozen
group-chunk notice remains present. Touched modules have no deprecation
diagnostics. This is the finite-base item in #24, not completion of its
remaining foundational carryovers.

## Focused semantic j-coordinate and Frobenius-soundness checkpoint (#23)

`Config/JCoordinates` owns the semantic `jTupleOf` constructor and its
coordinate API. `Interpretation/FrobLinkSoundness` owns explicit geometric
sum/product witnesses and common-parameter links;
`Counterexamples/GenericArithmetic` now contains the literal predicates
and refutations. Existing public names are preserved. Four superseded
private helpers are replaced by the representative-calculus API or
Mathlib's `AlgebraicIndependent.ne_zero`. There are no duplicate aliases.

Eight new declarations have named consumers: generic triple-to-pair
selection and its nonvanishing lemma serve the refutations/links; power
transport of an independent pair, semantic tuple normalization and
positive Frobenius point normalization serve `frobEq_of_frobenius_twist`.
This theorem proves that semantic tuples whose parameters differ by a
positive Frobenius power satisfy `FrobEq`, using a fresh common-parameter
bridge. The displayed wrappers retain `[Infinite k]` and rank five;
removing their now-redundant infinite-base binders is a separate
strengthening. The converse and semantic completeness remain open.

Claude prepared the focused extraction. Codex independently checked all
six extraction/arithmetic modules on the pushed finite-base baseline
(34.17 s, peak 3.48 GiB, minimum available 39.69 GiB); the arithmetic
modules remain private pending their own checkpoint. Baseline/split
artifact comparisons cover 63/67 declarations and check placements,
axioms, statements, bodies and deny-list metadata. The only deletions
are the four superseded private helpers; the eight additions are exact.
Six statement differences name the replacement proof arguments.
Applying only the three explicit helper renames and private-name
normalization makes all common statement hashes identical and leaves
exactly three body differences: two Mathlib nonvanishing replacements
and one inlined pair-range proof. In particular both nonfunctional
existence refutation bodies agree under that exact ledger; reference-set
equality was not used as proof-body identity. The source edits were
reviewed directly. Later changes are module documentation and two
docstring line wraps only. The code was committed and pushed as `c171657`. Shared full `lake build`
passed in 22.11 s (peak family RSS 7.21 GiB, minimum available 38.45 GiB),
and `lake exe book` passed in 8.04 s (peak 1.53 GiB, minimum available
40.12 GiB). Fresh shared Sig/Proof/Rename probes preserve the reviewed
67 statements/values, exact eight additions/four private deletions, all
66 authored module placements and standard axioms. The on-demand
`jTupleOf.congr_simp` equation retains its original Counterexamples
consumer placement; an extra provenance assertion initially assumed the
constructor's module and was corrected against the actual baseline and
shared artifacts. The only additional signature differences are the two
documented docstring line wraps. Hygiene covers 208 library/root Lean
files. The 64 HTML page paths and frozen notice are preserved; the new
semantic soundness prose is present. Touched modules have no deprecations. Fixed-class arithmetic, totalization, ratio
semantics and the historical M4a chain remain open or frozen as before.

The documentation-only evidence follow-up also passes the required full
build (4.02 s) and rendered book (8.04 s).

## Generic meet/join arithmetic checkpoint (#23)

`Interpretation/JArith` implements the four subtraction and five division
meets from EH95 Lemma 2.11, Figures 4–5. Their independent-input coordinate
identities imply generic negation, inverse, addition and multiplication.
`JArithSem` uses the shared `jTupleOf` constructor, defines Point-valued
relations by those geometric operations, and proves their function
properties, independent-input unique outputs and semantic membership.
Rank-five soundness gives geometric J membership over any base field;
six redundant infinite-base binders are removed from these new wrappers.
No configuration completeness is used in the arithmetic computations.
The source/book status is updated; literal-refutation provenance stays
intact. The new book subsection documents the coupled construction.

Claude supplied the generic arithmetic and deduplicated semantic draft.
Codex independently checked the final two modules against the focused
main APIs (30.15 s, peak 3.47 GiB, minimum available 39.61 GiB), without
warnings. A 102-record canonical/final statement/body comparison finds
exactly the six strengthened membership wrappers and no other changes.
All 100 public artifact axiom reports are standard; excluding generated
equations, these cover 89 authored public declarations (theorems and
definitions). The shared full `lake build` passed in 48.27 s (peak family RSS 6.15 GiB,
minimum available 38.34 GiB); `lake exe book` passed in 8.04 s (peak
1.54 GiB, minimum available 40.02 GiB). Fresh shared signature/body
comparisons match the independently checked 102-record final artifacts
without exceptions; all 100 public axiom reports match the standard-axiom
review. Hygiene covers 210 library/root Lean files. All 64 existing HTML
page paths remain, and the coupled-arithmetic subsection adds one page
(65 total); its computation and open-boundary prose is checked. The
blueprint renders to 54 pages without undefined/overfull diagnostics;
the changed status paragraph on page 34 is visually reviewed. New
arithmetic modules compile without warnings.

Fixed-class/Frobenius correctness, extension to all input pairs, totalized
field operations and ratio semantics remain open. This checkpoint proves
the generic coordinate computations and preserves the corrected
configuration completeness boundary.

## Specific Q/Q′ counterexample prerequisites (#25)

Three focused modules support the named `Counterexamples.QDescent`
targets over ℚ(s,t,e₁,e₂,e₃): `Closure/RationalFunctions` proves that
algebraic elements over the coefficient field are constants and that a
nonzero constant times a variable is not a square;
`Correspondence/WeightedSupport` proves algebraicity of `s/u²` from a
`(2,1)`-weighted-homogeneous equation and its support-pair criterion;
`Correspondence/MultiplicativeQuotient` derives interalgebraic coordinate
quotients from common nonzero coset exponents, and applies the existing
multiplicative correspondence theorem with its ACF/freshness hypotheses.
The integer-power closure helper is made public for that named consumer;
its type and proof are unchanged. No second correspondence classification
or duplicated helper is introduced. These facts are prerequisites; the
concrete Q/Q′ geometric witnesses, semantic contradiction and general
completeness statements are not proved by this checkpoint.

Claude prepared the lemmas. Codex independently compiled all four modules
(6.03 s, peak 2.30 GiB, minimum available 40.57 GiB) and verified nine
standard-axiom reports including the promoted helper. The strict
71→79 signature and 68→76 body comparisons have exactly eight new
lemmas and no existing type/body change; only the single helper privacy
flag changes, and exported deny-list metadata is unchanged. Subsequent
source edits are module documentation only. The book identifies the
remaining concrete-witness and semantic-contradiction obligations.
The shared full `lake build` passed in 52.30 s (peak family RSS 10.27 GiB,
minimum available 37.45 GiB), and `lake exe book` passed in 8.04 s
(peak 1.53 GiB, minimum available 40.02 GiB). Fresh shared 79-record
signature and 76-record body comparisons match the independent review
without exceptions; all nine selected theorem axiom reports match,
and each new lemma's authored module placement is checked. The existing
`Multiplicative` source changes only at the single visibility word. Hygiene
covers 213 library/root Lean files. All prior HTML paths remain (65 pages
total); the new prerequisite prose and remaining obligations are checked.
Touched modules have no deprecation diagnostics.

## Algebraic-base lattice and configuration lift (#7, #25)

`Transfer/Lift` now proves closure trace, an injective order-preserving
closed-field lift, bottom/finite-join preservation, exact matroid rank
and point transport along a k-embedding with an algebraic enlarged base.
Over an algebraically closed overfield it preserves binary meets. Its
finite-generator atom-capture transfer uses the existing one-quantifier
theorem and needs no transcendence-degree or infinite-base hypothesis.
`Transfer/LiftConfig` lifts partial quadrangles, full Q witnesses and
Q/Q′ configurations. It reflects partial quadrangles and multiplication
diagrams of lifted points, and reflects a Q witness when the three
clause-(vi) quadrangle witnesses are explicitly supplied as K-points.
It asserts no general descent of existential witnesses. Neither module
imports the private JAssembly completeness interface. Their named
consumers are the remaining point-level J arrows and the explicit
`Counterexamples.QDescent` geometric witnesses. Both concrete #25 Lean
refutations and unconditional J ACF completeness remain open.

Claude supplied the drafts. Codex compiled both against main 3061254
(6.00 s, peak 2.42 GiB, minimum available 40.31 GiB), repairing two
reflection proof rewrites for the A/C joins without changing statements.
The historical configuration-lift block is preserved verbatim. An
independently compiled reduced historical block permits an exact
37→41 signature and body comparison: four explicitly reviewed reflection
additions, zero existing type/body changes, and unchanged deny metadata.
All 41 public axiom reports use only standard axioms. The book corrects
its stale finite-base and arbitrary-field Q/Q′ status prose.
The shared full `lake build` passed after the module-documentation line
wrap (20.01 s, peak family RSS 10.49 GiB, minimum available 39.31 GiB),
and the rendered book passed in 8.00 s (peak 1.55 GiB, minimum available
39.79 GiB). Fresh shared signatures, bodies, axiom reports and explicit
reflection statements match the independent review exactly, including
the K-valued quadrangle hypothesis. The 41 artifact records cover 40
authored public declarations and one generated congruence theorem;
all authored/generated module placements are checked. Hygiene covers
215 library/root files, all 65 HTML paths are preserved, and the
finite-base/counterexample/completeness/frozen notices are verified.
Both new modules have no diagnostics. The eight prerequisite lemmas'
preceding commit 3061254 now has successful full CI.

## Semantic J assembly and point-level descent (#6, #7)

`Config/JAssembly` assembles semantic Q and two Q′ projections into one
semantic J tuple over an algebraically closed pair of rank at least five.
It aligns their additive/multiplicative correspondences through affine
Frobenius and shifted-binomial rigidity. Geometric J completeness is
packaged as `JCompletenessACF` and reduced to explicit ACF Q/Q′
completeness hypotheses; these inputs remain unproved. Its shifted
binomial lemmas are also the named prerequisites of the reviewed
Frobenius-incidence converse, avoiding a second proof family.
`Transfer/JDescent` proves point-level (1)⇔(2) for perfect K of rank at
least five and geometric (4)⇒(3). With the existing finite-base (1)⇒(4),
it packages J equivalence under explicit `JCompletenessACF`, including
the canonical algebraic closure form. No infinite-base assumption or
arbitrary-field Q/Q′ equivalence enters these arrows. The unconditional
T4 completeness obligation stays open.

Claude supplied the drafts and extracted the already integrated
configuration-lift block from JDescent. Codex independently compiled the
remaining two modules on main 2f25a78 (6.00 s, peak 2.74 GiB, minimum
available 40.15 GiB), without diagnostics. A fresh historical/full versus
focused comparison covers 77→81 signature and body records with zero
existing changes; the only four additions are the reflection lemmas
already on main in 2f25a78. All 40 public declarations of these two new
modules have standard axiom reports. The conditional hypotheses are
inspected in the emitted statements. The book adds a semantic-assembly
section and updates the point-descent status; the blueprint correction
records the still-open ACF inputs. Lift checkpoint 2f25a78 has successful
full CI.
The shared full `lake build` passed in 36.01 s (peak family RSS 11.68 GiB,
minimum available 38.14 GiB); `lake exe book` passed in 8.00 s (peak
1.55 GiB, minimum available 39.80 GiB). All 81 shared signature/body
records, the 40 axiom reports and six inspected conditional statements
match the independent review exactly. The two new modules contribute
29 semantic-assembly and 11 point-descent declarations, with unchanged
source bodies and no diagnostics. Hygiene covers 217 library/root files.
All 65 prior HTML paths remain, and one semantic-assembly page is added
(66 total); conditional-completeness, concrete-refutation and frozen
boundaries are checked. The revised blueprint renders to 54 pages
without undefined/overfull diagnostics; the changed status on page 31
is visually reviewed. Claude acknowledged the source-only geometric
consumer task after the corrected chit resend and retains no build slot.

## Frobenius incidence rigidity and semantic consumers (#23)

`Interpretation/FrobLinkRigidity` proves that concurrence of the three
closure lines forces the parameters to differ by a natural Frobenius
power, over an algebraically closed pair. Its scaled-locus argument
reads both signed characters from one support pair, extracts common
primitive exponents and applies shifted-binomial rigidity from the
existing JAssembly chain. `FrobLinkRelative` transfers the algebraic
facts to an algebraically closed overfield/algebraic base and reflects
the exact conclusion along the embedding. `FrobLinkSemantic` consumes
the geometric concurrency, rank and parameter clauses with explicit
semantic endpoint equations over any base. `FrobEqForward` composes
the two twists under an explicit semantic-middle-tuple hypothesis;
the canonical form names perfection, rank five and unproved ACF
`JCompletenessACF`. No unconditional bridge completeness, original
common-representative alignment, setoid law or field operation law
is claimed. These results retain the original geometric predicates.

Claude supplied the canonical drafts. Codex compiled all four on main
a8233d8 (6.00 s, peak 2.65 GiB, minimum available 40.19 GiB) and checked
a final focused version (6.00 s, peak 2.65 GiB, minimum available
40.17 GiB), without diagnostics. The final core module is named
FrobLinkRigidity. Three duplicate/one-use helpers are removed in favor
of Mathlib's unit theorem and the existing point-representative API.
An exact 24→21 signature/body comparison has these three deletions,
exactly two proof edits, zero surviving statement changes and unchanged
deny metadata. All 21 public authored theorems have standard axiom
reports; the five displayed rigidity/conditional-converse interfaces
are inspected. Module documentation changes only after the reviewed
proofs are accepted. The source/book identify the still-open
common-representative and completeness obligations.
The shared full build passed in 26.01 s (peak family RSS 10.15 GiB,
minimum available 38.07 GiB); the rendered book passed in 8.00 s
(peak 1.55 GiB, minimum available 38.67 GiB). Fresh shared 21-record
signatures/bodies, axiom reports and five typed interfaces match the
independent review exactly. All 21 authored module placements and
proof-source bodies are checked; final module-documentation edits are
the only source differences. Hygiene covers 221 library/root files.
All 66 existing HTML paths remain, and the semantic/completeness,
infinite-base soundness-wrapper and frozen boundaries are verified.
The revised blueprint renders to 54 pages without undefined/overfull
diagnostics; its changed status across pages 32–33 is visually checked.
The four new modules have no diagnostics. The preceding semantic J
assembly/point-transfer commit a8233d8 now has successful full CI.


## Concrete Q/Q′ refutations (#25)

Counterexamples/QDescent reflects the explicit table-7.1 and table-7.2
witnesses and the eight-point multiplication diagram from an algebraic
closure. All supplied points arise by images, inverses or squares of
elements of K. Its Q/Q′ consumers need five independent elements over
the base; no geometric completeness hypothesis or general witness
descent theorem is used.

Counterexamples/QSemantic proves the characteristic-zero obstruction:
semantic representatives for ([s],[st²],[s(1+t)²],[t]) force s/x² to be
algebraic. It fixes one curve polynomial before both scaled loci,
derives characters at one support pair, and uses the signed-character
result at exponential characteristic one to fix y/x=t. Applying the
first character to every support pair gives (2,1)-weighted homogeneity.
The Q′ ratio follows from the multiplicative-quotient theorem with an
explicit fresh independent element. Algebraic-base invariance and
ambient transport return the obstruction to the original fields.

Counterexamples/QRefutation combines the explicit geometric witnesses
with the semantic obstruction. Both correctness assertions fail over
FractionRing (MvPolynomial (Fin 5) k) for every characteristic-zero k.
Closure/RationalFunctions contains the generic independent-variable
lemma and proves X_i/x² transcendental for nonzero x from its existing
constant-element/nonsquare theorems. Test/RationalFunctionField now uses
that generic independence lemma instead of duplicating its proof.
The original geometric definitions and withdrawn statement provenance
remain; both specific refutations are proved, while general witness
descent, corrected arbitrary-field semantics and ACF completeness are
separate open obligations.

Claude supplied source-only drafts and a source fidelity/dependency
audit. Codex independently compiled owned copies against 4b66682. The
geometric draft needed two finite-vector elaboration repairs; the
semantic/refutation draft was immediately proof-green. The final
focused chain fixes the three style diagnostics, removes the JArith
import by direct membership rewrites, and drops unused algebraic-closure
assumptions on exactly four pure helper statements. The independent
artifact ledger preserves every other statement, all module placements,
and only the nine corresponding new proof edits plus the one existing
acceptance-test deduplication. All 28 new authored public theorems use
standard axioms; typed interfaces verify both generic characteristic-zero
and rational concrete refutations, perfection, rank at least five and
relatively algebraically closed constants. For the private rational
specialization probe, the canonical coefficient-field algebra instance
is selected explicitly; the two Mathlib rational-algebra instances are
propositionally equal but not definitionally equal.
The final independent focused chain passed in 12.00 s (peak family RSS
2.76 GiB, minimum available 39.76 GiB) without diagnostics. A strict
40→40 signature/body ledger includes the existing nine-declaration
rational-function acceptance module: four helper statements strengthen,
exactly ten proof edits match the reviewed scope, and no declarations
are added or removed relative to the compiled draft/test baseline. All
40 public declarations have standard axiom reports; the 28 new authored
theorems occupy the intended modules. The seven typed interfaces pass.
The shared full build passed in 42.01 s (peak 10.83 GiB, minimum available
37.76 GiB); the book passed in 8.00 s (peak 1.53 GiB, minimum available
39.55 GiB). Fresh shared signatures, proof bodies, all axiom reports
and typed interfaces match the independent artifacts exactly (6.00 s,
peak 2.60 GiB, minimum available 40.00 GiB). Hygiene covers 224
library/root files. All 66 existing HTML paths remain; both refutations,
their seven docstrings, open general-descent/ACF boundaries and the
frozen M4a notice are checked. The revised blueprint renders to 54
pages without undefined/overfull diagnostics, and pages 31–32 are
visually reviewed. The final prerequisite documentation reflow and
this validation record receive the mandatory repeated build/book gates.


## Foundation transport, existence and naturality (#24, #10)

`Closure/CrossBase` proves equivariance of relative closure and closed-lattice
transport for a field isomorphism carrying one base image onto the other.
It constructs the induced compatible scalar isomorphism and proves the
identity/composition/inverse transport laws. Compatibility is an explicit
hypothesis; no reconstruction or completeness input is assumed.

`Geometry/Transport` extends a closure-preserving point equivalence uniquely
to an order isomorphism and recovers the original point map. Order
isomorphisms preserve finite independence, finite geometric rank and
arbitrary independent representative families. Transcendence degree is
invariant, with universe lifts when necessary, and exact finite geometric
rank agrees with the transcendence degree of the closed intermediate field.
No infinite-base or perfect-field hypothesis is needed for these interfaces.

`Perfection/Existence` supplies a chosen perfection in every exponential
characteristic using the relative perfect closure inside an algebraic
closure. This focused leaf keeps the algebraic-closure constructor out of
the existing Subfield/Lattice dependency cone. The existing `ofCharZero`
constructor and its rational-function acceptance consumer are unchanged.
`Perfection/Naturality` extends a field isomorphism uniquely to arbitrary
chosen perfections, proves its groupoid laws, and transports perfected
subfields and compatible perfected bases. The perfection lattice
isomorphisms intertwine this transport; the identity field map compares two
choices and acts as the identity on the original closed-field lattice.

Claude audited the frozen source drafts and their blueprint consumers with
no builds or main edits. Codex independently compiled owned snapshots
against `8798315`, removed exactly two unused helpers, and made exactly two
proof edits: the deprecated `if_pos` becomes `ite_eq_left` in the existing
`Perfection.isRAC_perfIF`, and `haveI` becomes `have` in the new
transcendence-basis/closure bridge. All 113 surviving declaration statements,
definition bodies, attributes and declaration docstrings match the original
115-record draft ledger. The two constructor/instance declarations move
byte-for-byte from Subfield to Existence. The previous-main 55-record ledger
is preserved, with only the documented existing proof edit. There are 57
new authored declarations and one reviewed generated `baseRingHom.eq_1`;
all 110 public definitions/theorems have standard-axiom reports.

The final six-module independent compile passes without diagnostics in
6.00 s (peak family RSS 1.14 GiB, minimum available 40.10 GiB). Nine typed
interfaces pass, including arbitrary-characteristic existence, the ZMod 3
constructor, closure-compatible point transport, rank/trdeg agreement,
cross-base closure transport, naturality and comparison of two choices.
The shared full build passes in 680.21 s (peak 12.06 GiB, minimum available
37.86 GiB); it recompiles the dependents of the foundational documentation
corrections. The rendered book passes in 8.00 s (peak 1.56 GiB, minimum
available 39.88 GiB). Fresh shared signatures, proof bodies, public axiom
reports and all nine interfaces match the independent artifacts exactly
(6.00 s, peak 2.42 GiB, minimum available 40.43 GiB). Hygiene covers 228
library/root files. All 66 existing HTML paths remain among 69 pages; the
new transport/naturality sections, all displayed interfaces, preserved
representative calculus and frozen M4a notice are checked. The blueprint
renders to 55 pages without undefined/overfull diagnostics; the new
foundation status on page 11 and the following page are visually reviewed.
This final documentation record receives the mandatory repeated full-build
and book gates before commit.

At that transport checkpoint, explicit `Induces` packaging remained open
(#24); the next checkpoint below completes it. The literal/quotient functors,
existence of reconstruction and uniqueness-up-to-Frobenius converse remain
open (#8–#10). The source-only design audit for `Induces`
distinguishes the intersection formula (no extra base hypothesis) from
recovery of the literal perfected bases (both bases relatively algebraically
closed), as required by the main theorem's context. No checkbox for these
remaining obligations was discharged by that transport checkpoint.


## Explicit induced-map interface (#24, #10)

`Perfection/Induces` implements the blueprint's exact equality of perfected
closed subfields. Its membership theorem gives the intersection formula as
preimage along the target inclusion; the inducing field map determines its
lattice map uniquely. At the bottom it always transports the perfected
relative algebraic closures of the bases. Recovery of the literal perfected
bases explicitly assumes both bases relatively algebraically closed, as in
the main theorem. The contextual qualification and a source-level example
with ℚ and ℚ(√2) were recorded on #24 before the draft and source clarification.

A compatible isomorphism of chosen perfections induces the conjugated
closed-lattice map, without a rank or extra base hypothesis; inducing is
exactly equality with this map. Original field isomorphisms induce their
direct closed-field transport through the unique perfection extensions.
The identity compares two choices and induces the identity lattice map.
Integral Frobenius twists of an inducing field map induce the same map.
The converse uniqueness-up-to-Frobenius implication remains open, as does
existence of a field map for an arbitrary lattice isomorphism and full
literal/quotient functorial assembly (#8–#10).

Claude supplied a frozen 155-line source-only draft against the accepted
foundation inputs; Codex verified the source/input hashes and independently
compiled it against `665ee50`. The original source compiled unchanged and
without diagnostics. A coercion rewrite in the private set-preimage test
harness was repaired using `Subfield.mem_map`; no public source change was
needed. The final module changes only its status documentation, and its
namespace is byte-for-byte the original. The exact 14→14 signature/body
ledger preserves all statements, bodies, attributes, declaration docstrings
and exported deny-list metadata. It comprises ten authored public APIs,
one private bottom helper, and three explicitly audited generated public
lemmas: `Perfection.inducedIso.eq_1`, `Perfection.inducedIso.congr_simp` and
`CrossBase.closedIFMap.congr_simp`. All three are emitted in the Induces
module; their namespace prefixes do not change their module placement.
All 13 public and the private-helper axiom reports use standard axioms.

The final private compile/probe gate passes in 6.00 s (peak family RSS
2.45 GiB, minimum available 40.07 GiB). Nine typed interfaces pass, including
the actual set-preimage formula, unique lattice map, explicitly qualified
base recovery, assumption-free compatible converse, Frobenius invariance,
two-choice comparison and agreement with original field transport. The
shared full build passes in 24.01 s (peak 8.27 GiB, minimum available
38.16 GiB); the rendered book passes in 8.00 s (peak 1.56 GiB, minimum
available 39.81 GiB). Fresh shared signatures, proof bodies, public axiom
reports and all nine interfaces match the independent artifacts exactly
(6.00 s, peak 2.42 GiB, minimum available 40.30 GiB). Hygiene covers 229
library/root files. All 69 existing HTML paths remain among 70 pages; all
ten displayed interfaces, base hypotheses, remaining reconstruction
boundaries and frozen M4a notice are checked. The blueprint renders to 55
pages without undefined/overfull diagnostics; pages 5, 11 and 12 are
visually reviewed. This final documentation record receives the mandatory
repeated full-build and book gates before commit.

The foundational #24 checklist is complete with this explicit interface.
The public reconstruction existence, full uniqueness and functorial
milestones remain open; the U3–U5 checkboxes in #10 are not discharged.


## Frobenius kernel, two-generic intersection and rank refutation (#9)

The kernel theorem is proved with an explicit rank-five hypothesis:
`exists_eq_frobeniusZPow_of_point_fixed` applies to every field automorphism
of a perfect field fixing the transcendental points. It needs neither base
preservation nor a relatively closed base. The proof transports elementwise
j-rigidity through algebraic closures, compares independent pairs using fresh
elements and recovers algebraic elements by addition and cancellation.
`eq_refl_of_point_fixed` gives characteristic-zero identity; the independent
`frobeniusZPow_injective` clause needs only a transcendental element and
positive characteristic.

The displayed source theorem had omitted the rank hypothesis, despite its
proof and the main target using it. This was reported on #9 before any source
change. `Counterexamples/KernelRank.not_forall_eq_refl_of_point_fixed` refutes
the rank-free characteristic-zero claim over ℚ(t)/ℚ and records the
relatively closed base. The local translation fixes every point and moves t.
The corrected blueprint retains the full original displayed wording from
`641a09e` in source comments and an audit remark. Five typed refutation
interfaces check characteristic zero, perfection, relative closedness,
the literal refutation and preservation of the coefficient field.

`racl_pair_mul_inf_racl_pair_mul` proves the literal two-generic intersection.
Its helper `racl_insert_inf_racl_insert` is an infimum-equality wrapper around
the existing `mem_racl_of_mem_racl_insert` and accepts arbitrary base sets:
finiteness and the other element's freshness are unnecessary. The all-point
recovery half of R3 remains open. The bypassed #11 linear-disjointness
obligations also remain open.

Claude supplied and source-audited the frozen drafts; Codex independently
compiled immutable original, split and final snapshots against `641a09e`.
The original→split ledger preserves all 46 declarations, with five authored
Frobenius APIs plus their generated equation moved and one held-consumer iff
temporarily added. Final cleanup removes that unused iff and two duplicate
helpers; the surviving kernel statements are unchanged. The 47→44 ledger
records one generic intersection statement strengthening, the shared
`Perfection.frobZPow` definition body, its generated equation type and four
theorem proof edits. The nested generated proof renaming in exponent
separation is matched only by identical theorem-statement keys, including
numeric underscore suffixes; no blanket type normalization is used.

The counterexample has one authored declaration and the public generated
`AclGeom.Test.t.eq_1` emitted in its module. Its source-only draft needed
explicit M1 type parameters and restricted generator simplification; no
heartbeat increase was used. A final collaborator review generalized the
statement from ℚ to every field and quantified base-preserving algebra
automorphisms explicitly, removing the temporary coefficient-algebra
instance priority. The exact ledger records this authored statement/docstring
and proof strengthening; the generated equation's type and proof are unchanged. All 46 combined public declarations use only standard axioms, every
generated declaration has an explicit module placement, and all 15 typed
interfaces pass. The common Frobenius implementation also preserves the
original perfection group-power expression definitionally and the existing
Induces forward fibre law.

After the counterexample strengthening and line-length cleanup, the full
shared library build passed in 16.00 s (peak family RSS 10.60 GiB, minimum
available memory 37.29 GiB); the book passed in 10.00 s. All 46 shared
signature/proof/axiom records match the independent final artifacts exactly,
and all 15 interfaces pass (10.00 s, peak 2.56 GiB, minimum available 38.31 GiB).
Hygiene covers 232 library files. All 70 previous HTML paths remain among
76 pages; the new chapter's eleven displayed docstrings, rank qualification,
open recovery/linear-disjointness boundaries and frozen 117-declaration
notice pass review. The blueprint is 55 pages; pages 39–40 were rendered
and visually checked, with no undefined references or overfull boxes.
Final documentation build/book and staged-byte/push gates are required before
the checkpoint commit. U1 and the intersection part of R3 are this
checkpoint's scope; R1/R2/R4, recovery of all points, reconstruction existence,
full functorial assembly, M4 and the held FrobEqCorrect/L2 work remain open.


## Supplied-endpoint uniqueness and the Frobenius fibre (#9, #10)

`Reconstruct/Uniqueness` proves the uniqueness clause of the main target
for explicit inducing isomorphisms of arbitrary chosen perfections.
`Induces.point_symm_trans` shows that their target difference fixes every
principal closure, without rank or relatively closed base hypotheses.
The same Induces equations identify the image of every perfected closed
subfield; the perfection lattice isomorphism makes these all target closed
subfields. An order isomorphism of the original lattices and the target
perfection order isomorphism transport source rank five to the perfected
target, with universe lifts handled by the existing transport API.

The kernel yields `Induces.exists_eq_trans_frobZPow` with the correct
orientation `Φ₂ = Φ₁.trans (ρ.frobZPow n)`. Together with the accepted
forward invariance, `Induces.iff_exists_eq_trans_frobZPow` describes the
full fibre once one inducing map is supplied. The independent
`trans_frobZPow_injective` clause takes the lattice isomorphism and rank
explicitly, with no unused Induces hypothesis. `Induces.eq_of_p_eq_one`
gives literal uniqueness in characteristic zero. No agreement of the two
recorded exponential characteristics, target-rank or relatively closed-base
hypothesis is added. Reconstruction existence and assembly remain open.

Claude supplied the frozen source-only drafts; Codex verified both draft
hashes and all six input hashes against pushed `76484ae`. The draft note
still named `641a09e` with working-tree kernel candidates; chit #3663
confirmed, and the independent ledger verified, that these inputs are exactly
the pushed kernel checkpoint. The raw draft compiles unchanged and preserves
all 15 old declaration signatures and normalized proof bodies.

The final 22→22 ledger has zero statement, attribute, docstring or definition
body changes. Exactly two existing Kernel theorem proofs now use the shared
`frobeniusZPow_eq_one_of_eq_one`, removing duplicated characteristic-zero
computations. There are six new authored public theorems, one private shared
rank helper and no new generated declarations; the existing
`frobeniusZPow.eq_1` has an explicit placement check. All 21 public reports
and the private helper use standard axioms. Twelve identical original/final
typed interfaces pass, including independent universe levels, original-field
characteristic zero, characteristic three, original compatible transport
and the comparison of two arbitrary choices of perfection.

The full shared library build passes in 24.02 s (peak family RSS 8.07 GiB,
minimum available memory 34.85 GiB), and the rendered book passes in 10.00 s.
The isolated reconstruction chapter required its explicit Uniqueness import;
that integration error was fixed before these gates passed. The exact 22
shared signatures/proofs, 21 public standard-axiom reports, private helper and
all twelve interfaces match the independent final review (8.00 s, peak
2.54 GiB, minimum available 36.58 GiB). The unchanged Induces namespace is
byte-checked. Hygiene covers 233 library files; all 76 previous HTML paths
remain among 77 pages, with the six new displayed docstrings and explicit
source-rank/endpoints/open-existence boundaries checked. The 55-page blueprint
has visual review of pages 40–42 with no undefined references or overfull boxes.

Visual review also found the old assembly paragraph still claiming a complete
proof of existence. This status overclaim was reported on #9 before correction;
the original phrasing is retained in source comments. The target and planned
interface are unchanged, while the assembly text now explicitly depends on the
open interpretation and recovery inputs. Final documentation build/book and
staged-byte/push gates remain required before the checkpoint commit.
The supplied-endpoint uniqueness half is this checkpoint's scope. R1/R2/R3b/R4
recovery, reconstruction existence, full functorial assembly, M4 and the held
FrobEqCorrect/L2 work remain open.


## Conditional point recovery and atomistic extension (#9)

`Reconstruct/Points` now proves `eq_closedIFMap_of_point_eq`: a compatible
field isomorphism agreeing with the prescribed lattice isomorphism on
principal closures outside `racl {a}` induces the whole lattice map.
Compatibility and that outside-point formula are explicit hypotheses.
They are the outputs of still-open base recovery R1 and scalar elimination
R2, rather than claims that those tasks have been proved.

The proof follows a shorter route than the blueprint's meet/intersection
argument. Exchange identifies every point represented inside `racl {a}`
with the single exceptional point. Two bijections agreeing away from one
point agree there as well; the existing `latticeIsoOfPointEquiv_unique`
then identifies the lattice maps. No rank, freshness or relatively closed
base assumption is needed. The parameter may be algebraic. The existing
`ClosedIF.mem_point_symm` supplies the exchange step, avoiding a duplicate
representative-transcendence calculation.

`CrossBase.closedIFMap_point` supplies point transport for the compatible
isomorphism and immediately yields the all-point formula. Its narrow import
changes from `Closure.ClosedLattice` to `Geometry.Points`, the module defining
principal closures; there is no cycle. The Points skeleton drops its broad
`Reconstruct.Base` import in favour of CrossBase and Geometry.Transport.
The only public additions are these two blueprint-facing theorems, with
one private bijection helper and no new generated declarations.

Claude supplied frozen source-only drafts; Codex independently verified the
two hashes and seven dependencies against pushed `33c4d07`. The private
compile exposed a default-simplifier rewrite from a representative's
principal closure back to its point. The reviewed original uses narrowly
listed singleton/point-membership rewrites. A follow-up harness typo used
the namespace-qualified singleton lemma, which was corrected before the
green private original gates. The frozen source files remain preserved.

The 22→25 ledger preserves all 22 old signatures and raw proof/body hashes
exactly, including generated `CrossBase.baseRingHom.eq_1` and its module.
Reviewed original and final 25-record signatures agree completely:
statements, attributes, declaration docstrings and definition bodies do
not change. The sole proof cleanup is the new point theorem's use of the
existing point-exchange API. All 24 public reports and the private helper
use standard axioms.

Eight identical original/final typed interfaces pass with independent
universe levels. They test principal-closure transport, the precise
conditional lattice equality, every point, every closed-field image,
the lift to chosen perfections and its inducing relation, perfected-lattice
conjugacy back to original fields, an algebraic zero parameter and identity
specialization.

The full library build passes in 50.01 seconds (peak family RSS 10.25 GiB,
minimum available memory 34.25 GiB), and the rendered book in 14.00 seconds.
The shared artifact check reproduces the exact 25-record signature/proof
ledger, 24 public standard-axiom reports plus the private helper, and all eight
typed interfaces (6.00 seconds, peak 2.32 GiB, minimum available 37.24 GiB).
The code sources are byte-exact with the private accepted candidate.
Hygiene covers 233 library files. All 77 old HTML paths remain among 78 pages,
with both new docstrings, explicit hypotheses, open recovery and the frozen
117-item notice checked. The blueprint renders in two passes without undefined
references or overfull boxes, now 56 pages; pages 38–43 were visually reviewed.
Final documentation build/book and the exact five-path staged-byte gate follow
before commit and push. R1/R2, unconditional R3b/R4, reconstruction
existence and final assembly remain open. The two-generic intersection
remains a proved blueprint lemma despite the different propagation proof;
#11's bypassed obligations, frozen M4a and held FrobEqCorrect/L2 are unaffected.


## Conditional Frobenius-link equivalence and fixed-class description (#23)

`Interpretation/FrobEqCorrect` proves the exact Frobenius-link equivalence
for supplied semantic endpoints, both with natural powers in either orientation
and with integer Frobenius powers. The immediate consumer
`frobEq_jTupleOf_iff` identifies the class of `j(x₀,a)` with all semantic
tuples `j(x,a)` having the same literal parameter. A geometric endpoint is
made semantic by the existing J descent API, and inverse Frobenius normalizes
its parameter without moving any closed point.

Perfection, source rank five and the still-open ACF `JCompletenessACF`
input are explicit. No relatively closed base or infinite-base hypothesis is
added. The predicates remain the original geometric `FrobEq` and `J`.
The natural/integral conversion `exists_frobeniusZPow_iff`, previously held
for lack of a landed consumer, now has the immediate literal-equivalence
consumer. There are exactly four new public theorems and no new private or
generated declarations.

Seven `FrobLinkSoundness` wrappers lose redundant `Infinite k` hypotheses:
the independent sum/product witnesses and five Frobenius-class soundness
theorems. The existing arbitrary-base rank-five configuration soundness
already supplies their proofs. A narrowly defined check removes only an
unused forall binder of type `Infinite` and proves all fourteen old
remaining types structurally identical; exactly seven such binders disappear.
Their seven type/proof hash changes are ledgered. All other old signatures,
attributes, declaration docstrings, definition bodies and raw proof bodies
remain exact. The old generated `frobeniusZPow.eq_1` placement is explicit.

Claude supplied frozen source-only drafts. Codex verified two draft hashes
and seven main dependency hashes against `7681ac3`, together with the
owned finite-base Soundness input `9427859f`. The frozen draft compiles
unchanged. Reviewed original and final eighteen-record signatures and raw
proof bodies agree exactly; all eighteen public declarations use standard
axioms. Fourteen identical original/final typed interfaces test all seven
finite-base wrappers, generic exponent conversion, the two semantic
equivalences, same-parameter class description, characteristic-zero literal
parameter equality, anchor-independent class membership and finite-base
class membership. The characteristic-zero test has no finite-base assumption.
A harness namespace typo and accidental literal Status newline escapes were
repaired privately before the green gates; no main code contained placeholders.

The R1/R2 displayed proofs depend on the refuted literal RatioEq/JMul semantics.
This dependency was reported on #23 and #9 before adding a source warning.
The original propositions and proofs are preserved. Their outputs remain the
explicit inputs of conditional point propagation, rather than proved recovery.

The full library build passes in 48.01 seconds (peak family RSS 8.33 GiB,
minimum available memory 33.94 GiB), and the rendered book in 10.00 seconds,
with no touched-module diagnostics. The shared check reproduces all eighteen
signatures and raw bodies, standard-axiom reports and fourteen interfaces
(6.00 seconds, peak 2.61 GiB, minimum available 36.70 GiB); code bytes match
the private accepted candidate. Hygiene covers 234 library files. All 78 old
HTML paths remain among 79 pages; all four new docstrings, explicit completeness,
finite-base soundness and open class-operation boundaries pass inspection.
The frozen 117-item notice is retained. The first TeX render found an overfull
line joining long theorem names; splitting the sentences fixes it. Two-pass
TeX now has no undefined references or overfull boxes and remains 56 pages,
with visual review of pages 32–34 and 38–40. The original R1/R2 propositions
and proofs and the FrobClass namespace are byte-exact with the pushed baseline.
The continuation-text integration assertion needed a documentation-only match
repair before acceptance; all eight scoped paths are now complete. Final
full build/book and exact staged-byte checks follow before commit and push.
Unconditional ACF completeness, the original simultaneous-representative
calculation, setoid laws, the coordinate bijection, corrected fixed-class
operations, ratio semantics, totalization, R1/R2 and reconstruction existence
remain open. The frozen M4a chain is untouched.


## Coordinates on the fixed Frobenius class (#23)

`Interpretation/ClassCoordinates` proves blueprint Lemma `mu-bij`.
`eq_of_jTupleOf_eq` shows that two tuples with the same literal parameter
coincide only if their first field coordinates coincide. It uses rank-five
freshness and the accepted arbitrary-field j-rigidity, with the exponential
characteristic chosen internally as `ringExpChar k`. The transcendental
parameter separates natural Frobenius exponents; in characteristic zero
Frobenius is the identity. This injectivity needs no perfection, relative
algebraic closedness, infinite base or configuration-completeness input.

`jClassEquiv` is the actual coordinate equivalence from the geometric
`FrobEq` class of `j(x₀,a)` onto the elements outside `racl k {a}`.
The inverse sends such an element to its semantic tuple, with independence
supplied by exchange. Surjectivity onto the geometric class uses the accepted
class description, keeping perfection, rank five and ACF `JCompletenessACF`
explicit. `jClassEquiv_jTupleOf` gives the blueprint evaluation formula
`μ(j(x,a)) = x`. These are three public declarations with two private
helpers, all consumed by the displayed coordinate bijection. No generated
declaration is introduced.

Claude supplied the frozen source-only draft `5ce5c0fb`. Codex verified
all eight dependency hashes against pushed `2ec826b`, then compiled it
independently. The initial bijective-constructor placeholders did not infer
the independence proof terms through the private encoding definition; the
reviewed original supplies the existing private proofs explicitly. Frozen
source provenance is retained. Original and final five-record signatures and
raw proof/definition bodies agree exactly, with unchanged statements,
attributes and declaration docstrings. All three public and both private
axiom reports are standard, including the private encoding definition.

Nine identical original/final interfaces pass with independent universe
levels. They include arbitrary-field, finite-base and characteristic-zero
injectivity, the actual geometric-class/domain equivalence, bijectivity,
coordinate evaluation, inverse encoding, every outside-closure coordinate
and a finite-base equivalence. The equivalence-valued harness examples were
marked noncomputable, and private Status newline escapes were corrected
before the green gates. Main code contains no proof placeholders.

The full library build passes in 38.01 s (8.19 GiB sampled peak family RSS,
minimum 34.45 GiB available); the book passes in 10 s. Shared probes pass in
8 s, reproducing all five signatures and raw bodies exactly, both private
and all public standard axiom reports, and the same nine typed interfaces.
All 235 library files are free of proof placeholders and project axioms.
The book has 80 HTML pages, retaining all 79 old paths and displaying the
three new docstrings, the explicit completeness input and the open arithmetic
scope. The frozen 117-declaration M4a page is preserved. Two source passes
produce 56 pages without undefined references or overflow. The actual
changed page 34 was rendered and visually checked; the original coordinate
lemma and proof are byte-exact. Both existing module namespaces are also
byte-exact; only their status headers changed. Final full build/book checks
are repeated after recording these results.
Corrected fixed-class generic operations are the next consumer. Unconditional
ACF completeness, the original simultaneous-representative calculation,
setoid laws, ratio semantics, totalization, R1/R2 and reconstruction existence
remain open; the frozen M4a chain is untouched.

## Corrected generic arithmetic on the fixed class (#23)

`Interpretation/ClassArithmetic` computes the four coupled EH95 relations
on the original geometric Frobenius class. If two class members satisfy
`PointTripleIndependent` on their first coordinates and the parameter,
then every `JAddRel`, `JMulRel`, `JSubRel` or `JDivRel` output belongs to
the same class and its `jClassEquiv` coordinate is the sum, product,
difference or quotient of the input coordinates. Perfection, rank five,
the exponential characteristic and still-open ACF J-completeness remain
explicit. No relatively closed or infinite base hypothesis is used.

One private helper presents the two geometric inputs as tuples with the
same literal parameter. The accepted rank-three closure lemma supplies
independent generators; the accepted coupled generic semantics gives the
output tuple, soundness gives its class membership, and the coordinate
evaluation law gives the field formula. The predicates are geometric
meet/join relations, and the genericity hypothesis remains geometric;
no semantic redefinition is introduced.

Claude's immutable source-only draft `2e59baa0` was recorded against local
`2df132b` during transient GitHub write failures. That exact checkpoint
was subsequently pushed before this review. Codex checked all seven input
hashes against the published pin. The frozen draft compiled without repairs.
Original and final private chains pass in 8 s each, with all five signatures
and raw proofs exact, four public and one private standard axiom reports,
and no generated declarations. Twelve byte-identical interfaces pass with
independent universe levels: all four operations over arbitrary bases,
finite bases and characteristic zero. Only the module status header changes
from the immutable draft; statements, attributes and declaration docstrings
are exact.

Four existing module namespaces are byte-exact; their status headers now
point to the conditional generic class semantics. The book displays all
four results. The source retains the original literal definitions, theorem
statements and historical proofs. A residual blanket assertion that all
transcription-table items were already proved was reported on issue #1
(comment 6041011479) before its status prose was corrected; the original
wording is retained in a source comment.

The full library build passes in 36.01 s (10.19 GiB sampled peak family
RSS, minimum 34.98 GiB available); the book passes in 8 s. Shared artifact
probes pass in 6 s, reproducing the same five signatures/raw proofs, four
public and one private standard axiom reports, and twelve typed interfaces.
All 236 library files pass proof-placeholder/project-axiom hygiene. The
book has 81 HTML pages, retaining all 80 old paths and displaying all four
docstrings with geometric genericity and explicit completeness. The frozen
117-declaration M4a page is preserved. Two source passes produce 56 pages
without undefined references or overflow. Actual changed pages 1, 34–36,
38 and 52 were rendered and visually checked, including the ratio warning
after normalizing extracted whitespace to identify it. All 49 original
mathematical statement blocks and 44 original proof blocks are byte-exact.
The original checklist status wording is retained as a source comment.
Final full build/book checks are repeated after recording these results.
Non-generic totalization, corrected ratio semantics, setoid laws, unconditional
ACF completeness, the bypassed simultaneous-representative obligation,
R1/R2 and reconstruction existence remain open. The frozen M4a chain is
untouched.

## Corrected ratio semantics with the exact rank-five budget (#23)

`Interpretation/Ratio` replaces the empty M0 skeleton with the corrected
geometric ratio predicate and its forward, reverse and equivalence theorems.
The predicate retains four products through four auxiliary class members,
using the coupled `JMulRel` and a `PointTripleIndependent` clause for each
product. It contains no semantic coordinates. The four input class
memberships are explicit in the semantic theorems.

`RatioEq.div_eq` applies to every geometric witness, converts its four
products to field equations by the accepted generic class semantics, and
cancels nonzero coordinates. `ratioEq_of_div_eq` presents the four input
members with the same literal parameter. Equality of ratios recovers one
coordinate from the other three; a multiplier fresh over the explicit
four-element set consisting of the parameter and those three coordinates
therefore avoids all five values. The rank-five oracle supplies it.
Four independent triples establish all four product genericity clauses.
Their pair restrictions provide independence and class membership for
all auxiliary tuples, without duplicating or promoting the private
coordinate-pair helper. `ratioEq_iff` gives the exact decoded-ratio
equivalence. Perfection, exponential characteristic, rank five and
still-open ACF J-completeness remain explicit throughout the semantic
theorems; the predicate itself is geometric over arbitrary fields.

Claude supplied frozen source-only draft `f1faad39`. Codex checked all
eleven dependency hashes and the original empty skeleton against pushed
`04846d1`, independently audited the equations and rank budget, and compiled
the immutable source without repairs. The old skeleton has zero records.
Original and final six-record signatures and raw proof/definition bodies
agree exactly. All four public and two private axiom reports are standard,
including the geometric predicate definition. No generated declaration
is introduced, and no statement, attribute or declaration docstring changes.
The private source passes in 12 s and the final chain in 8 s.

Nine byte-identical original/final interfaces and behavior probes pass
with independent universe levels. They check arbitrary bases, finite
bases and characteristic zero, the universal forward witness and reverse
orientation, repeated input pairs, pair reversal, chained decoded equalities
and all diagonal pairs representing one. Genericity is required in the
witness products, not between numerator and denominator. These probes do
not package a main ratio setoid or construct its quotient/decoding.

Four existing module namespaces are byte-exact; only status headers change.
The original literal ratio definition and refutation remain preserved, and
the source displays the corrected geometric predicate separately, with
the explicit unproved completeness input.

The full library build passes in 32.01 s (6.69 GiB sampled peak family RSS,
minimum 36.79 GiB available), and the book in 8 s. Shared artifact probes
pass in 6 s with the same six signatures/raw bodies, all four public and
two private standard axiom reports and nine interfaces/behaviors. All
236 library files pass proof-placeholder/project-axiom hygiene. The book
has 82 HTML pages, preserving all 81 old paths and the frozen
117-declaration M4a page; four new docstrings display each product's
geometric genericity, explicit completeness and open quotient/totalization
scope. Source verification now requires stable auxiliary/contents output:
the initial two-pass output had stale contents page references. Four passes
produce 57 pages with stable auxiliary, contents and bookmark hashes and
no undefined references, overflow or rerun warnings. Actual changed pages
1, 2, 34–37 and 53 were rendered and visually checked after convergence.
All 49 original mathematical statement blocks and 44 original proof blocks
remain byte-exact. Final full build/book checks are repeated after recording
these results.
Ratio setoid/quotient construction, decoding, non-generic totalization,
field graphs, unconditional completeness, the bypassed representative
obligation, R1/R2 and reconstruction existence remain open. The frozen
M4a chain is untouched.

## The geometric ratio quotient and bijective nonzero decoding (#23/#8)

`Interpretation/Decode` proves the corrected ratio relation an equivalence
on pairs of members of the fixed geometric class, packages its setoid and
quotient, and decodes that quotient bijectively to the actual nonzero
field elements `Kˣ`. These six public declarations establish the nonzero
part of blueprint `decode-equiv`; every semantic statement and definition
keeps perfection, exponential characteristic, rank five and the still-open
ACF `JCompletenessACF` input explicit. The setoid relation itself is the
geometric `RatioEq`, with no semantic replacement.

`ratioDecode` descends by `Quotient.lift` and the universal corrected
ratio semantics. Its evaluation law computes a representative as the
ratio of its two coordinates. Injectivity uses the reverse ratio
implication. For surjectivity, a multiplier is fresh over the explicit
three-element set `{a,z,x₀}`; cancellation of the nonzero `z` shows
both `t` and `z*t` avoid the closure of `{x₀,a}`. Independent
triples and their pair restrictions supply the two class members
`j(z*t,a)` and `j(t,a)`, with ratio `z`. No pair helper is
promoted or duplicated, and the one exclusion calculation stays in place.
The theorem retains the uniform rank-five input used for class soundness.

The one new coordinate helper `jClassEquiv_ne_zero` is consumed by the
quotient decoding and by a separately ledgered proof-only cleanup of
`RatioEq.div_eq`. All eleven older signatures, attributes and declaration
docstrings are exact. Ten older raw proof/definition bodies are exact;
only that named proof changes. All eighteen original/final signatures
and raw bodies agree exactly. All fourteen public and four private axiom
reports are standard, including the three new definitions. There are no
new private helpers or generated declarations.

Claude froze source-only bundle `34d2ca37` (Decode), `09be3b60`
(coordinates) and `1b186aab` (Ratio) against pushed `2cb0133`. Codex
checked eight dependency hashes and both byte-exact bases, independently
reviewed the geometric quotient and freshness budget, and compiled all
three frozen sources without repairs in 14 s. Final sources pass in 10 s;
a private quotient-equality probe required the setoid supplied explicitly
to `Quotient.sound`, then all fifteen interfaces pass in 4 s on both
overlays. They use independent universes and check arbitrary/finite bases,
characteristic zero, actual geometric setoid relation, both evaluation
routes, quotient equality, global injectivity, surjectivity and the
nonzero helper. No source proof needed repair.

Three additional existing module namespaces remain byte-exact; their
status headers now identify the nonzero decoding. Original mathematical
statement/proof blocks and the literal refutation remain preserved.
The full library build passes in 36.01 s (10.18 GiB sampled peak family
RSS, minimum 36.38 GiB available); the book passes in 8 s. Shared artifact
probes pass in 6 s, reproducing all eighteen signatures/raw bodies, fourteen
public/four private standard-axiom reports and fifteen interfaces.
All 237 library files pass proof-placeholder/project-axiom hygiene.
The book has 83 HTML pages, retaining all 82 old paths and the frozen
117-declaration M4a page. Seven new docstrings display the geometric setoid,
three-element freshness, explicit completeness and still-open zero/TOT
scope. Four source passes produce 57 pages with stable auxiliary, contents
and bookmark hashes, with no undefined references, overflow or rerun
warnings. Actual changed pages 1, 2, 34–37 and 53 are rendered and visually
checked; page 36's final equation ends at 771.93 pt, before the footer
at 787.71 pt. All 49 original mathematical statement blocks and 44 proof
blocks stay byte-exact. Final full build/book checks repeat after recording
these results.
Adjoining zero, non-generic totalization, quotient field operations, global
Frobenius setoid, unconditional completeness, simultaneous representatives,
field graphs, R1/R2 and reconstruction remain open. The frozen M4a chain
is untouched.

## The adjoined-zero carrier and full decoding equivalence (#23/#8)

`Interpretation/Interp` defines the corrected geometric ratio quotient
with an adjoined zero, as `RatioInterp := WithZero (Quotient ratioSetoid)`.
Its `ratioInterpDecode` is an actual equivalence onto all of `K`,
with the named zero and representative evaluation laws both reducing by
`rfl`. This proves the full corrected blueprint `decode-equiv`.
Perfection, exponential characteristic, rank five and the still-open ACF
`JCompletenessACF` input remain explicit throughout. No quotient field
operations or transported field structure are installed before totalization.

The proof uses Mathlib directly: `Equiv.optionCongr` extends the accepted
nonzero decoding, and `WithZero.withZeroUnitsEquiv.toEquiv` identifies
the units with an adjoined zero with the field. The carrier abbreviation
is reducible, with the actual geometric quotient inside it. There is
no local bijectivity or zero-detection boilerplate.

Claude supplied source-only draft `a56e1fa8` pinned to pushed `e15d81d`.
Codex checked the three local and two Mathlib hashes, independently
audited the construction and compiled its immutable source without
repairs in 6 s. The Status-only final chain passes in 8 s.
All four original/final signatures and raw proof/definition bodies
are exact, and all four public axiom reports are standard, including
both definitions. No private helper or generated declaration is added.
Fifteen byte-identical interfaces pass on both overlays, with independent
universes, arbitrary/finite bases and characteristic zero. They check the
literal WithZero quotient carrier, equivalence onto all K, named zero and
representative evaluation, global zero detection and surjectivity, both
inverse laws, and that genuine quotient representatives decode nonzero.

Seven existing module namespaces remain byte-exact. Six headers identify
the new full decoding; the field skeleton imports its carrier but retains
open field operations, total graphs, naturality and reconstruction.
Original mathematical statement/proof blocks and literal refutation
provenance remain preserved.
The full library build passes in 38.01 s (10.17 GiB sampled peak family
RSS, minimum 36.48 GiB available), and the book in 8 s. Shared artifact
probes pass in 6 s with all four exact signatures/raw bodies, all four
public standard-axiom reports including both definitions and fifteen
interfaces. All 238 library files pass proof-placeholder/project-axiom
hygiene. The book has 84 HTML pages, preserving all 83 old paths and the
frozen 117-declaration M4a page; four new docstrings show the actual
carrier, explicit completeness, zero/representative evaluations and
still-open field/TOT scope. Source checking caught one overfull line in
the new evaluation-law prose, which was fixed by a paragraph break before
acceptance. Four passes then produce 58 pages with stable auxiliary,
contents and bookmark hashes, with no undefined references, overflow
or rerun warnings. Actual changed pages 1, 2, 34–37 and 54 are rendered
and visually checked. All original 49 mathematical statement blocks
and 44 proof blocks remain byte-exact. Final full build/book checks
repeat after recording these results.
Non-generic totalization, quotient field operations, global Frobenius
setoid, unconditional completeness, simultaneous representatives, field
graphs, R1/R2 and reconstruction remain open. The frozen M4a chain is
untouched.

## Corrected two-addition total negation and shared geometric genericity (#23/#8)

`Interpretation/TotalOps` begins corrected non-generic totalization with
the blueprint's two-addition negation detour. `JNegTotalRel` retains
two auxiliary class members `z,r`, the coupled clauses `u+z=r`
and `v+r=z`, and a geometric `PointTripleIndependent` input clause
for each addition. The predicate contains no semantic coordinates.
`JNegTotalRel.neg_eq` applies to every witness, giving `µ(v)=-µ(u)`.
The converse presents inputs with the common literal parameter and uses
a multiplier fresh over the explicit two-element set `{a,x}`. Insertion
gives `(x,z,a)` independent; mutual closure membership gives
`(-x,x+z,a)` independent. The witnesses `j(z,a)` and `j(x+z,a)`
are both class members and both additions are generic.
`jNegTotalRel_iff` proves the exact corrected semantic equivalence,
under explicit perfection, exponential characteristic, uniform rank five
and still-open ACF J completeness, over arbitrary base fields.
No genericity between the original two inputs is assumed.

The one existing `pointTripleIndependent_jTupleOf` helper moves from
private Ratio to public `FrobLinkSoundness` before any `include htr`.
Its type, declaration docstring and raw proof are exact. Its signature
uses no perfection, characteristic, rank-five, completeness or infinite
base assumption. Named consumers are four ratio products, two negation
additions and the direct-link proof. Only the named
`directFrobLink_jTupleOf` proof replaces its inline duplicate with
this helper. No new rank, linear or pair helper is introduced.

Claude supplied frozen sources `94853196` (TotalOps), `0964b535`
(soundness) and `e9fcbc6d` (Ratio) against pushed `0231f69`.
Codex checked eight dependency hashes and exact base files, independently
audited the relation and witness budget, and compiled the immutable
bundle without proof repairs in 14 s. Two `show` style warnings are
fixed to `change` in the private final; the final passes in 10 s
with no warning and the same kernel proof bodies.

The thirteen older signatures, attributes and declaration docs are
exact except the single ledgered helper module/visibility change.
Twelve older raw bodies are exact; only the direct-link proof consumes
the helper. All seventeen original/final signatures and raw bodies are
exact. All sixteen public and one private axiom reports are standard,
including the new geometric predicate. Four public declarations are new
and one existing helper is promoted/moved; no private/generated
declaration is added.

Ten byte-identical original/final typed interfaces pass with independent
universes. They check arbitrary and finite bases, characteristic zero,
every witness and the converse orientation, reversal, tuple-level double
negation, characteristic-zero irreflexivity, the pure geometric predicate,
and the moved helper without rank/perfection/completeness hypotheses.
The original literal negation and totalization expressions/derivation
stay byte-exact, in addition to the original mathematical statement and
proof blocks. They remain historical/open because their argument uses
the refuted literal generic semantics; no separate negation-detour
counterexample is claimed.
The full library build passes in 40.01 s (7.71 GiB sampled peak family
RSS, minimum 36.44 GiB available), the book in 8 s and shared probes in
6 s. Shared artifacts reproduce all seventeen exact signature/raw-body
records, sixteen public/one private standard-axiom reports and ten
independent interfaces. All 239 library files pass placeholder/project
axiom hygiene. The book has 85 HTML pages, retaining all 84 old paths
and the frozen 117-declaration M4a page. Five new/promoted docstrings
show the two geometric additions, each genericity clause, fresh
two-element set, explicit completeness and still-open full addition/TOT
scope. Four source passes converge to 58 pages with stable auxiliary,
contents and bookmarks, with no undefined references, overflow or rerun
warnings. Actual changed pages 1, 2, 35 and 36 are rendered and visually
checked. The source paragraph audit restores the abstract's explicit
completeness phrase before acceptance. All original49 mathematical
statement blocks/44 proofs and the literal negation/TOT derivation remain
byte-exact. Final full build/book checks repeat after recording these results.
Total nonzero addition, full totalization, quotient field operations,
global Frobenius setoid, unconditional completeness, simultaneous
representatives, total graphs, R1/R2 and reconstruction remain open.
The frozen M4a chain is untouched.

## Corrected total nonzero addition with derived output membership (#23/#8)

`Interpretation/TotalOps` now proves the corrected counterpart of
blueprint `lem:total-nonzero-add`. `JAddTotalNZRel` retains four
auxiliary class members `z,nz,r,s`, corrected negation of `z`,
and three coupled generic additions `u+z=r`, `v+nz=s` and
`r+s=w`. Its geometric definition does not assume output membership
or input genericity and contains no semantic coordinates.

`JAddTotalNZRel.exists_mem_add` applies to every witness, deriving
`w` in the class and `µ(w)=µ(u)+µ(v)`. The converse presents all
three tuples with the common literal parameter, so `c=x+y`.
One element fresh over the explicit three-element set `{a,x,y}`
gives `(x,z,a)` and `(y,-z,a)` by insertion, and
`(c,x+z,a)` because membership of `x+z` in its closure would
put `z=(x+z)-x` in the original closure. Mutual closure membership
gives `(x+z,y-z,a)`. The four canonical tuples are class members;
the negation theorem and the three generic-sum theorems provide the
geometric witnesses. `jAddTotalNZRel_iff` leaves membership in the
right-hand existential for arbitrary raw output tuples.

This is class-level totalization for sums outside `racl k {a}`,
a stronger condition than being merely nonzero in `K`. Perfection,
exponential characteristic, uniform rank five and still-open ACF
J completeness remain explicit over arbitrary base fields. The local
freshness set has size three; no claim lowers the uniform rank bound.

Claude supplied immutable source `64ba2297` against pushed
`173d6ec`, with ten exact dependency hashes and an exact base copy.
Codex verified its append-only namespace and compiled the frozen source
without repairs in 14 s (peak 2.62 GiB, minimum available 36.59 GiB).
The header/status-only final passes in 10 s with no warnings and its
entire namespace is byte-exact to the draft. All nine original/final
signature and raw-body records are exact: four old declarations, four
authored new public declarations, and one generated match definition
`jAddTotalNZRel_iff.match_1_1` from existential destructuring.
All eight authored public and the generated definition use only
standard axioms, including both geometric predicates. No private
helper is added, and all four old attributes/docstrings/types/bodies
remain exact.

Ten byte-identical independent interfaces pass in separate universes:
arbitrary and finite bases, characteristic zero, every-witness output
membership/value, constructed converse, canonical raw-output equivalence
with the blueprint's actual Out condition, symmetry, raw-tuple
functionality, the pure geometric definition and the zero obstruction.
All original 49 mathematical statement blocks, 44 proof blocks and
the literal negation/TOT expressions and argument stay byte-exact.
The literal detour remains historical/open; no separate counterexample
is asserted. Full library/book passes in 46.01/10.00 s, with peak
8.36 GiB and minimum available 34.24 GiB for the library. All nine
independent/shared signature and raw-body records, eight authored public
and one generated standard-axiom reports and all ten interfaces pass.
Hygiene covers 239 library files with no proof placeholders or project
axioms. The book preserves all 85 older HTML paths among 86 and checks
the four new declaration docs, explicit completeness, derived output
membership, exact Out condition and open full-TOT obligations.
Four source passes converge in auxiliary/contents/bookmark hashes,
with 59 pages and no undefined references, overflows or rerun warnings.
Changed pages 1, 2 and 36 have visual review. All original 49 statements,
44 proofs and literal negation/TOT derivation remain exact.
Final documentation library/book and five-path staged-byte gates follow
before commit and push.

The prior `173d6ec` CI library/book job passed, but the overall
run `37655075766` concluded failure with no failed or deploy job.
GitHub refuses retrying that workflow. Issue REST PATCH failures were
bypassed with repository-scoped GraphQL, without changing settings.

Full ratio-carrier totalization, quotient field operations, geometric
graphs, global Frobenius setoid, unconditional completeness, simultaneous
representatives, R1/R2 and reconstruction remain open. The next
read-only peer audit checks the common-denominator addition graph.
The frozen M4a chain is untouched.

## Corrected total geometric operation graphs (#23/#8)

`Interpretation/Field` now proves the corrected totality/functionality
and decoded-operation part of blueprint `thm:total-field-graphs`.
`RatioAddGraph` retains the two named-zero cases and existential
class-member representatives with a common denominator: corrected
negation gives zero, or corrected total nonzero addition gives a ratio.
`RatioMulGraph` retains zero factors and two generic coupled products,
on the numerators and denominators. Quotient equalities use the actual
corrected geometric `ratioSetoid`. Definitions contain no coordinates,
choices or `Quotient.out`.

Both decode iffs apply to every witness, and their converses construct
witnesses for arbitrary carrier elements. Addition uses a common
denominator fresh over `{a,c,d}`, with class members supplied by the
existing coordinate equivalence inverse. Its inner addition detour may
use a fifth independent element, so the full construction retains the
uniform rank-five bound. Multiplication uses successive freshness over
`{a,c,d}` and `{a,c,d,b}`, giving the two independent triples
`(b,e,a)` and `(c*b,d*e,a)`. There is no extra sixth element.
Both `existsUnique` theorems use decoding bijectivity. Perfection,
exponential characteristic, rank five and still-open ACF J completeness
stay explicit, over arbitrary base fields. Common denominators are
existential: a prescribed one may make the numerator sum algebraic over
the parameter, even when the decoded sum is nonzero.

Claude supplied frozen Field `c2870a42`, Ratio `a2876cd8` and
ClassCoordinates `b125d8dd` against published `ebad9db`.
Codex verified thirteen input hashes and three exact bases, then
compiled the seven-module chain in 18 s (peak 2.65 GiB, minimum available
37.45 GiB), without source repairs or warnings. The initial six-second
attempt stopped on a private overlay symlink/root-path harness error
before Field compilation. Materializing unchanged dependency sources
fixed the harness. The final changes only module headers/status and
preserves all seven namespaces.

All seventeen original/final signature and raw-body records are exact.
All eleven old types/docs/attributes/raw bodies are exact except the
two ledgered private-to-public flags on `mul_fresh_notMem` and
`pair_of_notMem`. Their types/docs/proofs are unchanged, with named
old ratio/class and new graph consumers. Six public declarations are
new; no private/generated declaration is added. All sixteen public
and one private axiom reports are standard, including both geometric
graph definitions and the existing class encoding.

Twenty-two byte-identical independent-universe interfaces pass.
They cover arbitrary and finite bases, characteristics zero and two,
every witness and both converses, actual totality/functionality,
named-zero laws, geometric quotient representative invariance,
associativity/distributivity without carrier field operations,
base-valued inputs, opposite-input zero and rank-free helper types.
Only private interface-harness zero/numeral normalization needed repair.
Independent earlier probes also checked the exact common-denominator
and two-generic-product freshness budgets.

The recovery warning's blanket open-status qualification was reported
on issues 9 and 23 before its current-scope update; its earlier wording
is preserved in a source comment. Conditional total graphs do not
discharge R1/R2 or unconditional completeness. All original 49
statement blocks, 44 proof blocks and the literal total-field-graphs
argument remain exact. Full library/book passes in 50.01/10.00 s
(peak 9.84 GiB, minimum available 33.27 GiB), with no touched-module
warnings. All seventeen independent/shared records, sixteen public and
one private standard-axiom reports and twenty-two interfaces pass.
Hygiene covers 239 library files; all 86 old HTML paths survive among
87, with eight new or promoted docs and the frozen M4a status checked.
Four source passes converge in auxiliary/contents/bookmark hashes,
with 59 pages and no undefined references, overflows or rerun warnings.
Changed pages 1, 2, 39, 40 and 41 have visual review. New prose
overflows were fixed before acceptance, and the corrected subsection
was moved before the literal heading to keep that heading with its
original prose. The original mathematical blocks and literal argument
remain exact. Final documentation library/book and ten-path staged-byte
gates are required before commit and push.

Transported field structure, graph naturality, global Frobenius setoid,
unconditional ACF completeness, simultaneous representatives, R1/R2
and reconstruction remain open. A private downstream audit confirms
Mathlib's `Equiv.field` and `Equiv.ringEquiv` can give a named
field structure/decoding equivalence, preserving the named zero.
No carrier Field instance or corresponding declaration is installed.
That blueprint obligation remains even if a later route bypasses it.
The frozen M4a chain is untouched.

## Named interpreted field structure and geometric operations (#23/#8)

`Interpretation/Field` now proves the corrected conditional
field-transport obligation after the full geometric graphs. The named
reducible `ratioInterpField` uses Mathlib's `Function.Injective.field`
and the existing carrier zero, with Mathlib equivalence-transfer data
for all other operations, scalar actions and casts. It is not a global
instance. Its zero value and Zero structure agree definitionally with
the geometric adjoined zero, checked using Mathlib's instance-diamond
standard `with_reducible_and_instances rfl`. The stricter
`with_reducible rfl` alone cannot unfold the native instance constant.
There is no zero bridge lemma or additional helper chain.

`ratioInterpRingEquiv` is the actual decoding ring equivalence onto
all of `K`, built using Mathlib's `Equiv.ringEquiv`. Its map and
inverse are exactly the existing decoding equivalence. The two
`ratioAddGraph_iff_eq_add` and `ratioMulGraph_iff_eq_mul` theorems
identify the geometry-only graphs with the installed field operations.
They supply the named consumer for field transport in blueprint
`decode-equiv` and I5c; later graph-preserving carrier transport and
interpreted reconstruction consume these structures and laws.

Claude supplied frozen Field `afe43877` against published
`266cbfb`, with eleven exact project/Mathlib dependency hashes and
an exact base copy. Codex compiled the source unchanged in 12 s
(peak 2.66 GiB, minimum available 38.78 GiB). Two new-proof references
were deprecated in Mathlib. The final replaces them by the literal
Mathlib alias body `Equiv.eq_symm_apply.symm`, without changing their
types/docs/attributes. No source proof failure or mathematical repair
was needed. The final ten-second compilation is warning-free.

All ten original/final signatures/types/docs/attributes are exact.
Eight raw bodies are exact; only the two new theorem proof references
change as ledgered. All six existing graph declarations retain their
source, signatures and raw bodies. Four public declarations are new,
with no private helpers, generated declarations or global instances.
All ten axiom reports are standard, including the Field and RingEquiv
definitions. Eleven other touched library modules change only headers,
with their namespaces exact. The incidence module also reflows one existing
overlong docstring; its five types/attributes/raw bodies stay exact, with
only that whitespace doc hash changing. The final status audit found six older
blueprint paragraphs and six upstream headers with stale scope: accepted
conditional work was listed as open, a historical empty skeleton was not
marked superseded, and supplied-witness rigidity was omitted. This stale-scope finding was
reported on issue 23 before correction; all six earlier source wordings
are retained in TeX comments. These status corrections do not change any
mathematical statement or proof.

Twenty-nine byte-identical independent original/final interfaces pass:
arbitrary and finite bases, characteristic zero, actual Field/RingEquiv
and both graph/operation signatures, native-zero value and structure
coherence, decoding/inverse equality, actual field laws/inversion,
natural and rational casts, characteristic-two actual zero-sum and its
geometric graph, both installed operation outputs, and absence of a
global Field instance. Initial interface attempts needed proof-context
instances and Mathlib's standard reducible-and-instance transparency;
these were harness changes, not source repairs.

The warning-free full library build passes in 44.01 s (peak family
7.46 GiB, minimum available 35.82 GiB); the book passes in 10 s.
Shared acceptance takes 12 s and matches the final ten Field and five
incidence signature/raw-body/axiom records, plus the identical 29
interfaces. Fifteen compiled declarations have standard axioms.
Hygiene checks 239 library files without proof placeholders or project
axioms. The book has 88 HTML pages and retains all 87 prior paths,
including the frozen 117-item page and all four new declaration docs.
Four stable source passes produce 60 pages without unresolved labels,
overflow or rerun warnings. Actual final pages 1, 2, 34, 35, 36, 37, 38
and 40 pass visual review. All original 49 statements/44 proofs and the
literal TOT/interpreted-reconstruction argument remain exact; all six
prior status qualifications are preserved. Final documentation
library/book and exact sixteen-path staged-byte checks remain required
before commit and push. Perfection, uniform rank five and still-open ACF J
completeness remain explicit over any base field. Geometric naturality,
unconditional completeness, global Frobenius setoid, simultaneous
representatives, R1/R2 and full reconstruction remain open. The literal
source statements/proofs and frozen M4a chain remain unchanged.

## Pure geometric configuration naturality (#23/#8, I6b1)

`Config/Transport` preserves the configuration layer under an arbitrary
`ClosedIF k K ≃o ClosedIF l L`, with independent base/ambient universe
levels. Partial quadrangles transport through the existing rank and
Mathlib finite-supremum API. `QWitness.map` maps all 21 raw points;
its three join laws are consumed by `QWitness.Psi.map`, which handles
all 24 actual clauses, including all three universal-point clauses and
its quadrangle. Multiplication diagrams transport, and applying the
same maps to the inverse gives the geometric Q/Q′/J iff laws. These
are the configuration consumer for blueprint `interpreted-reconstruction`
and I6b1, with corrected interpretation transport as the next consumer.

Claude supplied frozen source `1dc2a300` against published `ccec377`,
with eleven exact project/Mathlib input hashes and six exact baseline
copies. Codex compiled it unchanged and warning-free in 8.05 s
(peak 2.37 GiB, minimum 37.14 GiB available). The final changes only the
module status qualification and passes in 8.04 s. Ten authored public
declarations and two generated equation lemmas are present
(`QWitness.map.eq_1` and `JGeom.eq_1`), with no private helpers
or global instances. All 12 signatures/types/docs/attributes/raw bodies
and standard-axiom reports are exact between original and final,
including the witness definition. No mathematical or proof repair
was needed.

Sixteen byte-identical original/final independent interfaces pass,
covering the ten exact cross-universe types, full raw-witness round trip,
whole-Psi and partial-quadrangle reflection, successive unrelated
lattices, finite bases and characteristic two. The separate existing-API
probe needed a typed finite-join equality before rewriting a RankEq
goal; that was a harness adjustment, not a source repair.

The latest prior named-field checkpoint `ccec377` has full build/book
and deployment CI success in run 37668882418. The warning-free full library passes in 44.24 s (peak family
11.32 GiB, minimum 34.50 GiB available); the rendered book passes in
10.06 s. Shared acceptance passes in 6.03 s, matching all 12 compiled
records and the identical 16 interfaces. Hygiene checks 240 library
files without proof placeholders or project axioms. The book has 89
HTML pages, retaining all 88 prior paths and all ten declaration docs,
including the frozen 117-item record. Four stable source passes produce
60 pages without undefined labels, overflow or rerun warnings. Actual
final pages 1, 2, 3, 41, 42 and 43 pass visual review. The final
documentation library/book and exact five-path staged-byte checks are
required before commit and push. No existing Lean declaration is changed.
No original 49 source statements or 44 proofs, literal TOT or interpreted
reconstruction arguments, or frozen 117-item M4a record are changed.

This configuration stage needs only Field/Algebra structures and the
closed-lattice order isomorphism, with no semantic, perfection,
rank-five or freshness assumption. Corrected relation/carrier transport,
geometric operation-graph naturality and interpreted reconstruction
remain open. Perfection/rank-five/ACF completeness stay explicit for
the earlier interpreted-field route; unconditional completeness, the
global Frobenius setoid, literal source arguments and R1/R2 remain open.

## Geometric Frobenius-link naturality (#23/#8, I6b2a)

`Interpretation/FrobTransport` proves five purely geometric iff laws
for an arbitrary `ClosedIF k K ≃o ClosedIF l L`: the derived product
relation, geometric J-locus, point-triple independence, directed links
and the two-edge bridge relation. All five directed-link fields
transport in both directions, including a single common multiplier
across all three rigid coordinates. The bridge tuple and both edge
orientations are preserved. The original relations and all existing
library declarations are unchanged. Invariance supplies neither
FrobEq reflexivity/transitivity nor functionality of the refuted
MulPoint relation. SumPoint is omitted because the corrected route
has no named consumer for a separate transport declaration.

The named consumers are directed-link transport, bridge transport,
corrected totalization/ratio transport and the later class/carrier map
in blueprint `interpreted-reconstruction`. There are no duplicate
`.map` or public direct-edge lemmas. Mathlib's `Equiv.piCongrRight`
supplies the tuple bijection; the edge iff is local to the bridge proof.

Claude supplied frozen source `4bd522d1` against published `47bd9f1`,
with eight exact project/Mathlib input hashes and two exact baselines.
Codex compiled it unchanged and warning-free in 6.04 s (peak 2.61 GiB,
minimum 38.47 GiB available). The final changes only its module status
and passes in 8.06 s. Five authored public declarations and one
generated `PointTripleIndependent.eq_1` equation lemma are present,
with no private helper or global instance. All six original/final
signatures/types/docs/attributes/raw bodies and standard-axiom reports
are exact. No source or interface-harness repair was needed.

Twelve byte-identical original/final independent interfaces pass:
five exact cross-universe signatures, an actual arbitrary raw-class
bijection via Mathlib `Equiv.subtypeEquiv`, its RFL pointwise map
and inverse round trip, a single-multiplier output, composition over
six universe levels, finite bases and characteristic two. This raw
class bijection uses invariant predicates and does not assume a
global Frobenius equivalence relation. The separate existing Mathlib
tuple-quantifier/inverse/parameter-equality API probe also passes.

The prior configuration checkpoint `47bd9f1` has full library/book
and deployment CI success in run 37672585265. The warning-free full library passes in 46.29 s (peak family
8.18 GiB, minimum 36.47 GiB available); the book passes in 10.07 s.
Shared acceptance passes in 6.04 s, matching all six compiled records
and the identical twelve interfaces. Hygiene checks 241 library files
without proof placeholders or project axioms. The book has 90 HTML
pages, retaining all 89 prior paths and all five declaration docs,
including the frozen 117-item record. Four stable source passes produce
60 pages without undefined labels, overflow or rerun warnings. Actual
final pages 1, 2, 3, 41, 42 and 43 pass visual review. Final
documentation library/book and exact five-path staged-byte checks are
required before commit and push. Original 49 source statements and
44 proofs, literal TOT/interpreted reconstruction arguments and the
frozen 117-item M4a record remain exact.

This relation stage takes no semantics, completeness, perfection,
rank-five, exponential-characteristic, Infinite or freshness input.
N2b coupled arithmetic and N2c totalization/ratio transport remain
held, as do the quotient-carrier and operation-graph naturality and
interpreted reconstruction. Earlier interpreted-field semantics keep
perfection/rank-five/ACF completeness explicit. Unconditional
completeness, the global Frobenius setoid, literal source obligations,
base recovery and scalar-one inputs remain open.

## Coupled arithmetic naturality (#23/#8, I6b2b)

`Interpretation/JArithTransport` imports only `JArithSem` and
proves four public transport laws across arbitrary closed-lattice
order isomorphisms, bases and universe levels. `jSub_map` and
`jDiv_map` hold for all closed-lattice five-tuples, with their
original coordinate order and coupling intact. Their named consumers
`jAddRel_map_iff` and `jMulRel_map_iff` preserve and reflect
the coupled sum/product relations on arbitrary point tuples.
Coordinate transport is RFL/local; the derived operations transport
locally, and Mathlib `Function.Injective.comp_left.eq_iff` reflects
the coordinate equalities. No extra normalization helper chain,
instance, genericity or semantic assumption is introduced.

The four declarations supply corrected total negation/nonzero addition
and ratio transport, and later full-carrier graph preservation, in
blueprint `interpreted-reconstruction`. No existing lattice/point
operation or interpretation definition is changed.

Claude supplied frozen source `9983d949` against published `9f9ee07`,
with eight exact project/Mathlib input hashes and two exact baseline
copies. Codex compiled it unchanged and warning-free in 8.06 s
(peak 2.62 GiB, minimum 39.08 GiB available). The final changes only
its module-status qualification and reflows that paragraph, passing
in 8.05 s. All eight original/final signatures/types/docs/attributes,
raw bodies and standard-axiom reports are exact. Four authored public
theorems and four generated equation lemmas (`jSub.eq_1`,
`jDiv.eq_1`, `JAddRel.eq_1` and `JMulRel.eq_1`) are
present, with no private helper or global instance. No mathematical,
proof or interface-harness repair was needed.

Ten byte-identical original/final independent interfaces pass:
four exact cross-universe types, whole raw-output reflection for
difference/quotient, composition over six universe levels, reflection
of actual unique point-tuple output, finite bases and characteristic
two. Separate existing-API probes for coordinate RFL, composition
injection and nested lattice formulas pass with the same narrow import.

The prior Frobenius-link checkpoint `9f9ee07` has full library/book
and deployment CI success in run 37674711938. The full library passes
in 54.35 s (peak 9.18 GiB, minimum 35.54 GiB available); the book
passes in 8.00 s. Shared acceptance passes in 6.00 s, matching all
eight compiled records and the identical ten interfaces. Hygiene checks
242 library files without proof placeholders or project axioms. The book
has 91 HTML pages, retaining all 90 prior paths and the four new
declaration docstrings, including the frozen 117-item record. Four stable
source passes produce 61 pages without undefined labels, overflow or
rerun warnings. Actual final pages 1, 2, 3, 42 and 43 pass visual
review. Final library/book and exact five-path staged-byte checks are
required before this natural checkpoint is committed and pushed. The preceding source progress paragraph still
listed coupled arithmetic as open; its scope correction was reported
on #23 before updating and its earlier wording is retained in a TeX
comment. All original 49 source statements and 44 proofs, literal
TOT/interpreted reconstruction arguments and the frozen 117-item M4a
record remain exact.

This stage takes no semantics, genericity, completeness, perfection,
rank-five, exponential-characteristic, Infinite or freshness input.
N2c totalization/ratio transport remains held, followed by carrier/
operation-graph naturality and interpreted reconstruction. Earlier
interpreted-field semantics keep perfection/rank-five/ACF completeness
explicit. Unconditional completeness, the global Frobenius setoid,
literal source obligations, base recovery and scalar-one inputs
remain open.

## Corrected totalization and ratio naturality (#23/#8, I6b2c)

`Interpretation/TotalTransport` imports only `FrobTransport`,
`JArithTransport` and `TotalOps`. Three public iff laws preserve
and reflect corrected negation, total nonzero addition and ratio
relation on arbitrary raw point tuples and arbitrary base tuples,
across independent bases and universe levels.

All 2/4/4 witness tuples are retained, with the two/three/four generic
coupled-operation clauses and every rank-three independence condition.
Mathlib `Equiv.piCongrRight` supplies witness preimages; lower
relation iff laws transfer the conjuncts. No extra hypothesis, global
setoid, private helper, instance or normalization chain is introduced.
Named consumers are class-pair quotient well-definedness and full-carrier
operation-graph preservation in blueprint `interpreted-reconstruction`.

Claude supplied frozen source `97eddeb3` against published `fb030c4`,
with eight exact project/Mathlib input hashes and four exact baselines.
Codex compiled it unchanged and warning-free in 6.00 s (peak 2.62 GiB,
minimum 37.71 GiB available). The status-only final passes in 8.00 s;
all three signatures/types/docs/attributes/raw bodies and standard-axiom
reports are exact. There are three authored public theorems, no new
generated equation lemmas and no private helper or global instance.
No source, proof or independent-interface repair was needed.

Ten byte-identical original/final interfaces pass: exact cross-universe
types, arbitrary target-output existence reflection, six-universe
addition/ratio composition, an actual corrected quotient/adjoined-zero
map under explicit semantic inputs and a supplied canonical-base image
equality, finite bases and characteristic two. Separate existing-API
probes for canonical image tuples, raw class equivalences and quotient/
option representative RFL pass without main changes.

The prior coupled-arithmetic checkpoint `fb030c4` has full library/
book and deployment CI success in run 37677086411. Three preceding
current source-progress qualifications were reported on #23 before
updating and retained in provenance comments. Three upstream transport
module status paragraphs are corrected in this checkpoint; their
namespaces are byte-exact, with combined compiled-record integrity
checks. Full library/book passes in 50.01/10.00 s (full peak 8.82 GiB,
minimum 35.44 GiB available). The book has 92 HTML pages, retaining
all 91 prior paths and the three new declaration docstrings. Four stable
source passes produce 61 pages without undefined labels, overflow or
rerun warnings; actual final pages 1, 2, 3, 41, 42, 43 and 44
pass visual review. Shared acceptance passes in 12.00 s: all three new
records and all 29 combined types/docs/attributes/raw bodies/standard
axiom reports match, with the identical ten interfaces. The three
existing library namespaces are byte-exact. Hygiene checks 243 library
files without proof placeholders or project axioms. Final sequential
library/book pass in 4.00/10.00 s without touched-module warnings.
Exact eight-path staged-byte gates remain required before this natural
checkpoint is committed and pushed. All original
49 source statements and 44 proofs, literal TOT/interpreted-reconstruction
arguments and the frozen 117-item M4a record remain exact.

This completes the pure corrected-relation transport stage I6b2, with
no semantic, genericity, completeness, perfection, rank-five, exponential-
characteristic, Infinite or freshness input. Quotient-carrier and full
operation-graph naturality and interpreted reconstruction remain open.
The separate four-public carrier/graph plan is agreed with the peer;
its draft remains held until this checkpoint is published. Earlier
field semantics keep perfection/rank-five/ACF completeness explicit.
Unconditional completeness, global Frobenius setoid, literal source
obligations, base recovery and scalar-one inputs remain open.

## Conditional geometric carrier and graph naturality (#23/#8, I6b3)

`Interpretation/Naturality` imports only `Field` and
`TotalTransport`. Four public declarations construct the actual
pointwise fixed-class map and corrected quotient/adjoined-zero map,
then preserve and reflect both total geometric operation graphs.
Every addition zero/common-denominator/opposite/nonzero branch and
multiplication zero/generic-product branch transfers with all witnesses
and rank-three independence clauses. Zero/representative and class-value
laws are RFL and remain inline. Witnesses pull back by surjectivity,
and equalities reflect by injectivity. No helper chain, private item,
global instance, `Quotient.out` or decoding-defined substitute is added.

The canonical image-base equality is an explicit hypothesis; rewriting
it is confined to propositions after restating class-map values in
pointwise form. The raw class map needs no semantic hypothesis. The
actual interpreted carriers retain perfection/rank-five/ACF-completeness
inputs and independent exponential characteristics on both sides,
across four independent universe levels and bases.

Claude supplied frozen source `e7159aa2` against published `b3f1262`,
with eleven exact project/Mathlib input hashes and six exact baseline
copies. Codex compiled it unchanged and warning-free in 6.00 s
(peak 2.57 GiB, minimum 36.47 GiB available). The status-only final
passes in 8.00 s. All four signatures/types/docs/attributes/raw bodies
and standard-axiom reports match, including both definitions; no new
generated declaration, private helper or global instance appears.
No source or proof repair was needed.

Sixteen accepted original/final interfaces are byte-identical:
raw class types/value/inverse/round-trip without semantic inputs;
actual carrier equivalence, native zero/representative/inverse-zero RFL;
both full-carrier graph iff types; actual named-field add/mul preservation
and a genuine RingEquiv consumer whose underlying Equiv is the geometric
map; output-functionality reflection, finite bases and characteristic two.
The root interface harness initially used unparenthesized notation-dot
projections and redundant proof-local `letI`; parentheses and
proof-local `let` instances fix those parser/style issues. The frozen
source and all mathematical proofs are unchanged.

The prior totalization/ratio checkpoint `b3f1262` has full library/
book and deployment CI success in run 37679279737. The conditional
image-base scope was reported on #23 before updating preceding source
progress and four upstream transport headers. Earlier source wording
is retained in provenance comments; old library namespaces and combined
compiled records stay exact. The full library/book passes in 54.01/8.00 s
(peak 8.93 GiB, minimum 36.34 GiB available for the build), and shared
comparison passes in 12.00 s (peak 2.61 GiB, minimum 38.19 GiB). All
33 combined types/docs/attributes/raw bodies and standard-axiom records
match, as do the sixteen accepted interface bytes. Hygiene covers 244
library files. The book retains all 92 prior HTML paths and adds one
four-docstring conditional naturality section. Earlier current source/book
progress scopes and the recovery warning were also reported before
qualification; old source wording is retained in comments. Original 49
source statements/44 proofs, literal TOT/interpreted-reconstruction
arguments and the frozen 117-item M4a record remain exact. Four stable TeX
passes produce 62 pages; actual visual review covers pages 1/2/3/33/34/35/37/
38/40/42/43/44/45, including earlier qualified scopes and the recovery warning.
A first layout check found an overflow in only the new paragraph; reflow
fixed it without a mathematical change. The pre-stage byte gate also caught
one overlong upstream header line; reflow leaves that namespace unchanged.
Final sequential library/book passes in 38.01/8.00 s (minimum available
37.41/37.95 GiB), with no touched-module warnings. Exact nine-path staged-byte
gates are checked before commit and push.

I6b3 is accepted with the image-base equality and carrier inputs explicit.
Its parent I6b and interpreted reconstruction I6c remain open: image-base
existence and the named induced RingEquiv/composed field isomorphism are
not yet declared. The separate two-public RingEquiv plan is agreed;
its draft remains held until this checkpoint is published. Unconditional
completeness, global Frobenius setoid, literal source obligations, base
recovery and scalar-one inputs remain open.


## Conditional induced ring isomorphisms (#23/#8, I6c1)

Two public definitions are appended in `Interpretation/Naturality`, with
no new import/helper/global instance: `ratioInterpMapRingEquiv` has exactly
the geometric `ratioInterpMap` as its underlying Equiv, and
`interpretedRingEquiv` is the actual `K ≃+* L` composite of the inverse
source decoding, geometric carrier map and target decoding. Add/mul laws
use the graph characterizations and naturality. Native zero, representative
and forward/inverse composite values are definitional; Mathlib supplies
one/inverse laws. All four prior declaration bytes are unchanged.

Claude froze source `07766340` against published `603c57b`, with eleven
exact inputs and three baseline copies. Original compilation passes in
6.00 s (peak 2.59 GiB, minimum 37.16 GiB available). Four unused explicit
lambda-binder warnings are fixed by naming `(r := r) (s := s)` in the two
source graph iffs. The final passes in 10.00 s (peak 2.62 GiB, minimum
36.94 GiB). All six original/final types/docs/attributes/raw bodies and
standard-axiom records remain exact, including both new definitions and
all four previous records. No mathematical source/proof repair is needed.

Eighteen accepted original/final interfaces have identical bytes and pass
warning-free: genuine named-field RingEquiv/type and exact geometric
toEquiv/pointwise map; native zero, inverse zero and representatives RFL;
actual add/mul/one/inverse laws; actual K-to-L type; forward/inverse
decode compositions RFL; the forward decode diagram, actual ring laws
and inverse roundtrip; independent universes/bases/separate exponents,
finite bases and characteristic two. The root harness initially lacked
proof-local named field contexts at projections/inverse/decode diagrams;
adding those contexts is only a fixture repair. The frozen source is
unchanged and all compiled final bodies remain exact.

Prior `603c57b` has full build/book/deployment CI success in run
37684293833. The current conditional reconstruction scope and five
upstream header-only qualifications were reported on #23 before changing
source/status prose. All five old namespaces and 43 prior compiled records
remain exact; all 45 combined public records have standard axioms. The full
library/book passes in 56.01/8.00 s (peak 8.90 GiB, minimum 36.39 GiB
available for the build). Shared six-record/eighteen-interface and 43-old/
45-total comparison passes in 14.00 s (peak 2.60 GiB, minimum 38.38 GiB).
Hygiene covers 244 files; the 94-page HTML book retains all 93 prior paths
and adds the two-docstring conditional induced-isomorphism section. Four
stable TeX passes produce 62 pages; actual visual review covers pages
1/2/3/41/42/43/44/45. The visual audit caught one earlier coupled status
missed by the first qualifier pass; the reported scope is fixed with old
wording retained in a comment. All original 49 source statements/44 proofs
and literal TOT/interpreted-reconstruction arguments remain exact. The
final prose review distinguishes definitional forward/inverse composite
values from the commuting decoding diagram, which uses inverse laws.
Final sequential library/book passes in 50.01/8.00 s (minimum available
36.98/38.72 GiB), with no touched-module warning. Exact nine-path staged-byte
gates precede commit/push.

This accepts I6c1, corrected interpreted reconstruction GIVEN the
canonical image-base equality, with both sides' perfection, rank-five,
separate exponential characteristic and ACF-completeness inputs explicit.
Parent I6b/I6c remain open until image-base existence and the conditional
existence endpoint; that separate two-public plan is agreed and remains
held until this checkpoint is published. R1/R2, unconditional completeness,
global Frobenius setoid, literal source obligations, full inducing
reconstruction and the frozen M4a obligations remain open/preserved.


## Conditional canonical image base and field-isomorphism existence (#23/#8, I6c2)

Exactly two public theorems are appended in `Interpretation/Naturality`,
with unchanged imports and no helper/private/global instance/evaluation
declaration. `exists_map_jTupleOf_eq` supplies an actual independent target
pair and the canonical tuple equality from source rank/pair, the lattice
map and target perfection/exponential characteristic/ACF J completeness.
Target rank is derived locally by the lifted transcendence-degree transport.
Source perfection/completeness and target rank are absent from its inputs.
Its consumer `nonempty_ringEquiv_of_closedIF_orderIso` chooses a source
pair inline using rank-five freshness and exchange, obtains the image pair
and applies `interpretedRingEquiv`. The conclusion is actual
`Nonempty (K ≃+* L)`. Both perfections, separate exponents, source rank five
and BOTH still-open ACF J-completeness hypotheses remain explicit; no
source/target pair, target rank or image-base equality is supplied.

Claude froze source `ac56183e` against published `f014650`, with eleven
exact peer inputs, nine root inputs and one exact baseline copy. The six
accepted declaration prefix bytes are unchanged. Original compilation is
warning-free in 8.00 s (peak 2.55 GiB, minimum 36.40 GiB available). A
header/status-only final passes in 12.00 s (peak 2.61 GiB, minimum
36.28 GiB). All eight original/final types/docs/attributes/raw bodies and
standard-axiom records remain exact, including the prior six. No production
mathematical/source/proof repair is needed.

Twenty-seven accepted original/final interfaces have identical bytes and
pass warning-free: all eighteen accepted actual geometric/named-field
RingEquiv checks plus nine minimal-signature, actual image coordinate/point,
reverse image/field equivalence, finite-base and characteristic-zero/two
checks across four independent universes. Root initially copied an older
pre-acceptance RingEquiv fixture; it failed only for missing proof-local
field contexts. Restoring the exact accepted eighteen-interface fixture is
a harness-copy correction only. All nine new fixtures pass unchanged. The
accepted original/interface/45-prior-record run takes 10.00 s (peak 2.61 GiB,
minimum 36.19 GiB). No production repair is hidden by this fixture correction.

Prior `f014650` has exact CI37686716943 full library/book/deployment success.
The conditional scope was reported on #23 before integration and before
qualifying fourteen current source progress paragraphs and five upstream
headers. Earlier source wording is retained in comments. All five old
namespaces and 45 prior compiled records must remain exact; shared 47-total
standard-axiom records, all original 49 source statements/44 proofs and the
literal TOT/interpreted-reconstruction arguments are checked before push.
Full library/book, hygiene, retained HTML, actual rendered-source/provenance
and exact nine-path staged-byte gates precede commit/push.

This accepts I6c2 only in its conditional scope. The theorem asserts field
isomorphism existence; it does not prove `Induces` compatibility with the
given lattice map or recovery of the base fields. General I6b/I6c retain
their original/open scope. R1/R2, unconditional completeness, global
Frobenius setoid, literal/TOT/simultaneous-representative obligations, full
inducing reconstruction and frozen M4a remain open/preserved.


The integrated gates pass: full library/book **58.33/8.04 s** (library
peak **8.88 GiB**, minimum **35.43 GiB** available), shared eight-record/
twenty-seven-interface/45-old/47-total comparison **16.00 s** (peak
**2.63 GiB**, minimum **37.73 GiB**). All 45 old types/docs/attributes/raw
bodies and axioms are exact; all 47 combined public records use only standard
axioms. All five upstream namespaces are byte-exact with header-only
changes. Hygiene passes for **244** library files. HTML has **95** pages
retaining all **94** old paths and both new theorem docstrings; the frozen
117-item M4a page is unchanged in scope. The source is stable after four
passes at **63** pages, with no unresolved reference/overflow and actual
visual review of pages **1/2/3/33/34/35/38/40/41/42/43/44/45/46**. All 49
original statements/44 proofs and the complete literal TOT/interpreted
reconstruction arguments are byte-exact. Final serial library/book and
exact staged-byte gates precede the nine-path checkpoint commit/push.


## No-fresh relative base-ratio corollary (#5/#9, R1a/C7b)

Two public theorems replace the empty `Reconstruct/Base` skeleton. Imports
are only `Interpretation.Naturality` and Mathlib's `RatFunc.AsPolynomial`;
there is no helper/private/global instance/evaluation declaration or local
algebra structure. `base_ratio_rel` states ratio algebraicity over arbitrary
k/K from the actual independent pair and both element/product
interalgebraicity pairs. No fresh element in K, rank, perfection,
completeness or exponential-characteristic input is assumed. The proof
embeds K into the algebraic closure of K(X), enlarges the base algebraically,
uses the transcendental variable as the required third element, applies
the existing base-ratio correspondence lemma, and pulls algebraicity back.
`base_ratio_mem_range` gives the original u₁/u₂ ratio in the actual image
of k, with explicit IsRAC of the intermediate-field bottom. Its consumers
are the literal corollary and actual R1b interpreted-ring base recovery.

Claude froze `f66a0a45` against published `e7179bd`, with eleven peer/eleven
root input hashes and an exact skeleton baseline. Original compilation and
nine interfaces pass unchanged and warning-free in 8.00 s (peak 2.86 GiB,
minimum 39.35 GiB available). A header/status-only final and before-main
47-public-record capture pass in 14.00 s (peak 2.87 GiB, minimum 39.32 GiB).
All two original/final types/docs/attributes/raw bodies and standard-axiom
records are exact, with identical namespace bytes and nine fixture bytes.
The checks cover minimal no-fresh/algebraicity signatures, inverse
orientation, actual RAC-base range/witness/subfield membership, independent
base/ambient universes, finite bases, characteristics zero/two and the
original algebraically closed-base case without ambient closure. All nine
new interfaces pass unchanged. No production proof/source repair is needed.

The combined baseline harness initially imported only the old Base skeleton,
which does not import Naturality/Transport. Root added an explicit
Naturality import to that capture fixture; this was a harness import repair
only, with no production change. The accepted original/final records and
all 47 old records are captured after that correction. Root's prior
RatFunc/algebraic-closure freshness and RAC-membership API probe uses
existing global instances and passes in about 1 s (nested peak 2.85 GiB;
the outer two-second sampler missed the RSS peak).

Prior e7179bd exact CI37689183902 is fully green including library/book and
deployment. The source proof discrepancy and intended scope were reported
on #5 before code, and the five-path integration scope on #9 before source
qualifications. The original corollary proof incorrectly names independent
correspondence points (u₁,b)/(u₂,b); the formal core uses (u₁,u₂)/(b,b).
All original 49 source statements/44 proofs and literal TOT/interpreted
reconstruction arguments remain exact. Full library/book, shared
two-record/nine-interface/47-old/49-total, hygiene, retained HTML and actual
rendered-source/provenance plus exact five-path staged bytes precede push.

This proves R1a/C7b, the base-ratio corollary prerequisite. Actual R1b
`CrossBase.Compatible (interpretedRingEquiv …)`, scalar one, full Induces
reconstruction, unconditional J completeness, the remaining C7/group/
three-pair/tensor obligations and frozen M4a remain open/preserved. The
separate three-public R1b plan is held until this checkpoint is published.

The integrated full library/book pass in 40.22/8.04 s; the shared two-record,
nine-interface and 47-old/49-total comparison passes in 12.07 s. All 47 prior
compiled types/docs/attributes/raw bodies and axioms are exact; all 49
combined public records use standard axioms. All ten prior root inputs
except the replaced Base skeleton are byte-exact, including Naturality
and the root import. Hygiene covers 244 files with no placeholders/project
axioms. All 95 old HTML paths remain among 96 pages, with both new
base-ratio docstrings and the open recovery boundaries checked. The source
renders in four stable passes, still 63 pages; all six changed/reflowed
pages (1, 2, 3, 26, 27, 28) were actually visually inspected and pass.
No touched-module warning or mathematical source/proof repair is needed.
The final serial library/book and exact five-path staging gate precede
commit/push; CI for this new checkpoint is reported in the issues.


## Actual conditional base recovery (#9, R1b)

Exactly three public theorems are appended in `Reconstruct/Base`, with
the one justified `Closure.CrossBase` import. All existing carrier,
rank-five/perfection, separate exponential-characteristic, both ACF
J-completeness and image-pair inputs remain explicit. Forward
`interpretedRingEquiv_algebraMap_mem` needs target RAC only, handles zero
and encodes a nonzero base scalar as the ratio of `j(c x₀,a)` to the
canonical denominator `j(x₀,a)`. The denominator's target tuple is pinned
by hφ. Target B1 yields the numerator; only zero/product point coordinates
and the accepted no-fresh base-ratio corollary are needed.
`interpretedRingEquiv_symm` identifies the actual inverse with the swapped
construction, without RAC and with the redundant inverse tuple equality
explicit. Its pointwise composite values agree by reflexivity.
`interpretedRingEquiv_compatible` derives the inverse tuple equality
inline and applies forward inclusion both ways under both RAC bases.
Its conclusion is actual `CrossBase.Compatible (interpretedRingEquiv …)`.

Claude froze `4cf53a47` against published `29bbb8a`, with eleven peer
inputs, twelve root inputs and one exact baseline. The initial uncompiled
source failed at a redundant symmetry tail after congr had already closed
the goal (2.01 s). Root and Claude agreed the bounded replacement
`RingEquiv.ext fun _ ↦ rfl`, deleting unused local inverse proofs. Both
passing ext/reflexivity variants showed an unintended simplifier-generated
`interpretedRingEquiv.congr_simp`. Replacing the forward zero-case
`by simp` with explicit map_zero/congrArg/trans identities removes it.
The failed original and both passing generated-inventory variants are
preserved. There is no other production repair; all public statements,
binders, docs, attributes, imports/counts and the two old declaration bytes
stay unchanged. Peer ACKs are 3919/3922.

The accepted review and header/status-only final pass in 10.05/10.06 s,
with peaks 2.86/2.91 GiB and minimum available memory 38.90/38.82 GiB.
All five accepted original/final theorem types/docs/attributes/raw bodies
and standard-axiom records are exact; their namespaces are identical.
There is no helper/private/global instance/evaluation/generated declaration.
All twelve new and nine old interfaces pass unchanged and warning-free:
minimal target-only RAC membership, no-RAC actual inverse, both-RAC
Compatible, actual forward/inverse scalar witnesses, base-range image
equality, an actual induced base-field RingEquiv, compatible principal-point
transport, zero, finite bases and characteristics zero/two, across
independent universes. Before-main capture of all 49 old compiled records
passes in 6.03 s and matches the prior accepted shared inventory.

The prior 29bbb8a exact CI37692166084 is fully green, including library/book
and deployment. The seven-path integration and source qualifications were
reported on #9 before main edits. Naturality changes only its header; its
eight declarations remain exact. Older current source progress wording
is retained in comments, with conditional R1b distinguished from the open
unconditional R1/R2 scope. All original 49 statements/44 proofs and literal
TOT/interpreted arguments remain exact. Full library/book, shared
five-record/21-interface/49-old/52-total comparison, hygiene, retained HTML,
stable source rendering/actual visual review and exact staged bytes
precede commit/push.

This accepts corrected conditional R1b, not unconditional source R1.
Scalar one/R2, Induces, unconditional J completeness, full inducing
reconstruction, global/literal/TOT obligations and broader C7/group/
three-pair/tensor/frozen M4a remain open/preserved. Earlier checkpoint
sections retain their historical scope.

The integrated full library/book pass in 58.31/8.04 s; the shared
five-record/21-interface and 49-old/52-total comparison passes in 14.08 s.
All 49 prior compiled types/docs/attributes/raw bodies and axioms remain
exact, and all 52 combined public records use standard axioms. Naturality
is header-only with its complete namespace unchanged; all ten other prior
root inputs and the root import are byte-exact. Hygiene covers 244 files.
All 96 old HTML paths remain among 97 pages, with the three new recovery
docstrings, explicit hypotheses and open general boundaries checked. The
source renders in four stable passes, now 64 pages; all sixteen changed/
context pages (1, 2, 3, 26–29, 42–47, 49–51) were actually visually
inspected and pass. No touched-module warning remains. Final serial
library/book and exact seven-path staging precede commit/push; CI for the
new checkpoint is reported in the issues.


## Actual conditional scalar one and outside-point recovery (#9, R2a/b/c)

The focused new `Reconstruct/Scalar` imports Base only and has exactly
three public theorems, with no helper/private/global instance/evaluation/
generated declaration or duplicate RingEquiv. For the same actual map H,
`interpretedRingEquiv_coord` proves y·H(x₀)=H(x)·x₀' from actual tuple
images. `interpretedRingEquiv_base_coord` proves H(x₀)=x₀'.
`interpretedRingEquiv_point` proves e([x])=[H(x)] outside racl_k{a}.
None assumes RAC. Both perfections/rank-five bounds, separate exponential
characteristics, both still-open ACF J-completeness inputs and the actual
canonical image-base equality remain explicit. Source genericity uses two
fresh elements over a. Target genericity comes from mapped point-triple
independence plus tuple-image coordinates 0/0/4, then the semantic coupled
product and three multiplied coordinate identities force scalar one.
This geometrical route replaces the original choice over acl(a,x₀,t₀),
which is preserved as a literal proof obligation with its statement.

Claude froze c9089e23 against published eb4546d (10 peer inputs, 15 root
inputs, exact Base/Naturality baseline copies). The initial source run
failed only at two unqualified pair_mul_a references (2.00 s). The bounded
repair qualifies them as JArith.pair_mul_a, with peer ACK3950; all public
statements/binders/docs/attributes/imports/count stay unchanged. The next
source run compiled all three records but exposed a root-only dependent
rewrite in fixture9; evaluation via congrArg/trans repairs that fixture
proof only. Both failed evidence sets and the frozen source are preserved.
There is no other production repair.

Accepted original/header-status-only final pass in 12.00/10.00 s (peak
2.88 GiB, minimum available 38.28/38.26 GiB). All three types/docs/attributes/
raw bodies and standard-axiom records are exact; namespace bytes match.
All twelve new and twenty-one byte-exact old typed interfaces pass without
warnings: minimal no-RAC coordinate/base/outside-point laws, independent
input point recovery, full tuple-image consequence from actual B1 and the
public laws, actual inverse/base-coordinate behavior, swapped inverse point
recovery, feeding actual compatibility and outside points to the existing
whole-lattice API, all principal points, finite bases and characteristics
zero/two across independent universes. These fixtures check downstream
behavior but do not supply the held public R3/R4 declarations. Before-main
capture passes in 6.03 s with all 52 prior records exact.

The scope/route qualification was reported on issue9 before main/source
edits. Integration adds Scalar/root import and current book/source status;
Base, Naturality and Points change only module prose/status headers, with
all complete namespaces and old compiled records exact. The previously
promised whole-file baseline preservation is qualified solely for those
current-status headers, with the root integration scope communicated to
the peer before edits. The source preserves old progress in comments,
every original 49 statements/44 proofs and the literal TOT/interpretation
chunk. Prior eb4546d CI37695087697 is fully green for build/book/deploy.
Full serial library/book, shared 3-record/33-interface/52-old/55-total checks,
hygiene, retained HTML, stable source rendering with actual visual review,
final serial build/book and exact staging precede commit/push.
The initial integrated full build passed in 60.01 s but the pre-staging
warning gate caught one newly long Points status-header line. Wrapping
that prose line preserves its complete namespace; the post-wrap full
build passes in 20.00 s with no touched-module warning. The new source
prose initially put a Lean listing inside math mode; moving the listing
outside math fixes rendering, with the failed PDF evidence retained.
Actual visual review also found two old scalar-open consumer scopes;
they are qualified with their prior wording retained, making five current
source progress qualifications. The final stable source has 65 pages,
with 13 affected/context pages actually reviewed.

Only corrected conditional R2a/b/c are accepted. General unconditional
R1/R2, public inducing/existence assembly, chosen-perfection reconstruction,
unconditional J completeness and global/literal/TOT/three-pair/tensor/
frozen M4a remain open. The next named consumer is a bounded two-public
actual closedIFMap inducing/existence slice; peer drafting remains held
until this checkpoint is published. Historical checkpoint sections retain
their earlier scope.


## Actual conditional inducing equality and existence (#9, perfected R3/R4)

The focused new `Reconstruct/Existence` imports Points and Scalar only.
Exactly two public theorems, no helpers/private/generated/global-instance/
evaluation/duplicate RingEquiv: `closedIFMap_interpretedRingEquiv` uses
actual compatibility and outside points to prove e=closedIFMap H for the
same interpretedRingEquiv. Its exact carrier, image-pair and both RAC
inputs are explicit. `exists_ringEquiv_closedIFMap_eq` then proves
there is a compatible RingEquiv inducing e, with only source rank five,
both perfect ambient fields, separate exponential characteristics, both
still-open ACF J-completeness hypotheses and both RAC bases. Source pair,
target rank and actual image pair are derived inline. No pair, target
rank, image equality, point/scalar oracle or inducing endpoint is supplied.

Claude froze bea65e68 against published e6f35fc (10 peer inputs, 18 root
inputs and exact Scalar/Base/Naturality/Points baseline copies). Original
and header/status-only final pass in 12.00/12.00 s, peaks 2.90 GiB and
minimum available 38.18/38.26 GiB. The original source is byte-exact
frozen; no production or fixture-proof repair is needed. All two types/
docs/attributes/raw bodies/standard-axiom records and namespaces are exact.
Twelve new independent typed behaviors and 33 byte-exact previous
fixtures pass warning-free: minimal actual H equality, every principal
point, every closed-field set image, full inverse point recovery, minimal
no-pair inducing existence and its all-point/image consequences, actual
compatible base RingEquiv, finite bases and characteristics zero/two.
One behavior checks extension to arbitrary chosen perfections of these
already-perfect inputs, not the general nonperfect-field theorem.
Before-main capture passes in 6.00 s with all 55 prior records exact.

The perfected conditional scope and original-field caveats were posted
on issue9 before main/source edits. Base, Naturality, Scalar and Points
change only current status headers, preserving all complete namespaces.
Root adds only the Existence import. Current source progress is qualified
with prior wording retained; every original 49 statements/44 proofs and
the literal interpretation/TOT chunk remain exact. Prior e6f35fc
CI37697686422 is fully green for library/book/deploy. Full serial library/
book, shared two-record/45-interface/55-old/57-total comparison, hygiene,
retained HTML, stable PDF and actual affected/context visual review,
final serial library/book and exact staging precede commit/push.

This accepts only the corrected conditional perfect-field inducing/
existence step. The original nonperfect fields require chosen-perfection
lattice transport, RAC of the perfected base, actual Perfection.Induces
existence and assembly with the landed Frobenius uniqueness. These are
the named next consumers and remain open. General unconditional
R1/R2/R3/R4, unconditional ACF completeness, literal RatioEq/TOT/scalar
arguments, bypassed linear-disjointness and frozen M4a scope retain their
recorded status. Historical checkpoint sections keep their earlier scope.


## Actual conditional original-field existence through chosen perfections (#9)

The focused new Reconstruct/Target imports Perfection.Induces and
Reconstruct.Existence only. Exactly two public results in namespace
Perfection, no helper/private/generated/global-instance/evaluation/duplicate
RingEquiv: isRAC_basePerf derives perfected-base RAC from ORIGINAL-base RAC
with no rank or completeness. exists_induces constructs a compatible map
of arbitrary chosen perfections inducing the original lattice isomorphism.
The original fields need not be perfect. Only original source rank five,
both original RAC bases, the bundles and both exact perfected ACF
J-completeness hypotheses are supplied. Perfected source rank, perfected-base
RAC and conjugation are derived inline; separate bundle characteristic
parameters stay separate. Two local Prop-valued PerfectField witnesses are
necessary because the bundle supplies PerfectRing; no local Algebra instance,
pair, target rank, point/scalar or inducing oracle is supplied.

Claude froze 1dbeb730 against dab374c (16 peer inputs, 24 root inputs and
four exact baseline copies). Frozen production source compiles with two local haveI style warnings. Root
initially missed these in private logs; the full warning gate caught them before
staging. Only two local Prop-valued haveI commands are replaced by Mathlib-
preferred have, agreed by peer4021, with warned source/proof/log evidence
preserved. Accepted original/header-only final pass14.00/14.01s, peaks2.91GiB
and minimum available38.01/37.98GiB. Frozen signatures/docs/attributes/types
and standard axioms are exact; accepted original/final raw bodies match. Two types/docs/attributes/raw bodies,
namespace bytes and standard-axiom records are exact. No other production repair.
One new root fixture's unused existential compatibility binder was renamed
_hPhi; source-success/fixture-warning evidence is retained. A root preflight
declaration scanner misread header prose and was corrected before actual
Lean compilation, retaining failed guard/missing-directory evidence.

Twelve new warning-free typed behaviors and all 45 byte-exact previous
interfaces pass (57 total): minimal RAC and actual algebraic membership,
minimal original-field existence, literal perfected-subfield equalities,
every intersection formula, actual compatible base RingEquiv, inducing-map
conjugacy, all Frobenius twists and exact fibre for this constructed witness,
finite bases and characteristics zero/two across independent universes.
The fibre is a private consumer check, not an extra public assembler.
Before-main capture passes 8.00s with all 57 prior records exact and main clean.

Scope and stale source status were reported on issue9 before main/source
edits (6048732435). Existence and Induces change only current headers with
full namespaces exact; root adds Target only. All nine changed current source scopes preserve earlier wording; every original49 statements/44 proofs and literal interpretation,
TOT and proposed assembly proof remain exact. Prior dab374c CI37699869146 is
fully green for library/book/deploy. Full serial library/book, shared two-record,
57-interface/57-old/59-total comparison, hygiene, retained HTML, stable PDF,
actual affected/context visual review, final serial library/book and exact
scoped staging precede commit/push.

Only conditional original-field chosen-perfection inducing existence is
accepted. The next named consumer is a public conditional target assembly
combining rank, base/intersection formulas, Frobenius uniqueness and converse.
Final Reconstructs/target assembly, general unconditional R1/R2/R3/R4,
unconditional completeness, literal/TOT/scalar, bypassed linear-disjointness
and broader group/three-pair/tensor/frozen obligations remain open. Historical
checkpoint sections retain their earlier scope; peer assembly drafting remains
held until this checkpoint is published.

Actual source review also found crowded double-digit subsection numbers in
the table of contents; the number column alone is widened before final rendering.


## Public conditional lattice-form reconstruction target (#9/#10)

Main's empty skeleton is replaced by exactly three public declarations:
Reconstructs, a reducible alias of the actual Perfection.Induces equality;
exists_reconstruction, the minimal conditional public existence signature;
and reconstruction_target, one assembled conditional blueprint Thm target.
It provides lifted rank equality, a compatible field isomorphism of arbitrary
chosen perfections, every perfected image/original intersection formula,
the exact Frobenius fibre, characteristic-zero literal uniqueness,
positive-characteristic injectivity of the integral exponent, and the
compatible converse. Only both original RAC bases, original source rank
five, the bundles and both EXACT perfected ACF J-completeness inputs are
supplied. No original PerfectField, target rank, pair, image equality,
point/scalar/Induces oracle or matching characteristic parameter is assumed.

Claude froze Main c9b87be2 against published6e7b7b3, with ten input hashes
and a byte copy of the empty-skeleton baseline; root pins26 inputs.
Frozen original passes unchanged in 14.08 s; accepted final passes
16.09 s and changes only the current status header. All three compiled
public types/docs/attributes/raw bodies/namespace and standard axiom reports
are exact. No production or fixture repair, helper, private/generated
item, global/local instance, evaluation or duplicate relation is added.
Main imports only Target and Uniqueness; the root already imports Main and
Functorial separately and stays byte-exact.

Fifteen new warning-free independent typed behaviors plus all 57 previous
byte-exact fixtures pass (72 total). They check minimal public existence,
the actual perfected-base Subfield image, actual set intersection inside
the ORIGINAL target field, both directions of the fibre, actual ∃! integral
exponent, literal ∃! reconstruction in ORIGINAL characteristic zero and
unique exponent in ORIGINAL characteristic two for arbitrary bundles,
finite bases, independent universes, compatible converse and uniqueness of
the induced lattice map without rank/completeness. Before-main59 capture
passes 6.03s with all 59 prior compiled records exact and main clean.

Conditional scope/current source status corrections were reported on issue9
before integration (6049028844). Only four old Lean headers change; their full
namespaces remain byte-exact. Every original49 mathematical statements and
44 proof blocks, literal interpretation/TOT, assembly listing/proposed proof
and frozen 117-item M4a remain exact; earlier current progress wording is
preserved in source comments. Full serial library/book, shared3-record/
72-interface/59-old/62-total comparison, hygiene, retained HTML, stable PDF
with actual affected/context visual inspection, final full library/book and
exact ten-path staging precede commit and push. Previous6e7b7b3 CI37702330392
is fully green for library/book and deployment.

Only conditional public U2b/U2c subitems are accepted. Both perfected
completeness inputs, general unconditional recovery/reconstruction, literal
ratio/TOT/scalar, bypassed linear-disjointness, broader group/three-pair/
tensor/frozen M4a, point-geometry/automorphism and functorial forms remain
open. The next bounded public consumer is chosen only after publication.


## Completeness dependency and current-status reconciliation (#6/#22)

The public lattice-form target is now conditional on both exact perfected
ACF J-completeness inputs. The next mathematical priority is discharging
those inputs, rather than adding public wrappers. Semantic J assembly
now reduces each rank-five ACF input to guarded Q completeness and Q′ completeness (#27).
The old unguarded AffineGridExtraction and QCompletenessACF were subsequently refuted
even for ACF pairs with five independent elements. Guarded extraction requires
I≠D and I≠P; both guards come from J multiplication distinctness. Guarded Q
completeness needs only the four outputs and remains open. The frozen 117-item M4a stays frozen.

The audit found stale current prose: Config.Correctness and issues 6/22
still called the accepted concrete arbitrary-field Q/Q′ refutations open;
issue 6 still called concrete geometry transport open. Both are proved:
Config.Transport maps partial quadrangles, all Psi clauses, multiplication
diagrams and Q/Q′/J along arbitrary closed-lattice order isomorphisms,
without completeness/perfection/rank/freshness. Counterexamples.QRefutation
proves not_forall_qGeom_imp_qSem and not_forall_q'Geom_imp_q'Sem in
characteristic zero over rational functions in five variables.
Correctness/Transport change current headers only, with full namespaces
byte-exact. The configuration chapter's current overview/transport status
is reconciled; no declaration, proof, source statement or source PDF changes.
Status discrepancies and the scope were reported before edits on issue 6
(6049189938). Full library/book and scoped commit/push validate the cleanup.

Claude's read-only G1 audit 4068 confirms Language's incidence/collinearity,
partial quadrangle and named-triple permutation, FiniteRank's finite-rank
interfaces and concrete invariance in Geometry/Config Transport. Broad G1
stays open with explicit unimplemented generic-formula recursion and named
MemCl/Col invariance interfaces. The accepted concrete per-predicate route
bypasses the blueprint's proposed generic recursion method; no bypassed
obligation is silently closed. General ACF Q/Q′/J completeness, corrected
extraction, geometric projection identities, general witness descent and
group/action integration remain open. The completeness-engine audit is
read-only; no new source draft, Lean/main ownership, child agents or frozen
bookkeeping expansion is delegated.


## Degenerate Psi refutation and guarded completeness repair (#27/#6/#22)

The literal Psi allows Q=E=G=T=[c], H=S=[a], I=D=[ax] in the independent
five-coordinate table. The four changed meets are proved, not assumed; all
remaining clauses use the verified table witness. QSem.ratio_ne and
ratio_ne_fst prove both necessary output inequalities. The counterexample
refutes unguarded geometric Q completeness over any field with five independent
elements, and the exact legacy QCompletenessACF and AffineGridExtraction with
both actual ACF assumptions. It also refutes the unguarded geometric Q
projection to J. The old #25 unguarded Q conclusion is superseded; the
independent arbitrary-field Q′ refutation remains relevant.

GuardedAffineGridExtraction and GuardedQCompletenessACF require both I≠D and
I≠P. They are explicit OPEN propositions, never axioms or proved classification
interfaces. Actual multiplication distinctness supplies both outer guards in J.
The two existing JAssembly inputs are retyped to guarded Q completeness;
JCompletenessACF and every Main public target are unchanged. Guarded correctness
and geometric projection are conditional on the explicit guarded input. The
three vacuous unguarded correctness wrappers are removed; legacy target definitions
remain marked refuted with this issue reference for their negative consumers.

The source error and concrete scope were reported BEFORE main/source edits on
issues 6/22/12, then both guards on 27/6. All 49 original full mathematical statement
blocks remain in the source, including the two refuted statements in explicitly
labelled historical false branches from ed61c33. Of the 49 active statements,
47 stay exact; q-correct and affine-grid-extraction gain both guards and explicit
OPEN completeness qualification. All 44 proof blocks, original listings and the
literal ratio/TOT section stay byte-exact. Q′/J statements are unchanged and
qualified as completeness obligations using guarded Q. No supplied private paper
is committed or reproduced. Frozen 117-item M4a remains untouched.

Claude supplied the source-only degeneration and read-only guard/consumer audit.
The first frozen draft failed 28.14s on a namespace call and full-record kernel
comparison. The private repair uses one opaque witness helper, the explicit
namespace call and omit hind in; the second run failed 2.01s on that section binder,
and the third passed 2.00s. Seven public/four private authored declarations and
four actual behaviors passed independently with standard axioms. The original
frozen bytes and both failures remain outside git. The repaired guarded nine-module
chain passes 16.00s warning-free. The previous run compiled with six touched
show→change warnings, one unused Fin.snoc simp argument, and five new long lines;
those exact style repairs are recorded, with no weakened checking. Normalized
proof bodies for every old declaration remain exact except the two deliberately
retyped JAssembly theorems. The diagnostic harness initially expected 18 additions;
its actual 24 authored additions (20 public/four private) and all ten genuine
behaviors passed; the count assertion was corrected with no source/fixture repair.

The separate origin-shift refutation privately passed default checking with two
public/two private declarations and two actual behaviors, but is deferred from
this focused checkpoint. It refutes action-origin uniqueness, not guarded
completeness. Next work is the genuine guarded extraction/group-action engine
and multiplication converse; no new frozen bookkeeping is authorized.


Final shared QA for the guarded checkpoint: full library/book compilation is green
80.02s (minimum available 35.93GiB, sampled family RSS10.91GiB); website generation
is green 8.00s (minimum 37.65GiB/RSS1.56GiB). The initial applied fullbuild stopped
98.03s at 29.22GiB as required; its evidence is retained and excluded from acceptance.
The serialized warm retry passed 10.00s (minimum 35.30GiB/RSS3.30GiB). Root waited for
each actual process exit before the next Lean/Lake family; the guarded slot stayed exclusive.

All 72 earlier actual fixtures and their62 combined public signatures/proofs/axioms
remain exact against the final main imports. The nine touched modules'125 scoped
declarations and ten new actual guarded/refutation behaviors also match the private
acceptance, with standard axioms only. This is a scoped audit, not a whole-library
axiom audit. The first shared harness added production style lint to the historical
external fixtures and found old whitespace diagnostics; that failed evidence is retained.
The fixtures are byte-exact and use their historical diagnostic lint scope; new actual
behaviors and production use standard lint, and every kernel invocation uses default
checking. No fixture or production proof was repaired for that harness mismatch.
The corrected shared run passed 20.00s (minimum 37.30GiB/RSS2.90GiB).

Claude's read-only final review found a nolinkurl escaping bug, clearer naming of both
source refutations, historical-sketch wording, missing spaces and two grammar nits.
These were fixed with no mathematics change. Source PDF now has 69pages after four
stable passes with no overflow/undefined label. All 20 selected current pages are visually
accepted: 13 current image bytes match previously actually viewed renders, and seven
changed/new pages were actually viewed after final repairs. Actual review caught an
orphaned final bibliography entry; two failed layouts remain outside git, and the
bibliography now starts on its own page. All 101 HTML pages remain, with current
refuted/guarded/open status and the frozen 117 record visible. Full source/byte guards
and exact 13-path stage/commit/push complete the checkpoint. Only the refutations,
necessary guards and conditional reduction are accepted; both guarded completeness
inputs, multiplication converse, ACF Q′/J completeness and group/action extraction remain open.
