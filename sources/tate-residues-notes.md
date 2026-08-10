# Notes: Tate's trace-theoretic residues

Reference for the residue theory formalized in
`AclGeom/Tate/FinitePotent.lean`, `AclGeom/Curves/TateResidue.lean`,
and `AclGeom/Curves/GlobalResidue.lean`.

Primary sources:

- J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS (4) 1
  (1968), 149–159.
- F. Pablos Romo, *On the general reciprocity law* (arXiv:1305.7066)
  — §2 restates Tate's definitions and property list in the form used
  here.

## The setup (as formalized)

For a k-vector space `V` and subspace `A`, Tate's commensurability
order `A ≺ B` means `A ⊆ B + (finite-dimensional)` (`AlmostLE`). An
endomorphism is **finite-potent** if some power has finite-dimensional
range; such operators have a **trace** computed on any *core* (a
finite-dimensional invariant subspace absorbing a power); the trace is
well-defined because the induced map beyond a core is nilpotent.

The **trace class** `E₀(A)` consists of `T` with range almost inside
`A` and `T(A)` finite-dimensional. For a place `P` of a function
field, `A := O_P` and the operators `ε∘m_f` (projection onto `O_P`
composed with multiplication) satisfy: the commutator
`[ε∘m_f, m_g] ∈ E₀`, and

```
res_P(f dg) := Tr [ε ∘ m_f, m_g]
```

is independent of the chosen projection `ε` (and of commensurable
changes of `A`, e.g. filtration stages `π^{−m}O_P`).

## Properties (with pointers to the formalization)

1. Bilinearity in `f` and `g` (`residue_add_left/right`,
   `residue_smul_left/right`).
2. `res(f dg) = 0` for `f, g ∈ O_P` — R2 (`residue_eq_zero_of_mem`).
3. `res(f dg) = 0` when `ord f ≥ m+1`, `ord g ≥ −m` — the threshold
   (`residue_eq_zero_of_ord_ge`); the mirror version
   (`ord f ≥ −m`, `ord g ≥ m+1`) is the next target.
4. `res(g⁻¹ dg) = ord_P(g)` for `ord g ≥ 0` (`residue_inv_self`),
   via the transversal-dimension count `dim O_P/gO_P = ord g`.
5. Leibniz: `res(x d(gh)) = res(xg dh) + res(xh dg)`
   (`residue_mul_right`).
6. Monomial table: `res(π^a d(π^b)) = 0` for `a+b ≠ 0`
   (`residue_zpow_pi_zpow_eq_zero`); `res(π^{−b} d(π^b)) = b`
   (`residue_zpow_pi_self`).
7. Residue theorem: `Σ_P res_P(f dg) = 0`
   (`sum_residue_eq_zero`), proved à la Tate by computing the trace of
   one global adelic commutator two ways (triple decomposition
   against the diagonal from Riemann–Roch 1.5.8, versus blockwise
   localization).
8. The functional `ω_g := (α ↦ Σ_P res_P(α_P dg))` is a Weil
   differential (`residueFunctional_mem_weilDifferentialsAt`),
   nonzero when `g` is a uniformizer
   (`residueFunctional_pi_ne_zero`).

These are consumed by the P6 rigidity argument described in
`CONTINUATION.md`.
