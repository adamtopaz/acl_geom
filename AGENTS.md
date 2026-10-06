# Rules for agents working in this repository

These rules apply to every agent working on `acl_geom`, alongside the handoff
guide in [`CONTINUATION.md`](CONTINUATION.md). If the two disagree, this file
wins.

## Hard rules

1. **Never read secrets.** Do not open, print, copy or search for credentials
   of any kind: API keys, tokens, passwords, SSH or signing keys, `.env`
   files, `gh` authentication data, chit account keys, other agents' tokens,
   or environment variables that hold them. If a task seems to need a secret,
   stop and ask Adam on a GitHub issue.
2. **GitHub scope is this repository only.** The only thing on GitHub that
   agents may act on is `adamtopaz/acl_geom`: its issues, branches, commits,
   pull requests and CI runs. Do not create, modify, comment on or delete
   anything else on GitHub (other repositories, gists, account or
   organization settings), and do not change this repository's settings,
   secrets or Pages configuration unless Adam asks for it on an issue.
3. **Talk to Adam only through GitHub issues** on this repository. Questions
   that block work use the `question-for-adam` label. Issue comments are
   posted through Adam's `gh` account; do not add signature lines.
4. **No unproved mathematics.** No `sorry`, `admit` or project `axiom` on
   `main`. Never axiomatize a blueprint statement. A result that depends on an
   unproved hypothesis must name that hypothesis in its statement and must
   never be described as proved.
5. **Sources stay out of git.** Paywalled or private papers that Adam
   provides live outside the repository
   (`/home/adam/projects/autoformalization/acl_geom-sources/`) and are never
   committed or quoted at length in the repository.

## Avoiding technical debt

- **Every declaration earns its place.** New code should prove a blueprint
  statement or be a reusable lemma with a named consumer. Do not grow chains
  of normalization or bookkeeping that do not converge on a blueprint
  statement (see the frozen M4a log in `CONTINUATION.md` and #19).
- **Check targets before building toward them.** Before investing in an
  interface such as `AffineGridExtraction`, check that it is not false or
  vacuous (#22). When a target turns out to be wrong, commit a refutation
  lemma alongside the corrected statement.
- **Keep claims accurate.** Docstrings, `**Status:**` lines, the book and
  `CONTINUATION.md` must match what is actually proved. Update them in the
  same change as the code they describe.
- **Keep builds fast.** Keep modules focused and imports narrow; split files
  that grow past a few thousand lines (#18).
- **Leave no dead ends.** Delete superseded code, or mark it superseded with
  an issue reference. Fix deprecation warnings in code you touch. Any
  `set_option` that weakens checking needs a comment saying why.
- **Prefer Mathlib.** Use existing Mathlib API before writing local versions.
  Write code to Mathlib's standards so it could be upstreamed.

## Mathematical fidelity

- `sources/blueprint.tex` is the source of truth. If you find an error in it,
  report it on an issue with a counterexample or refutation before changing
  any statement, and keep the provenance of the original wording.
- Blueprint statements that the Lean route bypasses remain obligations. Do not
  close them merely because nothing uses them.

## Collaboration between agents

- Two agents share this checkout: `aclgeom.claude` and `aclgeom.codex`. They
  coordinate through chit direct messages and agree on file ownership before
  editing.
- Only one Lake build family runs at a time in the shared checkout. Stop a
  build if available memory falls below 30 GiB. Never run `lake` inside
  `.lake/packages`.

## Workflow

- Validate with a full `lake build` and `lake exe book` before every commit.
- Commit and push at every natural checkpoint, in small increments that are
  always green.
- After each substantive push, post a progress comment on the relevant issue.
