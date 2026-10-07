# acl_geom

A formalization, in Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4),
of the Evans–Hrushovski–Gismatullin reconstruction theorem (recovering a field from the
combinatorial geometry of algebraic dependence over it), following the blueprint in
[`sources/blueprint.tex`](sources/blueprint.tex).

## Status

Work in progress; the theorem is not yet fully formalized. The current
coverage audit, open gaps and priorities are on issue
[#19](https://github.com/adamtopaz/acl_geom/issues/19), and
[`CONTINUATION.md`](CONTINUATION.md) is the handoff guide for contributors.
The library contains no `sorry` and no project axioms.

## Layout

* `AclGeom/` — the formalization itself (a Lean library depending on Mathlib).
* `AclGeomBook.lean`, `AclGeomBook/` — a [Verso](https://github.com/leanprover/verso)
  document (manual genre) that serves as a standalone exposition of the result.
  Lean code in the document is elaborated against the `AclGeom` library, so the
  displayed statements always match the formal development.
* `AclGeomBookMain.lean` — the executable that renders the document to HTML.
* `sources/` — the LaTeX blueprint.

## Building

```
lake exe cache get   # fetch Mathlib build cache (first time / after updates)
lake build           # builds the library, the document, and the renderer
```

## Generating and viewing the webpage

```
lake exe book
```

writes the website to `_out/html-multi`. Verso's HTML must be served over HTTP
(opening the files directly in a browser won't work), e.g.:

```
python3 -m http.server 8000 --directory _out/html-multi
```

then visit <http://localhost:8000>.
