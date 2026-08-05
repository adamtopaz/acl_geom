# acl_geom

A formalization, in Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4),
of the Evans–Hrushovski–Gismatullin reconstruction theorem (recovering a field from the
combinatorial geometry of algebraic dependence over it), following the blueprint in
[`sources/blueprint.tex`](sources/blueprint.tex).

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

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
