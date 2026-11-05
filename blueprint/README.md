# Blueprint and progress website

The blueprint is the informal proof of the paper, organized as a dependency graph of definitions and
results. Each node links to its Lean declaration. The chapter titles name the paper sections they
cover, and [../docs/PAPER_MAP.md](../docs/PAPER_MAP.md) gives the correspondence for every numbered
statement.

- `src/`: leanblueprint sources. Chapters 1–10 follow the paper; chapters 12–13 cover the two
  results beyond the paper.
- `site/`: the generated website (`site/index.html` dashboard, `site/blueprint/` HTML, `site/blueprint.pdf`).
- `CONVENTIONS.md`: node format and labels.
- `tools/`: Lean status extraction (`LeanStatus.lean`), the all-declaration axiom check
  (`AllAxioms.lean`), source inventory, validation and site generation.
- `build/lean_status.json`: the fingerprinted compiled status report behind the saved dashboard.

The dashboard opens from `file://` and has overview, dependency graph, node table and QA views. KaTeX and Cytoscape load from CDNs, so math rendering and the
graph need internet.

**Status:** all 553 nodes are fully proved: 476 results and 77 definitions, mapping to 825 Lean
declarations. The verification steps are listed in the [top-level README](../README.md#verification).

## Build and refresh

Run from the project root:

```bash
# Complete authoritative refresh: build every imported Lean module and collect axiom data.
blueprint/tools/refresh.sh --lean

# Full HTML/PDF site using a fresh Lean build.
WITH_LEAN=1 blueprint/build.sh

# Re-render using the cached report; its freshness is checked and displayed.
blueprint/build.sh

# Fast inventory while editing; this is explicitly unverified.
blueprint/tools/refresh.sh --source
```

The renderer requires `latexmk`, `pdflatex`, Graphviz, and a leanblueprint installation. On Debian
or Ubuntu, the TeX packages `texlive-latex-extra`, `texlive-fonts-recommended` and
`texlive-science`, together with `latexmk` and `graphviz`, provide the needed system tools.
The default Python
virtual environment is `~/.venvs/gsqg-blueprint`; override it with `BLUEPRINT_VENV`. To create it:

```bash
python3 -m venv ~/.venvs/gsqg-blueprint
~/.venvs/gsqg-blueprint/bin/pip install -r blueprint/requirements.txt
```

`BLUEPRINT_SKIP_PDF=1` explicitly requests an HTML-only build. Otherwise a failed PDF or HTML build
fails the command and retains the previous site. Logs are copied into `blueprint/build/` on failure.
The normal build stages outputs before publishing; generated status markers are inserted only in a
copy of the LaTeX, so the rendered blueprint and dashboard use the same evidence.

To check a writable copy when the original external `.lake` cannot be written:

```bash
blueprint/tools/refresh.sh --lean --project /tmp/gsqg-review-build
WITH_LEAN=1 LEAN_PROJECT=/tmp/gsqg-review-build blueprint/build.sh
```

The build copy must contain identical Lean and blueprint inputs. Its root `GSQG` import is always
built. The existing `.lake` symlink must not be replaced. `LEAN_STATUS=/absolute/path/report.json`
can supply another report; missing files fail, and reports without matching provenance are not
certified as current.

## What the numbers mean

“Locally proved” means the proof is complete relative to other blueprint declarations. “Fully
proved” means Lean's transitive axiom collection finds no `sorryAx` and no unexpected axioms in any
listed declaration. Standard logical axioms remain allowed. Definitions are counted separately
from theorem proofs. The main theorem is not fully proved while any admitted dependency remains.

A source scan does not establish that files compile. Generated structure fields and external names
are unknown until checked by Lean. Compiled reports carry a source fingerprint, timestamp and
compiler version; old reports cannot silently certify new edits. Actual Lean dependencies supplement
the maintained dependency graph. QA reports ownership conflicts, missing dependencies, cycles and
unexpected axioms; a cycle caused by grouped blueprint nodes is not a circular Lean proof.

Proof status concerns the Lean statements as written; their correspondence with the paper's
numbered statements is given in [../docs/PAPER_MAP.md](../docs/PAPER_MAP.md).

## Maintenance checks

```bash
python3 -m unittest discover -s blueprint/tools/tests
python3 blueprint/tools/tests/check_lean_status.py
node blueprint/tools/tests/check_dashboard.js
python3 blueprint/tools/sync_uses.py --check
python3 blueprint/tools/tests/check_rendered_graph.py
```

`sync_uses.py` reads current source chapters and detects omitted proof references. Use `--apply`
only after reviewing whether a citation is a proof prerequisite; explanatory references can point
to later results. The tool allows forward edges but refuses edges that would introduce a cycle.

`build_site.py` is the parser and dashboard generator; `collect_status.py` orchestrates full builds
and snapshot validation; `LeanStatus.lean` follows actual compiled dependencies, including private
helpers; `source_status.py` provides the unverified inventory; `render_status.py` annotates staged
LaTeX; `status_common.py` owns provenance and atomic JSON writes. Successful full site builds also
refresh `lean_decls`. The dashboard's primary theorem is `thm:main`; `build_site.py --target LABEL`
selects another one.

`site/` is ready for static hosting; it is not currently deployed.
