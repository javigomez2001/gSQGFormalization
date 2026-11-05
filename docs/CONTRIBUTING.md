# Maintaining the formalization

Changes should preserve agreement between the paper, the Lean statements, the blueprint and the
reported proof status. Read [CONVENTIONS.md](CONVENTIONS.md) before changing mathematical
interfaces.

## Mathematical changes

Keep the compiler and dependency versions pinned unless the purpose of the change is an explicit
upgrade. Build the complete root after changing a statement or proof:

```bash
lake build GSQG
blueprint/tools/refresh.sh --lean
lake env lean --run blueprint/tools/AllAxioms.lean GSQG /tmp/gsqg-all-axioms.json
```

Check quantifiers, uniform constants, domains, convergence, regularity and normalization against
the manuscript. A complete proof of a weakened statement is not a faithful formalization. When a
statement's Lean encoding differs in form from the paper, explain it in the declaration's docstring
and in [PAPER_MAP.md](PAPER_MAP.md).

The reporting tools follow private helpers and transitive axioms. The only permitted logical
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Reporting changes

The Python reporting tools use the standard library. Their regression checks are:

```bash
python3 -m unittest discover -s blueprint/tools/tests
python3 blueprint/tools/tests/check_lean_status.py
node blueprint/tools/tests/check_dashboard.js
python3 blueprint/tools/tests/check_rendered_graph.py
```

The compiled extractor regression uses a temporary fixture with deliberate admissions and an
extra axiom; that fixture is never imported by the mathematical project.

After changes to blueprint statements, dependency edges or status, rebuild the website as described
in [blueprint/README.md](../blueprint/README.md). The generated graph, PDF and dashboard should refer
to the same checked snapshot. `build_site.py --target <label>` selects the dashboard's primary
theorem (default `thm:main`).

## Citation metadata

Update the paper title and citation metadata in [CITATION.cff](../CITATION.cff) when publication
details are available. The GitHub checks build the project and check the axioms of every
declaration on each push to `main` and each pull request.
