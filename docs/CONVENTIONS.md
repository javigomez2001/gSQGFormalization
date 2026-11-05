# Lean conventions for the gSQG formalization

The source paper is `paper/gsqg_Nov26.tex`; the blueprint is `blueprint/src/chapters/`. The pinned
compiler and dependency revision are in `lean-toolchain` and `lake-manifest.json`. Do not update
them as part of routine proof work.

Fresh clones use Lake's ordinary local `.lake` directory. Some working copies use an external
`.lake` symlink; preserve it. If that cache is read-only, build in a writable copy with the same
inputs and use the reporting script's `--project` option. A source scan is not a compiled check.

## Modules

- `GSQG/Definitions/*.lean`: shared definitions — operators, function spaces, the approximate family,
  and the statement predicates of the fixed-point backbone. `GSQG/Auxiliary/`: special integrals.
- `GSQG/Sec1_Introduction/`, `Sec3_FixedPoint/`, `Sec4_Analysis/`, `Sec5_ApproximateSolution/`,
  `Sec6_LinearInverse/`, `Sec7_NonlinearEstimates/`, `AppendixAB/`: the paper's sections, in order.
  `Sec3_FixedPoint/MainTheorem.lean` assembles Theorem 1.1; `Sec1_Introduction/GeometricFrontEquation.lean`
  bridges the formal operator to the paper's literal geometric front equation.
- `GSQG/SchauderEstimate/`: the interior fractional Schauder estimate (cited in §4, proved here).
- `GSQG/PatchEquation/`: derivation of the front equation from the 2D weak patch system.
- `docs/PAPER_MAP.md`: every numbered statement of the paper and its Lean declaration.

Use existing declarations rather than adding local copies. Cross-module imports are allowed when
acyclic; check downstream consumers after changing a statement.

## Faithful statements

1. Match the paper and blueprint's quantifiers, domains, regularity, convergence, and conclusions.
   Put `∃ C, 0 < C ∧ ∀ ...` before every parameter in which the constant must be uniform. Distinct
   implicit constants in the paper need not be identical in Lean. Do not assume the desired result
   or weaken a statement merely to make its proof easier.
2. Use `deriv`, `iteratedDeriv`, `HasDerivAt`, `ContDiff`, and the common `GSQG/Definitions` API. A
   bound on Lean's total derivative alone does not assert differentiability. Include the regularity
   needed by users of the lemma, and distinguish pointwise from almost-everywhere assertions.
3. When the paper asserts convergence, state `Integrable`, `IntegrableOn`, `IntervalIntegrable`, or
   the appropriate improper-limit property. A Bochner integral's default value is not convergence.
   Parenthesize integral terms in sums: an integral binder extends over subsequent summands.
4. Real-valued `xNorm`, `yNorm`, and Hölder norms use `ENNReal.toReal`. Supply membership or finiteness
   before using such a quantity as a norm; `⊤.toReal = 0` must never make an estimate vacuous.
5. Keep the Fourier convention, `c_α`, and all scaling powers consistent with `GSQG/Definitions`. If
   using a distributional or chosen representative, explicitly prove the representation property;
   membership of the default zero function alone is insufficient.
6. Definitions must not hide `sorry` in data. Use an explicit existence theorem before choice when
   necessary. Do not introduce `axiom`, `native_decide`, `implemented_by`, or opaque proof shortcuts.
   Do not set `maxHeartbeats` above 800000.
7. When a Lean statement encodes a paper statement in a particular way (an explicit threshold, a
   truncation parameter, a more general range), explain the encoding in the declaration's docstring
   and in `docs/PAPER_MAP.md`. Check every consumer and rebuild the full project after changing a
   statement.

## Blueprint nodes and status

Use `GSQG.` plus the blueprint label without `def:/lem:/prop:/thm:/cor:` where practical. Every
node lists its declarations in `\lean{...}`; every declaration has exactly one owning node. Other
nodes refer to that owner through `\uses`, not by duplicating its Lean-name mapping. Separate pure
definitions and statement predicates from theorems that establish their properties. Do not add
generated `\leanok` markers to maintained sources.

The dashboard distinguishes:

- **Locally proved**: the checked proof has no `sorry` except through other blueprint declarations.
  Non-blueprint helpers, including private helpers, are followed.
- **Fully proved**: all listed declarations exist and their transitive Lean axiom sets contain no
  `sorryAx` or unexpected axioms. This is independent of omissions in the handwritten graph.
- **Source inventory**: a textual approximation, never a kernel certificate. Missing generated or
  external declarations remain unknown. Stale compiled reports are explicitly marked stale.

The standard logical axioms `propext`, `Classical.choice`, and `Quot.sound` are permitted. A locally
proved main theorem with unfinished upstream lemmas is not a completed formalization. Proof status
concerns the Lean statements as written; their correspondence with the paper is recorded in
`docs/PAPER_MAP.md`.

## Validation and reporting

Check a module with `lake env lean GSQG/<Folder>/<Module>.lean` (for example
`lake env lean GSQG/Sec5_ApproximateSolution/E5.lean`). Imported `.olean` files must match the changed
statements; a source check against stale imports does not validate integration.

From the project root:

```bash
blueprint/tools/refresh.sh --lean
WITH_LEAN=1 blueprint/build.sh
python3 -m unittest discover -s blueprint/tools/tests
```

`--lean` builds the complete `GSQG` root before collecting status, even when optional module names
are supplied. The reports include fingerprints of the Lean/blueprint inputs and refuse to publish
a supposedly current result if those inputs change during checking. For a fast unverified preview,
use `blueprint/tools/refresh.sh --source`. Keep `blueprint/README.md` synchronized with the
reporting commands.
