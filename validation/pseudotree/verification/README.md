# Completed validation record

These are the final local validation results from 2026-11-24, on Lean
`v4.35.0-rc3`. The dependency pins and the three import-only upstream changes
are documented in the parent README and `../import-patches/`.

| Check | Result | Record |
| --- | --- | --- |
| Root `lake build` | Passed | `root-build.txt` |
| Existing `Checks.lean` | Passed | `root-existing-checks.txt` |
| Existing `ChecksFullTypes.lean` | Passed | `root-full-types.txt` |
| Existing `PartialTypesChecks.lean` | Passed | `root-partial-types.txt` |
| Root `PseudotreeChecks.lean` | Passed; 1,304 declarations audited | `root-pseudotree-axioms.txt` |
| Optional `lake build PseudotreeValidation` | Passed; 3,457 dependency jobs | `optional-build.txt` |
| Optional `Checks.lean` | Passed; 3,160 declarations audited | `optional-axioms.txt` |

The optional audit includes the final `chain_degree` and
`chain_degree_diaries` theorems in the repository's original
`IsBigRamseyDegree` API, the concrete infinite-degree theorem, and all their
transitive dependencies. Its allowlist contains exactly `propext`,
`Classical.choice`, and `Quot.sound`; any additional axiom is an error.
The source scan additionally found no `sorry`, `admit`, `native_decide`, or
custom `axiom` declaration in either new pseudotree source directory.

`validation.json` records commands, exit statuses, the toolchain, source-scan
result, and hashes of the reviewed manuscript artifacts. `source-sha256.json`
records every checked pseudotree source file. The original mathematical
statements, exact scope, proof changes, and independent finite checks are
explained in `../../../docs/Pseudotree-Audit.md` and
`../../../docs/Pseudotree-Mathlib.md`.

Compiler log lines have trailing whitespace stripped; messages and recorded
exit statuses are unchanged. This record captures local validation completed
before publication. GitHub Actions results are recorded separately on the
pull request and commits.
