# Manuscript-marker follow-up validation

These checks were completed on 2026-11-24 after adding `WordLex.lean` and
exporting its general ternary-word lexicographic statements from both packages.
All four commands passed. The root namespace audit checks 1,307 declarations;
the optional mathlib/Milliken audit checks 3,163. Both permit only `propext`,
`Classical.choice`, and `Quot.sound`; the new three public statements use only
`propext` and `Quot.sound`.

`validation.json` records the commands, exit codes, toolchain, and hashes of
the changed Lean files. The adjacent logs retain the compiler output, with
trailing whitespace stripped. These are local checks; GitHub Actions reports
publication checks separately. The parent directory preserves the earlier
complete chain-degree validation without changing its historical counts.
