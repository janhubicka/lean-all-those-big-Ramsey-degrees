# Validation ledger: poset-diaries-fat-trees

Baseline: manuscript main at 43c862790a9cea38717f1e59fa4230b325a1a19e.
Counts are equal-weight proof obligations, not estimates of remaining effort.
I = complete proof code written, pending check; V = exact statement checked on
a successful commit with a transitive axiom audit; O = open. V also counts as
implemented. A theorem conditional on an unproved manuscript premise does not
close that premise. The status of imported declarations is audited separately.

| Track | Implemented | Verified | Units |
|---|---:|---:|---:|
| A. Ternary words and boring extensions | 2/7 (28.6%) | 0/7 | 7 |
| B. Diaries and shape maps | 0/6 | 0/6 | 6 |
| C. Rooted successor monoid and fat images | 0/6 | 0/6 | 6 |
| D. Synchronisation and unrooted Ramsey | 0/5 | 0/5 | 5 |
| E. Generic poset and type-complete levels | 0/5 | 0/5 | 5 |
| F. Copy space and abstract Ellentuck | 0/7 | 0/7 | 7 |
| **Overall** | **2/36 (5.6%)** | **0/36 (0%)** | **36** |

## Obligations and interfaces

| ID | Status | Manuscript label / deliverable |
|---|---|---|
| A1 | I | def:delta: finite level distance, zero/triangle/bound |
| A2 | I | lem:extend: clipped minimum extension, including empty domain |
| A3 | O | def:word-prec and eq:short-word: order laws, prefix truncation |
| A4 | O | def:word-elt, def:comp: coordinate order and compatibility |
| A5 | O | prop:orders: linear extensions, mixed transitivity, compatible cases |
| A6 | O | eq:delta-iso: append isometry and pair distance classification |
| A7 | O | lem:boring and rem:polymorphism: exact equivalence on compatible sets; clarify full-level wording |
| B1 | O | def:posetdiary: exact four diary events |
| B2 | O | def:interesting: interesting levels and shape deletion |
| B3 | O | shape maps, uniqueness, embeddings and composition |
| B4 | O | lem:lift(1): shape preservation under ambient maps |
| B5 | O | lem:lift(2): extension of rooted equal-shape maps |
| B6 | O | cited poset-diary representation and relative embedding-type bridge |
| C1 | O | def:stree: rooted forest, levels, successor operation |
| C2 | O | prop:monoid: insertion maps and closed monoid M1 |
| C3 | O | prop:monoid: M2 skip decomposition |
| C4 | O | prop:monoid: M3 duplication |
| C5 | O | lem:cone-cover: canonical fat maps and cone coverage |
| C6 | O | thm:shaperamseyN, thm:shapeborel: finite action and Borel/Baire transfer |
| D1 | O | lem:sync: interval/prefix and block coding |
| D2 | O | lem:sync: root retention and exact embedding-type conclusion |
| D3 | O | finite colour transfer, thm:unrooted(1) |
| D4 | O | Borel continuity and all-copy factorization |
| D5 | O | thm:unrooted(2): exact Borel statement |
| E1 | O | generic poset: one-point types, countability and extension property |
| E2 | O | prop:complete: construct a type-complete diary (including cited construction) |
| E3 | O | lem:hereditary: type-complete levels of copies |
| E4 | O | lem:word-amalg(1): rooted universality fixing finite leaves |
| E5 | O | lem:word-amalg(2): countable extension respecting the prescribed subforest; block and sandwich argument |
| F1 | O | lem:axioms: typed approximations, A1 |
| F2 | O | lem:axioms: A2, depth/terminal-level formula |
| F3 | O | lem:axioms: closedness of the approximation image |
| F4 | O | lem:a31-a4: A3.1 |
| F5 | O | lem:a31-a4: A4 finite restriction and all extensions |
| F6 | O | prop:a32: ordinary A3.2, no weakening |
| F7 | O | thm:main: exact topological Ramsey-space theorem via abstract Ellentuck |

## Parallel work boundaries

A is independent; B uses A3–A7, C uses A1–A7 and the successor API. E1 and the
block/sandwich core of E5 can start independently of B/C/D. D1 can be developed
with word order and then joined with B/C; F1/F2 can start on the copy interface
once B fixes its representation. F3 uses E3; F4/F5 use C/D/E; F6 uses D/E.
F7 joins all F obligations. Work initially in joint commits, with no per-track
CI matrix. Do not create six expensive builds. Only promote I to V against
the actual commit and audit output.

## Adversarial review checkpoints

- Distinguish prefix partial order from coded partial order, including mixed
  length comparisons. The full ternary level is not in general compatible.
- Check M2 when the skipped level is immediately before the first image
  level, and M3 with relative (not absolute) levels. Check root preservation.
- Upstream finite theorem has a typed action; prove that it is the manuscript
  composition. Upstream fat Borel endpoint accepts Baire fibres; prove the
  pullback and neighbourhood/cone comparison, not just surjectivity.
- E2 imports a cited, modified diary construction, not a theorem already in
  Lean. Keep the leaf-only step and type bijectivity explicit.
- A3.2 proof must handle arbitrary (X\subseteq Y) with nonempty [a,X],
  not just a basic member, and preserve the exact recorded prefix tree.
- For E5, verify distinctness of block-encoded words and bounds, every
  outside word's first m+1 complete blocks, and the infinite union embedding.
- Closedness must show every surviving recorded prefix is eventually realised
  by a leaf; a naive inverse limit of finite leaf sets is insufficient.
- Initial extension uses the clipped candidate set containing 2; on the empty
  domain it picks 2, rather than the manuscript's 1. Both satisfy the
  existential theorem; no claim of identical empty-domain formula.

Initial status: implementation only, no successful build. No separate
referee agent was available; the checks above are manual review obligations.
