# All those big Ramsey degrees — Lean

Companion formalization of `janhubicka/All-those-big-Ramsey-degrees`.
The manuscript is authoritative for mathematical scope. This is a Lean/Std-only
library with no mathlib dependency. Run `lake build`, then `lake env lean Checks.lean`.

## Interface index

| Module | Main interfaces |
| --- | --- |
| `Relational` | `Language`, `RelStructure`, `Embedding`, `Enumeration`, `EnumeratedStructure`, `OrderedEmbedding`, `BigRamseyBound`, `IsBigRamseyDegree`, `HasFiniteBigRamseyDegrees` |
| `FullTypes` | `FullType`, `typeOf`, `SameFullType`, `evaluate_reindex`, `evaluate_rebase`, coordinate and parameter restriction |
| `TypeRespecting` | `Prefix`, `TailTuple`, `SameType`, `NTypeRespecting`, `MaximumArity`, `TypeRespecting`; identities, composition and downward monotonicity |
| `MetricInterpolation` | `clip`, its bounds/fixed-value/positivity/Lipschitz/pair-sum lemmas, `interpolation`: natural-number scalar core |
| `GroupLabelTypes` | `Compatible`, `eq_of_anchor`, `restrict_compatible`, `restriction_injective`, `typeMap_covers`, `same_profile_pair` |
| `TwoColourTriangles` | `Triangle`, `SmallSAP`, `Listed`, `classification`, `mixed_only_fails`: exact small-base palette classification |
| `TriangleRepair` | `RepairSystem`, `step`, `run`, `AtAnchor`, `run_fixed`, `run_pairs`, `step_anchor`, `run_anchor`, `run_covers`, `uniform_choice` |
| `ThreeColourCertificates` | `Triangle`, `RepairLaw`, `Obstruction`, `SmallSAP`, `certifiedSystem`; checked repair/obstruction/relabelling/classification certificates and `classified_smallSAP` |
| `LatticeInterpolation` | `LatticeAdd`, `clip`, `clip_bounds`, `clip_fixed`, `clip_nonzero`, `clip_nonexpansive`, `clip_pair_bound`, `interpolation`: partially ordered scalar core |

Full types mean **full quantifier-free types**, including internal relations,
unary information and repeated relation entries. Big Ramsey degrees count
embeddings. Enumeration is separate from the language. `NTypeRespecting n` tests
all tuple sizes at most `n`, including finite tails. `MaximumArity` requires a
positive sharp bound (or value one), not an arbitrary arity parameter.

`typeOf` and `SameFullType` use atomic relational diagrams. To interpret these
as realised full types, parameter and future-vertex naming together must be
injective. The `Prefix`/`TailTuple` application satisfies this requirement.
More general coordinate restrictions are available for pulled-back diagrams.

## Uniform triangle repair

`uniform_choice` constructs one rule on an arbitrary type set Q by processing
any list covering the finite base. It proves simultaneously that every anchor
triangle is valid, every possible future-pair colour is preserved, and every
protected value which was initially valid is fixed.

Q need not be finite, and the base size has no bound. `RepairSystem` contains
three finite colour identities, not an assumption of the desired uniform-choice
conclusion. The theorem's seed pair law and valid base/type profiles are explicit.
The manuscript derives them from the genuine type-amalgamation request.

The certificate module exhausts all 1024 symmetric three-colour triangle
palettes up to the six colour permutations. Its 208 representatives consist of
23 with displayed repair operations, the square palette (169), and 184 with
explicit failed one-point strong-amalgamation requests over bases of size at
most three. In the original labels the counts are 106, 6 and 912. The finite
identities, genuine obstruction validity, relabellings and exhaustive coverage
are checked by ordinary `decide` in the Lean kernel, not `native_decide`.
The displayed counts are also checked by the manuscript's separate verifier.
The square has no repair operation of this form; the manuscript proves its
TRAP through finite homogeneous quotients and valid-type coverage.

## Lattice-valued interpolation

`LatticeAdd` lists standard lattice and commutative monoid laws, with additive
translations preserving meets and joins. It assumes neither a linear order nor
an interpolation conclusion. The proved rule is
`clip lower upper original = meet (join lower original) upper`.
The pair-bound proof distributes addition over both meets; it never assumes
two arbitrary distance values are comparable. The positivity result separately
assumes that a meet of nonzero values is nonzero.

The manuscript instantiates this argument for finite lattice-valued metrics,
including distributive-lattice ultrametrics with meet-irreducible zero and any
finite number of bounded integer metrics on a common vertex set. Prescribed
type maps may mix coordinates. Metric endpoint geometry, the induced local
triangle repair, cycle completion and the relational TRAP interpretation are
written proofs, not yet Lean instantiations of this scalar module.

## Validation

Foundations at `b44a67b98744590825680904a5d8d53140dd7ffb` passed run
`38271277558`; metric interpolation at `36c600fa1cedca9d00cc5b68a4932ddada42c080`
passed run `38279289894`. Group-profile and two-colour modules at
`424ea0ad09e6e3bdf63efd1a78062e90ac763b5c` passed run `38295072697`.
Uniform repair and three-colour certificates, with consolidated dependency
reports, passed at `04b7a27d80032971afe45306886aa70869d100a1` in Actions run
`38299496216`, job `114978660403`.
Lattice interpolation at `ffa04e9450788f05b26b685e7166ed2c85cfcc32` passed the
build and proof-dependency checks in run `38303147784`, job `114990695365`.
These runs used Lean `v4.35.0-rc3`. The present integration retains both branches
and requires its own consolidated CI run. No custom axiom or proof placeholder
is used. `Checks.lean` is the single dependency-report entry point.

## Remaining interfaces and proofs

Coherent full-type maps, their uniform continuation property and the manuscript
TRAP property are not yet concretely encoded. The split equivalence, arity
reduction and covered-type lemma retain written proofs. For metric TRAP the
endpoint geometry and all-continuations interpretation still need formalizing.
The natural-number and lattice scalar modules have different explicit inputs;
no silent specialization of a linear-order argument to a lattice is made.

For triangle repair, connect the checked invariant and certificates to full-type
interfaces. For finite homogeneous quotients, formalize coordinate fibres,
saturation by a continuation, and valid-type surjectivity. `classified_smallSAP`
assumes small AP for the canonical representative; the checked colour equivalence
supports the written relabelling argument. It does not itself assert an undefined
class-level strong AP or TRAP predicate. For lattice metrics, construct finite
lower/upper endpoints and instantiate the local-repair theorem.

The manuscript proves TRAP for all 112 strong-AP three-colour triangle palettes
and for the stated lattice-valued metric families, for arbitrary finite bases.
These are not yet end-to-end Lean TRAP theorems. The unrestricted cycles-and-cliques
conjecture and general upper-bound Ramsey theorem remain unproved here.
Internal weak-type comparison is absent from this public repository. Mathematical
reviews are self-audits, not independently spawned referee reports.
