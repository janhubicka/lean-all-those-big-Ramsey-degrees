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
any list covering the finite base. It proves simultaneously:

* every base-anchor triangle is valid;
* every possible future-pair colour is preserved;
* every protected value which was initially valid is fixed.

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

The square has no repair operation of this form. The manuscript proves its
TRAP via the finite homogeneous quotient theorem and the covered-type lemma.
Thus no general claim that a repair always exists is made.

## Validation

Foundations at `b44a67b98744590825680904a5d8d53140dd7ffb` passed run
`38271277558`; metric interpolation at `36c600fa1cedca9d00cc5b68a4932ddada42c080`
passed run `38279289894`. Group-profile and two-colour modules at
`424ea0ad09e6e3bdf63efd1a78062e90ac763b5c` passed run `38295072697`.
The uniform-repair module and every three-colour certificate at
`54fb32adf222c11c7dbb23ec4dc2f9d4208740c5` passed the library build in Actions
run `38297965889`, job `114973570239`, on Lean `v4.35.0-rc3`.
The present commit consolidates all dependency reports into `Checks.lean`,
which is run by CI; the unused separate checks file is removed.
No custom axiom or proof placeholder is used.

## Remaining interfaces and proofs

Coherent full-type maps, their uniform continuation property and the manuscript
TRAP property are not yet concretely encoded. The split equivalence, arity
reduction and covered-type lemma retain written proofs. For metric TRAP the
endpoint geometry and all-continuations interpretation still need formalizing;
the scalar module uses ordinary natural-number addition, not every distance monoid.

For triangle repair, connect the checked abstract invariant and finite certificates
to the relational full-type interfaces. For the square and general finite
homogeneous quotients, formalize coordinate fibres, saturation by a continuation,
and the resulting surjectivity of valid type maps. `classified_smallSAP` currently
assumes the small-AP property of the canonical representative; the checked
colour equivalence supports the written relabelling argument. It does not itself
assert an undefined class-level strong AP or TRAP predicate.

The manuscript now has a complete written proof of TRAP for all 112 strong-AP
three-colour triangle palettes, for arbitrary finite bases. This is not yet an
end-to-end Lean theorem. The unrestricted cycles-and-cliques conjecture and the
general upper-bound Ramsey theorem remain unproved here. Internal weak-type
comparison material is absent from this public repository. Mathematical reviews
are self-audits, not independently spawned referee reports.
