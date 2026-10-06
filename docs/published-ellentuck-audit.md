# Published Abstract Ellentuck audit

Reference: Stevo Todorčević, *Introduction to Ramsey Spaces*, Annals of
Mathematics Studies 174, Princeton University Press, 2010, Chapter 5,
§5.1, especially the displayed axioms A.1--A.4 and Theorem 5.4.

This audit was done in three deliberately separate adversarial passes.

## Referee A — axioms

The printed one-sorted axioms are represented as follows.

| Source | Lean | Audit |
|---|---|---|
| A.1(1) `r₀(A)=∅` | `ApproximationSystem.approx_zero` | literal |
| A.1(2) separation | `ApproximationSystem.separated` | equivalent contrapositive |
| A.1(3) equal approximations have equal length and equal earlier approximations | level-indexed `Approx n` plus `coherent` | length equality is enforced by typing |
| A.2(1) finite lower cones of `≤fin` | `Finitization.lowerFinite` | literal |
| A.2(2) finitization of `≤` | `Finitization.realizesOrder` | literal |
| A.2(3) initial-segment compatibility | `Finitization.prefix_leFin` | literal after typed `IsInitial` |
| A.3(1) nonempty amalgamation at depth | `AbstractRamseySpace.amalgamation_nonempty` | literal |
| A.3(2) `A ≤ B`, `[a,A]≠∅`, and `∅≠[a,A']⊆[a,A]` | `AbstractRamseySpace.amalgamation_refine_published` | literal; internal field drops only the A.3(1)-redundant nonemptiness conjunct |
| A.4 one-step pigeonhole | `AbstractRamseySpace.pigeonhole` | complement is written equivalently as disjointness |

A previous API comment incorrectly called the special case
`A ∈ [a,B]` the "textbook A.3(2)".  That special case is sufficient to
derive the printed A.3(2), but it is not the statement on the page.  The
preferred constructor is now `AbstractRamseySpace.ofPublishedAxioms`.
The old `ofStandardAxioms` and `amalgamation_refine_standard` names are
kept only so existing applications such as the fat-tree development do not
break.

The classical Ellentuck validation now explicitly proves the full printed
A.3(2), including `[a,A'] ≠ ∅`, as
`Examples.Ellentuck.amalgamation_refine` and packages the space through
`ofPublishedAxioms`.

## Referee B — theorem statement

Theorem 5.4 says that a closed triple satisfying A.1--A.4 is a topological
Ramsey space: every set with the property of Baire is Ramsey and every
meagre set is Ramsey null.

The public source-facing endpoint is now

`RamseySpace.abstractEllentuck_textbook`.

Its conclusion is `IsTopologicalRamseySpaceTextbook`, which uses the
literal Chapter 5 definitions: for every nonempty basic neighborhood
`[a,A]`, there is `B ∈ [a,A]` whose `[a,B]` is homogeneous (or
disjoint in the Ramsey-null case).

The forcing proof internally uses a depth-preserving formulation because it
composes better.  The theorem
`isTopologicalRamseySpace_iff_textbook` proves that this internal
formulation is equivalent to the printed basic-neighborhood one under
A.1--A.4.

The closedness hypothesis is exposed as
`ApproximationSystem.IsClosedApproximationImage`.  It is the finite-prefix
characterization of closedness of the approximation image in the product of
the discrete level spaces.  The older name `IsMetricallyClosed` is a
compatibility alias.

## Referee C — proof dependencies and circularity

CI checks both the direct proof of Abstract Ellentuck and the independent
derivation through the two-sorted Abstract Ramsey Theorem.

The checked endpoints include:

- `AbstractRamseySpace.ofPublishedAxioms`;
- `isTopologicalRamseySpace_iff_textbook`;
- `abstractEllentuck_textbook`;
- `TwoSorted.abstractEllentuck_textbook_via_abstractRamsey`;
- the classical Ellentuck specialization.

The audit rejects `sorryAx` and any transitive axiom beyond Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.  Fusion remains derived
from A.2 plus closedness alone, so applications can use fusion while proving
A.4 without circularly assuming the Ramsey-space theorem.

## Result

After the cleanup there are two intentionally different API layers:

1. the **published interface**, used for statements, examples, and source
   comparison;
2. the **depth-form implementation interface**, used internally by the
   combinatorial forcing proof.

They are formally connected by equivalence theorems rather than being
silently conflated.
