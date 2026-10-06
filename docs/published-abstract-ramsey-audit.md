# Published Abstract Ramsey audit

Reference: Stevo Todorčević, *Introduction to Ramsey Spaces*, Chapter 4.
For a convenient verbatim summary of the Chapter 4 axioms, see
J. G. Mijares and J. E. Nieto, *A Parametrization of the Abstract Ramsey
Theorem*, §2.

This file records the source-facing correspondence for the two-sorted system
`(R,S,≤,≤⁰,r,s)`.  The implementation may use derived depth lemmas, but the
public data should not assume more than A.1--A.6.

## A.1--A.3: approximation sequences

The object sort is `TwoSorted.ApproximationSequence`; the reduction sort
reuses `ApproximationSystem`.  In both cases finite approximations are
indexed by their level, so the equality-of-length clause of A.3 is enforced
by typing.  Surjectivity says that `Approx n` is exactly the range of the
nth approximation map.

| Source | Lean | Audit |
|---|---|---|
| A.1 common zeroth approximation | `empty`, `approx_zero` | literal |
| A.2 separation | `separated` | equivalent extensional form |
| A.3 coherence | level-indexed `Approx n`, `coherent` | length equality by typing |

## A.4: finitization

The published two-sorted A.4 does **not** require the reduction relation
`≤fin` itself to be a quasi-order.  It asks only for finite lower cones,
recovery of `≤`, recovery of `≤⁰`, the mixed transitivity clause, and the
object-prefix lifting clause.

The Lean interface now matches those five clauses directly:

| Source | Lean |
|---|---|
| finite `≤fin` lower cones | `ReductionFinitization.lowerFinite` |
| finite `≤⁰fin` lower cones | `Finitization.lowerFinite0` |
| recover `X ≤ Y` | `ReductionFinitization.realizesOrder` |
| recover `A ≤⁰ Y` | `Finitization.realizesOrder0` |
| `a ≤⁰fin x ≤fin y → a ≤⁰fin y` | `Finitization.trans0` |
| object-prefix lifting | `Finitization.prefix0` |

An earlier version reused the one-sorted Chapter 5 `Finitization` for the
reduction side, which additionally assumed reflexivity, transitivity, and a
reduction-prefix axiom.  Those assumptions were unused and have been removed.

## A.5: amalgamation

`AbstractRamseySystem.amalgamation_nonempty` and
`AbstractRamseySystem.amalgamation_refine` are the two printed clauses.
Depth is represented relationally by `Finitization.HasDepth a Y d` instead
of by a partial integer-valued function.

## A.6: pigeonhole

The internal field carries the unique depth witness explicitly because this
is convenient for the forcing proof.  The source-facing theorem

`AbstractRamseySystem.pigeonhole_published`

takes only the printed compatibility hypothesis `[a,Y] ≠ ∅` and returns the
unique finite depth together with the homogeneous reduction.  Conversely,

`AbstractRamseySystem.ofPublishedAxioms`

builds the internal structure from this source-facing formulation.

## Closedness and theorem

Only the reduction sort is required to be closed.  The final theorem is
`TwoSorted.abstractRamsey`, with `abstractRamsey_iff` exposing the
Baire/Ramsey and meagre/Ramsey-null equivalences.  The diagonal development
then derives the one-sorted Abstract Ellentuck theorem from this Chapter 4
theorem.

CI contains a constructor-level regression check for A.4 and transitive axiom
reports for the published A.6 bridge and the final theorem.  In particular,
future refactors cannot silently reintroduce the stronger one-sorted
finitization assumptions.
