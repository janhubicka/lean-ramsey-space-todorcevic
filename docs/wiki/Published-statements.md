# Source correspondence: Todorčević Chapters 4 and 5

**Reference.** S. Todorčević, *Introduction to Ramsey Spaces* (2010), Chapter 4, ``4.1–4.3; Chapter 5, `5.1 and Theorem 5.4. [Publisher's table of contents](https://doi.org/10.1515/9781400835409). The source-level audit notes are also in [Chapter 4](../published-abstract-ramsey-audit.md) and [Chapter 5](../published-ellentuck-audit.md).

## Chapter 4 — Abstract Ramsey theorem, two sorts

Here `R` is the object space, `S` the reduction space, `r_n(A)` and `s_n(X)` are approximation sequences, `\le` orders reductions, and `\le^0` relates objects to reductions. The core is `RamseySpace.TwoSorted.System`.

| Printed ingredient | Lean declaration | Exact distinction |
| --- | --- | --- |
| A.1–A.3: first approximation is empty, separation, and coherence of initial segments | `TwoSorted.ApproximationSequence` for `R`; `ApproximationSystem` for `S` | `Approx n` is *indexed* by length, so no separate length-equality assertion is needed; `approx_surjective` says these are precisely realized approximations |
| A.4: finite reduction cones and recovery of `\le` | `TwoSorted.ReductionFinitization` | **No reflexivity or transitivity of finite `\le_{fin}` is assumed in Chapter 4** |
| A.4: finite cross cones, recovery of `\le^0`, mixed composition and prefix lifting | `TwoSorted.Finitization` | `leFin0` is between object and reduction *finite approximations*, not a single-sort shortcut |
| A.5: nonempty amalgamation at depth and refinement | `TwoSorted.AbstractRamseySystem.amalgamation_nonempty` and `amalgamation_refine` | Depth represented by the predicate `HasDepth a Y d` rather than a partial numeral |
| A.6: pigeonhole for next approximations | `TwoSorted.AbstractRamseySystem.pigeonhole_published` / `ofPublishedAxioms` | Published form starts with nonempty `[a,Y]`; the internal structure also supplies the uniquely determined depth proof |
| Closed reduction sort | `P.Red.IsMetricallyClosed` | The object sort need not itself be closed |
| Baire ⇔ Ramsey; meagre ⇔ null | `TwoSorted.abstractRamsey_iff` | The associated `S`-Baire and `S`-Ramsey notions are abstract, not Mathlib Baire-measurability |
| Full package, including countable and Souslin closure | `TwoSorted.abstractRamsey_full` | `AbstractRamseyConclusion` groups the separately proved results |

**Important negative test.** The Chapter 4 `ReductionFinitization` must *not* be replaced by the Chapter 5 `Finitization`: the latter requires a quasi-order and initial-segment law for the finite reduction relation, which are not part of Chapter 4's published A.4. The regression constructor in `scripts/CheckAbstractRamsey.lean` assumes only the Chapter 4 clauses.

## Chapter 5 — Abstract Ellentuck theorem

This uses a single set of infinite objects `S.Point` with a quasi-order, approximation maps `r_n`, and finite approximations `S.Approx n`.

| Printed ingredient | Lean declaration | Exact distinction |
| --- | --- | --- |
| A.1(1) `r_0(A)=\varnothing` | `ApproximationSystem.approx_zero` | The empty approximation is explicitly stored |
| A.1(2) uniqueness by all finite approximations | `ApproximationSystem.separated` | The contrapositive has the same content |
| A.1(3) length and coherence | indexed `Approx n`; `coherent` | The type index enforces equal length |
| A.2(1) finite `\le_{fin}` lower cones | `Finitization.lowerFinite` | Used critically for finite decision and fusion |
| A.2(2) approximation/order recovery | `Finitization.realizesOrder` | Direct equivalence |
| A.2(3) prefix lifting | `Finitization.prefix_leFin` | Written with typed `IsInitial` |
| A.3(1) amalgamation nonemptiness | `AbstractRamseySpace.amalgamation_nonempty` | Nonempty basic neighborhoods at appropriate depths |
| A.3(2) amalgamation refinement | `amalgamation_refine_published`, `ofPublishedAxioms` | The internal field omits only nonemptiness of output, **derivable from A.3(1)** |
| A.4 one-step pigeonhole | `AbstractRamseySpace.pigeonhole` | Homogeneity expressed as containment or disjointness |
| Closed approximation-code image | `ApproximationSystem.IsTychonoffClosed` | Discrete `(\bigcup_n AR_n)^\omega` product as printed |
| Theorem 5.4 | `RamseySpace.abstractEllentuck_textbook` | The exact basic-neighborhood Baire/meagre conclusions |

Two representation bridges matter:

1. `isTychonoffClosed_iff_isClosedApproximationImage` proves that the Tychonoff-product closure assumption is equivalent to the finite-prefix realization property used in fusion. `IsMetricallyClosed` is an implementation-friendly name for the latter; no countable metric is postulated.
2. `isTopologicalRamseySpace_iff_textbook` proves that the depth-preserving Ramsey and Ramsey-null predicates are equivalent to the printed predicates quantifying over **nonempty** `[a,A]` and producing a smaller `B\in[a,A]`.

The chosen version of A.3(2) is *not* the special case where `A\in[a,B]`. The special-case conclusion remains as `amalgamation_refine_onBasicMember`. Historical compatibility names obscuring that distinction have been removed from the public API.

## Direct and derived Theorem 5.4

`RamseySpace.abstractEllentuck_textbook` is proved by the direct one-sorted forcing/fusion development. `TwoSorted.abstractEllentuck_textbook_via_abstractRamsey` instead specializes Chapter 4 to the diagonal system `R=S` and `\le^0=\le`; the bridge `TwoSorted.diagonalAbstractRamseySystem` transforms the hypotheses. These *are deliberately independent proof paths*, not redundant theorem names.

## Classical Ellentuck example

`RamseySpace.Examples.Ellentuck.classicalEllentuck` verifies the whole instance on infinite subsets of the naturals represented by strictly increasing enumerations `\mathbb N\hookrightarrow_o\mathbb N`. Files `Examples/EllentuckBasic`, `Finitization`, `Depth`, `Amalgamation`, `Pigeonhole`, `Axioms` and `Closed` expose the actual witnesses. The pigeonhole proof uses an elementary infinite-pigeonhole argument rather than applying Abstract Ellentuck to prove its own A.4.

## Scope boundaries

This formalization proves the **abstract** Chapter 4 and Chapter 5 endpoints, the diagonal derivation, and the classical example. It does *not* mean every application throughout those chapters (infinite block sequences, located words, vector spaces, etc.) is independently formalized here. Likewise a generic finite-colouring consequence does not by itself establish that an arbitrary concrete tree, group, or ordered class satisfies A.4. The proof in an application must separately establish its own axioms.
