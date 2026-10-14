# Auxiliary lemma index — mathematical guide

The names below are exact or namespace-qualified Lean declarations, grouped by their *mathematical job*. The list includes useful intermediate results not normally named as separate theorems in the published Chapter 4 or 5 proofs.

## Initial segments and basic neighborhoods

| Lean declaration | Meaning |
| --- | --- |
| `ApproximationSystem.FiniteApprox` and `finiteApprox` | `Σ n, Approx n` and the packaged `n`th approximation |
| `IsInitial`; `isInitial_of_point` | a pair of finite approximations comes from one point and has increasing lengths |
| `isInitial_left_eq_of_right_point` | an initial segment of `r_m(Y)` must be `r_n(Y)` |
| `neighborhood_initial_subset` | a longer approximation yields a smaller basic neighborhood |
| `levelNeighborhood_mono` | if `X∈[n,Y]` then `[n,X]⊆[n,Y]` |
| `oneStepApproximations` and `oneStepApproximations_mono` | admissible one-step approximations, monotone in the reduction |

## Finitization, depth and amalgamation

| Lean declaration | Meaning |
| --- | --- |
| `Finitization.HasDepth` | least index at which a finite approximation is finitely below `B` |
| `hasDepth_unique` | every finite approximation has at most one depth in a given `B` |
| `depthApproximations_finite` | finitely many approximations occur for a fixed exact depth |
| `exists_hasDepth_of_mem_neighborhood` | genuine compatibility witnesses existence of a depth |
| `hasDepth_iff_of_mem_levelNeighborhood` | depth preserved by a same-depth refinement |
| `exists_hasDepth_ge_of_le` | long prefixes eventually have arbitrarily high depth below a reduction |
| `AbstractRamseySpace.amalgamation_refine_onBasicMember` | useful special case of full published A.3(2) |
| `amalgamation_refine_published` | restore the printed nonempty output from A.3(1) |

The two-sorted counterparts are under `TwoSorted.Finitization`; its `le0_trans` is *proved* from the mixed finite composition axiom rather than separately assumed.

## Fusion and forcing

| Lean declaration | Meaning |
| --- | --- |
| `ApproximationSystem.IsFusionFrom` | decreasing sequence with successively protected finite prefixes |
| `FusionComplete.exists_limit` | a fusion sequence has a common infinite limit preserving its selected finite prefixes |
| `Finitization.fusionComplete_of_isMetricallyClosed` | fusion from A.2 and closedness alone |
| `CombinatorialForcing.Accepts`, `Rejects`, `Decides` | forcing predicates used to dichotomize neighborhoods |
| `exists_global_decider` | one refinement decides all finite approximations at relevant depths |
| `exists_refinement_rejects_oneStep` | one-step pigeonhole turns rejection into a useful avoidance condition |
| `exists_refinement_rejects_endExtensions` | fusion makes rejection persistent along relevant longer prefixes |
| `isRamsey_iUnion` and `isRamseyNull_iUnion` | sigma closure, using finite-level stabilization before fusion |

The analogous two-sorted lemmas live in `TwoSorted.CombinatorialForcing`; some require the separate `TwoSorted.Finitization` fields that are absent from the one-sorted system.

## Topological bridges and exact theorem wrappers

| Lean declaration | Meaning |
| --- | --- |
| `ApproximationSystem.IsEllentuckOpen` | open unions of actual basic neighborhoods |
| `isOpen_ellentuck_iff` | this definition is the topology's `IsOpen` predicate |
| `isTychonoffClosed_iff_isClosedApproximationImage` | printed product topology ↔ finite-prefix closedness |
| `isRamsey_iff_onBasicNeighborhoods` | depth-preserving formulation ↔ printed nonempty-neighborhood Ramsey property |
| `isRamseyNull_iff_onBasicNeighborhoods` | corresponding equivalence for the null notion |
| `isTopologicalRamseySpace_iff_textbook` | both forms of the final topological theorem agree |
| `abstractEllentuck_textbook` | Chapter 5, Theorem 5.4 |
| `TwoSorted.abstractRamsey_iff` and `abstractRamsey_full` | Chapter 4 conclusions, including sigma and Souslin closures |
| `TwoSorted.abstractEllentuck_textbook_via_abstractRamsey` | Chapter 5 theorem as a diagonal consequence of Chapter 4 |

## Generic finite-colour tools

| Lean declaration | Human-readable statement |
| --- | --- |
| `ApproximationSystem.isOpen_approxColourFibre` | fixing the colour of the `m`th approximation defines an open set |
| `finiteBaireColouring` | any finite colouring of infinite points whose fibres have the Baire property becomes constant on a basic-neighborhood refinement |
| `finiteApproximationColouring` | any finite colouring of one approximation level becomes constant on all such approximations visible inside a refined basic neighborhood |

These three declarations now live in `RamseySpace.FiniteColouring`, with no dependence on Milliken. They are *abstract consequences*, not additional axioms.

## How to find a lemma by need

For a new topological Ramsey space, start from `Basic`, `Finitization`, `Axioms`, `Closed` and `AbstractEllentuck`. For Chapter 4 applications, start at `TwoSorted.Basic` and `TwoSorted.Finitization`. For analytic closure under the Souslin operation, see `TwoSorted.SouslinEnvelope` and `SouslinClosure`. To inspect a proof without importing unrelated examples, import that module directly. The [Using the library](Using-the-library.md) guide has minimal imports and examples.
