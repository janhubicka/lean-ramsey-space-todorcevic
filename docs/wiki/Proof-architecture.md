# Proof architecture and differences from the printed proofs

The main formalization has two deliberately distinct proof paths: the direct Chapter 5 forcing proof, and the Chapter 4 two-sorted proof together with its diagonal Chapter 5 specialization. Their separate existence is a meaningful mathematical cross-check rather than a reason to delete one path.

## The book's mathematical picture

A Ramsey-space structure has infinite objects `X`, finite approximations `r_n(X)`, and a refinement order. Its basic neighborhood is

```text
[a,B] = { X : X ≤ B and r_n(X) = a }    where a has length n,
[n,B] = [r_n(B),B].
```

The forcing theorem must refine `B` while preserving finite initial information. The asymmetry between the reduction side `S` and the objects `R` is real in the Chapter 4 theorem; Chapter 5 is the diagonal specialization.

## Stage 1: approximation and finite depth

`RamseySpace.Basic` enforces zero approximation, separation and initial-segment coherence. The finite syntax is indexed by source level. `Finitization` recovers the infinite order from the finite one and proves that the level of first compatibility is unique:

```text
HasDepth a B d:
  a ≤fin r_d(B), and a is not ≤fin r_e(B) for every e < d.
```

Finite lower cones yield finite sets `depthApproximations B d`. This finiteness, rather than any global finite set of all approximations, drives decision at each stage. `exists_hasDepth_ge_of_le` is the unbounded-depth escape needed for countable unions and extensions.

For two-sorted objects, the reduction finitization cannot be imported unchanged from the one-sorted theory: Chapter 4 A.4 deliberately assumes fewer properties of `≤fin`. The mixed `leFin0` and its prefix lifting lemma are separate.

## Stage 2: forcing by acceptance and rejection

`Forcing.lean` introduces `Accepts`, `Rejects` and `Decides`. Acceptance is inclusion of a basic neighborhood in the target; rejection means that no admissible same-depth refinement can accept. The two directions propagate under reduction, but not by a naive unconstrained monotonicity statement: whenever nonemptiness is relevant, it must be retained.

`Decision.lean` first decides finitely many prefixes, then decides a complete finite depth layer, and finally fuses a sequence of increasingly protected decisions (`decisionFusion`, `exists_global_decider`). The *finite lower-cone* assumption is what makes the finite-stage induction legitimate.

## Stage 3: rejecting all end-extensions

`Reject.lean` uses A.4 to refine a rejection of `a` so that one-step extensions cannot all be accepted. `EndExtension.lean` iterates this, with finite depth layers and `rejectionFusion`, to obtain a reduction rejecting every relevant longer approximation. At this stage A.3 prevents an empty neighborhood from being substituted for a genuine witness.

This is the combinatorial heart of the proof. Replacing `[a,A] ≠ ∅` by `A ∈ [a,B]` everywhere would produce a stronger, *nonpublished* axiom and conceal a real hypothesis. The bridge in `Standard.lean` proves equivalence of the convenient depth-form and genuine basic-neighborhood Ramsey definitions.

## Stage 4: fusion from closedness

`Closed.lean` defines an approximation code `c(n)`, finite-prefix realizability, and closedness of the image. For a fusion sequence `Y_k`, finite blocks of its stable approximation code are realized; closedness produces an infinite limit `X`. Finitization then proves `X ≤ Y_k` for all `k`.

Crucially, `Finitization.fusionComplete_of_isMetricallyClosed` uses **only A.2 and code closedness**. In Chapter 4 the weaker `ReductionFinitization` provides the corresponding two-sorted fusion via `TwoSorted.Closed`. Neither proof assumes A.3 or A.4.

`ClosedTopology.lean` supplies an explicit equivalence with the book's topology: the range of `X ↦ (n ↦ ⟨n,r_n(X)⟩)` is closed in the Tychonoff product of the discrete disjoint union of all finite approximation levels. The dependent code and the literal `AR^ω` code are not silently identified.

## Stage 5: Baire and meagre, then topology

`Baire.lean` identifies abstract Baire sets with combinatorially Ramsey sets and abstract meagre sets with Ramsey-null sets. `Sigma.lean` and `NullSigma.lean` obtain countable closure by deciding finitely many initial targets, then fusing. `TopologyBridge.lean` converts topological nowhere-dense and Baire-measurable sets for the actual Ellentuck topology.

The final `abstractEllentuck` theorem uses those bridges; `abstractEllentuck_textbook` then switches to the printed closedness and basic-neighborhood predicates by two **proved equivalences**. This is more explicit than leaving the distinction between source notation and implementation as a comment.

## Stage 6: Chapter 4 and Souslin closure

`TwoSorted.Forcing`, `Decision`, `Reject`, `EndExtension` and `Baire` implement the genuinely two-sorted version. The Souslin proof additionally uses `TwoSorted.Relative`, `RelativeSigma`, `SouslinDecision`, `SouslinEnvelope` and `SouslinClosure`. Its envelope construction is a refined countable-stage argument: choose approximations along a branch and control their residuals to show that the Souslin operation preserves the `S`-Ramsey property.

`TwoSorted.abstractRamsey_full` packages the Baire/Ramsey equivalence, meagre/null equivalence, countable closures, and Souslin closure. The Souslin result is stronger than merely stating `abstractRamsey`, and should be verified as its own endpoint.

## Stage 7: the diagonal bridge

`TwoSorted.Diagonal` sets the two sorts equal and identifies `≤⁰` with `≤`. The published A.1–A.4 data construct the corresponding Chapter 4 structure. Its bridge lemmas identify the one- and two-sorted neighborhoods, depths, and abstract Baire/meagre/Ramsey notions. `AbstractEllentuckViaRamsey.lean` builds Theorem 5.4 from Chapter 4 *without invoking the direct* `abstractEllentuck` theorem.

## Differences from the published presentation

1. Finite approximation *length* is encoded in the type `Approx n` instead of a separate length function. `approx_surjective` keeps this representation faithful.
2. Partial depth is a proposition `HasDepth a B d` with a uniqueness theorem, not a partial natural-valued function.
3. The internal A.3(2) omits only the output nonemptiness conjunct, which is proved by A.3(1). `ofPublishedAxioms` and `amalgamation_refine_published` restore the complete printed form.
4. Closedness is used operationally through finite-prefix realizability, then proved equivalent to literal Tychonoff closedness of the approximation-code range.
5. Forcing uses named stage selectors and explicit fusion witnesses to expose construction invariants to Lean. Some of these are useful standalone lemmas rather than numbered paper statements.
6. The two independent proofs are retained, but compatibility-only constructors and misplaced application-independent colour lemmas are retired.

This page describes the *actual proof graph*, not a conjectured equivalence between unrelated Ramsey theorems. The theorem statements and audit evidence are collected in [Published statements](Published-statements.md) and [Adversarial referee record](Adversarial-referee-record.md).
