# Using `lean-ramsey-space-todorcevic`

This is a library for *building new Ramsey-space instances*. It does not assume trees, words, orders on finite structures, a fixed branching alphabet, or a concrete application. Use the weakest import that gives the lemma you need.

## Add a dependency

Place this in your Lake `lakefile.toml` and replace the revision by a checked commit from the [audit tracker](../audit-tracker-20261014.md):

```toml
[[require]]
name = "ramsey-space-todorcevic"
git = "https://github.com/janhubicka/lean-ramsey-space-todorcevic"
rev = "<tested-Git-SHA>"
```

Keep Lean and Mathlib versions compatible with the pinned version (inspect `lean-toolchain` and `lakefile.toml` of the library). Then run `lake update`, `lake exe cache get` and `lake build`. Both original consumers, `lean-milliken` and `lean-successors`, serve as integration tests, not as premises of this library.

## Minimal imports and example expressions

```lean
import RamseySpace.AbstractEllentuck
-- or: import RamseySpace -- full public umbrella

#check RamseySpace.ApproximationSystem
#check RamseySpace.Finitization
#check RamseySpace.AbstractRamseySpace
#check RamseySpace.AbstractRamseySpace.ofPublishedAxioms
#check RamseySpace.Finitization.fusionComplete_of_isMetricallyClosed
#check RamseySpace.abstractEllentuck_textbook
#check RamseySpace.isTopologicalRamseySpace_iff_textbook
```

A typical consequence for an already established one-sorted instance is:

```lean
import RamseySpace.AbstractEllentuck

example {S : RamseySpace.ApproximationSystem}
    (R : RamseySpace.AbstractRamseySpace S)
    (hc : S.IsTychonoffClosed) :
    RamseySpace.IsTopologicalRamseySpaceTextbook (S := S) :=
  RamseySpace.abstractEllentuck_textbook R hc
```

When the pigeonhole axiom A.4 is still under construction, fusion is *already available* from A.2 and closedness:

```lean
import RamseySpace.Closed

example {S : RamseySpace.ApproximationSystem}
    (F : RamseySpace.Finitization S)
    (hc : S.IsMetricallyClosed) :
    RamseySpace.FusionComplete S :=
  F.fusionComplete_of_isMetricallyClosed hc
```

This ordering is important for nontrivial applications: proving A.4 should not presuppose the Abstract Ellentuck theorem.

## One-sorted setup: A.1–A.4

Define `S : ApproximationSystem` with `Point`, typed `Approx n`, quasi-order `le`, approximation maps, surjectivity, empty level, separation and coherence. Realised approximation types are preferable to arbitrary syntax with a separate realizability predicate.

Define `F : Finitization S`: finite lower cones, recovered order, finite relation and the initial-segment compatibility axiom. The *typed* finite object `S.FiniteApprox := Σ n, S.Approx n` keeps its level in the object; do not conflate source length and ambient height in tree applications.

Package A.3 and A.4 by `AbstractRamseySpace.ofPublishedAxioms`. Its input A.3(2) requires **`A ≤ B` and `[a,A]` nonempty**, not the stronger accidental requirement `A ∈ [a,B]`. Its output includes nonemptiness of the refined `[a,A']`. If you already have `R`, the easy basic-member specialization is `R.amalgamation_refine_onBasicMember`.

Finally establish `S.IsTychonoffClosed` (or `S.IsClosedApproximationImage` and the equivalence lemma) and apply `abstractEllentuck_textbook`.

## Two-sorted setup: A.1–A.6

```lean
import RamseySpace.TwoSorted.AbstractRamsey

#check RamseySpace.TwoSorted.ApproximationSequence
#check RamseySpace.TwoSorted.System
#check RamseySpace.TwoSorted.ReductionFinitization
#check RamseySpace.TwoSorted.Finitization
#check RamseySpace.TwoSorted.AbstractRamseySystem.ofPublishedAxioms
#check RamseySpace.TwoSorted.abstractRamsey
#check RamseySpace.TwoSorted.abstractRamsey_iff
#check RamseySpace.TwoSorted.abstractRamsey_full
```

Use `System.Obj` for the object-approximation sequence and `System.Red` for the ordered reduction space; put `le0` between them. Establish `ReductionFinitization` and the cross finite relation `leFin0`. Chapter 4's finite reduction relation does **not** have to be a quasi-order; imposing the Chapter 5 finitization record as a substitute is an unjustified strengthening.

`TwoSorted.AbstractRamseySystem.ofPublishedAxioms` takes A.5 and the source-facing A.6; the compatibility predicate `F.HasDepth a Y d` is the *least* possible depth. Closedness is required only for `P.Red`. The result proves the `S`-Ramsey and `S`-Ramsey-null conclusions, plus their Baire/meagre characterizations and stronger countable/Souslin closure statements in `abstractRamsey_full`.

## Finite-colour consequences — no tree import

```lean
import RamseySpace.FiniteColouring

#check RamseySpace.ApproximationSystem.isOpen_approxColourFibre
#check RamseySpace.finiteBaireColouring
#check RamseySpace.finiteApproximationColouring
```

The first lemma shows that the fibre of a fixed approximation-level colouring is Ellentuck-open. The second homogenizes a finite Baire-fibre colouring of *points* of an arbitrary topological Ramsey space on a smaller basic neighbourhood. The third specializes to a finite colouring `colour : S.Approx m → κ` at a prescribed level. No Halpern–Läuchli or Milliken theorem is used by these proofs.

These generic statements moved from `lean-milliken` to this abstract library after the October 2026 minimality audit. Tree-specific strong-subtree corollaries remain in Milliken.

## Classical Ellentuck test case and diagnostics

The independent example is `RamseySpace.Examples.Ellentuck.classicalEllentuck`. Read `Examples/EllentuckPigeonhole.lean` for a concrete A.4 proof and `Examples/EllentuckAmalgamation.lean` for the printed A.3(2). To diagnose an instance, check A.1 coherence and surjectivity, finiteness of depth layers, both forms of A.3, a genuine A.4, and code closedness *in this order*.

Inspect trusted assumptions with `#print axioms YourMainTheorem`; our CI rejects `sorryAx` and anything outside standard Lean proof axioms. See the [audit tracker](../audit-tracker-20261014.md) for reproducible commands.
