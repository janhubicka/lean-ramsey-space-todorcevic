# Formalization roadmap

## Status

Both of Todorčević's principal abstract Ramsey theorems are formalized.  The
development contains no intentional `sorry`, `admit`, or additional
`axiom` declarations.

## Chapter 4: Abstract Ramsey Theorem

The two-sorted development follows the data
`(R, S, ≤, ≤⁰, r, s)`.

| Ingredient | Lean module | Status |
|---|---|---|
| object approximation sequence A.1--A.3 | `RamseySpace.TwoSorted.Basic` | proved/interface complete |
| reduction approximation system A.1--A.3 | `RamseySpace.Basic` | proved/interface complete |
| A.4 finitization `≤fin`, `≤⁰fin` | `RamseySpace.TwoSorted.Finitization` | proved/interface complete |
| A.5 amalgamation | `RamseySpace.TwoSorted.Axioms` | proved/interface complete |
| A.6 pigeonhole | `RamseySpace.TwoSorted.Axioms` | proved/interface complete |
| S-Ramsey / S-Ramsey-null / S-Baire / S-meagre | `RamseySpace.TwoSorted.Ramsey` | defined |
| closedness ⇒ fusion completeness of S | `RamseySpace.TwoSorted.Closed` | proved |
| accept/reject/decision forcing | `RamseySpace.TwoSorted.Forcing`, `Decision` | proved |
| one-step rejection propagation | `RamseySpace.TwoSorted.Reject` | proved |
| rejection of all end-extensions | `RamseySpace.TwoSorted.EndExtension` | proved |
| S-Baire iff S-Ramsey | `RamseySpace.TwoSorted.Baire` | proved |
| S-meagre iff S-Ramsey-null | `RamseySpace.TwoSorted.Baire` | proved |
| **Abstract Ramsey Theorem** | `RamseySpace.TwoSorted.AbstractRamsey` | **proved** |

The main theorem is

```lean
theorem TwoSorted.abstractRamsey
    (R : TwoSorted.AbstractRamseySystem P)
    (hclosed : P.Red.IsMetricallyClosed) :
    TwoSorted.IsRamseySpace R
```

and `TwoSorted.abstractRamsey_iff` records the stronger pair of equivalences.

## Chapter 5: Abstract Ellentuck Theorem

| Ingredient | Lean module | Status |
|---|---|---|
| A.1 approximation system | `RamseySpace.Basic` | proved/interface complete |
| A.2 finitization and depth | `RamseySpace.Finitization` | proved/interface complete |
| A.3 amalgamation | `RamseySpace.Axioms` | source-faithful constructor + internal generalized form |
| A.4 pigeonhole | `RamseySpace.Axioms` | source-faithful interface |
| combinatorial forcing | `RamseySpace.Forcing`, `Decision`, `Reject`, `EndExtension` | proved |
| abstract Baire iff Ramsey | `RamseySpace.Baire` | proved |
| abstract meagre iff Ramsey null | `RamseySpace.Baire` | proved |
| Ramsey σ-field / Ramsey-null σ-ideal | `RamseySpace.Sigma`, `NullSigma` | proved |
| metric closedness ⇒ fusion complete | `RamseySpace.Closed` | proved |
| Ellentuck topology and topological bridge | `RamseySpace.Ellentuck`, `TopologyBridge` | proved |
| **Abstract Ellentuck Theorem** | `RamseySpace.AbstractEllentuck` | **proved** |
| literal basic-neighborhood formulation | `RamseySpace.AbstractEllentuck`, `Standard` | proved |

## Relationship between the two theorems

`RamseySpace.TwoSorted.Diagonal` constructs the diagonal two-sorted system
with `R = S` and `≤⁰ = ≤`, and proves that the two-sorted Baire/Ramsey and
meagre/Ramsey-null notions reduce to the one-sorted notions.

`RamseySpace.TwoSorted.AbstractEllentuckViaRamsey` then derives the complete
topological Abstract Ellentuck theorem from the Abstract Ramsey theorem:
open sets are handled through the diagonal S-Baire theorem, nowhere-dense sets
through the diagonal S-meagre theorem, and the meagre/Baire-property cases by
the Ramsey-null sigma ideal and the usual open-plus-meagre decomposition.

Thus the repository contains both an independent one-sorted proof and a
machine-checked derivation of Abstract Ellentuck from Abstract Ramsey.

## Classical Ellentuck validation

The standard Ellentuck space `([ℕ]^ω, ⊆, r)`, represented by increasing
enumerations `ℕ ↪o ℕ`, is a complete validation example.

| Ingredient | Lean module | Status |
|---|---|---|
| A.1 | `Examples.EllentuckBasic` | proved |
| A.2 + depth API | `Examples.EllentuckFinitization`, `EllentuckDepth` | proved |
| A.3(1), A.3(2) | `Examples.EllentuckAmalgamation` | proved |
| A.4 infinite pigeonhole | `Examples.EllentuckPigeonhole` | proved |
| package A.1--A.4 | `Examples.EllentuckAxioms` | proved |
| metric closedness | `Examples.EllentuckClosed` | proved |
| classical Ellentuck theorem | `Examples.EllentuckTheorem` | proved |

The A.4 proof uses only the ordinary infinite pigeonhole principle for a
Boolean coloring of tail offsets; no abstract Ramsey theorem is used in the
validation.

## Next targets

1. Add small convenience constructors/API for concrete two-sorted
   applications.
2. Add another standard two-sorted example from the Ramsey-space literature
   as an independent validation of A.1--A.6.
3. Continue source-by-source auditing against Todorčević's notation and theorem
   numbering.
