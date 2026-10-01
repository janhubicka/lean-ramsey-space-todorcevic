# Formalization roadmap

## Abstract theorem

The repository formalizes Todorčević's abstract Ramsey-space theorem in layers.

| Todorčević ingredient | Lean module | Status |
|---|---|---|
| A.1 approximation system | `RamseySpace.Basic` | proved/interface complete |
| A.2 finitization and depth, including A.2(3) | `RamseySpace.Finitization` | proved/interface complete |
| A.3 amalgamation | `RamseySpace.Axioms` | source-faithful constructor + internal generalized form |
| A.4 pigeonhole | `RamseySpace.Axioms` | source-faithful interface |
| Ramsey / Ramsey-null sets | `RamseySpace.Ramsey`, `RamseySpace.Standard` | depth form + textbook form proved equivalent |
| combinatorial forcing / Lemmas 4.31–4.35 | `RamseySpace.Forcing`, `Decision`, `Reject`, `EndExtension` | proved |
| abstract Baire = Ramsey (Lemma 4.36) | `RamseySpace.Baire` | proved |
| σ-field closure of Ramsey sets (Lemma 4.37) | `RamseySpace.Sigma` | proved |
| abstract meagre = Ramsey null / σ-ideal | `RamseySpace.Baire`, `RamseySpace.NullSigma` | proved |
| metrically closed ⇒ fusion complete | `RamseySpace.Closed` | proved |
| Ellentuck topology bridge | `RamseySpace.Ellentuck`, `RamseySpace.TopologyBridge` | proved |
| Abstract Ellentuck Theorem | `RamseySpace.AbstractEllentuck` | proved |
| literal textbook theorem statement | `RamseySpace.AbstractEllentuck`, `RamseySpace.Standard` | proved |

There are no intentional `sorry`, `admit`, or extra axioms in the development.

## Classical Ellentuck validation

The standard Ellentuck space `([ℕ]^ω, ⊆, r)`, represented by increasing
enumerations `ℕ ↪o ℕ`, is now a complete validation example.

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
Boolean coloring of tail offsets; no Ramsey-space theorem is used in the
validation itself.

## Next targets

1. Add a small downstream-application API so a client project normally only
   proves A.1--A.4 and metric closedness.
2. Connect `lean-sucessors` to this repository and instantiate the framework
   for successor trees.
3. In the successor-tree instance, isolate the Hales--Jewett argument precisely
   as the proof of A.4.

## Application boundary

This repository stays independent of successor trees. The intended dependency is

```text
lean-ramsey-space-todorcevic
             ↑
             |
      lean-sucessors
```

The successor-tree project should instantiate the source-faithful A.1--A.4
interface. Its Hales--Jewett pigeonhole argument is expected to discharge A.4.
