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

## Validation examples

Next targets:

1. Formalize the classical Ellentuck space `([ℕ]^ω, ⊆, r)` and instantiate
   A.1--A.4 using the source-faithful constructor. This is the main sanity
   check that the abstraction matches the standard example.
2. Derive the usual Ellentuck theorem from `abstractEllentuck_onBasicNeighborhoods`.
3. Add a small API for downstream applications so that a project normally only
   proves A.1--A.4 and metric closedness.

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
