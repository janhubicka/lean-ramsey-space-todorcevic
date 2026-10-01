# Formalization roadmap

## Abstract theorem

The repository formalizes Todorčević's abstract Ramsey-space theorem in layers.

| Todorčević ingredient | Lean module | Status |
|---|---|---|
| A.1 approximation system | RamseySpace.Basic | initial formalization |
| A.2 finitization and depth | RamseySpace.Finitization | initial formalization |
| A.3 amalgamation | RamseySpace.Axioms | statement |
| A.4 pigeonhole | RamseySpace.Axioms | statement |
| Ramsey / Ramsey-null sets | RamseySpace.Ramsey | definitions + basic lemmas |
| combinatorial forcing / Lemmas 4.31–4.35 | RamseySpace.Forcing, Decision, Reject, EndExtension | proved |
| abstract Baire = Ramsey (Lemma 4.36) | RamseySpace.Baire | in progress |
| abstract meagre = Ramsey null (Lemma 4.38) | RamseySpace.Baire | in progress |
| σ-field / σ-ideal closure (Lemmas 4.37–4.38) | planned | next |
| metrically closed ⇒ fusion complete | planned | |
| Ellentuck topology bridge | planned | |
| Abstract Ellentuck Theorem | planned | |

## Application boundary

This repository stays independent of successor trees. The intended dependency
points from lean-successors to this repository. The successor-tree project will
instantiate A.1--A.4; its Hales--Jewett pigeonhole argument is expected to
discharge A.4.
