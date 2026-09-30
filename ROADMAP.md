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
| metrically closed approximation space | planned | next |
| accept/reject decision lemma | planned | next |
| fusion | planned | next |
| open sets are Ramsey | planned | |
| meagre sets are Ramsey-null | planned | |
| Baire-property sets are Ramsey | planned | |
| Abstract Ellentuck Theorem | planned | |

## Application boundary

This repository stays independent of successor trees. The intended dependency
points from lean-sucessors to this repository. The successor-tree project will
instantiate A.1--A.4; its Hales--Jewett pigeonhole argument is expected to
discharge A.4.
