# Todorčević's abstract Ramsey-space theorems — Lean research library

This is the source-controlled research wiki for [lean-ramsey-space-todorcevic](https://github.com/janhubicka/lean-ramsey-space-todorcevic). The purpose is to let mathematicians *reuse* a verified Ramsey-space library, not to tie the formalization to either of its initial consumers.

The repository has two substantial mathematical theorems:

* **Abstract Ramsey theorem, Chapter 4:** for a two-sorted system `(R,S,\le,\le^0,r,s)` satisfying A.1–A.6, with the reduction side closed.
* **Abstract Ellentuck theorem, Chapter 5, Theorem 5.4:** for a closed one-sorted approximation space satisfying A.1–A.4, every Baire set is Ramsey and every meagre set is Ramsey null.

Both the direct one-sorted proof and the independent *diagonal specialization of the Chapter 4 theorem* are available. An instance for the classical Ellentuck space `[\mathbb N]^\omega` provides an end-to-end test.

## Guide to the library

| Page | For |
| --- | --- |
| **[Using the library](Using-the-library.md)** | Lake dependency, imports, constructors and examples for new Ramsey spaces |
| **[Published statements](Published-statements.md)** | Exact A.1–A.6 and A.1–A.4 correspondence, closedness and theorem scopes |
| **[Proof architecture](Proof-architecture.md)** | Readable forcing, accept/reject, fusion, diagonal and Souslin proofs; comparisons with printed arguments |
| **[Auxiliary lemmas](Auxiliary-lemmas.md)** | Index of useful finite-depth, prefix, fusion, topology, closure and finite-colour lemmas |
| **[Adversarial referee record](Adversarial-referee-record.md)** | Separately executed mathematical, kernel-trust and minimality/dependency attack passes |
| **[Audit tracker](../audit-tracker-20261014.md)** | Exact source/CI/downstream validation state and follow-up criteria |
| **[Publishing the wiki](Publishing.md)** | Sync from source-controlled Markdown to the separate GitHub Wiki Git repository |

## Start from the mathematical endpoints

```lean
import RamseySpace

-- Chapter 5: literal Tychonoff closedness and textbook basic neighbourhoods.
#check RamseySpace.abstractEllentuck_textbook
-- Chapter 4: two-sorted Abstract Ramsey Theorem.
#check RamseySpace.TwoSorted.abstractRamsey
#check RamseySpace.TwoSorted.abstractRamsey_full
-- Chapter 5 obtained independently as a Chapter 4 diagonal case.
#check RamseySpace.TwoSorted.abstractEllentuck_textbook_via_abstractRamsey
-- Concrete classical Ellentuck example.
#check RamseySpace.Examples.Ellentuck.classicalEllentuck
-- Application-independent finite-colour corollaries.
#check RamseySpace.finiteBaireColouring
#check RamseySpace.finiteApproximationColouring
```

The shortest path for a new application is to provide an `ApproximationSystem` and `Finitization`, prove the source-facing A.3/A.4 hypotheses, establish metric closedness from approximation codes, and invoke `abstractEllentuck_textbook`. For Chapter 4 applications, use `TwoSorted.System`, `TwoSorted.Finitization` and the A.5/A.6 package. Fusion already follows from finitization plus closedness; there is no circular dependence on pigeonhole.

## What is — and is not — claimed

The final Lean declarations are proofs of the statements shown by their types. A filename or a paper comparison is *not* itself a proof. The full Abstract Ramsey and Abstract Ellentuck endpoints, their diagonal connection, and the classical Ellentuck validation have kernel-checked proofs in the baseline. The statement-by-statement audit distinguishes genuinely formalized conclusions from related, unformalized examples and applications elsewhere in Todorčević's book. It does not claim that every theorem in Chapters 4 and 5 has been separately formalized.

The source of truth for this Wiki is `docs/wiki/`. Proof status must be checked at the documented CI commit. Source: Stevo Todorčević, *Introduction to Ramsey Spaces*, Annals of Mathematics Studies 174, Princeton University Press, 2010, Chapters 4 and 5.
