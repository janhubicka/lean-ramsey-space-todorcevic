# Ramsey-space library adversarial audit tracker — 14 October 2026

## Goal and baseline

The library is intended as a reusable, mathematically faithful verification of Todorčević's Abstract Ramsey theorem (Chapter 4) and Abstract Ellentuck theorem (Chapter 5), **not** as a private appendix to Milliken or successors. The audit starts from `janhubicka/lean-ramsey-space-todorcevic` main at `0515f911ad1cc2eb619ca4bc22f75f2e7c386944`. The source of tracked changes is [PR #14](https://github.com/janhubicka/lean-ramsey-space-todorcevic/pull/14).

## Review evidence and dispositions

| Referee question | Baseline finding | Action / evidence |
| --- | --- | --- |
| Does Chapter 5 A.3(2) have the printed hypotheses? | Yes, the published constructor requires `A≤B` and `[a,A]` nonempty. The legacy special-case constructor was confusingly named. | Retired `ofStandardAxioms` and `amalgamation_refine_standard`; retained the useful `amalgamation_refine_onBasicMember`. Check `scripts/CheckPublishedEllentuck.lean`. |
| Does Chapter 4 A.4 silently require an order on `≤fin`? | No: `TwoSorted.ReductionFinitization` does **not** assume reflexivity/transitivity of the finite relation. | Preserve weaker Chapter 4 structure; constructor-level test in `scripts/CheckAbstractRamsey.lean`. |
| Does A.4 require the conclusion it is used to prove? | No: `Finitization.fusionComplete_of_isMetricallyClosed` needs only A.2 and approximation closedness. | Keep the independent theorem; check `scripts/CheckFirstApplication.lean`. |
| Are the two closedness notions actually equal? | The book's discrete Tychonoff product code and finite-prefix-realisation criterion are proved equivalent in `ClosedTopology`. | Keep conversion and published theorem type test. |
| Does the direct proof sneakily invoke the two-sorted theorem (or vice versa)? | The one-sorted forcing development and diagonal two-sorted specialization are separately proved. | Retain both independent proof paths, not redundant aliases. |
| Is the complete Chapter 4 theorem audited? | Baseline checked Baire/Ramsey but omitted separate `Souslin` and `AbstractRamseyConclusion` #print axioms endpoints. | Add all three checks to `scripts/CheckAbstractRamsey.lean`. |
| Do generic colour lemmas belong to Milliken? | No: they mention only arbitrary topological Ramsey spaces. | Move `finiteBaireColouring` and `finiteApproximationColouring` (and open colour-fibre lemma) to `RamseySpace.FiniteColouring`; remove duplicate downstream file. |
| Does one umbrella import need every proof module explicitly? | No: final theorem modules import their transitive prerequisites. | Reduce `RamseySpace.lean` to canonical public endpoints; verify full build/consumer imports. |
| Are the applications and auxiliary lemmas explained to new users? | Baseline README covered main theorems but not enough proof structure or API navigation. | Publish source-controlled researcher wiki pages with mathematical crosswalk and theorem/lemma descriptions. |

## Independent adversarial passes

1. **Semantic referee:** compare the *unfolded hypotheses* of A.1–A.6 and A.1–A.4, the full statement of Theorem 5.4, and topological closedness with the actual published hypotheses. Probe witness emptiness, minimality of depth, and reduction/object-sort confusion.
2. **Proof-integrity referee:** inspect the import graph for dependence cycles, trace forcing, decision, rejection and Souslin closures, reject source admissions and nonstandard transitive kernel axioms on final theorem endpoints, and separately verify the diagonal derivation.
3. **Minimality / API referee:** compare declarations and imports with all consumers; remove compatibility names only when replacements are source-faithful and regression-tested; relocate application-independent proofs to the correct library without importing tree-specific material.

These are separately organized *adversarial review perspectives*, not claims of independently recruited human referees or external verification.

## Reproducible checks

Run on the PR commit and the merged commit:

```bash
lake update
lake exe cache get
lake build
lake env lean scripts/CheckFirstApplication.lean
lake env lean scripts/CheckPublishedEllentuck.lean
lake env lean scripts/CheckAbstractRamsey.lean
lake env lean scripts/CheckFiniteColouring.lean
```

The workflow `.github/workflows/lean.yml` records logs and checks the number of `#print axioms` reports with `scripts/check-axiom-log.py`. Only `propext`, `Classical.choice` and `Quot.sound` are accepted. The source audit rejects `sorry`, `admit`, and locally declared `axiom`.

## Consumer integration and release gate

Three consumers require updates: [lean-successors PR #413](https://github.com/janhubicka/lean-successors/pull/413), [lean-milliken PR #153](https://github.com/janhubicka/lean-milliken/pull/153), and [lean-dualtree PR #273](https://github.com/janhubicka/lean-dualtree/pull/273). They all use the audited core revision `263e11eefa81fefc17896392fb48bf09c8ac6f3e`, verified by [GitHub Actions run 38625850153](https://github.com/janhubicka/lean-ramsey-space-todorcevic/actions/runs/38625850153), and its merged PR #14 (merge commit `ead838518f36f160ed04e6427b7a51e385046a73`). In Milliken, the duplicate `FiniteColourRamseySpace.lean` is deleted and `RamseySpace.FiniteColouring` imported instead. Before merging any downstream PR, verify that repository's full CI; do not infer consumer success from core success.

## Explicit nonclaims

This audit does **not** establish a new formalization of every concrete Ramsey space in the book. The core library formalizes the central *abstract* theorems and a concrete classical Ellentuck example. Its generic finite-colour theorem has no independent power to prove tree-specific A.4: those obligations belong in the downstream library. A successful Lean CI checks the elaborated theorem types and their kernel dependencies; manuscript correspondence is separately audited as above.

## Wiki publication evidence

The Wiki was initialized and the source pages were successfully pushed by
[Publish Ramsey-space wiki run 38626621204](https://github.com/janhubicka/lean-ramsey-space-todorcevic/actions/runs/38626621204)
on 14 October 2026. The actual separate Wiki commit is `7e5bc43` on the
Wiki's `master` branch. See the [live researcher wiki](https://github.com/janhubicka/lean-ramsey-space-todorcevic/wiki).
