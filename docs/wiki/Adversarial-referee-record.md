# Adversarial referee record — Ramsey-space research library

**Audit baseline:** `main` at `0515f911ad1cc2eb619ca4bc22f75f2e7c386944`. This report records three deliberately different adversarial attacks on the complete abstract proof and its exported API; they are not certificates from independently hired human mathematicians. For exact CI results and downstream builds, consult the [audit tracker](../audit-tracker-20261014.md).

## Referee A: theorem semantics and the printed axioms

**Attack:** pretend the Lean identifiers have misleading names, unfold every axiom and theorem proposition, and ask whether the book's hypotheses are neither lost nor silently strengthened. Test nonempty basic neighborhoods, finite-approximation indices, reduction-vs-object confusion and pathologies of finitization.

**A.1 / A.2:** A level-indexed `Approx n` represents a realized finite approximation. `approx_surjective` prevents adding arbitrary nonrealizable finite codes without proof; `separated` and `coherent` give the original initial approximation axioms. In Chapter 5, `Finitization` has finite lower cones, order recovery and prefix lifting. **Verdict: source-faithful typed representation.**

**Two-sorted Chapter 4 A.4:** An invalid “simplification” would reuse the stronger Chapter 5 `Finitization` record for the reduction sort, imposing reflexivity, transitivity and an additional finite-prefix condition. Those properties are *not* printed in Chapter 4 A.4. The current `ReductionFinitization` requires only finite reduction lower cones and recovery of the infinite reduction relation; mixed transitivity and lifting remain in the cross finitization. **Verdict: keep weaker record; regression-test precise constructor.**

**Chapter 5 A.3(2):** The book assumes `A≤B` with `[a,A]` nonempty. An old convenience constructor instead assumed `A∈[a,B]`, a stronger and misleading special case. The preferred `ofPublishedAxioms` takes the full hypothesis, while `amalgamation_refine_onBasicMember` is a derived special-case lemma. The internal A.3(2) drops the output nonemptiness, which A.3(1) proves. **Verdict: retire obsolete aliases, preserve published constructor and explicit recovery lemma.**

**Empty-set trap:** A pigeonhole or homogeneity conclusion is vacuous when its basic neighborhood is empty. The published interfaces use `HasDepth` together with A.3(1) to ensure the required genuine nonempty neighborhood, and the Chapter 4 A.6 wrapper starts with `[a,Y] ≠ ∅`. A “shorter” structure that omits the nonemptiness axiom is **not an acceptable simplification**.

**Closedness trap:** The final Chapter 5 theorem must use closedness in the *discrete product* `AR^ℕ`, not an arbitrary unrelated topological-space instance. `IsTychonoffClosed` and `isTychonoffClosed_iff_isClosedApproximationImage` establish the finite-prefix equivalence. Published Ramsey means homogeneous refinement `B∈[a,A]`, not just a depth-layer witness. The theorem `isTopologicalRamseySpace_iff_textbook` explicitly mediates this distinction. **Verdict: preserve published theorem interfaces.**

**Source scope:** `abstractRamsey_full` includes closure under Souslin's operation in addition to Baire/Ramsey and meagre/null equivalences. `abstractEllentuck_textbook` is Chapter 5's full Baire/meagre topological conclusion, not only open colouring. Classical Ellentuck verifies one concrete example; many other applications from the book are *not* formalized.

## Referee B: kernel trust, proof dependencies and circularity

**Attack:** trace the exact transitive proof graph, challenge use of fusion before A.4, audit acceptance/rejection combinatorics, and insist on kernel axiom reports for the *strongest* theorem endpoints.

**Fusion dependency:** `Finitization.fusionComplete_of_isMetricallyClosed` needs finitization A.2 and closedness only. This is available while proving A.4 for a new concrete space and does not create an A.4 proof loop. The two-sorted analogue uses the weaker `ReductionFinitization`. **Verdict: retain this clean separation.**

**Forcing and rejection:** `Forcing` defines acceptance, rejection and decision. `Decision` handles finite approximations at protected depths and fuses a global decider; `Reject` uses one-step pigeonhole; `EndExtension` fuses persistent rejection along longer initial segments. Finite depth layers are essential to the simultaneous decision argument; the nonemptiness assumptions are essential when carrying rejection through refinements. These modules are mathematical proof content, not compatibility clutter.

**Independent proof check:** `AbstractEllentuck.lean` uses one-sorted forcing and topology bridges. `TwoSorted.AbstractEllentuckViaRamsey` specializes the separately proved Chapter 4 theorem via `Diagonal`; its source explicitly states that it does not invoke the first theorem. Keep both as independent regression paths. **Verdict: duplicate-looking *proof routes* are intentional.**

**Souslin boundary:** The Chapter 4 proof adds relative Baire/nowhere-meagre statements, diagonal decisions, an envelope and residual argument before the final Souslin closure. An audit checking only `TwoSorted.abstractRamsey` would overlook this part. **Repair:** print axioms for `TwoSorted.CombinatorialForcing.isRamsey_souslin`, `TwoSorted.abstractRamsey_souslin`, and `TwoSorted.abstractRamsey_full`.

**Trust gate:** Lean CI builds all source files, rejects admitted proofs, and parses `#print axioms` outputs on important endpoints with an explicit allowlist `propext`, `Classical.choice`, `Quot.sound`. This checks theorem integrity, not the mathematical interpretation of its statement; Referee A is the separate semantic audit. **Do not mark any modified revision kernel-tested until its GitHub Actions job succeeds.**

## Referee C: minimality, public API and downstream users

**Attack:** compare the one-sorted and two-sorted modules, identify declarations whose assumptions are independent of either consumer, remove misnamed compatibility wrappers, and ensure a change can be used by a new mathematician without importing hundreds of unrelated theorem files.

**Generic finite-colour lemmas:** `RamseySpace.finiteBaireColouring`, `RamseySpace.finiteApproximationColouring` and `ApproximationSystem.isOpen_approxColourFibre` were housed in `lean-milliken`. Their statements and proofs are independent of strong trees. **Repair:** move them to `RamseySpace.FiniteColouring`; Milliken imports the abstract module and retains only the tree-specific corollary.

**Compatibility names:** `amalgamation_refine_standard` was simply an alias of the surviving `amalgamation_refine_onBasicMember`. `ofStandardAxioms` served a stronger special-case constructor and encouraged conflation with the printed A.3(2). **Repair:** remove both, update `Standard.lean`, and teach clients the source-faithful constructor. A real application with basic-member-only hypotheses can prove the full constructor statement from a witness and `ofPublishedAxioms`; it need not expose a permanent confusing synonym.

**Umbrella import:** `RamseySpace.lean` previously imported almost every internal module explicitly, including imports supplied transitively by the main endpoints. **Repair:** import the main mathematical endpoints, diagonal bridge, classical example, closure API, and generic finite colours only. Internal imports remain available for proof developments that need them.

**Not redundant:** the two-sorted forcing proof cannot be deleted merely because one-sorted Abstract Ellentuck exists; it proves a genuinely different system and stronger Souslin conclusions. Similarly the classical example cannot be deleted without losing the principal end-to-end test of A.3 and A.4.

**Documentation and adoption:** A new researcher should find the exact theorem types, proof differences and auxiliary lemmas in this wiki, with a source-controlled audit trail and pinned CI checks. The three existing integrations at audit time are `lean-milliken`, `lean-successors` and `lean-dualtree`. Their CI builds are regression examples, not reasons to retain misleading aliases forever.

## Verified integration and genuine remaining limitations

- The extracted generic finite-colouring module and removal of obsolete aliases passed the core [Lean kernel audit](https://github.com/janhubicka/lean-ramsey-space-todorcevic/actions/runs/38636833578) and all **three** downstream integrations: [Milliken](https://github.com/janhubicka/lean-milliken/actions/runs/38636961931), [successors](https://github.com/janhubicka/lean-successors/actions/runs/38636888684), and [dualtree](https://github.com/janhubicka/lean-dualtree/actions/runs/38636910049). The independent successor V10 audit [also passed](https://github.com/janhubicka/lean-successors/actions/runs/38636888582).
- The separately compiled and published [GitHub Wiki](https://github.com/janhubicka/lean-ramsey-space-todorcevic/wiki) is live; the most recent successful [sync](https://github.com/janhubicka/lean-ramsey-space-todorcevic/actions/runs/38636833552) includes the shared-fusion discussion.
- This is **not** a claim that every concrete application in the book has been formalized. In particular, a *non-diagonal* concrete A.1–A.6 instance would be a valuable next independent application test. The classical Ellentuck example and the diagonal Chapter 4 specialization already compile.

The latest evidence, PRs, and regression gates are tracked in [audit tracker](../audit-tracker-20261014.md).
