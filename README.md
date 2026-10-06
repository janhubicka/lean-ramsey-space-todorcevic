# lean-ramsey-space-todorcevic

Lean 4 formalization of the two main abstract Ramsey-space theorems from
Todorčević's *Introduction to Ramsey Spaces*:

- the **Abstract Ramsey Theorem** for two-sorted systems
  `(R, S, ≤, ≤⁰, r, s)` satisfying A.1--A.6;
- the **Abstract Ellentuck Theorem** for a closed one-sorted
  approximation space satisfying A.1--A.4, with closedness stated in the
  book's Tychonoff-product form.

The repository also proves in Lean that the Abstract Ellentuck theorem is the
diagonal specialization of the Abstract Ramsey theorem, and independently
validates the framework on the classical Ellentuck space `[ℕ]^ω`.

The general development is application-independent. Projects such as
`lean-successors` can depend on this repository and only need to verify the
appropriate abstract axioms for their concrete Ramsey spaces.

## Main theorem entry points

- `RamseySpace.TwoSorted.abstractRamsey`
- `RamseySpace.TwoSorted.abstractRamsey_iff`
- `RamseySpace.abstractEllentuck_textbook` — literal Theorem 5.4 statement
- `RamseySpace.abstractEllentuck` — equivalent depth-form implementation
- `RamseySpace.TwoSorted.abstractEllentuck_textbook_via_abstractRamsey`
- `RamseySpace.TwoSorted.abstractEllentuck_via_abstractRamsey`
- `RamseySpace.Examples.Ellentuck.classicalEllentuck`


## Published Chapter 5 interface

The source-facing one-sorted API follows Chapter 5 of Todorčević literally:

- A.1 is represented by `ApproximationSystem`; levels of finite
  approximations are indexed in the type, so the "equal approximations have
  equal length" part of A.1(3) is enforced by typing.
- A.2 is `Finitization`.
- A.3(1) and A.4 are stored directly.  The internal A.3(2) field omits only
  the redundant printed conclusion `[a,A'] ≠ ∅`; A.3(1) derives it.
  `amalgamation_refine_published` restores the exact printed statement.
- `AbstractRamseySpace.ofPublishedAxioms` is the literal constructor.
  The older `ofStandardAxioms` is retained for compatibility; it accepts a
  convenient basic-member special case of A.3(2), not the printed Chapter 5
  formulation.
- `abstractEllentuck_textbook` states Theorem 5.4 using the book's
  literal closedness hypothesis: the approximation-code image is closed in
  the Tychonoff product of discrete approximation levels, together with the
  book's basic-neighborhood definitions of Ramsey and Ramsey null.
  `isTychonoffClosed_iff_isClosedApproximationImage` proves this equivalent
  to the finite-prefix criterion used internally by fusion. The older
  `abstractEllentuck` endpoint keeps that implementation-friendly form.

See `docs/published-ellentuck-audit.md` for the line-by-line Chapter 5 audit.
The corresponding Chapter 4 audit is
`docs/published-abstract-ramsey-audit.md`; in particular, the two-sorted
finitization interface assumes exactly the published A.4 clauses.

## Reference

Stevo Todorčević, *Introduction to Ramsey Spaces*, Annals of Mathematics
Studies 174, Princeton University Press, 2010.  The two-sorted abstract Ramsey
theory is developed in Chapter 4 and the topological / Ellentuck theory in
Chapter 5.
