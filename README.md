# lean-ramsey-space-todorcevic

Lean 4 formalization of the two main abstract Ramsey-space theorems from
Todorčević's *Introduction to Ramsey Spaces*:

- the **Abstract Ramsey Theorem** for two-sorted systems
  `(R, S, ≤, ≤⁰, r, s)` satisfying A.1--A.6;
- the **Abstract Ellentuck Theorem** for a metrically closed one-sorted
  approximation space satisfying A.1--A.4.

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
- A.3(1), the published A.3(2) with hypotheses `A ≤ B` and
  `[a,A] ≠ ∅`, and A.4 are the fields of `AbstractRamseySpace`.
- `AbstractRamseySpace.ofPublishedAxioms` is the literal constructor.
  The older `ofStandardAxioms` is retained for compatibility; it accepts a
  convenient basic-member special case of A.3(2), not the printed Chapter 5
  formulation.
- `abstractEllentuck_textbook` states Theorem 5.4 using the book's
  basic-neighborhood definitions of Ramsey and Ramsey null. The older
  `abstractEllentuck` endpoint uses an equivalent depth-based formulation
  convenient for the forcing proof.

See `docs/published-ellentuck-audit.md` for the line-by-line source audit.

## Reference

Stevo Todorčević, *Introduction to Ramsey Spaces*, Annals of Mathematics
Studies 174, Princeton University Press, 2010.  The two-sorted abstract Ramsey
theory is developed in Chapter 4 and the topological / Ellentuck theory in
Chapter 5.
