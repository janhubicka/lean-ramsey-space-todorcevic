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
- `RamseySpace.abstractEllentuck`
- `RamseySpace.TwoSorted.abstractEllentuck_via_abstractRamsey`
- `RamseySpace.Examples.Ellentuck.classicalEllentuck`

## Reference

Stevo Todorčević, *Introduction to Ramsey Spaces*, Annals of Mathematics
Studies 174, Princeton University Press, 2010.  The two-sorted abstract Ramsey
theory is developed in Chapter 4 and the topological / Ellentuck theory in
Chapter 5.
