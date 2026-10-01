import RamseySpace.Finitization

/-!
# Todorčević's abstract Ramsey-space axioms

A.1 is carried by ApproximationSystem, A.2 by Finitization, and this file
adds the amalgamation and pigeonhole axioms A.3 and A.4.
-/

namespace RamseySpace

universe u v

/-- A.1--A.4, before adding the topological closedness hypothesis used by the
Abstract Ellentuck Theorem. -/
structure AbstractRamseySpace (S : ApproximationSystem.{u, v}) where
  fin : Finitization S
  amalgamation_nonempty :
    ∀ {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ},
      fin.HasDepth a B d →
      ∀ ⦃A : S.Point⦄, A ∈ S.levelNeighborhood d B →
        (S.neighborhood a A).Nonempty
  amalgamation_refine :
    ∀ {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ},
      fin.HasDepth a B d →
      ∀ {A : S.Point}, S.le A B →
        (S.neighborhood a A).Nonempty →
        ∃ A', A' ∈ S.levelNeighborhood d B ∧
          S.neighborhood a A' ⊆ S.neighborhood a A
  pigeonhole :
    ∀ {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ},
      fin.HasDepth a B d →
      ∀ O : Set (S.Approx (n + 1)),
        ∃ A, A ∈ S.levelNeighborhood d B ∧
          (S.oneStepApproximations a A ⊆ O ∨
            Disjoint (S.oneStepApproximations a A) O)

end RamseySpace
