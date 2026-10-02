import RamseySpace.TwoSorted.Finitization

/-!
# A.5 and A.6 for the two-sorted Abstract Ramsey Theorem
-/

namespace RamseySpace
namespace TwoSorted

universe uR vR uS vS

/-- Todorčević A.1--A.6 for a two-sorted Ramsey system. -/
structure AbstractRamseySystem (P : System.{uR, vR, uS, vS}) where
  fin : Finitization P
  amalgamation_nonempty :
    ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point) {d : ℕ},
      fin.HasDepth a Y d →
      ∀ ⦃X : P.Red.Point⦄, X ∈ P.levelNeighborhood d Y →
        (P.objectNeighborhood a X).Nonempty
  amalgamation_refine :
    ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point) {d : ℕ},
      fin.HasDepth a Y d →
      ∀ {X : P.Red.Point}, P.Red.le X Y →
        (P.objectNeighborhood a X).Nonempty →
        ∃ Y', Y' ∈ P.levelNeighborhood d Y ∧
          P.objectNeighborhood a Y' ⊆ P.objectNeighborhood a X
  pigeonhole :
    ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point),
      (P.objectNeighborhood a Y).Nonempty →
      ∀ {d : ℕ}, fin.HasDepth a Y d →
      ∀ O : Set (P.Obj.Approx (n + 1)),
        ∃ X, X ∈ P.levelNeighborhood d Y ∧
          (P.oneStepObjectApproximations a X ⊆ O ∨
            Disjoint (P.oneStepObjectApproximations a X) O)

end TwoSorted
end RamseySpace
