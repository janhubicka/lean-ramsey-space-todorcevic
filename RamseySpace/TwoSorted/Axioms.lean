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
 

namespace AbstractRamseySystem

variable {P : System.{uR, vR, uS, vS}}

/-- Todorčević's printed A.6, represented without choosing a global depth
function.  Nonemptiness of `[a,Y]` implies a unique finite depth, which is
returned together with the homogeneous reduction. -/
theorem pigeonhole_published (R : AbstractRamseySystem P)
    {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point)
    (hne : (P.objectNeighborhood a Y).Nonempty)
    (O : Set (P.Obj.Approx (n + 1))) :
    ∃ d, R.fin.HasDepth a Y d ∧
      ∃ X, X ∈ P.levelNeighborhood d Y ∧
        (P.oneStepObjectApproximations a X ⊆ O ∨
          Disjoint (P.oneStepObjectApproximations a X) O) := by
  rcases hne with ⟨A, hA⟩
  rcases R.fin.exists_hasDepth_of_mem_objectNeighborhood hA with
    ⟨d, hd⟩
  rcases R.pigeonhole a Y ⟨A, hA⟩ hd O with
    ⟨X, hXY, hhom⟩
  exact ⟨d, hd, X, hXY, hhom⟩

/-- Build the A.1--A.6 interface from the published Chapter 4 formulations.

Because this development represents `depth_Y(a)` by the proposition
`HasDepth a Y d` rather than by a partial integer-valued function, the A.6
argument returns the unique finite depth together with its witness. -/
def ofPublishedAxioms
    (fin : Finitization P)
    (amalgamation_nonempty :
      ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point) {d : ℕ},
        fin.HasDepth a Y d →
        ∀ ⦃X : P.Red.Point⦄, X ∈ P.levelNeighborhood d Y →
          (P.objectNeighborhood a X).Nonempty)
    (amalgamation_refine :
      ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point) {d : ℕ},
        fin.HasDepth a Y d →
        ∀ {X : P.Red.Point}, P.Red.le X Y →
          (P.objectNeighborhood a X).Nonempty →
          ∃ Y', Y' ∈ P.levelNeighborhood d Y ∧
            P.objectNeighborhood a Y' ⊆ P.objectNeighborhood a X)
    (pigeonhole :
      ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point),
        (P.objectNeighborhood a Y).Nonempty →
        ∀ O : Set (P.Obj.Approx (n + 1)),
          ∃ d, fin.HasDepth a Y d ∧
            ∃ X, X ∈ P.levelNeighborhood d Y ∧
              (P.oneStepObjectApproximations a X ⊆ O ∨
                Disjoint (P.oneStepObjectApproximations a X) O)) :
    AbstractRamseySystem P where
  fin := fin
  amalgamation_nonempty := amalgamation_nonempty
  amalgamation_refine := amalgamation_refine
  pigeonhole := by
    intro n a Y hne d hd O
    rcases pigeonhole a Y hne O with
      ⟨e, he, X, hXY, hhom⟩
    have hed : e = d := fin.hasDepth_unique he hd
    subst e
    exact ⟨X, hXY, hhom⟩

end AbstractRamseySystem

end TwoSorted
end RamseySpace
