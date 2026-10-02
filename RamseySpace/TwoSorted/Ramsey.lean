import RamseySpace.TwoSorted.Axioms

/-!
# S-Ramsey, S-Ramsey-null, S-Baire, and S-meagre sets
-/

namespace RamseySpace
namespace TwoSorted

universe uR vR uS vS

variable {P : System.{uR, vR, uS, vS}}

/-- S-Ramsey: every nonempty [a,Y] has a same-depth homogeneous reduction. -/
def IsRamsey (R : AbstractRamseySystem P) (target : Set P.Obj.Point) : Prop :=
  ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point) {d : ℕ},
    R.fin.HasDepth a Y d →
      ∃ X, X ∈ P.levelNeighborhood d Y ∧
        (P.objectNeighborhood a X ⊆ target ∨
          Disjoint (P.objectNeighborhood a X) target)

/-- S-Ramsey null. -/
def IsRamseyNull (R : AbstractRamseySystem P) (target : Set P.Obj.Point) : Prop :=
  ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point) {d : ℕ},
    R.fin.HasDepth a Y d →
      ∃ X, X ∈ P.levelNeighborhood d Y ∧
        Disjoint (P.objectNeighborhood a X) target

/-- S-Baire, in Todorčević's abstract (not topological) sense. -/
def IsBaire (target : Set P.Obj.Point) : Prop :=
  ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point),
    (P.objectNeighborhood a Y).Nonempty →
      ∃ (m : ℕ) (b : P.Obj.Approx m) (X : P.Red.Point),
        P.Obj.IsInitial a b ∧ P.Red.le X Y ∧
          (P.objectNeighborhood b X).Nonempty ∧
          (P.objectNeighborhood b X ⊆ target ∨
            Disjoint (P.objectNeighborhood b X) target)

/-- S-meagre in the abstract Ramsey-theorem sense. -/
def IsMeagre (target : Set P.Obj.Point) : Prop :=
  ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point),
    (P.objectNeighborhood a Y).Nonempty →
      ∃ (m : ℕ) (b : P.Obj.Approx m) (X : P.Red.Point),
        P.Obj.IsInitial a b ∧ P.Red.le X Y ∧
          (P.objectNeighborhood b X).Nonempty ∧
          Disjoint (P.objectNeighborhood b X) target

/-- The conclusion of the Abstract Ramsey Theorem. -/
def IsRamseySpace (R : AbstractRamseySystem P) : Prop :=
  (∀ target, IsBaire target → IsRamsey R target) ∧
    (∀ target, IsMeagre target → IsRamseyNull R target)

end TwoSorted
end RamseySpace
