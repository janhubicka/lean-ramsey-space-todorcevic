import RamseySpace.TopologyBridge
import RamseySpace.Closed
import RamseySpace.Standard

/-!
# Topological Ramsey-space conclusions

Shared statement layer for the Abstract Ellentuck theorem.  Keeping these
definitions separate lets both the direct proof and the derivation from the
two-sorted Abstract Ramsey Theorem target exactly the same proposition.
-/

namespace RamseySpace

universe u v

/-- Depth-form internal version of the two conclusions of a topological
Ramsey space.  This is equivalent, using A.3, to Todorčević's literal
basic-neighborhood definition below. -/
def IsTopologicalRamseySpace
    {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S) : Prop :=
  (∀ target : Set S.Point,
      @BaireMeasurableSet S.Point S.ellentuckTopology target →
        IsRamsey R target) ∧
    (∀ target : Set S.Point,
      @_root_.IsMeagre S.Point S.ellentuckTopology target →
        IsRamseyNull R target)

/-- Literal Chapter 5 definition of a topological Ramsey space: property-of-Baire
sets are Ramsey and meagre sets are Ramsey null, with Ramsey/Ramsey-null
defined by refinements `B ∈ [a,A]`. -/
def IsTopologicalRamseySpaceOnBasicNeighborhoods
    {S : ApproximationSystem.{u, v}} : Prop :=
  (∀ target : Set S.Point,
      @BaireMeasurableSet S.Point S.ellentuckTopology target →
        IsRamseyOnBasicNeighborhoods target) ∧
    (∀ target : Set S.Point,
      @_root_.IsMeagre S.Point S.ellentuckTopology target →
        IsRamseyNullOnBasicNeighborhoods target)


/-- Short source-facing name for the literal Chapter 5 conclusion. -/
abbrev IsTopologicalRamseySpaceTextbook
    {S : ApproximationSystem.{u, v}} : Prop :=
  IsTopologicalRamseySpaceOnBasicNeighborhoods (S := S)

/-- The depth-form implementation and Todorčević's literal
basic-neighborhood formulation are equivalent under A.1--A.4. -/
theorem isTopologicalRamseySpace_iff_textbook
    {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S) :
    IsTopologicalRamseySpace R ↔
      IsTopologicalRamseySpaceTextbook (S := S) := by
  constructor
  · rintro ⟨hBaire, hMeagre⟩
    constructor
    · intro target hB
      exact (isRamsey_iff_onBasicNeighborhoods R target).1
        (hBaire target hB)
    · intro target hM
      exact (isRamseyNull_iff_onBasicNeighborhoods R target).1
        (hMeagre target hM)
  · rintro ⟨hBaire, hMeagre⟩
    constructor
    · intro target hB
      exact (isRamsey_iff_onBasicNeighborhoods R target).2
        (hBaire target hB)
    · intro target hM
      exact (isRamseyNull_iff_onBasicNeighborhoods R target).2
        (hMeagre target hM)

end RamseySpace
