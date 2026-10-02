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

/-- The two defining conclusions of a topological Ramsey space for the
Ellentuck topology. -/
def IsTopologicalRamseySpace
    {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S) : Prop :=
  (∀ target : Set S.Point,
      @BaireMeasurableSet S.Point S.ellentuckTopology target →
        IsRamsey R target) ∧
    (∀ target : Set S.Point,
      @_root_.IsMeagre S.Point S.ellentuckTopology target →
        IsRamseyNull R target)

/-- Literal textbook conclusion using refinements B ∈ [a,A] in the definitions
of Ramsey and Ramsey null. -/
def IsTopologicalRamseySpaceOnBasicNeighborhoods
    {S : ApproximationSystem.{u, v}} : Prop :=
  (∀ target : Set S.Point,
      @BaireMeasurableSet S.Point S.ellentuckTopology target →
        IsRamseyOnBasicNeighborhoods target) ∧
    (∀ target : Set S.Point,
      @_root_.IsMeagre S.Point S.ellentuckTopology target →
        IsRamseyNullOnBasicNeighborhoods target)

end RamseySpace
