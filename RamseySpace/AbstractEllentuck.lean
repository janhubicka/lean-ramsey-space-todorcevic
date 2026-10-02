import RamseySpace.TopologicalRamsey

/-!
# The Abstract Ellentuck Theorem

A closed approximation space satisfying Todorčević's axioms A.1--A.4 is a
topological Ramsey space.
-/

namespace RamseySpace

universe u v

/-- Todorčević's Abstract Ellentuck Theorem. -/
theorem abstractEllentuck
    {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed) :
    IsTopologicalRamseySpace R := by
  let C : FusionComplete S :=
    fusionComplete_of_isMetricallyClosed R hclosed
  constructor
  · intro target hB
    exact isRamsey_of_baireMeasurableSet_ellentuck R C hB
  · intro target hM
    exact isRamseyNull_of_isMeagre_ellentuck R C hM

theorem abstractEllentuck_baire
    {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed)
    {target : Set S.Point}
    (hB : @BaireMeasurableSet S.Point S.ellentuckTopology target) :
    IsRamsey R target :=
  (abstractEllentuck R hclosed).1 target hB

theorem abstractEllentuck_meagre
    {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed)
    {target : Set S.Point}
    (hM : @IsMeagre S.Point S.ellentuckTopology target) :
    IsRamseyNull R target :=
  (abstractEllentuck R hclosed).2 target hM

/-- Source-facing form of Todorčević's Abstract Ellentuck Theorem. -/
theorem abstractEllentuck_onBasicNeighborhoods
    {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed) :
    IsTopologicalRamseySpaceOnBasicNeighborhoods (S := S) := by
  constructor
  · intro target hB
    exact (isRamsey_iff_onBasicNeighborhoods R target).1
      (abstractEllentuck_baire R hclosed hB)
  · intro target hM
    exact (isRamseyNull_iff_onBasicNeighborhoods R target).1
      (abstractEllentuck_meagre R hclosed hM)

end RamseySpace
