import RamseySpace.TopologicalRamsey

/-!
# The Abstract Ellentuck Theorem

A closed approximation space satisfying Todorčević's axioms A.1--A.4 is a
topological Ramsey space. The forcing proof uses only fusion completeness;
closedness is one way of obtaining that property from A.2.
-/

namespace RamseySpace

universe u v

/-- The fusion form of the Abstract Ellentuck Theorem. -/
theorem abstractEllentuck_of_fusionComplete
    {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S)
    (C : FusionComplete S) :
    IsTopologicalRamseySpace R := by
  constructor
  · intro target hB
    exact isRamsey_of_baireMeasurableSet_ellentuck R C hB
  · intro target hM
    exact isRamseyNull_of_isMeagre_ellentuck R C hM

/-- Todorčević's Abstract Ellentuck Theorem. -/
theorem abstractEllentuck
    {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed) :
    IsTopologicalRamseySpace R :=
  abstractEllentuck_of_fusionComplete R
    (R.fin.fusionComplete_of_isMetricallyClosed hclosed)

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

/-- Source-facing fusion form, with refinements in the original nonempty
basic neighbourhood and with the original finite approximation unchanged. -/
theorem abstractEllentuck_of_fusionComplete_onBasicNeighborhoods
    {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S)
    (C : FusionComplete S) :
    IsTopologicalRamseySpaceOnBasicNeighborhoods (S := S) := by
  constructor
  · intro target hB
    exact (isRamsey_iff_onBasicNeighborhoods R target).1
      ((abstractEllentuck_of_fusionComplete R C).1 target hB)
  · intro target hM
    exact (isRamseyNull_iff_onBasicNeighborhoods R target).1
      ((abstractEllentuck_of_fusionComplete R C).2 target hM)

/-- Source-facing form of Todorčević's Abstract Ellentuck Theorem. -/
theorem abstractEllentuck_onBasicNeighborhoods
    {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed) :
    IsTopologicalRamseySpaceOnBasicNeighborhoods (S := S) :=
  abstractEllentuck_of_fusionComplete_onBasicNeighborhoods R
    (R.fin.fusionComplete_of_isMetricallyClosed hclosed)

end RamseySpace
