import RamseySpace.TopologicalRamsey

/-!
# The Abstract Ellentuck Theorem

A closed approximation space satisfying Todorčević's axioms A.1--A.4 is a
topological Ramsey space.
-/

namespace RamseySpace

universe u v

/-- Depth-form implementation of Todorčević's Abstract Ellentuck Theorem.
The literal published statement is `abstractEllentuck_textbook` below. -/
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

/-- Todorčević, Theorem 5.4 (Abstract Ellentuck Theorem), in the
literal Chapter 5 formulation: if the approximation image is closed and
A.1--A.4 hold, every property-of-Baire set is Ramsey and every meagre set is
Ramsey null, where Ramsey and Ramsey null quantify over nonempty basic
neighborhoods `[a,A]`. -/
theorem abstractEllentuck_textbook
    {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed) :
    IsTopologicalRamseySpaceTextbook (S := S) :=
  (isTopologicalRamseySpace_iff_textbook R).1
    (abstractEllentuck R hclosed)

/-- Compatibility name for the literal basic-neighborhood formulation. -/
theorem abstractEllentuck_onBasicNeighborhoods
    {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed) :
    IsTopologicalRamseySpaceOnBasicNeighborhoods (S := S) :=
  abstractEllentuck_textbook R hclosed

end RamseySpace
