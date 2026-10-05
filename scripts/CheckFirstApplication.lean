import RamseySpace.AbstractEllentuck

/-!
Regression tests motivated by the fat-tree application.

The fusion construction must be usable before A.3 or A.4 is available.
The topological conclusions must concern the literal Ellentuck topology and
Mathlib's Baire/meagre predicates, not an assumed combinatorial substitute.
The CI runner also checks the transitive axioms printed below.
-/

namespace RamseySpace.FirstApplicationAudit

universe u v

/-- No `AbstractRamseySpace` argument or typeclass is available here. -/
theorem fusion_before_pigeonhole
    {S : ApproximationSystem.{u, v}} (F : Finitization S)
    (hclosed : S.IsMetricallyClosed) : FusionComplete S :=
  F.fusionComplete_of_isMetricallyClosed hclosed

/-- The source-facing endpoint retains the actual basic-neighbourhood notion. -/
example {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed) :
    IsTopologicalRamseySpaceOnBasicNeighborhoods (S := S) :=
  abstractEllentuck_onBasicNeighborhoods R hclosed

/-- The topology is pinned explicitly, independently of ambient instances. -/
example {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed) (X : Set S.Point)
    (hX : @BaireMeasurableSet S.Point S.ellentuckTopology X) :
    IsRamsey R X :=
  abstractEllentuck_baire R hclosed hX

example {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed) (X : Set S.Point)
    (hX : @IsMeagre S.Point S.ellentuckTopology X) :
    IsRamseyNull R X :=
  abstractEllentuck_meagre R hclosed hX

end RamseySpace.FirstApplicationAudit

#print axioms RamseySpace.FirstApplicationAudit.fusion_before_pigeonhole
#print axioms RamseySpace.abstractEllentuck
#print axioms RamseySpace.abstractEllentuck_baire
#print axioms RamseySpace.abstractEllentuck_meagre
#print axioms RamseySpace.abstractEllentuck_onBasicNeighborhoods
