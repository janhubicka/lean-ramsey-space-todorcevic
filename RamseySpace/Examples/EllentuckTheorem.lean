import RamseySpace.Examples.EllentuckClosed
import RamseySpace.AbstractEllentuck

/-!
# The classical Ellentuck theorem

The abstract theorem specializes to the ordinary Ellentuck space of infinite
subsets of ℕ (represented by their increasing enumerations).
-/

namespace RamseySpace
namespace Examples
namespace Ellentuck

/-- The classical Ellentuck space is a topological Ramsey space. -/
theorem classicalEllentuck :
    IsTopologicalRamseySpaceOnBasicNeighborhoods (S := S) :=
  abstractEllentuck_onBasicNeighborhoods ramseySpace isMetricallyClosed

/-- Baire-measurable sets in the classical Ellentuck topology are Ramsey,
in the literal basic-neighborhood formulation. -/
theorem classicalEllentuck_baire
    {target : Set S.Point}
    (hB : @BaireMeasurableSet S.Point S.ellentuckTopology target) :
    IsRamseyOnBasicNeighborhoods target :=
  classicalEllentuck.1 target hB

/-- Meagre sets in the classical Ellentuck topology are Ramsey null,
in the literal basic-neighborhood formulation. -/
theorem classicalEllentuck_meagre
    {target : Set S.Point}
    (hM : @IsMeagre S.Point S.ellentuckTopology target) :
    IsRamseyNullOnBasicNeighborhoods target :=
  classicalEllentuck.2 target hM

end Ellentuck
end Examples
end RamseySpace
