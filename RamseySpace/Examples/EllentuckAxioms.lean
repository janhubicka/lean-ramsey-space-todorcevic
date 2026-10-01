import RamseySpace.Examples.EllentuckPigeonhole

/-!
# The classical Ellentuck space as an abstract Ramsey space

This packages the previously verified A.1--A.4 proofs using the
source-faithful constructor.
-/

namespace RamseySpace
namespace Examples
namespace Ellentuck

/-- The classical Ellentuck space satisfies Todorčević's axioms A.1--A.4. -/
def ramseySpace : AbstractRamseySpace S :=
  AbstractRamseySpace.ofStandardAxioms
    finitization
    amalgamation_nonempty
    amalgamation_refine_standard
    pigeonhole

end Ellentuck
end Examples
end RamseySpace
