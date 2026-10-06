import RamseySpace.Examples.EllentuckPigeonhole

/-!
# The classical Ellentuck space as an abstract Ramsey space

This packages the previously verified A.1--A.4 proofs using the
literal published-axiom constructor.
-/

namespace RamseySpace
namespace Examples
namespace Ellentuck

/-- The classical Ellentuck space satisfies Todorčević's axioms A.1--A.4. -/
def ramseySpace : AbstractRamseySpace S :=
  AbstractRamseySpace.ofPublishedAxioms
    finitization
    amalgamation_nonempty
    amalgamation_refine
    pigeonhole

end Ellentuck
end Examples
end RamseySpace
