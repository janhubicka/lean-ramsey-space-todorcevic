import RamseySpace.TwoSorted.Axioms
import RamseySpace.Closed

/-!
# Closedness and fusion for the reduction sort

Only the reduction sort `S` is required to be metrically closed in
Todorčević's Abstract Ramsey Theorem.
-/

namespace RamseySpace
namespace TwoSorted

universe uR vR uS vS

variable {P : System.{uR, vR, uS, vS}}

/-- The Chapter 4 reduction-side order-recovery axiom is sufficient
for fusion.  The proof is shared with the one-sorted development; no
extra quasi-order structure on `≤fin` is required. -/
theorem fusionComplete_of_isMetricallyClosed
    (R : AbstractRamseySystem P)
    (hclosed : P.Red.IsMetricallyClosed) :
    RamseySpace.FusionComplete P.Red :=
  RamseySpace.fusionComplete_of_closed_of_realizesOrder
    R.fin.redFin.leFin R.fin.redFin.realizesOrder hclosed

end TwoSorted
end RamseySpace
