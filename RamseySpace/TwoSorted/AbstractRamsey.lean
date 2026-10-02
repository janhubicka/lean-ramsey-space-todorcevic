import RamseySpace.TwoSorted.Baire

/-!
# Todorčević's Abstract Ramsey Theorem

This is the two-sorted theorem for
`(R,S,≤,≤⁰,r,s)` satisfying A.1--A.6 with the reduction sort S closed.
-/

namespace RamseySpace
namespace TwoSorted

universe uR vR uS vS

variable {P : System.{uR, vR, uS, vS}}

/-- Abstract Ramsey Theorem: a closed A.1--A.6 system is a Ramsey space. -/
theorem abstractRamsey
    (R : AbstractRamseySystem P)
    (hclosed : P.Red.IsMetricallyClosed) :
    IsRamseySpace R := by
  let C : RamseySpace.FusionComplete P.Red :=
    fusionComplete_of_isMetricallyClosed R hclosed
  constructor
  · intro target hB
    exact hB.isRamsey R C
  · intro target hM
    exact hM.isRamseyNull R C

/-- Strong form: S-Baire iff S-Ramsey and S-meagre iff S-Ramsey-null. -/
theorem abstractRamsey_iff
    (R : AbstractRamseySystem P)
    (hclosed : P.Red.IsMetricallyClosed) :
    (∀ target : Set P.Obj.Point,
      IsBaire target ↔ IsRamsey R target) ∧
    (∀ target : Set P.Obj.Point,
      IsMeagre target ↔ IsRamseyNull R target) := by
  let C : RamseySpace.FusionComplete P.Red :=
    fusionComplete_of_isMetricallyClosed R hclosed
  exact
    ⟨fun target => isBaire_iff_isRamsey R C target,
     fun target => isMeagre_iff_isRamseyNull R C target⟩

end TwoSorted
end RamseySpace
