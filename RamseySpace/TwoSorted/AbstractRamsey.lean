import RamseySpace.TwoSorted.SouslinClosure

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


/-- Countable-union closure of S-Ramsey sets, with metric closedness supplying
the fusion-completeness hypothesis. -/
theorem abstractRamsey_iUnion
    (R : AbstractRamseySystem P)
    (hclosed : P.Red.IsMetricallyClosed)
    (targets : ℕ → Set P.Obj.Point)
    (hRamsey : ∀ i, IsRamsey R (targets i)) :
    IsRamsey R (⋃ i, targets i) := by
  let C : RamseySpace.FusionComplete P.Red :=
    fusionComplete_of_isMetricallyClosed R hclosed
  exact CombinatorialForcing.isRamsey_iUnion R C targets hRamsey

/-- Countable-union closure of the S-Ramsey-null ideal. -/
theorem abstractRamseyNull_iUnion
    (R : AbstractRamseySystem P)
    (hclosed : P.Red.IsMetricallyClosed)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNull R (targets i)) :
    IsRamseyNull R (⋃ i, targets i) := by
  let C : RamseySpace.FusionComplete P.Red :=
    fusionComplete_of_isMetricallyClosed R hclosed
  exact CombinatorialForcing.isRamseyNull_iUnion R C targets hNull

/-- Souslin closure of the S-Ramsey field.  This is the conclusion of the
full Abstract Ramsey Theorem beyond the Baire/Ramsey equivalence packaged by
\`abstractRamsey\` and \`abstractRamsey_iff\`. -/
theorem abstractRamsey_souslin
    (R : AbstractRamseySystem P)
    (hclosed : P.Red.IsMetricallyClosed)
    (A : RamseySpace.Souslin.Scheme P.Obj.Point)
    (hA : ∀ s, IsRamsey R (A s)) :
    IsRamsey R (RamseySpace.Souslin.operation A) := by
  let C : RamseySpace.FusionComplete P.Red :=
    fusionComplete_of_isMetricallyClosed R hclosed
  exact CombinatorialForcing.isRamsey_souslin R C A hA

/-- Source-facing package of the full formalized Abstract Ramsey Theorem:
Baire = Ramsey, meagre = Ramsey-null, countable closure, and Souslin closure. -/
structure AbstractRamseyConclusion
    (R : AbstractRamseySystem P) : Prop where
  baire_iff_ramsey :
    ∀ target : Set P.Obj.Point,
      IsBaire target ↔ IsRamsey R target
  meagre_iff_null :
    ∀ target : Set P.Obj.Point,
      IsMeagre target ↔ IsRamseyNull R target
  ramsey_iUnion :
    ∀ (targets : ℕ → Set P.Obj.Point),
      (∀ i, IsRamsey R (targets i)) →
        IsRamsey R (⋃ i, targets i)
  null_iUnion :
    ∀ (targets : ℕ → Set P.Obj.Point),
      (∀ i, IsRamseyNull R (targets i)) →
        IsRamseyNull R (⋃ i, targets i)
  souslin :
    ∀ (A : RamseySpace.Souslin.Scheme P.Obj.Point),
      (∀ s, IsRamsey R (A s)) →
        IsRamsey R (RamseySpace.Souslin.operation A)

/-- Full packaged Abstract Ramsey Theorem. -/
theorem abstractRamsey_full
    (R : AbstractRamseySystem P)
    (hclosed : P.Red.IsMetricallyClosed) :
    AbstractRamseyConclusion R := by
  refine {
    baire_iff_ramsey := ?_
    meagre_iff_null := ?_
    ramsey_iUnion := ?_
    null_iUnion := ?_
    souslin := ?_
  }
  · exact (abstractRamsey_iff R hclosed).1
  · exact (abstractRamsey_iff R hclosed).2
  · intro targets hRamsey
    exact abstractRamsey_iUnion R hclosed targets hRamsey
  · intro targets hNull
    exact abstractRamseyNull_iUnion R hclosed targets hNull
  · intro A hA
    exact abstractRamsey_souslin R hclosed A hA

end TwoSorted
end RamseySpace
