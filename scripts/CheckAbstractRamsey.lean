import RamseySpace

/-!
Source-interface regression check for Todorčević's Chapter 4 A.4.
The constructor below assumes exactly the five printed finitization clauses;
in particular, no reflexivity, transitivity, or reduction-side prefix axiom
for `≤fin` is available.
-/

namespace RamseySpace.TwoSorted.PublishedAbstractRamseyAudit

universe uR vR uS vS

variable {P : System.{uR, vR, uS, vS}}

example
    (leFin : P.Red.FiniteApprox → P.Red.FiniteApprox → Prop)
    (lowerFinite : ∀ x, Set.Finite {y | leFin y x})
    (realizesOrder :
      ∀ X Y, P.Red.le X Y ↔
        ∀ n, ∃ m,
          leFin (P.Red.finiteApprox n X) (P.Red.finiteApprox m Y))
    (leFin0 : P.Obj.FiniteApprox → P.Red.FiniteApprox → Prop)
    (lowerFinite0 : ∀ x, Set.Finite {a | leFin0 a x})
    (realizesOrder0 :
      ∀ A Y, P.le0 A Y ↔
        ∀ n, ∃ m,
          leFin0 (P.Obj.finiteApprox n A) (P.Red.finiteApprox m Y))
    (trans0 :
      ∀ {a x y}, leFin0 a x → leFin x y → leFin0 a y)
    (prefix0 :
      ∀ {n m k : ℕ}
        {a : P.Obj.Approx n} {b : P.Obj.Approx m}
        {x : P.Red.Approx k},
        P.Obj.IsInitial a b →
        leFin0 ⟨m, b⟩ ⟨k, x⟩ →
        ∃ (j : ℕ) (y : P.Red.Approx j),
          P.Red.IsInitial y x ∧ leFin0 ⟨n, a⟩ ⟨j, y⟩) :
    Finitization P where
  redFin := {
    leFin := leFin
    lowerFinite := lowerFinite
    realizesOrder := realizesOrder
  }
  leFin0 := leFin0
  lowerFinite0 := lowerFinite0
  realizesOrder0 := realizesOrder0
  trans0 := trans0
  prefix0 := prefix0

end RamseySpace.TwoSorted.PublishedAbstractRamseyAudit


#print axioms RamseySpace.TwoSorted.AbstractRamseySystem.ofPublishedAxioms
#print axioms RamseySpace.TwoSorted.AbstractRamseySystem.pigeonhole_published
#print axioms RamseySpace.TwoSorted.fusionComplete_of_isMetricallyClosed
#print axioms RamseySpace.TwoSorted.CombinatorialForcing.exists_refinement_rejects_endExtensions
#print axioms RamseySpace.TwoSorted.IsBaire.isRamsey
#print axioms RamseySpace.TwoSorted.IsMeagre.isRamseyNull
#print axioms RamseySpace.TwoSorted.abstractRamsey
#print axioms RamseySpace.TwoSorted.abstractRamsey_iff
#print axioms RamseySpace.TwoSorted.abstractBaire_iff_isRamsey_via_abstractRamsey
#print axioms RamseySpace.TwoSorted.abstractEllentuck_via_abstractRamsey
