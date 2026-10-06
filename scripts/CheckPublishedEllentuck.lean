import RamseySpace

/-!
Source-interface regression checks for Todorčević, Chapter 5, §5.1 and
Theorem 5.4.  These examples intentionally restate the published hypotheses
rather than using convenience wrappers.
-/

namespace RamseySpace.PublishedEllentuckAudit

universe u v

variable {S : ApproximationSystem.{u, v}}

/-- The preferred constructor accepts the published A.3(2) directly:
`A ≤ B` plus nonemptiness of `[a,A]`. -/
example
    (fin : Finitization S)
    (a31 :
      ∀ {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ},
        fin.HasDepth a B d →
        ∀ ⦃A : S.Point⦄, A ∈ S.levelNeighborhood d B →
          (S.neighborhood a A).Nonempty)
    (a32 :
      ∀ {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ},
        fin.HasDepth a B d →
        ∀ {A : S.Point}, S.le A B →
          (S.neighborhood a A).Nonempty →
          ∃ A', A' ∈ S.levelNeighborhood d B ∧
            (S.neighborhood a A').Nonempty ∧
            S.neighborhood a A' ⊆ S.neighborhood a A)
    (a4 :
      ∀ {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ},
        fin.HasDepth a B d →
        ∀ O : Set (S.Approx (n + 1)),
          ∃ A, A ∈ S.levelNeighborhood d B ∧
            (S.oneStepApproximations a A ⊆ O ∨
              Disjoint (S.oneStepApproximations a A) O)) :
    AbstractRamseySpace S :=
  AbstractRamseySpace.ofPublishedAxioms fin a31 a32 a4

/-- The source-facing A.3(2) has both the printed Chapter 5 hypotheses and
the printed nonemptiness conclusion. -/
example (R : AbstractRamseySpace S)
    {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ}
    (hd : R.fin.HasDepth a B d)
    {A : S.Point} (hAB : S.le A B)
    (hne : (S.neighborhood a A).Nonempty) :
    ∃ A', A' ∈ S.levelNeighborhood d B ∧
      (S.neighborhood a A').Nonempty ∧
      S.neighborhood a A' ⊆ S.neighborhood a A :=
  R.amalgamation_refine_published a B hd hAB hne

/-- The literal Theorem 5.4 endpoint uses the published basic-neighborhood
definitions of Ramsey and Ramsey null. -/
example (R : AbstractRamseySpace S)
    (hclosed : S.IsClosedApproximationImage) :
    IsTopologicalRamseySpaceTextbook (S := S) :=
  abstractEllentuck_textbook R hclosed

/-- The depth-form implementation is proved equivalent to the textbook
statement, so internal forcing lemmas do not change the public theorem. -/
example (R : AbstractRamseySpace S) :
    IsTopologicalRamseySpace R ↔
      IsTopologicalRamseySpaceTextbook (S := S) :=
  isTopologicalRamseySpace_iff_textbook R

/-- The independent diagonal derivation lands in the same source-facing
statement. -/
example (R : AbstractRamseySpace S)
    (hclosed : S.IsClosedApproximationImage) :
    IsTopologicalRamseySpaceTextbook (S := S) :=
  TwoSorted.abstractEllentuck_textbook_via_abstractRamsey R hclosed

end RamseySpace.PublishedEllentuckAudit

#print axioms RamseySpace.AbstractRamseySpace.amalgamation_refine_published
#print axioms RamseySpace.AbstractRamseySpace.ofPublishedAxioms
#print axioms RamseySpace.isTopologicalRamseySpace_iff_textbook
#print axioms RamseySpace.abstractEllentuck_textbook
#print axioms RamseySpace.TwoSorted.abstractEllentuck_textbook_via_abstractRamsey
#print axioms RamseySpace.Examples.Ellentuck.classicalEllentuck
