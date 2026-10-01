import RamseySpace.Finitization

/-!
# Todorčević's abstract Ramsey-space axioms

A.1 is carried by `ApproximationSystem`, A.2 by `Finitization`, and this file
adds the amalgamation and pigeonhole axioms A.3 and A.4.

The structure stores a slightly generalized form of A.3(2), because that is
the form consumed repeatedly by the forcing proof.  The constructor
`AbstractRamseySpace.ofStandardAxioms` takes the textbook A.3(2) verbatim
and derives the generalized field.  Conversely,
`AbstractRamseySpace.amalgamation_refine_standard` recovers the textbook
form from the structure.
-/

namespace RamseySpace

universe u v

/-- A.1--A.4, before adding the topological closedness hypothesis used by the
Abstract Ellentuck Theorem. -/
structure AbstractRamseySpace (S : ApproximationSystem.{u, v}) where
  fin : Finitization S
  amalgamation_nonempty :
    ∀ {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ},
      fin.HasDepth a B d →
      ∀ ⦃A : S.Point⦄, A ∈ S.levelNeighborhood d B →
        (S.neighborhood a A).Nonempty
  amalgamation_refine :
    ∀ {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ},
      fin.HasDepth a B d →
      ∀ {A : S.Point}, S.le A B →
        (S.neighborhood a A).Nonempty →
        ∃ A', A' ∈ S.levelNeighborhood d B ∧
          S.neighborhood a A' ⊆ S.neighborhood a A
  pigeonhole :
    ∀ {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ},
      fin.HasDepth a B d →
      ∀ O : Set (S.Approx (n + 1)),
        ∃ A, A ∈ S.levelNeighborhood d B ∧
          (S.oneStepApproximations a A ⊆ O ∨
            Disjoint (S.oneStepApproximations a A) O)

namespace AbstractRamseySpace

variable {S : ApproximationSystem.{u, v}}

/-- Textbook A.3(2): if `A ∈ [a,B]` and `d = depth_B(a)`, there is
`A' ∈ [d,B]` with `[a,A'] ⊆ [a,A]`.

The stored `amalgamation_refine` field is a convenient consequence where
`A ∈ [a,B]` is weakened to `A ≤ B` together with nonemptiness of `[a,A]`.
-/
theorem amalgamation_refine_standard (R : AbstractRamseySpace S)
    {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ}
    (hd : R.fin.HasDepth a B d) {A : S.Point}
    (hA : A ∈ S.neighborhood a B) :
    ∃ A', A' ∈ S.levelNeighborhood d B ∧
      S.neighborhood a A' ⊆ S.neighborhood a A := by
  have hne : (S.neighborhood a A).Nonempty :=
    ⟨A, S.le_refl A, hA.2⟩
  exact R.amalgamation_refine a B hd hA.1 hne

/-- Build the internal A.1--A.4 interface from the literal textbook
formulations of A.3(1), A.3(2), and A.4.

This is the preferred constructor for applications: proving these arguments
amounts exactly to checking Todorčević's axioms. -/
def ofStandardAxioms
    (fin : Finitization S)
    (amalgamation_nonempty :
      ∀ {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ},
        fin.HasDepth a B d →
        ∀ ⦃A : S.Point⦄, A ∈ S.levelNeighborhood d B →
          (S.neighborhood a A).Nonempty)
    (amalgamation_refine_standard :
      ∀ {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ},
        fin.HasDepth a B d →
        ∀ {A : S.Point}, A ∈ S.neighborhood a B →
          ∃ A', A' ∈ S.levelNeighborhood d B ∧
            S.neighborhood a A' ⊆ S.neighborhood a A)
    (pigeonhole :
      ∀ {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ},
        fin.HasDepth a B d →
        ∀ O : Set (S.Approx (n + 1)),
          ∃ A, A ∈ S.levelNeighborhood d B ∧
            (S.oneStepApproximations a A ⊆ O ∨
              Disjoint (S.oneStepApproximations a A) O)) :
    AbstractRamseySpace S where
  fin := fin
  amalgamation_nonempty := amalgamation_nonempty
  amalgamation_refine := by
    intro n a B d hd A hAB hne
    rcases hne with ⟨X, hXaA⟩
    have hXaB : X ∈ S.neighborhood a B :=
      S.neighborhood_mono hAB hXaA
    rcases amalgamation_refine_standard a B hd hXaB with
      ⟨A', hA'B, hsub⟩
    exact ⟨A', hA'B, hsub.trans (S.neighborhood_mono hXaA.1)⟩
  pigeonhole := pigeonhole

end AbstractRamseySpace

end RamseySpace
