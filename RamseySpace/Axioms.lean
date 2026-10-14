import RamseySpace.Finitization

/-!
# Todorčević's abstract Ramsey-space axioms

A.1 is carried by `ApproximationSystem`, A.2 by `Finitization`, and this file
adds the amalgamation and pigeonhole axioms A.3 and A.4.

The structure stores a redundancy-free internal form of Todorčević's A.3(2):
if `A ≤ B` and `[a,A]` is nonempty, then one can refine inside
`[depth_B(a),B]` so that the new `[a,-]` neighborhood is contained in
`[a,A]`.  The printed axiom additionally says that this new neighborhood
is nonempty; that clause follows from A.3(1).  The theorem
`amalgamation_refine_published` and constructor `ofPublishedAxioms`
retain the clause explicitly, so the source-facing API is literal.

A separate consequence, `amalgamation_refine_onBasicMember`, covers the
useful case where the intermediate reduction already lies in `[a,B]`.
The public constructor `ofPublishedAxioms` follows the printed hypothesis.
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

/-- Todorčević's printed A.3(2), including the explicitly stated
nonemptiness of the refined neighborhood.  The internal structure omits
that redundant conjunct because A.3(1) supplies it automatically. -/
theorem amalgamation_refine_published (R : AbstractRamseySpace S)
    {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ}
    (hd : R.fin.HasDepth a B d) {A : S.Point}
    (hAB : S.le A B) (hne : (S.neighborhood a A).Nonempty) :
    ∃ A', A' ∈ S.levelNeighborhood d B ∧
      (S.neighborhood a A').Nonempty ∧
      S.neighborhood a A' ⊆ S.neighborhood a A := by
  rcases R.amalgamation_refine a B hd hAB hne with
    ⟨A', hA'B, hsub⟩
  exact ⟨A', hA'B, R.amalgamation_nonempty a B hd hA'B, hsub⟩

/-- Useful basic-member consequence of the published A.3(2): if
`A ∈ [a,B]` and `d = depth_B(a)`, there is `A' ∈ [d,B]` with
`[a,A'] ⊆ [a,A]`.

The published A.3(2) is the more general stored field
`AbstractRamseySpace.amalgamation_refine`, whose hypotheses are
`A ≤ B` and nonemptiness of `[a,A]`. -/
theorem amalgamation_refine_onBasicMember (R : AbstractRamseySpace S)
    {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ}
    (hd : R.fin.HasDepth a B d) {A : S.Point}
    (hA : A ∈ S.neighborhood a B) :
    ∃ A', A' ∈ S.levelNeighborhood d B ∧
      S.neighborhood a A' ⊆ S.neighborhood a A := by
  have hne : (S.neighborhood a A).Nonempty :=
    ⟨A, S.le_refl A, hA.2⟩
  exact R.amalgamation_refine a B hd hA.1 hne

/-- Build the A.1--A.4 interface from the literal published formulations of
A.3(1), A.3(2), and A.4.  A.1 is carried by `ApproximationSystem` and
A.2 by `Finitization`.

This is the preferred source-facing constructor. -/
def ofPublishedAxioms
    (fin : Finitization S)
    (amalgamation_nonempty :
      ∀ {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ},
        fin.HasDepth a B d →
        ∀ ⦃A : S.Point⦄, A ∈ S.levelNeighborhood d B →
          (S.neighborhood a A).Nonempty)
    (amalgamation_refine :
      ∀ {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ},
        fin.HasDepth a B d →
        ∀ {A : S.Point}, S.le A B →
          (S.neighborhood a A).Nonempty →
          ∃ A', A' ∈ S.levelNeighborhood d B ∧
            (S.neighborhood a A').Nonempty ∧
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
    rcases amalgamation_refine a B hd hAB hne with
      ⟨A', hA'B, _, hsub⟩
    exact ⟨A', hA'B, hsub⟩
  pigeonhole := pigeonhole

end AbstractRamseySpace

end RamseySpace
