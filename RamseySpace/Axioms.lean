import RamseySpace.Finitization

/-!
# Todorčević's abstract Ramsey-space axioms

A.1 is carried by `ApproximationSystem`, A.2 by `Finitization`, and this file
adds the amalgamation and pigeonhole axioms A.3 and A.4.

The structure stores Todorčević's published A.3(2) directly: if `A ≤ B`
and `[a,A]` is nonempty, then one can refine inside
`[depth_B(a),B]` so that the new `[a,-]` neighborhood is contained in
`[a,A]`.

Historically this library also exposed a convenient special case in which
`A` itself belongs to `[a,B]`, under the names
`amalgamation_refine_standard` and `ofStandardAxioms`.  That special
case is sufficient to derive the published axiom, but it is not the literal
formulation in Chapter 5.  The source-faithful constructor is now
`AbstractRamseySpace.ofPublishedAxioms`; the old names are retained only
for downstream compatibility.
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

/-- Legacy name for `amalgamation_refine_onBasicMember`.

This is a consequence of, not the literal formulation of, the published
A.3(2). -/
theorem amalgamation_refine_standard (R : AbstractRamseySpace S)
    {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ}
    (hd : R.fin.HasDepth a B d) {A : S.Point}
    (hA : A ∈ S.neighborhood a B) :
    ∃ A', A' ∈ S.levelNeighborhood d B ∧
      S.neighborhood a A' ⊆ S.neighborhood a A :=
  R.amalgamation_refine_onBasicMember a B hd hA

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
  amalgamation_refine := amalgamation_refine
  pigeonhole := pigeonhole

/-- Compatibility constructor from the special case of A.3(2) in which the
intermediate object itself belongs to `[a,B]`.

That special case implies the published A.3(2), but is not its literal
statement. New applications should normally use `ofPublishedAxioms`. -/
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
