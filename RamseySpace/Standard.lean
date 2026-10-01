import RamseySpace.Ramsey

/-!
# Source-facing Ramsey definitions

Todorčević defines a set to be Ramsey by quantifying directly over nonempty
basic neighborhoods `[a,A]` and asking for a homogeneous refinement
`B ∈ [a,A]`.  The forcing proof is cleaner with the equivalent depth-based
form in `RamseySpace.Ramsey`.

This file records the literal textbook definitions and proves the equivalence.
-/

namespace RamseySpace

universe u v

variable {S : ApproximationSystem.{u, v}}

/-- Textbook Ramsey property: every nonempty `[a,A]` contains
`B ∈ [a,A]` such that `[a,B]` is homogeneous. -/
def IsRamseyOnBasicNeighborhoods (target : Set S.Point) : Prop :=
  ∀ {n : ℕ} (a : S.Approx n) (A : S.Point),
    (S.neighborhood a A).Nonempty →
      ∃ B, B ∈ S.neighborhood a A ∧
        (S.neighborhood a B ⊆ target ∨
          Disjoint (S.neighborhood a B) target)

/-- Textbook Ramsey-null property: every nonempty `[a,A]` contains
`B ∈ [a,A]` with `[a,B]` disjoint from the target. -/
def IsRamseyNullOnBasicNeighborhoods (target : Set S.Point) : Prop :=
  ∀ {n : ℕ} (a : S.Approx n) (A : S.Point),
    (S.neighborhood a A).Nonempty →
      ∃ B, B ∈ S.neighborhood a A ∧
        Disjoint (S.neighborhood a B) target

theorem isRamsey_iff_onBasicNeighborhoods
    (R : AbstractRamseySpace S) (target : Set S.Point) :
    IsRamsey R target ↔ IsRamseyOnBasicNeighborhoods target := by
  constructor
  · intro hRamsey n a A hne
    rcases hne with ⟨X, hXaA⟩
    rcases R.fin.exists_hasDepth_of_mem_neighborhood hXaA with
      ⟨d, hd⟩
    rcases hRamsey a A hd with ⟨B, hBdA, hhom⟩
    have hneB : (S.neighborhood a B).Nonempty :=
      R.amalgamation_nonempty a A hd hBdA
    rcases hneB with ⟨C, hCaB⟩
    have hCaA : C ∈ S.neighborhood a A :=
      S.neighborhood_mono hBdA.1 hCaB
    refine ⟨C, hCaA, ?_⟩
    rcases hhom with hsub | hdis
    · exact Or.inl ((S.neighborhood_mono hCaB.1).trans hsub)
    · apply Or.inr
      rw [Set.disjoint_left] at hdis ⊢
      intro Y hYaC hYt
      exact hdis (S.neighborhood_mono hCaB.1 hYaC) hYt
  · intro hBasic n a A d hd
    have hne : (S.neighborhood a A).Nonempty :=
      R.amalgamation_nonempty a A hd
        (S.self_mem_levelNeighborhood d A)
    rcases hBasic a A hne with ⟨B, hBaA, hhom⟩
    rcases R.amalgamation_refine_standard a A hd hBaA with
      ⟨C, hCdA, hsub⟩
    refine ⟨C, hCdA, ?_⟩
    rcases hhom with ht | hdis
    · exact Or.inl (hsub.trans ht)
    · apply Or.inr
      rw [Set.disjoint_left] at hdis ⊢
      intro Y hYaC hYt
      exact hdis (hsub hYaC) hYt

theorem isRamseyNull_iff_onBasicNeighborhoods
    (R : AbstractRamseySpace S) (target : Set S.Point) :
    IsRamseyNull R target ↔ IsRamseyNullOnBasicNeighborhoods target := by
  constructor
  · intro hNull n a A hne
    rcases hne with ⟨X, hXaA⟩
    rcases R.fin.exists_hasDepth_of_mem_neighborhood hXaA with
      ⟨d, hd⟩
    rcases hNull a A hd with ⟨B, hBdA, hdis⟩
    have hneB : (S.neighborhood a B).Nonempty :=
      R.amalgamation_nonempty a A hd hBdA
    rcases hneB with ⟨C, hCaB⟩
    have hCaA : C ∈ S.neighborhood a A :=
      S.neighborhood_mono hBdA.1 hCaB
    refine ⟨C, hCaA, ?_⟩
    rw [Set.disjoint_left] at hdis ⊢
    intro Y hYaC hYt
    exact hdis (S.neighborhood_mono hCaB.1 hYaC) hYt
  · intro hBasic n a A d hd
    have hne : (S.neighborhood a A).Nonempty :=
      R.amalgamation_nonempty a A hd
        (S.self_mem_levelNeighborhood d A)
    rcases hBasic a A hne with ⟨B, hBaA, hdis⟩
    rcases R.amalgamation_refine_standard a A hd hBaA with
      ⟨C, hCdA, hsub⟩
    refine ⟨C, hCdA, ?_⟩
    rw [Set.disjoint_left] at hdis ⊢
    intro Y hYaC hYt
    exact hdis (hsub hYaC) hYt

end RamseySpace
