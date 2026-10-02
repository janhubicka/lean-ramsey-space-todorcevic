import RamseySpace.TwoSorted.SouslinDecision

/-!
# Souslin closure: local envelopes

This file formalizes the envelope in equation (4.13) of Todorcevic's proof.
The key point is that arbitrary unions of basic neighborhoods with a fixed
upper reduction are Baire relative to that upper reduction.
-/

namespace RamseySpace
namespace TwoSorted
namespace CombinatorialForcing

universe uR vR uS vS

variable {P : System.{uR, vR, uS, vS}}

/-- An arbitrary union of object basic neighborhoods with common reduction X. -/
def basicUnion (X : P.Red.Point)
    (O : ∀ n, P.Obj.Approx n → Prop) : Set P.Obj.Point :=
  {A | ∃ n (b : P.Obj.Approx n), O n b ∧ A ∈ P.objectNeighborhood b X}

/-- Arbitrary unions of basic neighborhoods are Baire below their common
upper reduction. -/
theorem basicUnion_isBaireBelow
    (R : AbstractRamseySystem P)
    (X : P.Red.Point)
    (O : ∀ n, P.Obj.Approx n → Prop) :
    IsBaireBelow X (basicUnion X O) := by
  classical
  intro n a Y hYX hne
  by_cases hinter :
      ∃ A, A ∈ P.objectNeighborhood a Y ∧ A ∈ basicUnion X O
  · rcases hinter with ⟨A, hAaY, m, b, hOb, hAbX⟩
    by_cases hnm : n ≤ m
    · have hab0 := P.Obj.isInitial_of_point hnm A
      have hab : P.Obj.IsInitial a b := by
        simpa [hAaY.2, hAbX.2] using hab0
      have hAbY : A ∈ P.objectNeighborhood b Y :=
        ⟨hAaY.1, hAbX.2⟩
      refine ⟨m, b, Y, hab, P.Red.le_refl Y, ⟨A, hAbY⟩, Or.inl ?_⟩
      intro B hBbY
      refine ⟨m, b, hOb, ?_⟩
      exact ⟨R.fin.le0_trans hBbY.1 hYX, hBbY.2⟩
    · have hmn : m ≤ n := by omega
      have hba0 := P.Obj.isInitial_of_point hmn A
      have hba : P.Obj.IsInitial b a := by
        simpa [hAaY.2, hAbX.2] using hba0
      refine ⟨n, a, Y, P.Obj.isInitial_refl a, P.Red.le_refl Y,
        hne, Or.inl ?_⟩
      intro B hBaY
      have hBbY : B ∈ P.objectNeighborhood b Y :=
        P.objectNeighborhood_initial_subset hba hBaY
      refine ⟨m, b, hOb, ?_⟩
      exact ⟨R.fin.le0_trans hBbY.1 hYX, hBbY.2⟩
  · refine ⟨n, a, Y, P.Obj.isInitial_refl a, P.Red.le_refl Y,
      hne, Or.inr ?_⟩
    rw [Set.disjoint_left]
    intro A hAaY hAU
    exact hinter ⟨A, hAaY, hAU⟩

theorem basicUnion_isRamseyBelow
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (X : P.Red.Point)
    (O : ∀ n, P.Obj.Approx n → Prop) :
    IsRamseyBelow R X (basicUnion X O) :=
  (basicUnion_isBaireBelow R X O).isRamseyBelow R C

/-- One basic object neighborhood is Baire below its upper reduction. -/
theorem objectNeighborhood_isBaireBelow
    (R : AbstractRamseySystem P)
    {m : ℕ} (b : P.Obj.Approx m) (X : P.Red.Point) :
    IsBaireBelow X (P.objectNeighborhood b X) := by
  classical
  intro n a Y hYX hne
  by_cases hinter :
      ∃ A, A ∈ P.objectNeighborhood a Y ∧
        A ∈ P.objectNeighborhood b X
  · rcases hinter with ⟨A, hAaY, hAbX⟩
    by_cases hnm : n ≤ m
    · have hab0 := P.Obj.isInitial_of_point hnm A
      have hab : P.Obj.IsInitial a b := by
        simpa [hAaY.2, hAbX.2] using hab0
      have hAbY : A ∈ P.objectNeighborhood b Y :=
        ⟨hAaY.1, hAbX.2⟩
      refine ⟨m, b, Y, hab, P.Red.le_refl Y, ⟨A, hAbY⟩, Or.inl ?_⟩
      intro B hBbY
      exact ⟨R.fin.le0_trans hBbY.1 hYX, hBbY.2⟩
    · have hmn : m ≤ n := by omega
      have hba0 := P.Obj.isInitial_of_point hmn A
      have hba : P.Obj.IsInitial b a := by
        simpa [hAaY.2, hAbX.2] using hba0
      refine ⟨n, a, Y, P.Obj.isInitial_refl a, P.Red.le_refl Y,
        hne, Or.inl ?_⟩
      intro B hBaY
      have hBbY : B ∈ P.objectNeighborhood b Y :=
        P.objectNeighborhood_initial_subset hba hBaY
      exact ⟨R.fin.le0_trans hBbY.1 hYX, hBbY.2⟩
  · refine ⟨n, a, Y, P.Obj.isInitial_refl a, P.Red.le_refl Y,
      hne, Or.inr ?_⟩
    rw [Set.disjoint_left]
    intro A hAaY hAbX
    exact hinter ⟨A, hAaY, hAbX⟩

theorem objectNeighborhood_isRamseyBelow
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    {m : ℕ} (b : P.Obj.Approx m) (X : P.Red.Point) :
    IsRamseyBelow R X (P.objectNeighborhood b X) :=
  (objectNeighborhood_isBaireBelow R b X).isRamseyBelow R C

/-- Union of the neighborhoods whose approximation is accepted for target. -/
def acceptedUnion
    (R : AbstractRamseySystem P)
    (target : Set P.Obj.Point) (X : P.Red.Point) : Set P.Obj.Point :=
  basicUnion X (fun _ b => Accepts target X b)

theorem acceptedUnion_isRamseyBelow
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (target : Set P.Obj.Point) (X : P.Red.Point) :
    IsRamseyBelow R X (acceptedUnion R target X) :=
  basicUnion_isRamseyBelow R C X (fun _ b => Accepts target X b)

/-- The local envelope Phi(X_s^*) from equation (4.13), in normalized
finite-sequence coding. -/
def souslinEnvelope
    (R : AbstractRamseySystem P)
    (A : Souslin.Scheme P.Obj.Point)
    {n : ℕ} (a : P.Obj.Approx n)
    (X : P.Red.Point) (s : List ℕ) : Set P.Obj.Point :=
  (P.objectNeighborhood a X ∩ Souslin.normalize A s) \
    acceptedUnion R (Souslin.tail (Souslin.normalize A) s)ᶜ X

/-- The normalized Souslin tail, restricted to the starting neighborhood,
is contained in its local envelope. -/
theorem tail_subset_souslinEnvelope
    (R : AbstractRamseySystem P)
    (A : Souslin.Scheme P.Obj.Point)
    {n : ℕ} (a : P.Obj.Approx n)
    (X : P.Red.Point) (s : List ℕ) :
    P.objectNeighborhood a X ∩ Souslin.tail (Souslin.normalize A) s ⊆
      souslinEnvelope R A a X s := by
  intro B hB
  refine ⟨⟨hB.1, Souslin.tail_normalize_subset A s hB.2⟩, ?_⟩
  intro hBU
  rcases hBU with ⟨m, b, hacc, hBbX⟩
  have hcomp : B ∈ (Souslin.tail (Souslin.normalize A) s)ᶜ :=
    hacc hBbX
  exact hcomp hB.2

/-- The local envelope is Ramsey below X when the original scheme consists
of Ramsey sets. -/
theorem souslinEnvelope_isRamseyBelow
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (A : Souslin.Scheme P.Obj.Point)
    (hA : ∀ s, IsRamsey R (A s))
    {n : ℕ} (a : P.Obj.Approx n)
    (X : P.Red.Point) (s : List ℕ) :
    IsRamseyBelow R X (souslinEnvelope R A a X s) := by
  have hbase : IsRamseyBelow R X (P.objectNeighborhood a X) :=
    objectNeighborhood_isRamseyBelow R C a X
  have hnodeGlobal : IsRamsey R (Souslin.normalize A s) :=
    normalize_isRamsey R C A hA s
  have hnode : IsRamseyBelow R X (Souslin.normalize A s) :=
    hnodeGlobal.isRamseyBelow R X
  have hinter :
      IsRamseyBelow R X
        (P.objectNeighborhood a X ∩ Souslin.normalize A s) :=
    hbase.inter R hnode
  have haccepted :
      IsRamseyBelow R X
        (acceptedUnion R (Souslin.tail (Souslin.normalize A) s)ᶜ X) :=
    acceptedUnion_isRamseyBelow R C _ X
  exact hinter.diff R haccepted

end CombinatorialForcing
end TwoSorted
end RamseySpace
