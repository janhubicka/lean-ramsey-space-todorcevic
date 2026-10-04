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
  {A | ∃ n, ∃ b : P.Obj.Approx n,
      O n b ∧ A ∈ P.objectNeighborhood b X}

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
    IsRamseyBelow R X (basicUnion X O) := by
  intro n a Y d hY hd
  exact
    (IsBaireBelow.isRamseyBelow R C
      (basicUnion_isBaireBelow R X O)) a Y hY hd

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
    IsRamseyBelow R X (P.objectNeighborhood b X) := by
  intro n a Y d hY hd
  exact
    (IsBaireBelow.isRamseyBelow R C
      (objectNeighborhood_isBaireBelow R b X)) a Y hY hd

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
  have hnode : IsRamseyBelow R X (Souslin.normalize A s) := by
    intro m b Y d hY hd
    exact
      (IsRamsey.isRamseyBelow R hnodeGlobal X) b Y hY hd
  have hinter :
      IsRamseyBelow R X
        (P.objectNeighborhood a X ∩ Souslin.normalize A s) := by
    intro m b Y d hY hd
    exact (IsRamseyBelow.inter R hbase hnode) b Y hY hd
  have haccepted :
      IsRamseyBelow R X
        (acceptedUnion R (Souslin.tail (Souslin.normalize A) s)ᶜ X) := by
    intro m b Y d hY hd
    exact
      (acceptedUnion_isRamseyBelow R C
        (Souslin.tail (Souslin.normalize A) s)ᶜ X) b Y hY hd
  unfold souslinEnvelope
  intro m b Y d hY hd
  exact (IsRamseyBelow.diff R hinter haccepted) b Y hY hd


/-- Todorčević Claim 4.39.1 in the normalized list coding.

Assume the common fusion object X decides the complement of the normalized
tail above s for every approximation whose X-depth is beyond the scheduled
code of s.  Then every S(≤X)-Baire subset of the part of the local envelope
outside that tail is S(≤X)-meagre. -/
theorem baireSubset_souslinEnvelope_diff_tail_isMeagreBelow
    (R : AbstractRamseySystem P)
    (A : Souslin.Scheme P.Obj.Point)
    {n : ℕ} (a : P.Obj.Approx n)
    (X : P.Red.Point) (s : List ℕ) (n0 : ℕ)
    (hdec :
      ∀ {m : ℕ} (b : P.Obj.Approx m) {d : ℕ},
        R.fin.HasDepth b X d →
        n0 + Encodable.encode s ≤ d →
        Decides R
          (Souslin.tail (Souslin.normalize A) s)ᶜ X b)
    {M : Set P.Obj.Point}
    (hM : IsBaireBelow (P := P) X M)
    (hsub :
      M ⊆
        souslinEnvelope R A a X s \
          Souslin.tail (Souslin.normalize A) s) :
    IsMeagreBelow (P := P) X M := by
  classical
  intro m b Y hYX hne
  by_cases hmeet :
      ∃ B, B ∈ P.objectNeighborhood b Y ∧ B ∈ M
  · rcases hmeet with ⟨B, hBbY, hBM⟩
    have hBX : P.le0 B X :=
      R.fin.le0_trans hBbY.1 hYX
    rcases R.fin.exists_hasDepth_ge_of_le0
        hBX m (n0 + Encodable.encode s) with
      ⟨l, d, hml, hscheduled, hdepth⟩
    let c0 : P.Obj.Approx l := P.Obj.approx l B
    have hbc0 : P.Obj.IsInitial b c0 :=
      ⟨hml, B, hBbY.2, rfl⟩
    have hBc0Y : B ∈ P.objectNeighborhood c0 Y :=
      ⟨hBbY.1, rfl⟩
    rcases hM c0 Y hYX ⟨B, hBc0Y⟩ with
      ⟨k, c, Z, hc0c, hZY, hneCZ, hhom⟩
    have hbc : P.Obj.IsInitial b c :=
      P.Obj.isInitial_trans hbc0 hc0c
    rcases hhom with hcell | hdis
    · exfalso
      have hacceptZ :
          Accepts
            (Souslin.tail (Souslin.normalize A) s)ᶜ Z c := by
        intro W hWcZ
        have hWM : W ∈ M := hcell hWcZ
        exact (hsub hWM).2
      have hZX : P.Red.le Z X :=
        P.Red.le_trans hZY hYX
      have hneCZ0 : (P.objectNeighborhood c Z).Nonempty :=
        hneCZ
      rcases hneCZ with ⟨W, hWcZ⟩
      have hWcX : W ∈ P.objectNeighborhood c X :=
        ⟨R.fin.le0_trans hWcZ.1 hZX, hWcZ.2⟩
      rcases R.fin.exists_hasDepth_of_mem_objectNeighborhood hWcX with
        ⟨e, hdepthC⟩
      have hde : d ≤ e :=
        R.fin.hasDepth_le_of_initial hc0c hdepth hdepthC
      have hscheduledC :
          n0 + Encodable.encode s ≤ e :=
        hscheduled.trans hde
      have hdecision :=
        hdec c hdepthC hscheduledC
      rcases hdecision with haccX | hrejX
      · have hWM : W ∈ M := hcell hWcZ
        have hEnv :
            W ∈ souslinEnvelope R A a X s :=
          (hsub hWM).1
        have hAccepted :
            W ∈ acceptedUnion R
              (Souslin.tail (Souslin.normalize A) s)ᶜ X := by
          exact ⟨k, c, haccX, hWcX⟩
        exact hEnv.2 hAccepted
      · have hrejZ :
            Rejects R
              (Souslin.tail (Souslin.normalize A) s)ᶜ Z c :=
          rejects_mono R hrejX hZX hneCZ0
        exact (Rejects.not_accepts R hrejZ) hacceptZ
    · exact ⟨k, c, Z, hbc, hZY, hneCZ, hdis⟩
  · refine ⟨m, b, Y, P.Obj.isInitial_refl b, P.Red.le_refl Y,
      hne, ?_⟩
    rw [Set.disjoint_left]
    intro B hBbY hBM
    exact hmeet ⟨B, hBbY, hBM⟩

end CombinatorialForcing
end TwoSorted
end RamseySpace
