import RamseySpace.Axioms

/-!
# Fusion limits

The combinatorial proof only needs the existence of limits for fusion sequences.
We isolate that property here; a later topology module will prove that
Todorčević's metric closedness hypothesis implies it.
-/

namespace RamseySpace

universe u v

namespace ApproximationSystem

variable (S : ApproximationSystem.{u, v})

/-- A fusion sequence whose kth protected level is n0+k. -/
def IsFusionFrom (n0 : ℕ) (Y : ℕ → S.Point) : Prop :=
  ∀ k, Y (k + 1) ∈ S.levelNeighborhood (n0 + k) (Y k)

end ApproximationSystem

/-- The fragment of closedness actually consumed by the forcing proof:
every arithmetic-level fusion sequence has a limit lying in every protected
neighborhood. -/
structure FusionComplete (S : ApproximationSystem.{u, v}) : Prop where
  limit :
    ∀ (n0 : ℕ) (Y : ℕ → S.Point),
      S.IsFusionFrom n0 Y →
      ∃ X, ∀ k, X ∈ S.levelNeighborhood (n0 + k) (Y k)

namespace FusionComplete

variable {S : ApproximationSystem.{u, v}} (C : FusionComplete S)

theorem exists_limit {n0 : ℕ} {Y : ℕ → S.Point}
    (hY : S.IsFusionFrom n0 Y) :
    ∃ X, ∀ k, X ∈ S.levelNeighborhood (n0 + k) (Y k) :=
  C.1 n0 Y hY

end FusionComplete

end RamseySpace
