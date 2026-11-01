import RamseySpace.EquivTransport

/-!
# Literal proper-prefix form of Todorčević's A.2(3)

The basic `Finitization.prefix_leFin` field permits reflexive initial
approximations, since `ApproximationSystem.IsInitial` uses `n ≤ m`.
The literal published A.2(3) instead requires proper initial segments
on both sides.

This independent property records the strict conclusion and proves its
preservation under exact reindexing. It does not alter the established
A.1--A.4 structure or introduce a new axiom.
-/

namespace RamseySpace

universe u v w

namespace Finitization

variable {S : ApproximationSystem.{u, v}} {α : Type w}

/-- Literal proper-prefix A.2(3): if a is a *proper* prefix of b and
b ≤fin c, some *proper* prefix d of c satisfies a ≤fin d. -/
def HasProperPrefixA2 (F : Finitization S) : Prop :=
  ∀ {n m k : ℕ} {a : S.Approx n} {b : S.Approx m} {c : S.Approx k},
    S.IsInitial a b →
    n < m →
    F.leFin ⟨m, b⟩ ⟨k, c⟩ →
    ∃ (j : ℕ) (d : S.Approx j),
      j < k ∧ S.IsInitial d c ∧ F.leFin ⟨n, a⟩ ⟨j, d⟩

/-- A strict published A.2(3) proof transports to a space whose
approximations and order were transported by a genuine point bijection. -/
theorem reindex_hasProperPrefixA2
    (F : Finitization S) (e : α ≃ S.Point)
    (hproper : F.HasProperPrefixA2) :
    (F.reindex e).HasProperPrefixA2 := by
  intro n m k a b c hab hnm hbc
  rcases hab with ⟨hnm', X, hXa, hXb⟩
  have habS : S.IsInitial a b :=
    ⟨hnm', e X, hXa, hXb⟩
  rcases hproper habS hnm hbc with ⟨j, d, hjk, hdc, hfin⟩
  rcases hdc with ⟨hjk', Y, hYd, hYc⟩
  refine ⟨j, d, hjk, ⟨hjk', e.symm Y, ?_, ?_⟩, hfin⟩
  · change S.approx j (e (e.symm Y)) = d
    simpa using hYd
  · change S.approx k (e (e.symm Y)) = c
    simpa using hYc

end Finitization
end RamseySpace
