import RamseySpace.Examples.EllentuckFinitization

/-!
# Proper initial segments in Todorčević's A.2(3)

The general `Finitization.prefix_leFin` currently uses reflexive
`IsInitial` on both sides. The published A.2(3) requires *proper*
initial approximations. We prove that stronger statement directly for the
classical Ellentuck space, and thus for any Hrushovski copy space obtained
by exact reindexing of the classical space.

This is an audit supplement, not a claim that the abstract finitization
interface already enforces properness.
-/

namespace RamseySpace.Examples.Ellentuck

/-- Classical Ellentuck satisfies the literal proper-prefix A.2(3). -/
theorem prefix_leFin_proper
    {n m k : ℕ} {a : Approx n} {b : Approx m} {c : Approx k}
    (hab : S.IsInitial a b) (hnm : n < m)
    (hbc : leFin ⟨m, b⟩ ⟨k, c⟩) :
    ∃ (j : ℕ) (d : Approx j),
      j < k ∧ S.IsInitial d c ∧ leFin ⟨n, a⟩ ⟨j, d⟩ := by
  rcases hab with ⟨_, X, hXa, hXb⟩
  let last : Fin m := ⟨n, hnm⟩
  have hlast : b.1 last ∈ finiteRange (⟨m, b⟩ : S.FiniteApprox) :=
    ⟨last, rfl⟩
  rcases hbc hlast with ⟨j, hj⟩
  rcases S.approx_surjective k c with ⟨Z, hZ⟩
  let d : Approx j.1 := S.approx j.1 Z
  refine ⟨j.1, d, j.2, ?_, ?_⟩
  · exact ⟨Nat.le_of_lt j.2, Z, rfl, hZ⟩
  · intro x hx
    change x ∈ Set.range a.1 at hx
    rcases hx with ⟨t, ht⟩
    have hXt := congrArg (fun q : Approx n => q.1 t) hXa
    change X t.1 = a.1 t at hXt
    have hXn := congrArg (fun q : Approx m => q.1 last) hXb
    change X n = b.1 last at hXn
    have hlt : x < b.1 last := by
      rw [← ht, ← hXt, ← hXn]
      exact X.strictMono t.2
    have habS : S.IsInitial a b :=
      ⟨Nat.le_of_lt hnm, X, hXa, hXb⟩
    have hsub : x ∈ finiteRange (⟨k, c⟩ : S.FiniteApprox) :=
      hbc ((finiteRange_subset_of_isInitial habS) ⟨t, ht⟩)
    rcases hsub with ⟨i, hi⟩
    have hij : i.1 < j.1 := by
      by_contra hnot
      have hji : j ≤ i := by omega
      have hle : c.1 j ≤ c.1 i := c.1.monotone hji
      have hle' : b.1 last ≤ x := by
        calc
          b.1 last = c.1 j := hj.symm
          _ ≤ c.1 i := hle
          _ = x := hi
      exact (not_le_of_gt hlt) hle'
    let ii : Fin j.1 := ⟨i.1, hij⟩
    refine ⟨ii, ?_⟩
    have hZi := congrArg (fun q : Approx k => q.1 i) hZ
    change Z i.1 = c.1 i at hZi
    change Z ii.1 = x
    exact hZi.trans hi

end RamseySpace.Examples.Ellentuck
