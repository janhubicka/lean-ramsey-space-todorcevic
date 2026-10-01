import RamseySpace.Examples.EllentuckFinitization

/-!
# The classical Ellentuck space: amalgamation

This file develops the standard prefix-plus-tail construction.  It first proves
A.3(1); the same construction is then used for A.3(2).
-/

namespace RamseySpace
namespace Examples
namespace Ellentuck

/-- Append the tail of A starting at d after the finite approximation a.
The hypothesis says that every value of a already occurs among the first d
values of A, so the resulting sequence is strictly increasing. -/
def splice {n : ℕ} (a : Approx n) (A : Point) (d : ℕ)
    (hsub :
      finiteRange (⟨n, a⟩ : S.FiniteApprox) ⊆
        finiteRange (S.finiteApprox d A)) :
    Point :=
  OrderEmbedding.ofStrictMono
    (fun k =>
      if hk : k < n then a.1 ⟨k, hk⟩
      else A (d + (k - n)))
    (by
      apply strictMono_nat_of_lt_succ
      intro k
      by_cases hk1 : k + 1 < n
      · have hk : k < n := by omega
        simp only [dif_pos hk, dif_pos hk1]
        exact a.1.strictMono (by simp)
      · by_cases hk : k < n
        · have hkn : k + 1 = n := by omega
          have hmem :
              a.1 ⟨k, hk⟩ ∈
                finiteRange (S.finiteApprox d A) := by
            apply hsub
            change a.1 ⟨k, hk⟩ ∈ Set.range a.1
            exact ⟨⟨k, hk⟩, rfl⟩
          rcases hmem with ⟨j, hj⟩
          change (approx d A).1 j = a.1 ⟨k, hk⟩ at hj
          change A j.1 = a.1 ⟨k, hk⟩ at hj
          simp only [dif_pos hk, dif_neg hk1, hkn, Nat.sub_self,
            Nat.add_zero]
          rw [← hj]
          exact A.strictMono j.2
        · have hk' : ¬ k + 1 < n := by omega
          simp only [dif_neg hk, dif_neg hk']
          apply A.strictMono
          omega)

@[simp] theorem splice_apply_lt {n : ℕ} (a : Approx n) (A : Point)
    (d : ℕ) (hsub) {k : ℕ} (hk : k < n) :
    splice a A d hsub k = a.1 ⟨k, hk⟩ := by
  simp [splice, hk]

@[simp] theorem splice_apply_ge {n : ℕ} (a : Approx n) (A : Point)
    (d : ℕ) (hsub) {k : ℕ} (hk : n ≤ k) :
    splice a A d hsub k = A (d + (k - n)) := by
  simp [splice, not_lt.mpr hk]

theorem approx_splice {n : ℕ} (a : Approx n) (A : Point) (d : ℕ)
    (hsub :
      finiteRange (⟨n, a⟩ : S.FiniteApprox) ⊆
        finiteRange (S.finiteApprox d A)) :
    approx n (splice a A d hsub) = a := by
  apply Subtype.ext
  apply DFunLike.ext _ _
  intro i
  change splice a A d hsub i.1 = a.1 i
  simpa using splice_apply_lt a A d hsub i.2

theorem splice_le {n : ℕ} (a : Approx n) (A : Point) (d : ℕ)
    (hsub :
      finiteRange (⟨n, a⟩ : S.FiniteApprox) ⊆
        finiteRange (S.finiteApprox d A)) :
    le (splice a A d hsub) A := by
  intro x hx
  rcases hx with ⟨k, rfl⟩
  by_cases hk : k < n
  · have hmem :
        a.1 ⟨k, hk⟩ ∈ finiteRange (S.finiteApprox d A) := by
      apply hsub
      change a.1 ⟨k, hk⟩ ∈ Set.range a.1
      exact ⟨⟨k, hk⟩, rfl⟩
    rcases hmem with ⟨j, hj⟩
    refine ⟨j.1, ?_⟩
    change (approx d A).1 j = splice a A d hsub k at hj ⊢
    change A j.1 = splice a A d hsub k at hj ⊢
    simpa using hj
  · refine ⟨d + (k - n), ?_⟩
    exact (splice_apply_ge a A d hsub (not_lt.mp hk)).symm

theorem splice_mem_neighborhood {n : ℕ} (a : Approx n)
    (A : Point) (d : ℕ)
    (hsub :
      finiteRange (⟨n, a⟩ : S.FiniteApprox) ⊆
        finiteRange (S.finiteApprox d A)) :
    splice a A d hsub ∈ S.neighborhood a A :=
  ⟨splice_le a A d hsub, approx_splice a A d hsub⟩

/-- Todorčević A.3(1) for the classical Ellentuck space. -/
theorem amalgamation_nonempty
    {n : ℕ} (a : Approx n) (B : Point) {d : ℕ}
    (hd : finitization.HasDepth a B d)
    ⦃A : Point⦄ (hA : A ∈ S.levelNeighborhood d B) :
    (S.neighborhood a A).Nonempty := by
  have hsubB :
      leFin (⟨n, a⟩ : S.FiniteApprox) (S.finiteApprox d B) :=
    hd.1
  have hprefix :
      S.finiteApprox d A = S.finiteApprox d B := by
    exact Sigma.ext rfl (heq_of_eq hA.2)
  have hsubA :
      leFin (⟨n, a⟩ : S.FiniteApprox) (S.finiteApprox d A) := by
    rw [hprefix]
    exact hsubB
  refine ⟨splice a A d hsubA, ?_⟩
  exact splice_mem_neighborhood a A d hsubA

end Ellentuck
end Examples
end RamseySpace
