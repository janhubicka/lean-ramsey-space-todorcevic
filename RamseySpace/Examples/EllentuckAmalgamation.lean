import RamseySpace.Examples.EllentuckDepth

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
          simp only [dif_pos hk, dif_neg hk1]
          rw [hkn, Nat.sub_self, Nat.add_zero, ← hj]
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
    change A j.1 = a.1 ⟨k, hk⟩ at hj
    rw [splice_apply_lt a A d hsub hk]
    exact hj
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


/-- Preserve the first e+1 values of B and then continue with the tail of A
past the finite approximation of length n. -/
def protect {n : ℕ} (B A : Point) (e : ℕ) (hn : 0 < n)
    (hboundary : B e = A (n - 1)) : Point :=
  OrderEmbedding.ofStrictMono
    (fun k =>
      if k < e + 1 then B k
      else A (n + (k - (e + 1))))
    (by
      apply strictMono_nat_of_lt_succ
      intro k
      by_cases hk1 : k + 1 < e + 1
      · have hk : k < e + 1 := by omega
        simp only [if_pos hk, if_pos hk1]
        exact B.strictMono (by omega)
      · by_cases hk : k < e + 1
        · have hke : k = e := by omega
          simp only [if_pos hk, if_neg hk1]
          rw [hke]
          simp only [Nat.sub_self, Nat.add_zero]
          rw [hboundary]
          exact A.strictMono (by omega)
        · simp only [if_neg hk, if_neg hk1]
          apply A.strictMono
          omega)

@[simp] theorem protect_apply_lt {n : ℕ} (B A : Point) (e : ℕ)
    (hn : 0 < n) (hboundary) {k : ℕ} (hk : k < e + 1) :
    protect B A e hn hboundary k = B k := by
  change (if k < e + 1 then B k
    else A (n + (k - (e + 1)))) = B k
  rw [if_pos hk]

@[simp] theorem protect_apply_ge {n : ℕ} (B A : Point) (e : ℕ)
    (hn : 0 < n) (hboundary) {k : ℕ} (hk : e + 1 ≤ k) :
    protect B A e hn hboundary k =
      A (n + (k - (e + 1))) := by
  change (if k < e + 1 then B k
    else A (n + (k - (e + 1)))) =
      A (n + (k - (e + 1)))
  rw [if_neg (not_lt.mpr hk)]

theorem approx_protect {n : ℕ} (B A : Point) (e : ℕ)
    (hn : 0 < n) (hboundary : B e = A (n - 1)) :
    approx (e + 1) (protect B A e hn hboundary) =
      approx (e + 1) B := by
  apply Subtype.ext
  apply DFunLike.ext _ _
  intro i
  change protect B A e hn hboundary i.1 = B i.1
  exact protect_apply_lt B A e hn hboundary i.2

theorem protect_le {n : ℕ} (B A : Point) (e : ℕ)
    (hn : 0 < n) (hboundary : B e = A (n - 1))
    (hAB : le A B) :
    le (protect B A e hn hboundary) B := by
  intro x hx
  rcases hx with ⟨k, rfl⟩
  by_cases hk : k < e + 1
  · refine ⟨k, ?_⟩
    exact (protect_apply_lt B A e hn hboundary hk).symm
  · have hk' : e + 1 ≤ k := not_lt.mp hk
    rw [protect_apply_ge B A e hn hboundary hk']
    apply hAB
    exact ⟨n + (k - (e + 1)), rfl⟩

theorem protect_mem_levelNeighborhood {n : ℕ} (B A : Point) (e : ℕ)
    (hn : 0 < n) (hboundary : B e = A (n - 1))
    (hAB : le A B) :
    protect B A e hn hboundary ∈
      S.levelNeighborhood (e + 1) B :=
  ⟨protect_le B A e hn hboundary hAB,
    approx_protect B A e hn hboundary⟩

/-- Every copy of a inside the protected-prefix splice already lies inside A. -/
theorem neighborhood_protect_subset {n : ℕ} (a : Approx n)
    (B A : Point) (e : ℕ) (hn : 0 < n)
    (hboundary : B e = A (n - 1))
    (hAa : approx n A = a) :
    S.neighborhood a (protect B A e hn hboundary)
      ⊆ S.neighborhood a A := by
  let last : Fin n := ⟨n - 1, by omega⟩
  intro X hX
  change Point at X
  refine ⟨?_, hX.2⟩
  change le X A
  intro x hx
  rcases hx with ⟨k, hkx⟩
  by_cases hkn : k < n
  · let i : Fin n := ⟨k, hkn⟩
    have hXa := congrArg (fun q : Approx n => q.1 i) hX.2
    have hAa' := congrArg (fun q : Approx n => q.1 i) hAa
    change X i.1 = a.1 i at hXa
    change A i.1 = a.1 i at hAa'
    refine ⟨k, ?_⟩
    calc
      A k = a.1 i := hAa'
      _ = X k := hXa.symm
      _ = x := hkx
  · have hnk : n ≤ k := not_lt.mp hkn
    have hlast_lt_k : n - 1 < k := by omega
    have hXlast0 := congrArg (fun q : Approx n => q.1 last) hX.2
    have hAlast0 := congrArg (fun q : Approx n => q.1 last) hAa
    change X last.1 = a.1 last at hXlast0
    change A last.1 = a.1 last at hAlast0
    have hgt : B e < x := by
      rw [hboundary, ← hAlast0, ← hXlast0, ← hkx]
      exact X.strictMono (by
        dsimp [last]
        exact hlast_lt_k)
    have hxP : x ∈ Set.range (protect B A e hn hboundary) :=
      hX.1 ⟨k, hkx⟩
    rcases hxP with ⟨t, ht⟩
    by_cases hte : t < e + 1
    · have hle : protect B A e hn hboundary t ≤ B e := by
        rw [protect_apply_lt B A e hn hboundary hte]
        exact B.monotone (by omega)
      have hxle : x ≤ B e := by
        rw [← ht]
        exact hle
      exact (not_lt_of_ge hxle hgt).elim
    · have hte' : e + 1 ≤ t := not_lt.mp hte
      refine ⟨n + (t - (e + 1)), ?_⟩
      calc
        A (n + (t - (e + 1))) =
            protect B A e hn hboundary t :=
          (protect_apply_ge B A e hn hboundary hte').symm
        _ = x := ht

/-- Todorčević A.3(2) for the classical Ellentuck space. -/
theorem amalgamation_refine_standard
    {n : ℕ} (a : Approx n) (B : Point) {d : ℕ}
    (hd : finitization.HasDepth a B d)
    {A : Point} (hA : A ∈ S.neighborhood a B) :
    ∃ A', A' ∈ S.levelNeighborhood d B ∧
      S.neighborhood a A' ⊆ S.neighborhood a A := by
  by_cases hn : n = 0
  · subst n
    have hd0 : d = 0 := depth_zero_of_empty a B hd
    subst d
    refine ⟨A, ?_, fun _ h => h⟩
    refine ⟨hA.1, ?_⟩
    change approx 0 A = approx 0 B
    rw [approx_zero, approx_zero]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rcases depth_succ_last a B hnpos hd with ⟨e, rfl, hlast⟩
    let last : Fin n := ⟨n - 1, by omega⟩
    have hAlast := congrArg (fun q : Approx n => q.1 last) hA.2
    change A last.1 = a.1 last at hAlast
    have hboundary : B e = A (n - 1) := by
      calc
        B e = a.1 last := by simpa [last] using hlast.symm
        _ = A last.1 := hAlast.symm
        _ = A (n - 1) := rfl
    let A' : S.Point := protect B A e hnpos hboundary
    refine ⟨A', ?_, ?_⟩
    · change protect B A e hnpos hboundary ∈
        S.levelNeighborhood (e + 1) B
      exact protect_mem_levelNeighborhood B A e hnpos hboundary hA.1
    · change S.neighborhood a (protect B A e hnpos hboundary) ⊆
        S.neighborhood a A
      exact neighborhood_protect_subset a B A e hnpos hboundary hA.2

end Ellentuck
end Examples
end RamseySpace
