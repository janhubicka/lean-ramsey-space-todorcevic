import RamseySpace.Examples.EllentuckAmalgamation

/-!
# The classical Ellentuck space: one-step tail combinatorics

Helpers for A.4.  We isolate the possible one-step extensions of a finite
approximation and the operation of thinning only the tail after a protected
depth.
-/

namespace RamseySpace
namespace Examples
namespace Ellentuck

/-- The point obtained by appending the tail of B starting at d+t after a. -/
def extensionPoint {n : ℕ} (a : Approx n) (B : Point) (d : ℕ)
    (hsub : leFin (⟨n, a⟩ : S.FiniteApprox) (S.finiteApprox d B))
    (t : ℕ) : Point :=
  splice a B (d + t) (by
    intro x hx
    exact prefixRange_mono B
      (show d ≤ d + t by omega) (hsub hx))

/-- The corresponding one-step finite approximation. -/
def extensionAt {n : ℕ} (a : Approx n) (B : Point) (d : ℕ)
    (hsub : leFin (⟨n, a⟩ : S.FiniteApprox) (S.finiteApprox d B))
    (t : ℕ) : Approx (n + 1) :=
  approx (n + 1) (extensionPoint a B d hsub t)

theorem extensionPoint_mem_neighborhood {n : ℕ} (a : Approx n)
    (B : Point) (d : ℕ)
    (hsub : leFin (⟨n, a⟩ : S.FiniteApprox) (S.finiteApprox d B))
    (t : ℕ) :
    extensionPoint a B d hsub t ∈ S.neighborhood a B := by
  unfold extensionPoint
  exact splice_mem_neighborhood _ _ _ _

theorem extensionAt_mem_oneStep {n : ℕ} (a : Approx n)
    (B : Point) (d : ℕ)
    (hsub : leFin (⟨n, a⟩ : S.FiniteApprox) (S.finiteApprox d B))
    (t : ℕ) :
    extensionAt a B d hsub t ∈ S.oneStepApproximations a B :=
  ⟨extensionPoint a B d hsub t,
    extensionPoint_mem_neighborhood a B d hsub t, rfl⟩

theorem extensionPoint_newValue {n : ℕ} (a : Approx n)
    (B : Point) (d : ℕ)
    (hsub : leFin (⟨n, a⟩ : S.FiniteApprox) (S.finiteApprox d B))
    (t : ℕ) :
    extensionPoint a B d hsub t n = B (d + t) := by
  unfold extensionPoint
  rw [splice_apply_ge _ _ _ _ le_rfl]
  simp

/-- Two points with the same n-prefix and the same nth value have the same
(n+1)-approximation. -/
theorem approx_succ_eq_of_prefix_eq_newValue {n : ℕ}
    {X Y : Point} (hp : approx n X = approx n Y)
    (hn : X n = Y n) :
    approx (n + 1) X = approx (n + 1) Y := by
  apply Subtype.ext
  apply DFunLike.ext _ _
  intro i
  by_cases hi : i.1 < n
  · let j : Fin n := ⟨i.1, hi⟩
    have h := congrArg (fun q : Approx n => q.1 j) hp
    change X j.1 = Y j.1 at h
    change X i.1 = Y i.1
    exact h
  · have hin : i.1 = n := by omega
    change X i.1 = Y i.1
    simpa [hin] using hn

theorem approx_succ_eq_extensionAt {n : ℕ} (a : Approx n)
    (B X : Point) (d : ℕ)
    (hsub : leFin (⟨n, a⟩ : S.FiniteApprox) (S.finiteApprox d B))
    (t : ℕ) (hXa : approx n X = a)
    (hnew : X n = B (d + t)) :
    approx (n + 1) X = extensionAt a B d hsub t := by
  unfold extensionAt
  apply approx_succ_eq_of_prefix_eq_newValue
  · exact hXa.trans
      (approx_splice _ _ _ _).symm
  · rw [extensionPoint_newValue]
    exact hnew

/-- Preserve the first d values of B and then follow B along an increasing
sequence of tail offsets. -/
def thinTail (B : Point) (d : ℕ) (sel : ℕ → ℕ)
    (hsel : StrictMono sel) : Point :=
  OrderEmbedding.ofStrictMono
    (fun k =>
      if k < d then B k
      else B (d + sel (k - d)))
    (by
      apply strictMono_nat_of_lt_succ
      intro k
      by_cases hk1 : k + 1 < d
      · have hk : k < d := by omega
        simp only [if_pos hk, if_pos hk1]
        exact B.strictMono (by omega)
      · by_cases hk : k < d
        · have hkd : k + 1 = d := by omega
          simp only [if_pos hk, if_neg hk1]
          rw [hkd, Nat.sub_self]
          apply B.strictMono
          omega
        · have hk' : ¬ k + 1 < d := by omega
          simp only [if_neg hk, if_neg hk']
          apply B.strictMono
          have hs : sel (k - d) < sel (k + 1 - d) :=
            hsel (by omega)
          omega)

@[simp] theorem thinTail_apply_lt (B : Point) (d : ℕ)
    (sel : ℕ → ℕ) (hsel : StrictMono sel)
    {k : ℕ} (hk : k < d) :
    thinTail B d sel hsel k = B k := by
  change (if k < d then B k else B (d + sel (k - d))) = B k
  rw [if_pos hk]

@[simp] theorem thinTail_apply_ge (B : Point) (d : ℕ)
    (sel : ℕ → ℕ) (hsel : StrictMono sel)
    {k : ℕ} (hk : d ≤ k) :
    thinTail B d sel hsel k = B (d + sel (k - d)) := by
  change (if k < d then B k else B (d + sel (k - d))) =
    B (d + sel (k - d))
  rw [if_neg (not_lt.mpr hk)]

theorem thinTail_le (B : Point) (d : ℕ)
    (sel : ℕ → ℕ) (hsel : StrictMono sel) :
    le (thinTail B d sel hsel) B := by
  intro x hx
  rcases hx with ⟨k, rfl⟩
  by_cases hk : k < d
  · exact ⟨k, (thinTail_apply_lt B d sel hsel hk).symm⟩
  · have hk' : d ≤ k := not_lt.mp hk
    rw [thinTail_apply_ge B d sel hsel hk']
    exact ⟨d + sel (k - d), rfl⟩

theorem approx_thinTail (B : Point) (d : ℕ)
    (sel : ℕ → ℕ) (hsel : StrictMono sel) :
    approx d (thinTail B d sel hsel) = approx d B := by
  apply Subtype.ext
  apply DFunLike.ext _ _
  intro i
  change thinTail B d sel hsel i.1 = B i.1
  exact thinTail_apply_lt B d sel hsel i.2

theorem thinTail_mem_levelNeighborhood (B : Point) (d : ℕ)
    (sel : ℕ → ℕ) (hsel : StrictMono sel) :
    thinTail B d sel hsel ∈ S.levelNeighborhood d B :=
  ⟨thinTail_le B d sel hsel, approx_thinTail B d sel hsel⟩

/-- Every infinite set of naturals has a strictly increasing enumeration of
an infinite subset. -/
theorem exists_strictMono_mem {t : Set ℕ} (ht : t.Infinite) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ i, f i ∈ t := by
  letI : Infinite t := Set.infinite_coe_iff.mpr ht
  obtain ⟨g, hg⟩ := Infinite.exists_strictMono_or_strictAnti t
  rcases hg with hmono | hanti
  · refine ⟨fun i => (g i).1, ?_, fun i => (g i).2⟩
    intro i j hij
    exact hmono hij
  · have hanti' : StrictAnti (fun i => (g i).1) := by
      intro i j hij
      exact hanti hij
    exact (not_strictAnti_of_wellFoundedLT
      (fun i => (g i).1) hanti').elim

end Ellentuck
end Examples
end RamseySpace
