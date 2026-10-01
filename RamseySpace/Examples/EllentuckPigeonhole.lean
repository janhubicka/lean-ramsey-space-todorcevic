import RamseySpace.Examples.EllentuckAmalgamation
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Nth

/-!
# The classical Ellentuck space: A.4 pigeonhole

For a finite approximation `a` of depth `d` in `B`, every one-step
extension is obtained by adjoining one value from the tail of `B` after the
protected prefix of length `d`.  We color these candidate tail values with
two colors according to membership in `O`, use the infinite pigeonhole
principle, and keep an infinite monochromatic tail.
-/

namespace RamseySpace
namespace Examples
namespace Ellentuck

/-- The finite range of `a` is contained in every longer prefix of `B`
starting at its depth. -/
theorem depth_range_subset_prefix {n d : ℕ} (a : Approx n) (B : Point)
    (hd : finitization.HasDepth a B d) (j : ℕ) (hdj : d ≤ j) :
    finiteRange (⟨n, a⟩ : S.FiniteApprox) ⊆
      finiteRange (S.finiteApprox j B) :=
  hd.1.trans (prefixRange_mono B hdj)

/-- The canonical one-step extension of `a` obtained by taking the
`q`th value of the tail of `B` beyond depth `d`. -/
def candidate {n d : ℕ} (a : Approx n) (B : Point)
    (hd : finitization.HasDepth a B d) (q : ℕ) : Approx (n + 1) :=
  let hsub :=
    depth_range_subset_prefix a B hd (d + q) (by omega)
  approx (n + 1) (splice a B (d + q) hsub)

theorem candidate_mem_oneStep {n d : ℕ} (a : Approx n) (B : Point)
    (hd : finitization.HasDepth a B d) (q : ℕ) :
    candidate a B hd q ∈ S.oneStepApproximations a B := by
  let hsub :=
    depth_range_subset_prefix a B hd (d + q) (by omega)
  refine ⟨splice a B (d + q) hsub, ?_, rfl⟩
  exact splice_mem_neighborhood a B (d + q) hsub

theorem candidate_last {n d : ℕ} (a : Approx n) (B : Point)
    (hd : finitization.HasDepth a B d) (q : ℕ) :
    (candidate a B hd q).1 ⟨n, by omega⟩ = B (d + q) := by
  let hsub :=
    depth_range_subset_prefix a B hd (d + q) (by omega)
  change splice a B (d + q) hsub n = B (d + q)
  simpa using
    (splice_apply_ge a B (d + q) hsub (k := n) (le_rfl : n ≤ n))

/-- Two `(n+1)`-approximations agree when they have the same
`n`-prefix and the same last value. -/
theorem approx_succ_eq_of_prefix_last {n : ℕ} {X Y : Point}
    (hp : approx n X = approx n Y) (hlast : X n = Y n) :
    approx (n + 1) X = approx (n + 1) Y := by
  apply Subtype.ext
  apply DFunLike.ext _ _
  intro i
  by_cases hi : i.1 < n
  · let j : Fin n := ⟨i.1, hi⟩
    have h := congrArg (fun q : Approx n => q.1 j) hp
    change X i.1 = Y i.1
    change X j.1 = Y j.1 at h
    exact h
  · have hin : i.1 = n := by omega
    change X i.1 = Y i.1
    simpa [hin] using hlast

/-- Keep the first `d` values of `B`, and afterwards keep precisely the
tail offsets satisfying an infinite predicate `p`. -/
noncomputable def homogeneousTail (B : Point) (d : ℕ)
    (p : ℕ → Prop) (hp : (Set.ofPred p).Infinite) : Point :=
  OrderEmbedding.ofStrictMono
    (fun k =>
      if hk : k < d then B k
      else B (d + Nat.nth p (k - d)))
    (by
      apply strictMono_nat_of_lt_succ
      intro k
      by_cases hk1 : k + 1 < d
      · have hk : k < d := by omega
        simp only [dif_pos hk, dif_pos hk1]
        exact B.strictMono (by omega)
      · by_cases hk : k < d
        · simp only [dif_pos hk, dif_neg hk1]
          apply B.strictMono
          omega
        · have hk' : ¬ k + 1 < d := by omega
          simp only [dif_neg hk, dif_neg hk']
          apply B.strictMono
          have hnth :
              Nat.nth p (k - d) < Nat.nth p (k + 1 - d) :=
            (Nat.nth_strictMono hp) (by omega)
          omega)

@[simp] theorem homogeneousTail_apply_lt (B : Point) (d : ℕ)
    (p : ℕ → Prop) (hp : (Set.ofPred p).Infinite)
    {k : ℕ} (hk : k < d) :
    homogeneousTail B d p hp k = B k := by
  simp [homogeneousTail, hk]

@[simp] theorem homogeneousTail_apply_ge (B : Point) (d : ℕ)
    (p : ℕ → Prop) (hp : (Set.ofPred p).Infinite)
    {k : ℕ} (hk : d ≤ k) :
    homogeneousTail B d p hp k =
      B (d + Nat.nth p (k - d)) := by
  simp [homogeneousTail, not_lt.mpr hk]

theorem homogeneousTail_le (B : Point) (d : ℕ)
    (p : ℕ → Prop) (hp : (Set.ofPred p).Infinite) :
    le (homogeneousTail B d p hp) B := by
  intro x hx
  rcases hx with ⟨k, rfl⟩
  by_cases hk : k < d
  · refine ⟨k, ?_⟩
    exact (homogeneousTail_apply_lt B d p hp hk).symm
  · refine ⟨d + Nat.nth p (k - d), ?_⟩
    exact (homogeneousTail_apply_ge B d p hp (not_lt.mp hk)).symm

theorem approx_homogeneousTail (B : Point) (d : ℕ)
    (p : ℕ → Prop) (hp : (Set.ofPred p).Infinite) :
    approx d (homogeneousTail B d p hp) = approx d B := by
  apply Subtype.ext
  apply DFunLike.ext _ _
  intro i
  change homogeneousTail B d p hp i.1 = B i.1
  exact homogeneousTail_apply_lt B d p hp i.2

theorem homogeneousTail_mem_levelNeighborhood (B : Point) (d : ℕ)
    (p : ℕ → Prop) (hp : (Set.ofPred p).Infinite) :
    homogeneousTail B d p hp ∈ S.levelNeighborhood d B :=
  ⟨homogeneousTail_le B d p hp, approx_homogeneousTail B d p hp⟩

/-- In a one-step extension of `a` inside a depth-preserving refinement,
the new value occurs in the refinement at an index at least the protected
depth. -/
theorem oneStep_new_index_ge_depth {n d : ℕ} (a : Approx n)
    (B A X : Point) (hd : finitization.HasDepth a B d)
    (hA : A ∈ S.levelNeighborhood d B)
    (hX : X ∈ S.neighborhood a A) :
    ∀ t, A t = X n → d ≤ t := by
  intro t ht
  have hdA : finitization.HasDepth a A d :=
    (finitization.hasDepth_iff_of_mem_levelNeighborhood hA).2 hd
  by_cases hn : n = 0
  · subst n
    have hd0 : d = 0 := depth_zero_of_empty a A hdA
    omega
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rcases depth_succ_last a A hnpos hdA with ⟨e, hde, hlast⟩
    subst d
    let last : Fin n := ⟨n - 1, by omega⟩
    have hXlast := congrArg (fun q : Approx n => q.1 last) hX.2
    change X last.1 = a.1 last at hXlast
    have hAe : A e = a.1 last := by
      simpa [last] using hlast.symm
    have hltX : X (n - 1) < X n := X.strictMono (by omega)
    have hltA : A e < A t := by
      rw [hAe, ← hXlast, ht]
      simpa [last] using hltX
    have het : e < t := (A.lt_iff_lt).mp hltA
    omega

/-- Every one-step approximation inside a homogeneous-tail refinement is the
canonical candidate corresponding to one of the selected tail offsets. -/
theorem oneStep_eq_candidate {n d : ℕ} (a : Approx n) (B : Point)
    (hd : finitization.HasDepth a B d)
    (p : ℕ → Prop) (hp : (Set.ofPred p).Infinite)
    {b : Approx (n + 1)}
    (hb : b ∈ S.oneStepApproximations a (homogeneousTail B d p hp)) :
    ∃ q, p q ∧ b = candidate a B hd q := by
  rcases hb with ⟨X, hX, hXb⟩
  change Point at X
  have hA :
      homogeneousTail B d p hp ∈ S.levelNeighborhood d B :=
    homogeneousTail_mem_levelNeighborhood B d p hp
  rcases hX.1 ⟨n, rfl⟩ with ⟨t, ht⟩
  have hdt : d ≤ t :=
    oneStep_new_index_ge_depth a B (homogeneousTail B d p hp) X
      hd hA hX t ht
  let q := Nat.nth p (t - d)
  have hpq : p q := Nat.nth_mem_of_infinite hp (t - d)
  refine ⟨q, hpq, ?_⟩
  rw [← hXb]
  let hsub :=
    depth_range_subset_prefix a B hd (d + q) (by omega)
  change approx (n + 1) X =
    approx (n + 1) (splice a B (d + q) hsub)
  apply approx_succ_eq_of_prefix_last
  · calc
      approx n X = a := hX.2
      _ = approx n (splice a B (d + q) hsub) :=
        (approx_splice a B (d + q) hsub).symm
  · calc
      X n = homogeneousTail B d p hp t := ht.symm
      _ = B (d + Nat.nth p (t - d)) :=
        homogeneousTail_apply_ge B d p hp hdt
      _ = B (d + q) := rfl
      _ = splice a B (d + q) hsub n := by
        symm
        simpa using
          (splice_apply_ge a B (d + q) hsub (k := n) (le_rfl : n ≤ n))

/-- Todorčević A.4 for the classical Ellentuck space. -/
theorem pigeonhole {n : ℕ} (a : Approx n) (B : Point) {d : ℕ}
    (hd : finitization.HasDepth a B d)
    (O : Set (Approx (n + 1))) :
    ∃ A, A ∈ S.levelNeighborhood d B ∧
      (S.oneStepApproximations a A ⊆ O ∨
        Disjoint (S.oneStepApproximations a A) O) := by
  classical
  let color : ℕ → Bool := fun q =>
    if candidate a B hd q ∈ O then true else false
  obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber color
  let p : ℕ → Prop := fun q => color q = c
  have hp : (Set.ofPred p).Infinite := by
    rw [← Set.infinite_coe_iff]
    simpa [p, Set.preimage, Set.mem_singleton_iff] using hc
  let A : Point := homogeneousTail B d p hp
  refine ⟨A, ?_, ?_⟩
  · exact homogeneousTail_mem_levelNeighborhood B d p hp
  · cases c with
    | false =>
        apply Or.inr
        apply Set.disjoint_left.mpr
        intro b hb hbO
        rcases oneStep_eq_candidate a B hd p hp hb with ⟨q, hpq, rfl⟩
        have hcolor : color q = false := hpq
        simpa [color, hbO] using hcolor
    | true =>
        apply Or.inl
        intro b hb
        rcases oneStep_eq_candidate a B hd p hp hb with ⟨q, hpq, rfl⟩
        have hcolor : color q = true := hpq
        by_contra hnot
        simpa [color, hnot] using hcolor

end Ellentuck
end Examples
end RamseySpace
