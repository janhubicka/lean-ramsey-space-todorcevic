import RamseySpace.Fusion

/-!
# Metric closedness and fusion

Todorčević identifies a Ramsey space with its approximation codes in a
countable product of discrete approximation spaces. The first-difference
closedness condition is expressed here without committing to a particular
metric construction: a code belongs to the closed image whenever each of its
finite prefixes is realized.

Closedness and A.2 already supply fusion limits. In particular, applications
may use this theorem while proving A.4: no Ramsey-space instance, amalgamation,
or pigeonhole assumption is needed. The old Ramsey-space-facing theorem is
retained as a compatibility wrapper.
-/

namespace RamseySpace

universe u v

namespace ApproximationSystem

variable (S : ApproximationSystem.{u, v})

/-- A full approximation code in the dependent product of the level spaces. -/
abbrev ApproximationCode := ∀ n, S.Approx n

/-- The code of an infinite object. -/
def code (X : S.Point) : S.ApproximationCode :=
  fun n => S.approx n X

/-- The first N levels of a code are realized by some point of the space. -/
def PrefixRealizable (c : S.ApproximationCode) (N : ℕ) : Prop :=
  ∃ X, ∀ n, n ≤ N → S.approx n X = c n

/-- First-difference/product closedness of the image of the approximation map. -/
def IsMetricallyClosed : Prop :=
  ∀ c : S.ApproximationCode,
    (∀ N, S.PrefixRealizable c N) →
      ∃ X, ∀ n, S.approx n X = c n

theorem fusion_le {n0 : ℕ} {Y : ℕ → S.Point}
    (hY : S.IsFusionFrom n0 Y) {i j : ℕ} (hij : i ≤ j) :
    S.le (Y j) (Y i) := by
  induction j, hij using Nat.le_induction with
  | base =>
      exact S.le_refl (Y i)
  | succ j hij ih =>
      exact S.le_trans (hY j).1 ih

theorem fusion_approx_eq {n0 : ℕ} {Y : ℕ → S.Point}
    (hY : S.IsFusionFrom n0 Y) {i j m : ℕ}
    (hij : i ≤ j) (hm : m ≤ n0 + i) :
    S.approx m (Y j) = S.approx m (Y i) := by
  induction j, hij using Nat.le_induction with
  | base =>
      rfl
  | succ j hij ih =>
      have hstep : S.approx m (Y (j + 1)) = S.approx m (Y j) :=
        S.approx_eq_of_mem_levelNeighborhood (hY j) (by omega)
      exact hstep.trans ih

end ApproximationSystem

/-- A.2 and metric closedness imply fusion completeness, independently of
A.3 and A.4. This is the interface to use when fusion is needed to establish
pigeonhole in a new application. -/
theorem Finitization.fusionComplete_of_isMetricallyClosed
    {S : ApproximationSystem.{u, v}} (F : Finitization S)
    (hclosed : S.IsMetricallyClosed) :
    FusionComplete S := by
  refine ⟨?_⟩
  intro n0 Y hY
  let c : S.ApproximationCode := fun n => S.approx n (Y (n + 1))

  have hpref : ∀ N, S.PrefixRealizable c N := by
    intro N
    refine ⟨Y (N + 1), ?_⟩
    intro n hn
    have hstab :
        S.approx n (Y (N + 1)) = S.approx n (Y (n + 1)) :=
      S.fusion_approx_eq hY (by omega) (by omega)
    simpa [c] using hstab

  rcases hclosed c hpref with ⟨X, hXcode⟩
  refine ⟨X, ?_⟩
  intro k
  constructor
  · apply (F.realizesOrder X (Y k)).2
    intro n
    let j : ℕ := max k (n + 1)
    have hkj : k ≤ j := Nat.le_max_left _ _
    have hnj : n + 1 ≤ j := Nat.le_max_right _ _
    have hYjYk : S.le (Y j) (Y k) :=
      S.fusion_le hY hkj
    rcases (F.realizesOrder (Y j) (Y k)).1 hYjYk n with
      ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hstab :
        S.approx n (Y j) = S.approx n (Y (n + 1)) :=
      S.fusion_approx_eq hY hnj (by omega)
    have hXj : S.approx n X = S.approx n (Y j) :=
      (hXcode n).trans hstab.symm
    simpa only [ApproximationSystem.finiteApprox, hXj] using hm
  · have hX :
        S.approx (n0 + k) X =
          S.approx (n0 + k) (Y (n0 + k + 1)) :=
      hXcode (n0 + k)
    have hstab :
        S.approx (n0 + k) (Y (n0 + k + 1)) =
          S.approx (n0 + k) (Y k) :=
      S.fusion_approx_eq hY (by omega) (by omega)
    exact hX.trans hstab

/-- Backwards-compatible Ramsey-space-facing form of fusion completeness.
Only the finitization component of the supplied instance is used. -/
theorem fusionComplete_of_isMetricallyClosed
    {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed) :
    FusionComplete S :=
  R.fin.fusionComplete_of_isMetricallyClosed hclosed

end RamseySpace
