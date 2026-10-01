import RamseySpace.Examples.EllentuckBasic

/-!
# The classical Ellentuck space: finitization

For finite approximations a,b we use the standard Ellentuck finitization

  a ≤fin b  iff  range(a) ⊆ range(b).

This file verifies all parts of Todorčević's A.2.
-/

namespace RamseySpace
namespace Examples
namespace Ellentuck

abbrev S := approximationSystem

/-- The underlying finite set of a tagged finite approximation. -/
def finiteRange (q : S.FiniteApprox) : Set ℕ :=
  match q with
  | ⟨_, a⟩ => Set.range a.1

/-- Standard Ellentuck finitization: finite-set inclusion. -/
def leFin (a b : S.FiniteApprox) : Prop :=
  finiteRange a ⊆ finiteRange b

theorem finiteRange_finite (q : S.FiniteApprox) :
    (finiteRange q).Finite := by
  rcases q with ⟨n, a⟩
  exact Set.finite_range a.1

theorem finiteRange_ncard (q : S.FiniteApprox) :
    (finiteRange q).ncard = q.1 := by
  rcases q with ⟨n, a⟩
  change (Set.range a.1).ncard = n
  rw [Set.ncard_range_of_injective a.1.injective, Nat.card_fin]

theorem finiteRange_injective :
    Function.Injective finiteRange := by
  rintro ⟨n, a⟩ ⟨m, b⟩ h
  have hnm : n = m := by
    have hc := congrArg Set.ncard h
    simpa [finiteRange_ncard] using hc
  subst m
  change Set.range a.1 = Set.range b.1 at h
  have hab : a.1 = b.1 :=
    OrderEmbedding.eq_of_range_eq h
  have hab' : a = b := Subtype.ext hab
  subst b
  rfl

theorem leFin_refl (a : S.FiniteApprox) :
    leFin a a :=
  fun _ h => h

theorem leFin_trans {a b c : S.FiniteApprox} :
    leFin a b → leFin b c → leFin a c :=
  fun hab hbc _ ha => hbc (hab ha)

/-- There are only finitely many finite approximations below a fixed one. -/
theorem lowerFinite (b : S.FiniteApprox) :
    Set.Finite {a | leFin a b} := by
  refine Set.Finite.of_finite_image ?_ finiteRange_injective.injOn
  apply (finiteRange_finite b).finite_subsets.subset
  rintro s ⟨a, ha, rfl⟩
  exact ha

/-- Ranges of initial approximations are monotone in the level. -/
theorem prefixRange_mono (X : Point) {n m : ℕ} (hnm : n ≤ m) :
    finiteRange (S.finiteApprox n X) ⊆
      finiteRange (S.finiteApprox m X) := by
  intro x hx
  change x ∈ Set.range (approx n X).1 at hx
  rcases hx with ⟨i, hi⟩
  let j : Fin m := ⟨i.1, lt_of_lt_of_le i.2 hnm⟩
  change x ∈ Set.range (approx m X).1
  refine ⟨j, ?_⟩
  change X j.1 = x
  change X i.1 = x at hi
  exact hi

theorem value_mem_prefix (X : Point) (j : ℕ) :
    X j ∈ finiteRange (S.finiteApprox (j + 1) X) := by
  change X j ∈ Set.range (approx (j + 1) X).1
  refine ⟨⟨j, Nat.lt_succ_self j⟩, ?_⟩
  rfl

/-- Every finite subset of the range of X is contained in some initial
approximation of X. -/
theorem finite_subset_prefix (X : Point) {t : Set ℕ}
    (ht : t.Finite) (hsub : t ⊆ Set.range X) :
    ∃ m, t ⊆ finiteRange (S.finiteApprox m X) := by
  induction t, ht using Set.Finite.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert x t hxt ht ih =>
      have hsubt : t ⊆ Set.range X := by
        intro y hy
        exact hsub (Set.mem_insert_of_mem x hy)
      rcases ih hsubt with ⟨m, hm⟩
      rcases hsub (Set.mem_insert x t) with ⟨j, hj⟩
      let M := max m (j + 1)
      refine ⟨M, ?_⟩
      intro y hy
      rcases Set.mem_insert_iff.mp hy with rfl | hy
      · apply prefixRange_mono X (Nat.le_max_right m (j + 1))
        rw [← hj]
        exact value_mem_prefix X j
      · exact prefixRange_mono X (Nat.le_max_left m (j + 1)) (hm hy)

/-- Recover the infinite reduction order from finite approximations. -/
theorem realizesOrder (X Y : Point) :
    le X Y ↔
      ∀ n, ∃ m,
        leFin (S.finiteApprox n X) (S.finiteApprox m Y) := by
  constructor
  · intro hXY n
    have hfin :
        (finiteRange (S.finiteApprox n X)).Finite :=
      finiteRange_finite _
    have hsub :
        finiteRange (S.finiteApprox n X) ⊆ Set.range Y := by
      intro x hx
      change x ∈ Set.range (approx n X).1 at hx
      rcases hx with ⟨i, hi⟩
      apply hXY
      refine ⟨i.1, ?_⟩
      change X i.1 = x at hi
      exact hi
    rcases finite_subset_prefix Y hfin hsub with ⟨m, hm⟩
    exact ⟨m, hm⟩
  · intro hfin
    intro x hx
    rcases hx with ⟨i, rfl⟩
    rcases hfin (i + 1) with ⟨m, hm⟩
    have hi :
        X i ∈ finiteRange (S.finiteApprox (i + 1) X) :=
      value_mem_prefix X i
    have hYi := hm hi
    change X i ∈ Set.range (approx m Y).1 at hYi
    rcases hYi with ⟨j, hj⟩
    refine ⟨j.1, ?_⟩
    change Y j.1 = X i at hj
    exact hj

/-- An initial approximation has its range included in the larger one. -/
theorem finiteRange_subset_of_isInitial {n m : ℕ}
    {a : S.Approx n} {b : S.Approx m}
    (hab : S.IsInitial a b) :
    finiteRange ⟨n, a⟩ ⊆ finiteRange ⟨m, b⟩ := by
  rcases hab with ⟨hnm, X, hXa, hXb⟩
  have hfa : S.finiteApprox n X = ⟨n, a⟩ := by
    exact Sigma.ext rfl (heq_of_eq hXa)
  have hfb : S.finiteApprox m X = ⟨m, b⟩ := by
    exact Sigma.ext rfl (heq_of_eq hXb)
  rw [← hfa, ← hfb]
  exact prefixRange_mono X hnm

/-- A.2(3) for finite-set inclusion. -/
theorem prefix_leFin
    {n m k : ℕ} {a : S.Approx n} {b : S.Approx m} {c : S.Approx k}
    (hab : S.IsInitial a b)
    (hbc : leFin ⟨m, b⟩ ⟨k, c⟩) :
    ∃ (j : ℕ) (d : S.Approx j),
      S.IsInitial d c ∧ leFin ⟨n, a⟩ ⟨j, d⟩ := by
  refine ⟨k, c, S.isInitial_refl c, ?_⟩
  exact leFin_trans (finiteRange_subset_of_isInitial hab) hbc

/-- A.2 for the classical Ellentuck space. -/
def finitization : Finitization S where
  leFin := leFin
  leFin_refl := leFin_refl
  leFin_trans := leFin_trans
  lowerFinite := lowerFinite
  realizesOrder := realizesOrder
  prefix_leFin := prefix_leFin

end Ellentuck
end Examples
end RamseySpace
