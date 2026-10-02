import RamseySpace.Basic

/-!
# Two-sorted abstract Ramsey systems

This is the data underlying Todorčević's Abstract Ramsey Theorem:
`(R, S, ≤, ≤⁰, r, s)`.

The object side `R` only needs its approximation sequence.  The reduction
side `S` also carries its quasi-order, so we reuse `ApproximationSystem`.
-/

namespace RamseySpace
namespace TwoSorted

universe uR vR uS vS

/-- A.1--A.3 approximation data, without an order on the underlying objects. -/
structure ApproximationSequence where
  Point : Type uR
  Approx : ℕ → Type vR
  approx : (n : ℕ) → Point → Approx n
  approx_surjective : ∀ n, Function.Surjective (approx n)
  empty : Approx 0
  approx_zero : ∀ X, approx 0 X = empty
  separated : ∀ {X Y}, (∀ n, approx n X = approx n Y) → X = Y
  coherent :
    ∀ {X Y n}, approx n X = approx n Y →
      ∀ m, m < n → approx m X = approx m Y

namespace ApproximationSequence

variable (R : ApproximationSequence.{uR, vR})

abbrev FiniteApprox := Σ n, R.Approx n

def finiteApprox (n : ℕ) (X : R.Point) : R.FiniteApprox :=
  ⟨n, R.approx n X⟩

/-- End-extension / initial-segment relation on object approximations. -/
def IsInitial {n m : ℕ} (a : R.Approx n) (b : R.Approx m) : Prop :=
  n ≤ m ∧ ∃ X, R.approx n X = a ∧ R.approx m X = b

theorem isInitial_refl {n : ℕ} (a : R.Approx n) :
    R.IsInitial a a := by
  refine ⟨le_rfl, ?_⟩
  rcases R.approx_surjective n a with ⟨X, hX⟩
  exact ⟨X, hX, hX⟩

theorem isInitial_of_point {n m : ℕ} (h : n ≤ m) (X : R.Point) :
    R.IsInitial (R.approx n X) (R.approx m X) :=
  ⟨h, X, rfl, rfl⟩

theorem isInitial_eq_sameLevel {n : ℕ}
    {a b : R.Approx n} (h : R.IsInitial a b) :
    a = b := by
  rcases h with ⟨_, X, hXa, hXb⟩
  exact hXa.symm.trans hXb

end ApproximationSequence

/-- The two infinite sorts and the cross reduction relation A ≤⁰ X. -/
structure System where
  Obj : ApproximationSequence.{uR, vR}
  Red : ApproximationSystem.{uS, vS}
  le0 : Obj.Point → Red.Point → Prop

namespace System

variable (P : System.{uR, vR, uS, vS})

/-- Basic object neighborhood [a,Y]. -/
def objectNeighborhood {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point) :
    Set P.Obj.Point :=
  {A | P.le0 A Y ∧ P.Obj.approx n A = a}

/-- The reduction neighborhood [x,Y]. -/
def reductionNeighborhood {n : ℕ} (x : P.Red.Approx n) (Y : P.Red.Point) :
    Set P.Red.Point :=
  P.Red.neighborhood x Y

/-- Level neighborhood [n,Y] on the reduction sort. -/
def levelNeighborhood (n : ℕ) (Y : P.Red.Point) : Set P.Red.Point :=
  P.Red.levelNeighborhood n Y

/-- One-step object approximations r_(n+1)[a,Y]. -/
def oneStepObjectApproximations {n : ℕ}
    (a : P.Obj.Approx n) (Y : P.Red.Point) :
    Set (P.Obj.Approx (n + 1)) :=
  {b | ∃ A, A ∈ P.objectNeighborhood a Y ∧ P.Obj.approx (n + 1) A = b}

@[simp] theorem mem_objectNeighborhood {n : ℕ}
    {a : P.Obj.Approx n} {Y : P.Red.Point} {A : P.Obj.Point} :
    A ∈ P.objectNeighborhood a Y ↔
      P.le0 A Y ∧ P.Obj.approx n A = a :=
  Iff.rfl

@[simp] theorem mem_levelNeighborhood {n : ℕ}
    {Y X : P.Red.Point} :
    X ∈ P.levelNeighborhood n Y ↔
      P.Red.le X Y ∧ P.Red.approx n X = P.Red.approx n Y :=
  Iff.rfl

theorem self_mem_levelNeighborhood (n : ℕ) (Y : P.Red.Point) :
    Y ∈ P.levelNeighborhood n Y :=
  P.Red.self_mem_levelNeighborhood n Y

theorem levelNeighborhood_mono {n : ℕ} {X Y : P.Red.Point}
    (hX : X ∈ P.levelNeighborhood n Y) :
    P.levelNeighborhood n X ⊆ P.levelNeighborhood n Y :=
  P.Red.levelNeighborhood_mono hX

theorem isInitial_oneStep {n : ℕ} {a : P.Obj.Approx n}
    {Y : P.Red.Point} {b : P.Obj.Approx (n + 1)}
    (hb : b ∈ P.oneStepObjectApproximations a Y) :
    P.Obj.IsInitial a b := by
  rcases hb with ⟨A, hA, hAb⟩
  exact ⟨Nat.le_succ n, A, hA.2, hAb⟩

theorem objectNeighborhood_initial_subset {n m : ℕ}
    {a : P.Obj.Approx n} {b : P.Obj.Approx m} {Y : P.Red.Point}
    (hab : P.Obj.IsInitial a b) :
    P.objectNeighborhood b Y ⊆ P.objectNeighborhood a Y := by
  rcases hab with ⟨hnm, W, hWa, hWb⟩
  intro A hA
  refine ⟨hA.1, ?_⟩
  have htop : P.Obj.approx m W = P.Obj.approx m A :=
    hWb.trans hA.2.symm
  have hpref : P.Obj.approx n W = P.Obj.approx n A := by
    by_cases hnm' : n = m
    · subst m
      exact htop
    · exact P.Obj.coherent htop n (by omega)
  exact hpref.symm.trans hWa

theorem objectNeighborhood_oneStep_subset {n : ℕ}
    {a : P.Obj.Approx n} {Y : P.Red.Point}
    {b : P.Obj.Approx (n + 1)}
    (hb : b ∈ P.oneStepObjectApproximations a Y) :
    P.objectNeighborhood b Y ⊆ P.objectNeighborhood a Y := by
  rcases hb with ⟨A, hA, hAb⟩
  intro B hB
  refine ⟨hB.1, ?_⟩
  have htop :
      P.Obj.approx (n + 1) B = P.Obj.approx (n + 1) A :=
    hB.2.trans hAb.symm
  have hpref : P.Obj.approx n B = P.Obj.approx n A :=
    P.Obj.coherent htop n (Nat.lt_succ_self n)
  exact hpref.trans hA.2

end System

end TwoSorted
end RamseySpace
