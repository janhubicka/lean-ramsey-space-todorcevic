import Mathlib

/-!
# Approximation systems for abstract Ramsey spaces

Finite approximations are indexed by their level. Thus the part of
Todorčević's A.1 saying that equal approximations have the same level is
represented by the type system rather than reproved as a proposition.
-/

namespace RamseySpace

universe u v

/-- The A.1 data of an abstract Ramsey space, together with a quasi-order on
infinite objects. Every element of `Approx n` is required to occur as an
actual nth approximation. -/
structure ApproximationSystem where
  Point : Type u
  Approx : ℕ → Type v
  le : Point → Point → Prop
  le_refl : ∀ X, le X X
  le_trans : ∀ {X Y Z}, le X Y → le Y Z → le X Z
  approx : (n : ℕ) → Point → Approx n
  approx_surjective : ∀ n, Function.Surjective (approx n)
  empty : Approx 0
  approx_zero : ∀ X, approx 0 X = empty
  separated : ∀ {X Y}, (∀ n, approx n X = approx n Y) → X = Y
  coherent :
    ∀ {X Y n}, approx n X = approx n Y →
      ∀ m, m < n → approx m X = approx m Y

namespace ApproximationSystem

variable (S : ApproximationSystem)

/-- A finite approximation with its level retained. -/
abbrev FiniteApprox := Σ n, S.Approx n

/-- Package the nth approximation of X as a finite approximation. -/
def finiteApprox (n : ℕ) (X : S.Point) : S.FiniteApprox :=
  ⟨n, S.approx n X⟩

/-- The initial-segment relation on level-indexed finite approximations. -/
def IsInitial {n m : ℕ} (a : S.Approx n) (b : S.Approx m) : Prop :=
  n ≤ m ∧ ∃ X, S.approx n X = a ∧ S.approx m X = b

theorem isInitial_refl {n : ℕ} (a : S.Approx n) :
    S.IsInitial a a := by
  refine ⟨le_rfl, ?_⟩
  rcases S.approx_surjective n a with ⟨X, hX⟩
  exact ⟨X, hX, hX⟩

theorem isInitial_of_point {n m : ℕ} (h : n ≤ m) (X : S.Point) :
    S.IsInitial (S.approx n X) (S.approx m X) :=
  ⟨h, X, rfl, rfl⟩

/-- The basic neighborhood [a,B]. -/
def neighborhood {n : ℕ} (a : S.Approx n) (B : S.Point) : Set S.Point :=
  {X | S.le X B ∧ S.approx n X = a}

/-- The depth-n neighborhood [n,B] = [r_n(B),B]. -/
def levelNeighborhood (n : ℕ) (B : S.Point) : Set S.Point :=
  S.neighborhood (S.approx n B) B

/-- The set of one-step extensions r_(n+1)[a,B]. -/
def oneStepApproximations {n : ℕ} (a : S.Approx n) (B : S.Point) :
    Set (S.Approx (n + 1)) :=
  {b | ∃ X, X ∈ S.neighborhood a B ∧ S.approx (n + 1) X = b}

@[simp] theorem mem_neighborhood {n : ℕ} {a : S.Approx n} {B X : S.Point} :
    X ∈ S.neighborhood a B ↔ S.le X B ∧ S.approx n X = a :=
  Iff.rfl

@[simp] theorem mem_levelNeighborhood {n : ℕ} {B X : S.Point} :
    X ∈ S.levelNeighborhood n B ↔
      S.le X B ∧ S.approx n X = S.approx n B :=
  Iff.rfl

theorem self_mem_levelNeighborhood (n : ℕ) (B : S.Point) :
    B ∈ S.levelNeighborhood n B :=
  ⟨S.le_refl B, rfl⟩

theorem approx_eq_of_mem_levelNeighborhood {d : ℕ} {X B : S.Point}
    (hX : X ∈ S.levelNeighborhood d B) {e : ℕ} (he : e ≤ d) :
    S.approx e X = S.approx e B := by
  by_cases hed : e = d
  · subst e
    exact hX.2
  · exact S.coherent hX.2 e (by omega)

theorem neighborhood_mono {n : ℕ} {a : S.Approx n} {A B : S.Point}
    (hAB : S.le A B) :
    S.neighborhood a A ⊆ S.neighborhood a B := by
  intro X hX
  exact ⟨S.le_trans hX.1 hAB, hX.2⟩

theorem levelNeighborhood_mono {n : ℕ} {A B : S.Point}
    (hA : A ∈ S.levelNeighborhood n B) :
    S.levelNeighborhood n A ⊆ S.levelNeighborhood n B := by
  intro X hX
  exact ⟨S.le_trans hX.1 hA.1, hX.2.trans hA.2⟩

theorem oneStepApproximations_mono {n : ℕ} {a : S.Approx n} {A B : S.Point}
    (hAB : S.le A B) :
    S.oneStepApproximations a A ⊆ S.oneStepApproximations a B := by
  intro b hb
  rcases hb with ⟨X, hXA, hXb⟩
  exact ⟨X, S.neighborhood_mono hAB hXA, hXb⟩

/-- A one-step extension determines a smaller basic neighborhood. -/
theorem neighborhood_oneStep_subset {n : ℕ} {a : S.Approx n} {B : S.Point}
    {b : S.Approx (n + 1)} (hb : b ∈ S.oneStepApproximations a B) :
    S.neighborhood b B ⊆ S.neighborhood a B := by
  rcases hb with ⟨X, hXB, hXb⟩
  intro Y hY
  refine ⟨hY.1, ?_⟩
  have htop : S.approx (n + 1) Y = S.approx (n + 1) X :=
    hY.2.trans hXb.symm
  have hpref : S.approx n Y = S.approx n X :=
    S.coherent htop n (Nat.lt_succ_self n)
  exact hpref.trans hXB.2

end ApproximationSystem

end RamseySpace
