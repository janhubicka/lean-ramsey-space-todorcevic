import RamseySpace.TwoSorted.Basic
import RamseySpace.Finitization

/-!
# A.4 finitization for two-sorted Ramsey systems
-/

namespace RamseySpace
namespace TwoSorted

universe uR vR uS vS

/-- Todorčević A.4 for `(R,S,≤,≤⁰,r,s)`.

The ordinary `Finitization` on `S` supplies `≤fin`; `leFin0` is the
cross finite relation `≤⁰fin`. -/
structure Finitization (P : System.{uR, vR, uS, vS}) where
  redFin : RamseySpace.Finitization P.Red
  leFin0 : P.Obj.FiniteApprox → P.Red.FiniteApprox → Prop
  lowerFinite0 : ∀ x, Set.Finite {a | leFin0 a x}
  realizesOrder0 :
    ∀ A Y, P.le0 A Y ↔
      ∀ n, ∃ m, leFin0 (P.Obj.finiteApprox n A) (P.Red.finiteApprox m Y)
  trans0 :
    ∀ {a x y},
      leFin0 a x → redFin.leFin x y → leFin0 a y
  prefix0 :
    ∀ {n m k : ℕ}
      {a : P.Obj.Approx n} {b : P.Obj.Approx m} {x : P.Red.Approx k},
      P.Obj.IsInitial a b →
      leFin0 ⟨m, b⟩ ⟨k, x⟩ →
      ∃ (j : ℕ) (y : P.Red.Approx j),
        P.Red.IsInitial y x ∧ leFin0 ⟨n, a⟩ ⟨j, y⟩

namespace Finitization

variable {P : System.{uR, vR, uS, vS}} (F : Finitization P)

/-- Cross depth: d is the least reduction level of Y finitizing a. -/
def HasDepth {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point) (d : ℕ) : Prop :=
  F.leFin0 ⟨n, a⟩ (P.Red.finiteApprox d Y) ∧
    ∀ e, e < d → ¬ F.leFin0 ⟨n, a⟩ (P.Red.finiteApprox e Y)

def depthApproximations (Y : P.Red.Point) (d : ℕ) :
    Set P.Obj.FiniteApprox :=
  {a | F.leFin0 a (P.Red.finiteApprox d Y) ∧
    ∀ e, e < d → ¬ F.leFin0 a (P.Red.finiteApprox e Y)}

@[simp] theorem mem_depthApproximations {n d : ℕ}
    {a : P.Obj.Approx n} {Y : P.Red.Point} :
    (⟨n, a⟩ : P.Obj.FiniteApprox) ∈ F.depthApproximations Y d ↔
      F.HasDepth a Y d :=
  Iff.rfl

theorem depthApproximations_finite (Y : P.Red.Point) (d : ℕ) :
    (F.depthApproximations Y d).Finite :=
  (F.lowerFinite0 (P.Red.finiteApprox d Y)).subset fun _ h => h.1

theorem hasDepth_unique {n : ℕ} {a : P.Obj.Approx n}
    {Y : P.Red.Point} {d e : ℕ}
    (hd : F.HasDepth a Y d) (he : F.HasDepth a Y e) :
    d = e := by
  apply le_antisymm
  · by_contra h
    exact (hd.2 e (lt_of_not_ge h)) he.1
  · by_contra h
    exact (he.2 d (lt_of_not_ge h)) hd.1

theorem exists_hasDepth_iff {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point) :
    (∃ d, F.HasDepth a Y d) ↔
      ∃ d, F.leFin0 ⟨n, a⟩ (P.Red.finiteApprox d Y) := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, hd.1⟩
  · intro h
    classical
    let d := Nat.find h
    refine ⟨d, Nat.find_spec h, ?_⟩
    intro e he
    exact Nat.find_min h he

/-- A genuine member of [a,Y] witnesses that a has a finite depth in Y. -/
theorem exists_hasDepth_of_mem_objectNeighborhood {n : ℕ}
    {a : P.Obj.Approx n} {A : P.Obj.Point} {Y : P.Red.Point}
    (hA : A ∈ P.objectNeighborhood a Y) :
    ∃ d, F.HasDepth a Y d := by
  rw [F.exists_hasDepth_iff]
  rcases (F.realizesOrder0 A Y).1 hA.1 n with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  simpa [ApproximationSequence.finiteApprox, hA.2] using hm

/-- The cross order is monotone in the reduction coordinate. -/
theorem le0_trans {A : P.Obj.Point} {X Y : P.Red.Point}
    (hAX : P.le0 A X) (hXY : P.Red.le X Y) :
    P.le0 A Y := by
  apply (F.realizesOrder0 A Y).2
  intro n
  rcases (F.realizesOrder0 A X).1 hAX n with ⟨m, hm⟩
  rcases (F.redFin.realizesOrder X Y).1 hXY m with ⟨k, hk⟩
  exact ⟨k, F.trans0 hm hk⟩

theorem objectNeighborhood_mono {n : ℕ} {a : P.Obj.Approx n}
    {X Y : P.Red.Point} (hXY : P.Red.le X Y) :
    P.objectNeighborhood a X ⊆ P.objectNeighborhood a Y := by
  intro A hA
  exact ⟨F.le0_trans hA.1 hXY, hA.2⟩

theorem oneStepObjectApproximations_mono {n : ℕ}
    {a : P.Obj.Approx n} {X Y : P.Red.Point}
    (hXY : P.Red.le X Y) :
    P.oneStepObjectApproximations a X ⊆
      P.oneStepObjectApproximations a Y := by
  rintro b ⟨A, hA, hAb⟩
  exact ⟨A, F.objectNeighborhood_mono hXY hA, hAb⟩

theorem hasDepth_iff_of_mem_levelNeighborhood {n d : ℕ}
    {a : P.Obj.Approx n} {X Y : P.Red.Point}
    (hX : X ∈ P.levelNeighborhood d Y) :
    F.HasDepth a X d ↔ F.HasDepth a Y d := by
  constructor
  · rintro ⟨hmain, hmin⟩
    constructor
    · simpa [ApproximationSystem.finiteApprox, hX.2] using hmain
    · intro e he
      have hpref : P.Red.approx e X = P.Red.approx e Y :=
        P.Red.approx_eq_of_mem_levelNeighborhood hX (Nat.le_of_lt he)
      simpa [ApproximationSystem.finiteApprox, hpref] using hmin e he
  · rintro ⟨hmain, hmin⟩
    constructor
    · simpa [ApproximationSystem.finiteApprox, hX.2] using hmain
    · intro e he
      have hpref : P.Red.approx e X = P.Red.approx e Y :=
        P.Red.approx_eq_of_mem_levelNeighborhood hX (Nat.le_of_lt he)
      simpa [ApproximationSystem.finiteApprox, hpref] using hmin e he

theorem hasDepth_le_of_initial {n m da db : ℕ}
    {a : P.Obj.Approx n} {b : P.Obj.Approx m} {Y : P.Red.Point}
    (hab : P.Obj.IsInitial a b)
    (hda : F.HasDepth a Y da) (hdb : F.HasDepth b Y db) :
    da ≤ db := by
  rcases F.prefix0 hab hdb.1 with ⟨j, y, hy, hay⟩
  rcases hy with ⟨hjk, X, hXy, hXtop⟩
  have hyeq : y = P.Red.approx j Y := by
    have htop :
        P.Red.approx db X = P.Red.approx db Y :=
      hXtop.trans rfl
    have hpref : P.Red.approx j X = P.Red.approx j Y := by
      by_cases hj : j = db
      · subst db
        exact htop
      · exact P.Red.coherent htop j (by omega)
    exact hXy.symm.trans hpref
  have haFin :
      F.leFin0 ⟨n, a⟩ (P.Red.finiteApprox j Y) := by
    simpa [ApproximationSystem.finiteApprox, hyeq] using hay
  by_contra h
  exact (hda.2 j (by omega)) haFin

end Finitization

end TwoSorted
end RamseySpace
