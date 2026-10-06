import RamseySpace.TwoSorted.Basic
import RamseySpace.Finitization

/-!
# A.4 finitization for two-sorted Ramsey systems
-/

namespace RamseySpace
namespace TwoSorted

universe uR vR uS vS

/-- The reduction-side part of Todorčević's two-sorted A.4.

Unlike the one-sorted Chapter 5 finitization axiom, Chapter 4 does not assume
that `≤fin` is itself a quasi-order, nor does it impose a separate
initial-segment compatibility axiom on reduction approximations.  It requires
only finite lower cones and recovery of the infinite reduction order. -/
structure ReductionFinitization
    (S : ApproximationSystem.{uS, vS}) where
  leFin : S.FiniteApprox → S.FiniteApprox → Prop
  lowerFinite : ∀ x, Set.Finite {y | leFin y x}
  realizesOrder :
    ∀ X Y, S.le X Y ↔
      ∀ n, ∃ m, leFin (S.finiteApprox n X) (S.finiteApprox m Y)

/-- Todorčević A.4 for `(R,S,≤,≤⁰,r,s)`.

`redFin` is exactly the reduction-side `≤fin` data required by A.4;
`leFin0` is the cross finite relation `≤⁰fin`. -/
structure Finitization (P : System.{uR, vR, uS, vS}) where
  redFin : ReductionFinitization P.Red
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
  rcases (Finitization.realizesOrder0 F A Y).1 hA.1 n with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  simpa [ApproximationSequence.finiteApprox, hA.2] using hm

/-- The cross order is monotone in the reduction coordinate. -/
theorem le0_trans (F : Finitization P) {A : P.Obj.Point} {X Y : P.Red.Point}
    (hAX : P.le0 A X) (hXY : P.Red.le X Y) :
    P.le0 A Y := by
  apply (Finitization.realizesOrder0 F A Y).2
  intro n
  rcases (Finitization.realizesOrder0 F A X).1 hAX n with ⟨m, hm⟩
  rcases ((Finitization.redFin F).realizesOrder X Y).1 hXY m with ⟨k, hk⟩
  exact ⟨k, Finitization.trans0 F hm hk⟩

theorem objectNeighborhood_mono (F : Finitization P)
    {n : ℕ} {a : P.Obj.Approx n}
    {X Y : P.Red.Point} (hXY : P.Red.le X Y) :
    P.objectNeighborhood a X ⊆ P.objectNeighborhood a Y := by
  intro A hA
  exact ⟨le0_trans F hA.1 hXY, hA.2⟩

theorem oneStepObjectApproximations_mono (F : Finitization P) {n : ℕ}
    {a : P.Obj.Approx n} {X Y : P.Red.Point}
    (hXY : P.Red.le X Y) :
    P.oneStepObjectApproximations a X ⊆
      P.oneStepObjectApproximations a Y := by
  rintro b ⟨A, hA, hAb⟩
  exact ⟨A, objectNeighborhood_mono F hXY hA, hAb⟩

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
  rcases Finitization.prefix0 F hab hdb.1 with ⟨j, y, hy, hay⟩
  have hyeq : y = P.Red.approx j Y :=
    P.Red.isInitial_left_eq_of_right_point hy
  have haFin :
      F.leFin0 ⟨n, a⟩ (P.Red.finiteApprox j Y) := by
    simpa [ApproximationSystem.finiteApprox, hyeq] using hay
  have hjdb : j ≤ db := hy.1
  by_contra h
  have hdbda : db < da := lt_of_not_ge h
  exact (hda.2 j (lt_of_le_of_lt hjdb hdbda)) haFin


/-- Along a cross reduction A ≤⁰ Y, depths of longer object approximations
are unbounded in Y.  This is the two-sorted form of the depth-growth fact
used in Todorčević's countable-union and Souslin arguments. -/
theorem exists_hasDepth_ge_of_le0 {A : P.Obj.Point} {Y : P.Red.Point}
    (hAY : P.le0 A Y) (L N : ℕ) :
    ∃ l d, L ≤ l ∧ N ≤ d ∧ F.HasDepth (P.Obj.approx l A) Y d := by
  classical
  by_contra h
  have hbad :
      ∀ l, L ≤ l →
        ∀ d, F.HasDepth (P.Obj.approx l A) Y d → d < N := by
    intro l hl d hd
    by_contra hdn
    have hNd : N ≤ d := le_of_not_gt hdn
    exact h ⟨l, d, hl, hNd, hd⟩

  let q : ℕ → P.Obj.FiniteApprox :=
    fun t => P.Obj.finiteApprox (L + t) A
  let T : Set P.Obj.FiniteApprox :=
    ⋃ d : Fin N, {p | F.leFin0 p (P.Red.finiteApprox d.1 Y)}

  have hTfin : T.Finite := by
    dsimp [T]
    exact Set.finite_iUnion
      (fun d : Fin N => F.lowerFinite0 (P.Red.finiteApprox d.1 Y))

  have hqinj : Function.Injective q := by
    intro i j hij
    have hfst := congrArg (fun p : P.Obj.FiniteApprox => p.1) hij
    dsimp [q, ApproximationSequence.finiteApprox] at hfst
    omega

  have hqsub : Set.range q ⊆ T := by
    rintro _ ⟨t, rfl⟩
    rcases (F.realizesOrder0 A Y).1 hAY (L + t) with ⟨m, hm⟩
    have hex :
        ∃ d, F.HasDepth (P.Obj.approx (L + t) A) Y d :=
      (F.exists_hasDepth_iff (P.Obj.approx (L + t) A) Y).2 ⟨m, hm⟩
    rcases hex with ⟨d, hd⟩
    have hdN : d < N := hbad (L + t) (by omega) d hd
    refine Set.mem_iUnion.2 ⟨(⟨d, hdN⟩ : Fin N), ?_⟩
    exact hd.1

  exact (Set.infinite_range_of_injective hqinj) (hTfin.subset hqsub)

end Finitization

end TwoSorted
end RamseySpace
