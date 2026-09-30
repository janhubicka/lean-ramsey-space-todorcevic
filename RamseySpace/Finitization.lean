import RamseySpace.Basic

/-!
# Finitization and depth

This file formalizes Todorčević's axiom A.2 and the depth of a finite
approximation inside an infinite object.
-/

namespace RamseySpace

universe u v

/-- Todorčević's finitization axiom A.2. -/
structure Finitization (S : ApproximationSystem.{u, v}) where
  leFin : S.FiniteApprox → S.FiniteApprox → Prop
  leFin_refl : ∀ a, leFin a a
  leFin_trans : ∀ {a b c}, leFin a b → leFin b c → leFin a c
  lowerFinite : ∀ b, Set.Finite {a | leFin a b}
  realizesOrder :
    ∀ X Y, S.le X Y ↔
      ∀ n, ∃ m, leFin (S.finiteApprox n X) (S.finiteApprox m Y)
  prefix_leFin :
    ∀ {n m k : ℕ} {a : S.Approx n} {b : S.Approx m} {c : S.Approx k},
      S.IsInitial a b →
      leFin ⟨m, b⟩ ⟨k, c⟩ →
      ∃ (j : ℕ) (d : S.Approx j), S.IsInitial d c ∧ leFin ⟨n, a⟩ ⟨j, d⟩

namespace Finitization

variable {S : ApproximationSystem.{u, v}} (F : Finitization S)

/-- d is the least level of B above the finite approximation a. -/
def HasDepth {n : ℕ} (a : S.Approx n) (B : S.Point) (d : ℕ) : Prop :=
  F.leFin ⟨n, a⟩ (S.finiteApprox d B) ∧
    ∀ e, e < d → ¬ F.leFin ⟨n, a⟩ (S.finiteApprox e B)

/-- Finite approximations whose depth in B is exactly d. -/
def depthApproximations (B : S.Point) (d : ℕ) : Set S.FiniteApprox :=
  {a | F.leFin a (S.finiteApprox d B) ∧
    ∀ e, e < d → ¬ F.leFin a (S.finiteApprox e B)}

@[simp] theorem mem_depthApproximations {n d : ℕ} {a : S.Approx n} {B : S.Point} :
    (⟨n, a⟩ : S.FiniteApprox) ∈ F.depthApproximations B d ↔
      F.HasDepth a B d :=
  Iff.rfl

theorem depthApproximations_finite (B : S.Point) (d : ℕ) :
    (F.depthApproximations B d).Finite :=
  (F.lowerFinite (S.finiteApprox d B)).subset fun _ ha => ha.1

theorem hasDepth_unique {n : ℕ} {a : S.Approx n} {B : S.Point} {d e : ℕ}
    (hd : F.HasDepth a B d) (he : F.HasDepth a B e) :
    d = e := by
  apply le_antisymm
  · by_contra h
    have hed : e < d := lt_of_not_ge h
    exact (hd.2 e hed) he.1
  · by_contra h
    have hde : d < e := lt_of_not_ge h
    exact (he.2 d hde) hd.1

theorem exists_hasDepth_iff {n : ℕ} (a : S.Approx n) (B : S.Point) :
    (∃ d, F.HasDepth a B d) ↔
      ∃ d, F.leFin ⟨n, a⟩ (S.finiteApprox d B) := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, hd.1⟩
  · intro h
    classical
    let d := Nat.find h
    refine ⟨d, Nat.find_spec h, ?_⟩
    intro e he
    exact Nat.find_min h he

theorem exists_hasDepth_of_mem_neighborhood {n : ℕ} {a : S.Approx n}
    {A B : S.Point} (hA : A ∈ S.neighborhood a B) :
    ∃ d, F.HasDepth a B d := by
  rw [F.exists_hasDepth_iff]
  rcases (F.realizesOrder A B).1 hA.1 n with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  simpa [ApproximationSystem.finiteApprox, hA.2] using hm

theorem hasDepth_iff_of_mem_levelNeighborhood {n d : ℕ}
    {a : S.Approx n} {X B : S.Point}
    (hX : X ∈ S.levelNeighborhood d B) :
    F.HasDepth a X d ↔ F.HasDepth a B d := by
  constructor
  · rintro ⟨hmain, hmin⟩
    constructor
    · simpa [ApproximationSystem.finiteApprox, hX.2] using hmain
    · intro e he
      have hpref : S.approx e X = S.approx e B :=
        S.approx_eq_of_mem_levelNeighborhood hX (Nat.le_of_lt he)
      simpa [ApproximationSystem.finiteApprox, hpref] using hmin e he
  · rintro ⟨hmain, hmin⟩
    constructor
    · simpa [ApproximationSystem.finiteApprox, hX.2] using hmain
    · intro e he
      have hpref : S.approx e X = S.approx e B :=
        S.approx_eq_of_mem_levelNeighborhood hX (Nat.le_of_lt he)
      simpa [ApproximationSystem.finiteApprox, hpref] using hmin e he

theorem hasDepth_le_of_initial {n m da db : ℕ}
    {a : S.Approx n} {b : S.Approx m} {Y : S.Point}
    (hab : S.IsInitial a b)
    (hda : F.HasDepth a Y da) (hdb : F.HasDepth b Y db) :
    da ≤ db := by
  rcases F.prefix_leFin hab hdb.1 with ⟨j, c, hc, hac⟩
  have hcEq : c = S.approx j Y :=
    S.isInitial_left_eq_of_right_point hc
  have haFin : F.leFin ⟨n, a⟩ (S.finiteApprox j Y) := by
    simpa [ApproximationSystem.finiteApprox, hcEq] using hac
  exact (F.hasDepth_le_of_leFin hda haFin).trans hc.1

theorem hasDepth_le_of_leFin {n : ℕ} {a : S.Approx n} {B : S.Point}
    {d e : ℕ} (hd : F.HasDepth a B d)
    (he : F.leFin ⟨n, a⟩ (S.finiteApprox e B)) :
    d ≤ e := by
  by_contra h
  have hed : e < d := lt_of_not_ge h
  exact (hd.2 e hed) he

end Finitization

end RamseySpace
