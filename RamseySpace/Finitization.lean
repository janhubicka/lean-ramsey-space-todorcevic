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
  realizesOrder :
    ∀ X Y, S.le X Y ↔
      ∀ n, ∃ m, leFin (S.finiteApprox n X) (S.finiteApprox m Y)
  lowerFinite : ∀ b, Set.Finite {a | leFin a b}

namespace Finitization

variable {S : ApproximationSystem.{u, v}} (F : Finitization S)

/-- d is the least level of B above the finite approximation a. -/
def HasDepth {n : ℕ} (a : S.Approx n) (B : S.Point) (d : ℕ) : Prop :=
  F.leFin ⟨n, a⟩ (S.finiteApprox d B) ∧
    ∀ e, e < d → ¬ F.leFin ⟨n, a⟩ (S.finiteApprox e B)

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

theorem hasDepth_le_of_leFin {n : ℕ} {a : S.Approx n} {B : S.Point}
    {d e : ℕ} (hd : F.HasDepth a B d)
    (he : F.leFin ⟨n, a⟩ (S.finiteApprox e B)) :
    d ≤ e := by
  by_contra h
  have hed : e < d := lt_of_not_ge h
  exact (hd.2 e hed) he

end Finitization

end RamseySpace
