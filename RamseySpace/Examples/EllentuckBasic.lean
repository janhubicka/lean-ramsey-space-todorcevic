import RamseySpace.Standard

/-!
# The classical Ellentuck space: approximation system

We present an infinite subset of ℕ by its unique increasing enumeration,
i.e. by an order embedding ℕ ↪o ℕ. Finite approximations are exactly the
finite restrictions which are realized by such an enumeration.

This file establishes A.1. Later files add A.2--A.4.
-/

namespace RamseySpace
namespace Examples
namespace Ellentuck

/-- Infinite subsets of ℕ, represented by increasing enumerations. -/
abbrev Point := ℕ ↪o ℕ

/-- Realized increasing approximations of length n. -/
def Approx (n : ℕ) :=
  {a : Fin n ↪o ℕ // ∃ X : Point, ∀ i : Fin n, X i.1 = a i}

/-- The identity enumeration, used only to name the unique length-zero
approximation. -/
def identityPoint : Point :=
  OrderEmbedding.ofStrictMono id strictMono_id

/-- Restrict an infinite increasing enumeration to its first n values. -/
def approx (n : ℕ) (X : Point) : Approx n :=
  ⟨OrderEmbedding.ofStrictMono (fun i : Fin n => X i.1) (by
      intro i j hij
      exact X.strictMono (by simpa using hij)),
    ⟨X, fun _ => rfl⟩⟩

/-- Ellentuck reduction is inclusion of the enumerated ranges. -/
def le (X Y : Point) : Prop :=
  Set.range X ⊆ Set.range Y

theorem le_refl (X : Point) : le X X :=
  fun _ h => h

theorem le_trans {X Y Z : Point} :
    le X Y → le Y Z → le X Z :=
  fun hXY hYZ _ hx => hYZ (hXY hx)

theorem approx_surjective (n : ℕ) :
    Function.Surjective (approx n) := by
  intro a
  rcases a.2 with ⟨X, hX⟩
  refine ⟨X, ?_⟩
  apply Subtype.ext
  apply DFunLike.ext _ _
  intro i
  change X i.1 = a.1 i
  exact hX i

def empty : Approx 0 :=
  approx 0 identityPoint

theorem approx_zero (X : Point) :
    approx 0 X = empty := by
  apply Subtype.ext
  apply DFunLike.ext _ _
  intro i
  exact Fin.elim0 i

theorem separated {X Y : Point}
    (h : ∀ n, approx n X = approx n Y) :
    X = Y := by
  apply DFunLike.ext _ _
  intro k
  let i : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  have hk := congrArg
    (fun a : Approx (k + 1) => a.1 i)
    (h (k + 1))
  change X k = Y k
  change X i.1 = Y i.1 at hk
  exact hk

theorem coherent {X Y : Point} {n : ℕ}
    (h : approx n X = approx n Y) :
    ∀ m, m < n → approx m X = approx m Y := by
  intro m hmn
  apply Subtype.ext
  apply DFunLike.ext _ _
  intro i
  let j : Fin n := ⟨i.1, lt_trans i.2 hmn⟩
  have hj := congrArg
    (fun a : Approx n => a.1 j) h
  change X i.1 = Y i.1
  change X j.1 = Y j.1 at hj
  exact hj

/-- A.1 for the classical Ellentuck space. -/
def approximationSystem : ApproximationSystem where
  Point := Point
  Approx := Approx
  le := le
  le_refl := le_refl
  le_trans := le_trans
  approx := approx
  approx_surjective := approx_surjective
  empty := empty
  approx_zero := approx_zero
  separated := separated
  coherent := coherent

end Ellentuck
end Examples
end RamseySpace
