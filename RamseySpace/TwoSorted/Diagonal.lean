import RamseySpace.TwoSorted.AbstractRamsey
import RamseySpace.Baire

/-!
# Diagonal specialization

Todorčević's Abstract Ellentuck Theorem is the one-sort specialization of the
more general Abstract Ramsey Theorem.  This file identifies the two interfaces
when R = S and ≤⁰ = ≤.
-/

namespace RamseySpace
namespace TwoSorted

universe u v

/-- Forget the order from a one-sorted approximation system. -/
def objectSequenceOf (S : ApproximationSystem.{u, v}) :
    ApproximationSequence.{u, v} where
  Point := S.Point
  Approx := S.Approx
  approx := S.approx
  approx_surjective := S.approx_surjective
  empty := S.empty
  approx_zero := S.approx_zero
  separated := S.separated
  coherent := S.coherent

/-- The diagonal two-sorted system associated to a one-sorted Ramsey space. -/
def diagonalSystem (S : ApproximationSystem.{u, v}) :
    System.{u, v, u, v} where
  Obj := objectSequenceOf S
  Red := S
  le0 := S.le

/-- A.2 finitization becomes A.4 finitization on the diagonal. -/
def diagonalFinitization {S : ApproximationSystem.{u, v}}
    (F : RamseySpace.Finitization S) :
    TwoSorted.Finitization (diagonalSystem S) where
  redFin := {
    leFin := F.leFin
    lowerFinite := F.lowerFinite
    realizesOrder := F.realizesOrder
  }
  leFin0 := F.leFin
  lowerFinite0 := F.lowerFinite
  realizesOrder0 := F.realizesOrder
  trans0 := F.leFin_trans
  prefix0 := by
    intro n m k a b x hab hbx
    change S.IsInitial a b at hab
    rcases F.prefix_leFin hab hbx with ⟨j, y, hy, hay⟩
    exact ⟨j, y, hy, hay⟩

/-- A one-sorted A.1--A.4 Ramsey space supplies the two-sorted A.1--A.6
system on the diagonal. -/
def diagonalAbstractRamseySystem
    {S : ApproximationSystem.{u, v}}
    (R : RamseySpace.AbstractRamseySpace S) :
    TwoSorted.AbstractRamseySystem (diagonalSystem S) where
  fin := diagonalFinitization R.fin
  amalgamation_nonempty := by
    intro n a Y d hd X hX
    exact R.amalgamation_nonempty a Y hd hX
  amalgamation_refine := by
    intro n a Y d hd X hXY hne
    exact R.amalgamation_refine a Y hd hXY hne
  pigeonhole := by
    intro n a Y hne d hd O
    exact R.pigeonhole a Y hd O

@[simp] theorem diagonal_objectNeighborhood
    (S : ApproximationSystem.{u, v})
    {n : ℕ} (a : S.Approx n) (Y : S.Point) :
    (diagonalSystem S).objectNeighborhood a Y =
      S.neighborhood a Y :=
  rfl

@[simp] theorem diagonal_levelNeighborhood
    (S : ApproximationSystem.{u, v})
    (n : ℕ) (Y : S.Point) :
    (diagonalSystem S).levelNeighborhood n Y =
      S.levelNeighborhood n Y :=
  rfl

theorem diagonal_hasDepth_iff
    {S : ApproximationSystem.{u, v}}
    (F : RamseySpace.Finitization S)
    {n d : ℕ} {a : S.Approx n} {Y : S.Point} :
    (diagonalFinitization F).HasDepth a Y d ↔
      F.HasDepth a Y d :=
  Iff.rfl

theorem diagonal_isBaire_iff
    {S : ApproximationSystem.{u, v}}
    (target : Set S.Point) :
    TwoSorted.IsBaire (P := diagonalSystem S) target ↔
      RamseySpace.IsAbstractBaire target := by
  rfl

theorem diagonal_isMeagre_iff
    {S : ApproximationSystem.{u, v}}
    (target : Set S.Point) :
    TwoSorted.IsMeagre (P := diagonalSystem S) target ↔
      RamseySpace.IsAbstractMeagre target := by
  rfl

theorem diagonal_isRamsey_iff
    {S : ApproximationSystem.{u, v}}
    (R : RamseySpace.AbstractRamseySpace S)
    (target : Set S.Point) :
    TwoSorted.IsRamsey (diagonalAbstractRamseySystem R) target ↔
      RamseySpace.IsRamsey R target := by
  rfl

theorem diagonal_isRamseyNull_iff
    {S : ApproximationSystem.{u, v}}
    (R : RamseySpace.AbstractRamseySpace S)
    (target : Set S.Point) :
    TwoSorted.IsRamseyNull (diagonalAbstractRamseySystem R) target ↔
      RamseySpace.IsRamseyNull R target := by
  rfl

/-- The combinatorial core of Abstract Ellentuck follows directly by applying
the Abstract Ramsey Theorem to the diagonal system. -/
theorem abstractBaire_iff_isRamsey_via_abstractRamsey
    {S : ApproximationSystem.{u, v}}
    (R : RamseySpace.AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed)
    (target : Set S.Point) :
    RamseySpace.IsAbstractBaire target ↔
      RamseySpace.IsRamsey R target := by
  have h :=
    (TwoSorted.abstractRamsey_iff
      (diagonalAbstractRamseySystem R) hclosed).1 target
  exact (diagonal_isBaire_iff target).symm.trans
    (h.trans (diagonal_isRamsey_iff R target))

/-- Likewise for meagre / Ramsey-null sets. -/
theorem abstractMeagre_iff_isRamseyNull_via_abstractRamsey
    {S : ApproximationSystem.{u, v}}
    (R : RamseySpace.AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed)
    (target : Set S.Point) :
    RamseySpace.IsAbstractMeagre target ↔
      RamseySpace.IsRamseyNull R target := by
  have h :=
    (TwoSorted.abstractRamsey_iff
      (diagonalAbstractRamseySystem R) hclosed).2 target
  exact (diagonal_isMeagre_iff target).symm.trans
    (h.trans (diagonal_isRamseyNull_iff R target))

end TwoSorted
end RamseySpace
