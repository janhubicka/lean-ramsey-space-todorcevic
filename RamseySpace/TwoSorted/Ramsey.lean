import RamseySpace.TwoSorted.Axioms

/-!
# S-Ramsey, S-Ramsey-null, S-Baire, and S-meagre sets
-/

namespace RamseySpace
namespace TwoSorted

universe uR vR uS vS

variable {P : System.{uR, vR, uS, vS}}

/-- S-Ramsey: every nonempty [a,Y] has a same-depth homogeneous reduction. -/
def IsRamsey (R : AbstractRamseySystem P) (target : Set P.Obj.Point) : Prop :=
  ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point) {d : ℕ},
    R.fin.HasDepth a Y d →
      ∃ X, X ∈ P.levelNeighborhood d Y ∧
        (P.objectNeighborhood a X ⊆ target ∨
          Disjoint (P.objectNeighborhood a X) target)

/-- S-Ramsey null. -/
def IsRamseyNull (R : AbstractRamseySystem P) (target : Set P.Obj.Point) : Prop :=
  ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point) {d : ℕ},
    R.fin.HasDepth a Y d →
      ∃ X, X ∈ P.levelNeighborhood d Y ∧
        Disjoint (P.objectNeighborhood a X) target

/-- S-Baire, in Todorčević's abstract (not topological) sense. -/
def IsBaire (target : Set P.Obj.Point) : Prop :=
  ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point),
    (P.objectNeighborhood a Y).Nonempty →
      ∃ (m : ℕ) (b : P.Obj.Approx m) (X : P.Red.Point),
        P.Obj.IsInitial a b ∧ P.Red.le X Y ∧
          (P.objectNeighborhood b X).Nonempty ∧
          (P.objectNeighborhood b X ⊆ target ∨
            Disjoint (P.objectNeighborhood b X) target)

/-- S-meagre in the abstract Ramsey-theorem sense. -/
def IsMeagre (target : Set P.Obj.Point) : Prop :=
  ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point),
    (P.objectNeighborhood a Y).Nonempty →
      ∃ (m : ℕ) (b : P.Obj.Approx m) (X : P.Red.Point),
        P.Obj.IsInitial a b ∧ P.Red.le X Y ∧
          (P.objectNeighborhood b X).Nonempty ∧
          Disjoint (P.objectNeighborhood b X) target

theorem isRamsey_empty (R : AbstractRamseySystem P) :
    IsRamsey R (∅ : Set P.Obj.Point) := by
  intro n a Y d hd
  exact ⟨Y, P.self_mem_levelNeighborhood d Y, Or.inr (by simp)⟩

theorem isRamsey_univ (R : AbstractRamseySystem P) :
    IsRamsey R (Set.univ : Set P.Obj.Point) := by
  intro n a Y d hd
  exact ⟨Y, P.self_mem_levelNeighborhood d Y, Or.inl (by simp)⟩

theorem isRamseyNull_empty (R : AbstractRamseySystem P) :
    IsRamseyNull R (∅ : Set P.Obj.Point) := by
  intro n a Y d hd
  exact ⟨Y, P.self_mem_levelNeighborhood d Y, by simp⟩

theorem IsRamseyNull.isRamsey (R : AbstractRamseySystem P)
    {target : Set P.Obj.Point} (h : IsRamseyNull R target) :
    IsRamsey R target := by
  intro n a Y d hd
  rcases h a Y hd with ⟨X, hXY, hdis⟩
  exact ⟨X, hXY, Or.inr hdis⟩

theorem IsRamsey.compl (R : AbstractRamseySystem P)
    {target : Set P.Obj.Point} (h : IsRamsey R target) :
    IsRamsey R targetᶜ := by
  intro n a Y d hd
  rcases h a Y hd with ⟨X, hXY, hhom⟩
  refine ⟨X, hXY, ?_⟩
  rcases hhom with hsub | hdis
  · exact Or.inr (Set.disjoint_compl_right_iff_subset.mpr hsub)
  · exact Or.inl (Set.subset_compl_iff_disjoint_right.mpr hdis)

theorem IsRamseyNull.mono (R : AbstractRamseySystem P)
    {target subset : Set P.Obj.Point}
    (h : IsRamseyNull R target) (hsub : subset ⊆ target) :
    IsRamseyNull R subset := by
  intro n a Y d hd
  rcases h a Y hd with ⟨X, hXY, hdis⟩
  exact ⟨X, hXY, hdis.mono_right hsub⟩

/-- The core Baire/Ramsey conclusion of the Abstract Ramsey Theorem. -/
def IsRamseySpace (R : AbstractRamseySystem P) : Prop :=
  (∀ target, IsBaire target → IsRamsey R target) ∧
    (∀ target, IsMeagre target → IsRamseyNull R target)

end TwoSorted
end RamseySpace
