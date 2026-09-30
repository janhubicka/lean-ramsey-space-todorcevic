import RamseySpace.Axioms

/-!
# Ramsey and Ramsey-null subsets

These are Todorčević's Ramsey and Ramsey-null notions, using refinements in
the depth neighborhood [depth_B(a), B].
-/

namespace RamseySpace

universe u v

variable {S : ApproximationSystem.{u, v}} (R : AbstractRamseySpace S)

/-- A set is Ramsey if every finite-depth basic neighborhood has a homogeneous
refinement at the same depth. -/
def IsRamsey (X : Set S.Point) : Prop :=
  ∀ {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ},
    R.fin.HasDepth a B d →
      ∃ C, C ∈ S.levelNeighborhood d B ∧
        (S.neighborhood a C ⊆ X ∨ Disjoint (S.neighborhood a C) X)

/-- A set is Ramsey-null if every finite-depth basic neighborhood has a
same-depth refinement disjoint from it. -/
def IsRamseyNull (X : Set S.Point) : Prop :=
  ∀ {n : ℕ} (a : S.Approx n) (B : S.Point) {d : ℕ},
    R.fin.HasDepth a B d →
      ∃ C, C ∈ S.levelNeighborhood d B ∧ Disjoint (S.neighborhood a C) X

theorem isRamsey_empty : IsRamsey R (∅ : Set S.Point) := by
  intro n a B d hd
  exact ⟨B, S.self_mem_levelNeighborhood d B, Or.inr (by simp)⟩

theorem isRamsey_univ : IsRamsey R (Set.univ : Set S.Point) := by
  intro n a B d hd
  exact ⟨B, S.self_mem_levelNeighborhood d B, Or.inl (by simp)⟩

theorem isRamseyNull_empty : IsRamseyNull R (∅ : Set S.Point) := by
  intro n a B d hd
  exact ⟨B, S.self_mem_levelNeighborhood d B, by simp⟩

theorem IsRamseyNull.isRamsey {X : Set S.Point}
    (h : IsRamseyNull R X) :
    IsRamsey R X := by
  intro n a B d hd
  rcases h a B hd with ⟨C, hCB, hdis⟩
  exact ⟨C, hCB, Or.inr hdis⟩

theorem IsRamsey.compl {X : Set S.Point}
    (h : IsRamsey R X) :
    IsRamsey R Xᶜ := by
  intro n a B d hd
  rcases h a B hd with ⟨C, hCB, hhom⟩
  refine ⟨C, hCB, ?_⟩
  rcases hhom with hsub | hdis
  · exact Or.inr (Set.disjoint_compl_right_iff_subset.mpr hsub)
  · exact Or.inl (Set.subset_compl_iff_disjoint_right.mpr hdis)

theorem IsRamseyNull.mono {X Y : Set S.Point}
    (h : IsRamseyNull R X) (hYX : Y ⊆ X) :
    IsRamseyNull R Y := by
  intro n a B d hd
  rcases h a B hd with ⟨C, hCB, hdis⟩
  exact ⟨C, hCB, hdis.mono_right hYX⟩

end RamseySpace
