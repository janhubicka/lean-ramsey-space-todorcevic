import RamseySpace.Axioms

/-!
# Ramsey and Ramsey-null subsets

These are the combinatorial conclusions that the Abstract Ellentuck Theorem
will obtain from Baire/meagre hypotheses.
-/

namespace RamseySpace

universe u v

variable (S : ApproximationSystem.{u, v})

/-- A set is Ramsey if every nonempty basic neighborhood has a homogeneous
basic subneighborhood. -/
def IsRamsey (X : Set S.Point) : Prop :=
  ∀ {n : ℕ} (a : S.Approx n) (A : S.Point),
    (S.neighborhood a A).Nonempty →
      ∃ B, B ∈ S.neighborhood a A ∧
        (S.neighborhood a B ⊆ X ∨ Disjoint (S.neighborhood a B) X)

/-- A set is Ramsey-null if every nonempty basic neighborhood has a basic
subneighborhood disjoint from it. -/
def IsRamseyNull (X : Set S.Point) : Prop :=
  ∀ {n : ℕ} (a : S.Approx n) (A : S.Point),
    (S.neighborhood a A).Nonempty →
      ∃ B, B ∈ S.neighborhood a A ∧ Disjoint (S.neighborhood a B) X

theorem isRamsey_empty : IsRamsey S (∅ : Set S.Point) := by
  intro n a A h
  rcases h with ⟨B, hB⟩
  exact ⟨B, hB, Or.inr (by simp)⟩

theorem isRamsey_univ : IsRamsey S (Set.univ : Set S.Point) := by
  intro n a A h
  rcases h with ⟨B, hB⟩
  exact ⟨B, hB, Or.inl (by simp)⟩

theorem isRamseyNull_empty : IsRamseyNull S (∅ : Set S.Point) := by
  intro n a A h
  rcases h with ⟨B, hB⟩
  exact ⟨B, hB, by simp⟩

theorem IsRamseyNull.isRamsey {X : Set S.Point}
    (h : IsRamseyNull S X) :
    IsRamsey S X := by
  intro n a A hne
  rcases h a A hne with ⟨B, hBA, hdis⟩
  exact ⟨B, hBA, Or.inr hdis⟩

theorem IsRamsey.compl {X : Set S.Point}
    (h : IsRamsey S X) :
    IsRamsey S Xᶜ := by
  intro n a A hne
  rcases h a A hne with ⟨B, hBA, hhom⟩
  refine ⟨B, hBA, ?_⟩
  rcases hhom with hsub | hdis
  · exact Or.inr (Set.disjoint_compl_right_iff_subset.mpr hsub)
  · exact Or.inl (Set.subset_compl_iff_disjoint_right.mpr hdis)

theorem IsRamseyNull.mono {X Y : Set S.Point}
    (h : IsRamseyNull S X) (hYX : Y ⊆ X) :
    IsRamseyNull S Y := by
  intro n a A hne
  rcases h a A hne with ⟨B, hBA, hdis⟩
  exact ⟨B, hBA, hdis.mono_right hYX⟩

end RamseySpace
