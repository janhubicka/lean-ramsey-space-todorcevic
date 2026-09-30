import RamseySpace.Axioms

/-!
# Combinatorial forcing

Acceptance, rejection, and decision relative to a fixed target set.  This is the
Lean counterpart of Todorčević's Definition 4.30 and Lemmas 4.31--4.32.
-/

namespace RamseySpace
namespace CombinatorialForcing

universe u v

variable {S : ApproximationSystem.{u, v}}

/-- Y accepts a when the whole basic neighborhood [a,Y] lies in the target. -/
def Accepts (target : Set S.Point) (Y : S.Point) {n : ℕ} (a : S.Approx n) : Prop :=
  S.neighborhood a Y ⊆ target

/-- Y rejects a when [a,Y] is nonempty and no same-depth refinement accepts a. -/
def Rejects (R : AbstractRamseySpace S) (target : Set S.Point) (Y : S.Point)
    {n : ℕ} (a : S.Approx n) : Prop :=
  (S.neighborhood a Y).Nonempty ∧
    ∀ d, R.fin.HasDepth a Y d →
      ∀ X, X ∈ S.levelNeighborhood d Y → ¬ Accepts target X a

/-- Y decides a if it accepts or rejects it. -/
def Decides (R : AbstractRamseySpace S) (target : Set S.Point) (Y : S.Point)
    {n : ℕ} (a : S.Approx n) : Prop :=
  Accepts target Y a ∨ Rejects R target Y a

theorem accepts_of_neighborhood_empty {target : Set S.Point} {Y : S.Point}
    {n : ℕ} {a : S.Approx n} (h : S.neighborhood a Y = ∅) :
    Accepts target Y a := by
  unfold Accepts
  intro X hX
  rw [h] at hX
  exact False.elim (Set.not_mem_empty X hX)

theorem accepts_mono {target : Set S.Point} {X Y : S.Point}
    {n : ℕ} {a : S.Approx n} (hY : Accepts target Y a)
    (hXY : S.le X Y) :
    Accepts target X a := by
  unfold Accepts at hY ⊢
  exact (S.neighborhood_mono hXY).trans hY

theorem rejects_mono (R : AbstractRamseySpace S) {target : Set S.Point}
    {X Y : S.Point} {n : ℕ} {a : S.Approx n}
    (hY : Rejects R target Y a) (hXY : S.le X Y)
    (hne : (S.neighborhood a X).Nonempty) :
    Rejects R target X a := by
  rcases hY with ⟨_, hrejectY⟩
  refine ⟨hne, ?_⟩
  intro d hd Z hZd haccZ
  rcases hne with ⟨C, hC⟩
  have hCY : C ∈ S.neighborhood a Y :=
    S.neighborhood_mono hXY hC
  rcases R.fin.exists_hasDepth_of_mem_neighborhood hCY with ⟨e, he⟩
  have hnon : (S.neighborhood a Z).Nonempty :=
    R.amalgamation_nonempty a X hd hZd
  have hZY : S.le Z Y :=
    S.le_trans hZd.1 hXY
  rcases R.amalgamation_refine a Y he hZY hnon with ⟨Y', hY'depth, hsub⟩
  apply hrejectY e he Y' hY'depth
  unfold Accepts at haccZ ⊢
  exact hsub.trans haccZ

theorem decides_mono (R : AbstractRamseySpace S) {target : Set S.Point}
    {X Y : S.Point} {n : ℕ} {a : S.Approx n}
    (hY : Decides R target Y a) (hXY : S.le X Y) :
    Decides R target X a := by
  rcases hY with hacc | hrej
  · exact Or.inl (accepts_mono hacc hXY)
  · by_cases hne : (S.neighborhood a X).Nonempty
    · exact Or.inr (rejects_mono R hrej hXY hne)
    · apply Or.inl
      unfold Accepts
      intro Z hZ
      exact (hne ⟨Z, hZ⟩).elim

theorem exists_deciding (R : AbstractRamseySpace S) {target : Set S.Point}
    {Y : S.Point} {n : ℕ} {a : S.Approx n} {d : ℕ}
    (hd : R.fin.HasDepth a Y d) :
    ∃ X, X ∈ S.levelNeighborhood d Y ∧ Decides R target X a := by
  classical
  by_cases h :
      ∃ X, X ∈ S.levelNeighborhood d Y ∧ Accepts target X a
  · rcases h with ⟨X, hXd, hacc⟩
    exact ⟨X, hXd, Or.inl hacc⟩
  · have hne : (S.neighborhood a Y).Nonempty :=
      R.amalgamation_nonempty a Y hd (S.self_mem_levelNeighborhood d Y)
    refine ⟨Y, S.self_mem_levelNeighborhood d Y, Or.inr ?_⟩
    refine ⟨hne, ?_⟩
    intro e he X hXd hacc
    have hed : e = d := R.fin.hasDepth_unique he hd
    subst e
    exact h ⟨X, hXd, hacc⟩

theorem rejects_of_mem_levelNeighborhood (R : AbstractRamseySpace S)
    {target : Set S.Point} {X Y : S.Point} {n : ℕ} {a : S.Approx n} {d : ℕ}
    (hY : Rejects R target Y a) (hd : R.fin.HasDepth a Y d)
    (hX : X ∈ S.levelNeighborhood d Y) :
    Rejects R target X a :=
  rejects_mono R hY hX.1 (R.amalgamation_nonempty a Y hd hX)

theorem accepts_oneStep {target : Set S.Point} {Y : S.Point}
    {n : ℕ} {a : S.Approx n} {b : S.Approx (n + 1)}
    (hY : Accepts target Y a) (hb : b ∈ S.oneStepApproximations a Y) :
    Accepts target Y b := by
  unfold Accepts at hY ⊢
  exact (S.neighborhood_oneStep_subset hb).trans hY

/-- Lemma 4.32: a rejection cannot have a same-depth refinement accepting
every one-step extension. -/
theorem rejects_not_all_oneStep_accepts (R : AbstractRamseySpace S)
    {target : Set S.Point} {Y : S.Point} {n : ℕ} {a : S.Approx n} {d : ℕ}
    (hY : Rejects R target Y a) (hd : R.fin.HasDepth a Y d) :
    ¬ ∃ X, X ∈ S.levelNeighborhood d Y ∧
      ∀ b, b ∈ S.oneStepApproximations a X → Accepts target X b := by
  rintro ⟨X, hXd, hall⟩
  rcases hY with ⟨_, hrejectY⟩
  have hne : (S.neighborhood a X).Nonempty :=
    R.amalgamation_nonempty a Y hd hXd
  have hacc : Accepts target X a := by
    unfold Accepts
    intro C hC
    let b : S.Approx (n + 1) := S.approx (n + 1) C
    have hb : b ∈ S.oneStepApproximations a X :=
      ⟨C, hC, rfl⟩
    have haccb : Accepts target X b := hall b hb
    apply haccb
    exact ⟨hC.1, rfl⟩
  exact (hrejectY d hd X hXd) hacc

end CombinatorialForcing
end RamseySpace
