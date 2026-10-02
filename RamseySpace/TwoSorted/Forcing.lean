import RamseySpace.TwoSorted.Axioms

/-!
# Two-sorted combinatorial forcing

Acceptance, rejection, and decision for the Abstract Ramsey Theorem.
-/

namespace RamseySpace
namespace TwoSorted
namespace CombinatorialForcing

universe uR vR uS vS

variable {P : System.{uR, vR, uS, vS}}

/-- Y accepts a if the whole object neighborhood [a,Y] lies in target. -/
def Accepts (target : Set P.Obj.Point) (Y : P.Red.Point)
    {n : ℕ} (a : P.Obj.Approx n) : Prop :=
  P.objectNeighborhood a Y ⊆ target

/-- Y rejects a if [a,Y] is nonempty and no same-depth refinement accepts. -/
def Rejects (R : AbstractRamseySystem P) (target : Set P.Obj.Point)
    (Y : P.Red.Point) {n : ℕ} (a : P.Obj.Approx n) : Prop :=
  (P.objectNeighborhood a Y).Nonempty ∧
    ∀ d, R.fin.HasDepth a Y d →
      ∀ X, X ∈ P.levelNeighborhood d Y → ¬ Accepts target X a

def Decides (R : AbstractRamseySystem P) (target : Set P.Obj.Point)
    (Y : P.Red.Point) {n : ℕ} (a : P.Obj.Approx n) : Prop :=
  Accepts target Y a ∨ Rejects R target Y a

theorem accepts_mono (F : Finitization P)
    {target : Set P.Obj.Point} {X Y : P.Red.Point}
    {n : ℕ} {a : P.Obj.Approx n}
    (hY : Accepts target Y a) (hXY : P.Red.le X Y) :
    Accepts target X a := by
  unfold Accepts at hY ⊢
  exact (F.objectNeighborhood_mono hXY).trans hY

theorem rejects_mono (R : AbstractRamseySystem P)
    {target : Set P.Obj.Point} {X Y : P.Red.Point}
    {n : ℕ} {a : P.Obj.Approx n}
    (hY : Rejects R target Y a)
    (hXY : P.Red.le X Y)
    (hne : (P.objectNeighborhood a X).Nonempty) :
    Rejects R target X a := by
  rcases hY with ⟨_, hrejectY⟩
  refine ⟨hne, ?_⟩
  intro d hd Z hZd haccZ
  rcases hne with ⟨A, hA⟩
  have hAY : A ∈ P.objectNeighborhood a Y :=
    R.fin.objectNeighborhood_mono hXY hA
  rcases R.fin.exists_hasDepth_of_mem_objectNeighborhood hAY with ⟨e, he⟩
  have hnon : (P.objectNeighborhood a Z).Nonempty :=
    R.amalgamation_nonempty a X hd hZd
  have hZY : P.Red.le Z Y :=
    P.Red.le_trans hZd.1 hXY
  rcases R.amalgamation_refine a Y he hZY hnon with
    ⟨Y', hY'depth, hsub⟩
  apply hrejectY e he Y' hY'depth
  unfold Accepts at haccZ ⊢
  exact hsub.trans haccZ

theorem decides_mono (R : AbstractRamseySystem P)
    {target : Set P.Obj.Point} {X Y : P.Red.Point}
    {n : ℕ} {a : P.Obj.Approx n}
    (hY : Decides R target Y a) (hXY : P.Red.le X Y) :
    Decides R target X a := by
  rcases hY with hacc | hrej
  · exact Or.inl (accepts_mono R.fin hacc hXY)
  · by_cases hne : (P.objectNeighborhood a X).Nonempty
    · exact Or.inr (rejects_mono R hrej hXY hne)
    · apply Or.inl
      intro A hA
      exact (hne ⟨A, hA⟩).elim

theorem exists_deciding (R : AbstractRamseySystem P)
    {target : Set P.Obj.Point} {Y : P.Red.Point}
    {n : ℕ} {a : P.Obj.Approx n} {d : ℕ}
    (hd : R.fin.HasDepth a Y d) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧ Decides R target X a := by
  classical
  by_cases h :
      ∃ X, X ∈ P.levelNeighborhood d Y ∧ Accepts target X a
  · rcases h with ⟨X, hXd, hacc⟩
    exact ⟨X, hXd, Or.inl hacc⟩
  · have hne : (P.objectNeighborhood a Y).Nonempty :=
      R.amalgamation_nonempty a Y hd (P.self_mem_levelNeighborhood d Y)
    refine ⟨Y, P.self_mem_levelNeighborhood d Y, Or.inr ?_⟩
    refine ⟨hne, ?_⟩
    intro e he X hXd hacc
    have hed : e = d := R.fin.hasDepth_unique he hd
    subst e
    exact h ⟨X, hXd, hacc⟩

theorem Rejects.not_accepts (R : AbstractRamseySystem P)
    {target : Set P.Obj.Point} {Y : P.Red.Point}
    {n : ℕ} {a : P.Obj.Approx n}
    (h : Rejects R target Y a) :
    ¬ Accepts target Y a := by
  intro hacc
  rcases h.1 with ⟨A, hA⟩
  rcases R.fin.exists_hasDepth_of_mem_objectNeighborhood hA with ⟨d, hd⟩
  exact (h.2 d hd Y (P.self_mem_levelNeighborhood d Y)) hacc

theorem rejects_of_mem_levelNeighborhood (R : AbstractRamseySystem P)
    {target : Set P.Obj.Point} {X Y : P.Red.Point}
    {n : ℕ} {a : P.Obj.Approx n} {d : ℕ}
    (hY : Rejects R target Y a) (hd : R.fin.HasDepth a Y d)
    (hX : X ∈ P.levelNeighborhood d Y) :
    Rejects R target X a :=
  rejects_mono R hY hX.1 (R.amalgamation_nonempty a Y hd hX)

theorem accepts_oneStep (R : AbstractRamseySystem P)
    {target : Set P.Obj.Point} {Y : P.Red.Point}
    {n : ℕ} {a : P.Obj.Approx n} {b : P.Obj.Approx (n + 1)}
    (hY : Accepts target Y a)
    (hb : b ∈ P.oneStepObjectApproximations a Y) :
    Accepts target Y b := by
  unfold Accepts at hY ⊢
  exact (P.objectNeighborhood_oneStep_subset hb).trans hY

theorem rejects_not_all_oneStep_accepts (R : AbstractRamseySystem P)
    {target : Set P.Obj.Point} {Y : P.Red.Point}
    {n : ℕ} {a : P.Obj.Approx n} {d : ℕ}
    (hY : Rejects R target Y a) (hd : R.fin.HasDepth a Y d) :
    ¬ ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ b, b ∈ P.oneStepObjectApproximations a X →
        Accepts target X b := by
  rintro ⟨X, hXd, hall⟩
  rcases hY with ⟨_, hrejectY⟩
  have hne : (P.objectNeighborhood a X).Nonempty :=
    R.amalgamation_nonempty a Y hd hXd
  have hacc : Accepts target X a := by
    intro A hA
    let b : P.Obj.Approx (n + 1) := P.Obj.approx (n + 1) A
    have hb : b ∈ P.oneStepObjectApproximations a X :=
      ⟨A, hA, rfl⟩
    have haccb : Accepts target X b := hall b hb
    apply haccb
    exact ⟨hA.1, rfl⟩
  exact (hrejectY d hd X hXd) hacc

end CombinatorialForcing
end TwoSorted
end RamseySpace
