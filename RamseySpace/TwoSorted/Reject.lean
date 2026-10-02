import RamseySpace.TwoSorted.Decision

/-!
# Propagating rejection to one-step object extensions
-/

namespace RamseySpace
namespace TwoSorted
namespace CombinatorialForcing

universe uR vR uS vS

variable {P : System.{uR, vR, uS, vS}}

theorem exists_refinement_rejects_oneStep
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    {target : Set P.Obj.Point} {Y : P.Red.Point}
    {n : ℕ} {a : P.Obj.Approx n} {d : ℕ}
    (hY : Rejects R target Y a) (hd : R.fin.HasDepth a Y d) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ b, b ∈ P.oneStepObjectApproximations a X →
        Rejects R target X b := by
  rcases exists_global_decider R C target d Y with
    ⟨Z, hZY, hdecZ⟩
  have hdZ : R.fin.HasDepth a Z d :=
    (R.fin.hasDepth_iff_of_mem_levelNeighborhood hZY).2 hd
  have hrejZ : Rejects R target Z a :=
    rejects_of_mem_levelNeighborhood R hY hd hZY
  let O : Set (P.Obj.Approx (n + 1)) := {b | Accepts target Z b}
  have hneAZ : (P.objectNeighborhood a Z).Nonempty :=
    R.amalgamation_nonempty a Y hd hZY
  rcases R.pigeonhole a Z hneAZ hdZ O with ⟨X, hXZ, hhom⟩
  have hXY : X ∈ P.levelNeighborhood d Y :=
    P.levelNeighborhood_mono hZY hXZ
  refine ⟨X, hXY, ?_⟩
  rcases hhom with hsub | hdis
  · exfalso
    apply rejects_not_all_oneStep_accepts R hrejZ hdZ
    refine ⟨X, hXZ, ?_⟩
    intro b hb
    have haccZ : Accepts target Z b := hsub hb
    exact accepts_mono R.fin haccZ hXZ.1
  · intro b hb
    have hbZ : b ∈ P.oneStepObjectApproximations a Z :=
      R.fin.oneStepObjectApproximations_mono hXZ.1 hb
    have hab : P.Obj.IsInitial a b :=
      P.isInitial_oneStep hbZ
    have hneBZ : (P.objectNeighborhood b Z).Nonempty := by
      rcases hbZ with ⟨A, hAa, hAb⟩
      exact ⟨A, hAa.1, hAb⟩
    rcases hneBZ with ⟨A, hAbZ⟩
    rcases R.fin.exists_hasDepth_of_mem_objectNeighborhood hAbZ with
      ⟨e, hdbZ⟩
    have hde : d ≤ e :=
      R.fin.hasDepth_le_of_initial hab hdZ hdbZ
    have hdec : Decides R target Z b :=
      hdecZ b hdbZ hde
    have hnotAccZ : ¬ Accepts target Z b := by
      intro hacc
      have hbO : b ∈ O := by
        simpa [O] using hacc
      exact Set.disjoint_left.1 hdis hb hbO
    have hrejBZ : Rejects R target Z b := by
      rcases hdec with hacc | hrej
      · exact (hnotAccZ hacc).elim
      · exact hrej
    have hneBX : (P.objectNeighborhood b X).Nonempty := by
      rcases hb with ⟨A, hAa, hAb⟩
      exact ⟨A, hAa.1, hAb⟩
    exact rejects_mono R hrejBZ hXZ.1 hneBX

end CombinatorialForcing
end TwoSorted
end RamseySpace
