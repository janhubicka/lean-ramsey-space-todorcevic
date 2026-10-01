import RamseySpace.Decision

/-!
# Propagating rejection to one-step extensions

This file formalizes Todorčević's Lemma 4.34: after a same-depth refinement,
rejection of a finite approximation propagates to all of its one-step
extensions.
-/

namespace RamseySpace
namespace CombinatorialForcing

universe u v

variable {S : ApproximationSystem.{u, v}}

/-- Todorčević Lemma 4.34. If Y rejects a, then there is a same-depth
refinement X such that X rejects every one-step extension of a compatible
with X. -/
theorem exists_refinement_rejects_oneStep
    (R : AbstractRamseySpace S) (C : FusionComplete S)
    {target : Set S.Point} {Y : S.Point}
    {n : ℕ} {a : S.Approx n} {d : ℕ}
    (hY : Rejects R target Y a) (hd : R.fin.HasDepth a Y d) :
    ∃ X, X ∈ S.levelNeighborhood d Y ∧
      ∀ b, b ∈ S.oneStepApproximations a X →
        Rejects R target X b := by
  rcases exists_global_decider R C target d Y with
    ⟨Z, hZY, hdecZ⟩
  have hdZ : R.fin.HasDepth a Z d :=
    (R.fin.hasDepth_iff_of_mem_levelNeighborhood hZY).2 hd
  have hrejZ : Rejects R target Z a :=
    rejects_of_mem_levelNeighborhood R hY hd hZY
  let O : Set (S.Approx (n + 1)) := {b | Accepts target Z b}
  rcases R.pigeonhole a Z hdZ O with ⟨X, hXZ, hhom⟩
  have hXY : X ∈ S.levelNeighborhood d Y :=
    S.levelNeighborhood_mono hZY hXZ
  refine ⟨X, hXY, ?_⟩
  rcases hhom with hsub | hdis
  · exfalso
    apply rejects_not_all_oneStep_accepts R hrejZ hdZ
    refine ⟨X, hXZ, ?_⟩
    intro b hb
    have haccZ : Accepts target Z b := by
      exact hsub hb
    exact accepts_mono haccZ hXZ.1
  · intro b hb
    have hbZ : b ∈ S.oneStepApproximations a Z :=
      S.oneStepApproximations_mono hXZ.1 hb
    have hab : S.IsInitial a b :=
      S.isInitial_oneStep hbZ
    have hneBZ : (S.neighborhood b Z).Nonempty := by
      rcases hbZ with ⟨W, hWa, hWb⟩
      exact ⟨W, hWa.1, hWb⟩
    rcases hneBZ with ⟨W, hWbZ⟩
    rcases R.fin.exists_hasDepth_of_mem_neighborhood hWbZ with
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
    have hneBX : (S.neighborhood b X).Nonempty := by
      rcases hb with ⟨V, hVa, hVb⟩
      exact ⟨V, hVa.1, hVb⟩
    exact rejects_mono R hrejBZ hXZ.1 hneBX

end CombinatorialForcing
end RamseySpace
