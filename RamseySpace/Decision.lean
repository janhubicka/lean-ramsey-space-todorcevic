import RamseySpace.Forcing
import RamseySpace.Fusion

/-!
# Finite-stage and fused decision

This file formalizes the finite-depth decision recursion and the fusion argument
of Todorčević's Lemma 4.33.
-/

namespace RamseySpace
namespace CombinatorialForcing

universe u v

variable {S : ApproximationSystem.{u, v}}

/-- Decision for a level-tagged finite approximation. -/
def DecidesFinite (R : AbstractRamseySpace S) (target : Set S.Point)
    (Y : S.Point) (q : S.FiniteApprox) : Prop :=
  match q with
  | ⟨_, a⟩ => Decides R target Y a

theorem decidesFinite_mono (R : AbstractRamseySpace S) {target : Set S.Point}
    {X Y : S.Point} {q : S.FiniteApprox}
    (h : DecidesFinite R target Y q) (hXY : S.le X Y) :
    DecidesFinite R target X q := by
  rcases q with ⟨n, a⟩
  simpa [DecidesFinite] using decides_mono R h hXY

/-- A finite family of approximations all having depth d can be decided
successively while staying inside [d,Y]. -/
theorem exists_refinement_decides_finite (R : AbstractRamseySpace S)
    {target : Set S.Point} (t : Set S.FiniteApprox) (ht : t.Finite)
    {Y : S.Point} {d : ℕ}
    (hdepth : t ⊆ R.fin.depthApproximations Y d) :
    ∃ X, X ∈ S.levelNeighborhood d Y ∧
      ∀ q ∈ t, DecidesFinite R target X q := by
  induction t, ht using Set.Finite.induction_on generalizing Y with
  | empty =>
      refine ⟨Y, S.self_mem_levelNeighborhood d Y, ?_⟩
      simp
  | @insert q t hqt ht ih =>
      have htdepth : t ⊆ R.fin.depthApproximations Y d := by
        intro p hp
        exact hdepth (by simp [hp])
      rcases ih htdepth with ⟨X, hXY, hdecX⟩
      have hqdepthSigma : q ∈ R.fin.depthApproximations Y d :=
        hdepth (by simp)
      rcases q with ⟨n, a⟩
      have hqdepthY : R.fin.HasDepth a Y d :=
        (R.fin.mem_depthApproximations).1 hqdepthSigma
      have hqdepthX : R.fin.HasDepth a X d :=
        (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hqdepthY
      rcases exists_deciding R hqdepthX with ⟨Z, hZX, hdecZ⟩
      have hZY : Z ∈ S.levelNeighborhood d Y :=
        S.levelNeighborhood_mono hXY hZX
      refine ⟨Z, hZY, ?_⟩
      intro p hp
      rcases (Set.mem_insert_iff.mp hp) with hp | hp
      · subst p
        simpa [DecidesFinite] using hdecZ
      · exact decidesFinite_mono R (hdecX p hp) hZX.1

/-- Decide every approximation at one fixed depth. -/
theorem exists_refinement_decides_depth (R : AbstractRamseySpace S)
    {target : Set S.Point} (Y : S.Point) (d : ℕ) :
    ∃ X, X ∈ S.levelNeighborhood d Y ∧
      ∀ q ∈ R.fin.depthApproximations Y d, DecidesFinite R target X q := by
  exact exists_refinement_decides_finite R
    (R.fin.depthApproximations Y d)
    (R.fin.depthApproximations_finite Y d)
    (fun _ h => h)

/-- Canonical choice of the next finite-stage deciding refinement. -/
noncomputable def decisionStep (R : AbstractRamseySpace S) (target : Set S.Point)
    (d : ℕ) (Y : S.Point) : S.Point :=
  Classical.choose (exists_refinement_decides_depth R (target := target) Y d)

theorem decisionStep_mem (R : AbstractRamseySpace S) (target : Set S.Point)
    (d : ℕ) (Y : S.Point) :
    decisionStep R target d Y ∈ S.levelNeighborhood d Y :=
  (Classical.choose_spec
    (exists_refinement_decides_depth R (target := target) Y d)).1

theorem decisionStep_decides (R : AbstractRamseySpace S) (target : Set S.Point)
    (d : ℕ) (Y : S.Point) {q : S.FiniteApprox}
    (hq : q ∈ R.fin.depthApproximations Y d) :
    DecidesFinite R target (decisionStep R target d Y) q :=
  (Classical.choose_spec
    (exists_refinement_decides_depth R (target := target) Y d)).2 q hq

/-- The fusion obtained by deciding the depth n0+k layer at stage k. -/
noncomputable def decisionFusion (R : AbstractRamseySpace S)
    (target : Set S.Point) (n0 : ℕ) (Y0 : S.Point) : ℕ → S.Point
  | 0 => Y0
  | k + 1 =>
      decisionStep R target (n0 + k) (decisionFusion R target n0 Y0 k)

theorem decisionFusion_isFusion (R : AbstractRamseySpace S)
    (target : Set S.Point) (n0 : ℕ) (Y0 : S.Point) :
    S.IsFusionFrom n0 (decisionFusion R target n0 Y0) := by
  intro k
  simpa [decisionFusion] using
    decisionStep_mem R target (n0 + k) (decisionFusion R target n0 Y0 k)

theorem decisionFusion_succ_decides (R : AbstractRamseySpace S)
    (target : Set S.Point) (n0 : ℕ) (Y0 : S.Point) (k : ℕ)
    {q : S.FiniteApprox}
    (hq : q ∈ R.fin.depthApproximations
      (decisionFusion R target n0 Y0 k) (n0 + k)) :
    DecidesFinite R target (decisionFusion R target n0 Y0 (k + 1)) q := by
  simpa [decisionFusion] using
    decisionStep_decides R target (n0 + k)
      (decisionFusion R target n0 Y0 k) hq

/-- Todorčević Lemma 4.33: after fusion, every approximation whose depth is
at least n0 is decided. -/
theorem exists_global_decider (R : AbstractRamseySpace S)
    (C : FusionComplete S) (target : Set S.Point) (n0 : ℕ) (Y0 : S.Point) :
    ∃ X, X ∈ S.levelNeighborhood n0 Y0 ∧
      ∀ {n : ℕ} (a : S.Approx n) {d : ℕ},
        R.fin.HasDepth a X d → n0 ≤ d → Decides R target X a := by
  let Y := decisionFusion R target n0 Y0
  have hfusion : S.IsFusionFrom n0 Y :=
    decisionFusion_isFusion R target n0 Y0
  rcases C.exists_limit hfusion with ⟨X, hX⟩
  refine ⟨X, ?_, ?_⟩
  · simpa [Y, decisionFusion] using hX 0
  · intro n a d hd hnd
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnd
    have hXk : X ∈ S.levelNeighborhood (n0 + k) (Y k) :=
      hX k
    have hdYk : R.fin.HasDepth a (Y k) (n0 + k) :=
      (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXk).1 hd
    have hq :
        (⟨n, a⟩ : S.FiniteApprox) ∈
          R.fin.depthApproximations (Y k) (n0 + k) :=
      (R.fin.mem_depthApproximations).2 hdYk
    have hdecStage :
        Decides R target (Y (k + 1)) a := by
      have h :=
        decisionFusion_succ_decides R target n0 Y0 k hq
      simpa [Y, DecidesFinite] using h
    have hle : S.le X (Y (k + 1)) :=
      (hX (k + 1)).1
    exact decides_mono R hdecStage hle

end CombinatorialForcing
end RamseySpace
