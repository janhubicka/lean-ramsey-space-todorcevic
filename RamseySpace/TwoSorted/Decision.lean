import RamseySpace.TwoSorted.Forcing
import RamseySpace.TwoSorted.Closed

/-!
# Finite-stage and fused decision in the two-sorted setting
-/

namespace RamseySpace
namespace TwoSorted
namespace CombinatorialForcing

universe uR vR uS vS

variable {P : System.{uR, vR, uS, vS}}

def DecidesFinite (R : AbstractRamseySystem P) (target : Set P.Obj.Point)
    (Y : P.Red.Point) (q : P.Obj.FiniteApprox) : Prop :=
  match q with
  | ⟨_, a⟩ => Decides R target Y a

theorem decidesFinite_mono (R : AbstractRamseySystem P)
    {target : Set P.Obj.Point} {X Y : P.Red.Point}
    {q : P.Obj.FiniteApprox}
    (h : DecidesFinite R target Y q) (hXY : P.Red.le X Y) :
    DecidesFinite R target X q := by
  rcases q with ⟨n, a⟩
  simpa [DecidesFinite] using decides_mono R h hXY

theorem exists_refinement_decides_finite
    (R : AbstractRamseySystem P)
    {target : Set P.Obj.Point}
    (t : Set P.Obj.FiniteApprox) (ht : t.Finite)
    {Y : P.Red.Point} {d : ℕ}
    (hdepth : t ⊆ R.fin.depthApproximations Y d) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ q ∈ t, DecidesFinite R target X q := by
  induction t, ht using Set.Finite.induction_on generalizing Y with
  | empty =>
      refine ⟨Y, P.self_mem_levelNeighborhood d Y, ?_⟩
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
      have hZY : Z ∈ P.levelNeighborhood d Y :=
        P.levelNeighborhood_mono hXY hZX
      refine ⟨Z, hZY, ?_⟩
      intro p hp
      rcases Set.mem_insert_iff.mp hp with hp | hp
      · subst p
        simpa [DecidesFinite] using hdecZ
      · exact decidesFinite_mono R (hdecX p hp) hZX.1

theorem exists_refinement_decides_depth
    (R : AbstractRamseySystem P)
    {target : Set P.Obj.Point} (Y : P.Red.Point) (d : ℕ) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ q ∈ R.fin.depthApproximations Y d,
        DecidesFinite R target X q :=
  exists_refinement_decides_finite R
    (R.fin.depthApproximations Y d)
    (R.fin.depthApproximations_finite Y d)
    (fun _ h => h)

noncomputable def decisionStep
    (R : AbstractRamseySystem P) (target : Set P.Obj.Point)
    (d : ℕ) (Y : P.Red.Point) : P.Red.Point :=
  Classical.choose (exists_refinement_decides_depth R (target := target) Y d)

theorem decisionStep_mem
    (R : AbstractRamseySystem P) (target : Set P.Obj.Point)
    (d : ℕ) (Y : P.Red.Point) :
    decisionStep R target d Y ∈ P.levelNeighborhood d Y :=
  (Classical.choose_spec
    (exists_refinement_decides_depth R (target := target) Y d)).1

theorem decisionStep_decides
    (R : AbstractRamseySystem P) (target : Set P.Obj.Point)
    (d : ℕ) (Y : P.Red.Point) {q : P.Obj.FiniteApprox}
    (hq : q ∈ R.fin.depthApproximations Y d) :
    DecidesFinite R target (decisionStep R target d Y) q :=
  (Classical.choose_spec
    (exists_refinement_decides_depth R (target := target) Y d)).2 q hq

noncomputable def decisionFusion
    (R : AbstractRamseySystem P) (target : Set P.Obj.Point)
    (n0 : ℕ) (Y0 : P.Red.Point) : ℕ → P.Red.Point
  | 0 => Y0
  | k + 1 =>
      decisionStep R target (n0 + k) (decisionFusion R target n0 Y0 k)

theorem decisionFusion_isFusion
    (R : AbstractRamseySystem P) (target : Set P.Obj.Point)
    (n0 : ℕ) (Y0 : P.Red.Point) :
    P.Red.IsFusionFrom n0 (decisionFusion R target n0 Y0) := by
  intro k
  simpa [decisionFusion] using
    decisionStep_mem R target (n0 + k)
      (decisionFusion R target n0 Y0 k)

theorem decisionFusion_succ_decides
    (R : AbstractRamseySystem P) (target : Set P.Obj.Point)
    (n0 : ℕ) (Y0 : P.Red.Point) (k : ℕ)
    {q : P.Obj.FiniteApprox}
    (hq : q ∈ R.fin.depthApproximations
      (decisionFusion R target n0 Y0 k) (n0 + k)) :
    DecidesFinite R target
      (decisionFusion R target n0 Y0 (k + 1)) q := by
  simpa [decisionFusion] using
    decisionStep_decides R target (n0 + k)
      (decisionFusion R target n0 Y0 k) hq

theorem exists_global_decider
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (target : Set P.Obj.Point) (n0 : ℕ) (Y0 : P.Red.Point) :
    ∃ X, X ∈ P.levelNeighborhood n0 Y0 ∧
      ∀ {n : ℕ} (a : P.Obj.Approx n) {d : ℕ},
        R.fin.HasDepth a X d → n0 ≤ d → Decides R target X a := by
  let Y := decisionFusion R target n0 Y0
  have hfusion : P.Red.IsFusionFrom n0 Y :=
    decisionFusion_isFusion R target n0 Y0
  rcases C.exists_limit hfusion with ⟨X, hX⟩
  refine ⟨X, ?_, ?_⟩
  · simpa [Y, decisionFusion] using hX 0
  · intro n a d hd hnd
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnd
    have hXk : X ∈ P.levelNeighborhood (n0 + k) (Y k) :=
      hX k
    have hdYk : R.fin.HasDepth a (Y k) (n0 + k) :=
      (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXk).1 hd
    have hq :
        (⟨n, a⟩ : P.Obj.FiniteApprox) ∈
          R.fin.depthApproximations (Y k) (n0 + k) :=
      (R.fin.mem_depthApproximations).2 hdYk
    have hdecStage : Decides R target (Y (k + 1)) a := by
      have h :=
        decisionFusion_succ_decides R target n0 Y0 k hq
      simpa [Y, DecidesFinite] using h
    exact decides_mono R hdecStage (hX (k + 1)).1

end CombinatorialForcing
end TwoSorted
end RamseySpace
