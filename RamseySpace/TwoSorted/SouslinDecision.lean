import RamseySpace.Souslin
import RamseySpace.TwoSorted.RelativeSigma

/-!
# Souslin closure: common decision fusion

This file begins Todorcevic Lemma 4.39. Finite sequences are enumerated by
Encodable codes. At fusion stage k we decide the complements of the first
k+1 normalized Souslin tails on the entire protected depth layer.
-/

namespace RamseySpace
namespace TwoSorted
namespace CombinatorialForcing

universe uR vR uS vS

variable {P : System.{uR, vR, uS, vS}}

noncomputable def souslinSeq (i : ℕ) : List ℕ :=
  (@Encodable.decode (List ℕ) _ i).getD []

@[simp] theorem souslinSeq_encode (s : List ℕ) :
    souslinSeq (Encodable.encode s) = s := by
  simp [souslinSeq, Encodable.encodek]

theorem isRamsey_iInter
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (targets : ℕ → Set P.Obj.Point)
    (hRamsey : ∀ i, IsRamsey R (targets i)) :
    IsRamsey R (⋂ i, targets i) := by
  have hcomp : ∀ i, IsRamsey R ((targets i)ᶜ) := by
    intro i
    exact IsRamsey.compl R (hRamsey i)
  have hu : IsRamsey R (⋃ i, (targets i)ᶜ) :=
    isRamsey_iUnion R C (fun i => (targets i)ᶜ) hcomp
  have heq : (⋃ i, (targets i)ᶜ)ᶜ = ⋂ i, targets i := by
    ext x
    simp
  rw [← heq]
  intro n a Y d hd
  exact (IsRamsey.compl R hu) a Y hd

theorem isRamseyBelow_iInter
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hRamsey : ∀ i, IsRamseyBelow R bound (targets i)) :
    IsRamseyBelow R bound (⋂ i, targets i) := by
  have hcomp : ∀ i, IsRamseyBelow R bound ((targets i)ᶜ) := by
    intro i
    exact IsRamseyBelow.compl R (hRamsey i)
  have hu : IsRamseyBelow R bound (⋃ i, (targets i)ᶜ) :=
    isRamseyBelow_iUnion R C bound (fun i => (targets i)ᶜ) hcomp
  have heq : (⋃ i, (targets i)ᶜ)ᶜ = ⋂ i, targets i := by
    ext x
    simp
  rw [← heq]
  intro n a Y d hY hd
  exact (IsRamseyBelow.compl R hu) a Y hY hd

theorem normalize_isRamsey
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (A : Souslin.Scheme P.Obj.Point)
    (hA : ∀ s, IsRamsey R (A s))
    (s : List ℕ) :
    IsRamsey R (Souslin.normalize A s) := by
  let targets : ℕ → Set P.Obj.Point :=
    fun n => if n ≤ s.length then A (s.take n) else Set.univ
  have htargets : ∀ n, IsRamsey R (targets n) := by
    intro n
    by_cases hn : n ≤ s.length
    · simpa [targets, hn] using hA (s.take n)
    · simpa [targets, hn] using isRamsey_univ R
  have heq : (⋂ n, targets n) = Souslin.normalize A s := by
    ext x
    simp [targets, Souslin.normalize]
  rw [← heq]
  intro n a Y d hd
  exact (isRamsey_iInter R C targets htargets) a Y hd

def DecidesTargetFinite
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    (Y : P.Red.Point) (i : ℕ) (q : P.Obj.FiniteApprox) : Prop :=
  DecidesFinite R (targets i) Y q

theorem decidesTargetFinite_mono
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    {X Y : P.Red.Point} {i : ℕ} {q : P.Obj.FiniteApprox}
    (h : DecidesTargetFinite R targets Y i q)
    (hXY : P.Red.le X Y) :
    DecidesTargetFinite R targets X i q :=
  decidesFinite_mono R h hXY

theorem exists_refinement_decides_targets_upTo
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    (t : Set P.Obj.FiniteApprox) (ht : t.Finite)
    {Y : P.Red.Point} {d : ℕ}
    (hdepth : t ⊆ R.fin.depthApproximations Y d)
    (k : ℕ) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ i, i ≤ k → ∀ q ∈ t,
        DecidesTargetFinite R targets X i q := by
  induction k generalizing Y with
  | zero =>
      rcases exists_refinement_decides_finite
          R (target := targets 0) t ht hdepth with
        ⟨X, hXY, hdec⟩
      refine ⟨X, hXY, ?_⟩
      intro i hi q hq
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      exact hdec q hq
  | succ k ih =>
      rcases ih hdepth with ⟨X, hXY, hdecX⟩
      have hdepthX : t ⊆ R.fin.depthApproximations X d := by
        intro q hq
        rcases q with ⟨m, b⟩
        have hdY : R.fin.HasDepth b Y d :=
          (R.fin.mem_depthApproximations).1 (hdepth hq)
        have hdX : R.fin.HasDepth b X d :=
          (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hdY
        exact (R.fin.mem_depthApproximations).2 hdX
      rcases exists_refinement_decides_finite
          R (target := targets (k + 1)) t ht hdepthX with
        ⟨Z, hZX, hdecZ⟩
      have hZY : Z ∈ P.levelNeighborhood d Y :=
        P.levelNeighborhood_mono hXY hZX
      refine ⟨Z, hZY, ?_⟩
      intro i hi q hq
      by_cases hik : i ≤ k
      · exact decidesTargetFinite_mono R targets (hdecX i hik q hq) hZX.1
      · have hiEq : i = k + 1 := by omega
        subst i
        exact hdecZ q hq

theorem exists_refinement_decides_targets_stage
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    (Y : P.Red.Point) (d k : ℕ) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ i, i ≤ k →
        ∀ q ∈ R.fin.depthApproximations Y d,
          DecidesTargetFinite R targets X i q :=
  exists_refinement_decides_targets_upTo R targets
    (R.fin.depthApproximations Y d)
    (R.fin.depthApproximations_finite Y d)
    (fun _ h => h) k

noncomputable def multiDecisionStep
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    (k d : ℕ) (Y : P.Red.Point) : P.Red.Point :=
  Classical.choose
    (exists_refinement_decides_targets_stage R targets Y d k)

theorem multiDecisionStep_mem
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    (k d : ℕ) (Y : P.Red.Point) :
    multiDecisionStep R targets k d Y ∈ P.levelNeighborhood d Y :=
  (Classical.choose_spec
    (exists_refinement_decides_targets_stage R targets Y d k)).1

theorem multiDecisionStep_decides
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    (k d : ℕ) (Y : P.Red.Point)
    {i : ℕ} (hi : i ≤ k) {q : P.Obj.FiniteApprox}
    (hq : q ∈ R.fin.depthApproximations Y d) :
    DecidesTargetFinite R targets
      (multiDecisionStep R targets k d Y) i q :=
  (Classical.choose_spec
    (exists_refinement_decides_targets_stage R targets Y d k)).2
      i hi q hq

noncomputable def multiDecisionFusion
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    (n0 : ℕ) (Y0 : P.Red.Point) : ℕ → P.Red.Point
  | 0 => Y0
  | k + 1 =>
      multiDecisionStep R targets k (n0 + k)
        (multiDecisionFusion R targets n0 Y0 k)

theorem multiDecisionFusion_isFusion
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    (n0 : ℕ) (Y0 : P.Red.Point) :
    P.Red.IsFusionFrom n0 (multiDecisionFusion R targets n0 Y0) := by
  intro k
  simpa [multiDecisionFusion] using
    multiDecisionStep_mem R targets k (n0 + k)
      (multiDecisionFusion R targets n0 Y0 k)

theorem multiDecisionFusion_succ_decides
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    (n0 : ℕ) (Y0 : P.Red.Point) (k : ℕ)
    {i : ℕ} (hi : i ≤ k) {q : P.Obj.FiniteApprox}
    (hq : q ∈ R.fin.depthApproximations
      (multiDecisionFusion R targets n0 Y0 k) (n0 + k)) :
    DecidesTargetFinite R targets
      (multiDecisionFusion R targets n0 Y0 (k + 1)) i q := by
  simpa [multiDecisionFusion] using
    multiDecisionStep_decides R targets k (n0 + k)
      (multiDecisionFusion R targets n0 Y0 k) hi hq

def souslinDecisionTarget
    (A : Souslin.Scheme P.Obj.Point) (i : ℕ) : Set P.Obj.Point :=
  (Souslin.tail (Souslin.normalize A) (souslinSeq i))ᶜ

theorem exists_souslin_decider
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (A : Souslin.Scheme P.Obj.Point)
    (n0 : ℕ) (Y0 : P.Red.Point) :
    ∃ X, X ∈ P.levelNeighborhood n0 Y0 ∧
      ∀ (s : List ℕ) {m : ℕ} (b : P.Obj.Approx m) {d : ℕ},
        R.fin.HasDepth b X d →
        n0 + Encodable.encode s ≤ d →
        Decides R (Souslin.tail (Souslin.normalize A) s)ᶜ X b := by
  let targets : ℕ → Set P.Obj.Point := souslinDecisionTarget A
  let Ys := multiDecisionFusion R targets n0 Y0
  have hfusion : P.Red.IsFusionFrom n0 Ys := by
    simpa [Ys] using multiDecisionFusion_isFusion R targets n0 Y0
  rcases C.exists_limit hfusion with ⟨X, hX⟩
  refine ⟨X, ?_, ?_⟩
  · simpa [Ys, multiDecisionFusion] using hX 0
  · intro s m b d hd hcode
    have hnd : n0 ≤ d := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnd
    have hcodek : Encodable.encode s ≤ k := by omega
    have hXk : X ∈ P.levelNeighborhood (n0 + k) (Ys k) := hX k
    have hdYk : R.fin.HasDepth b (Ys k) (n0 + k) :=
      (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXk).1 hd
    have hq :
        (⟨m, b⟩ : P.Obj.FiniteApprox) ∈
          R.fin.depthApproximations (Ys k) (n0 + k) :=
      (R.fin.mem_depthApproximations).2 hdYk
    have hdecStage :
        DecidesTargetFinite R targets (Ys (k + 1))
          (Encodable.encode s) (⟨m, b⟩ : P.Obj.FiniteApprox) := by
      simpa [Ys] using
        multiDecisionFusion_succ_decides
          R targets n0 Y0 k hcodek hq
    have hdecX :
        DecidesTargetFinite R targets X
          (Encodable.encode s) (⟨m, b⟩ : P.Obj.FiniteApprox) :=
      decidesTargetFinite_mono R targets hdecStage (hX (k + 1)).1
    simpa [DecidesTargetFinite, targets, souslinDecisionTarget,
      DecidesFinite] using hdecX

end CombinatorialForcing
end TwoSorted
end RamseySpace
