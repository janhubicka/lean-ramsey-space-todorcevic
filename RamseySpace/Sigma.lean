import RamseySpace.Baire

/-!
# Countable unions of Ramsey sets

This file formalizes Todorčević's Lemma 4.37.  The proof fuses finite
homogenizations: at stage k, every approximation of the protected depth is
made homogeneous for the first k+1 Ramsey sets.
-/

namespace RamseySpace
namespace CombinatorialForcing

universe u v

variable {S : ApproximationSystem.{u, v}}

/-- Homogeneity of a tagged finite approximation for a fixed target. -/
def HomogeneousFinite (target : Set S.Point) (Y : S.Point)
    (q : S.FiniteApprox) : Prop :=
  match q with
  | ⟨_, b⟩ =>
      S.neighborhood b Y ⊆ target ∨
        Disjoint (S.neighborhood b Y) target

theorem homogeneousFinite_mono {target : Set S.Point} {X Y : S.Point}
    {q : S.FiniteApprox} (h : HomogeneousFinite target Y q)
    (hXY : S.le X Y) :
    HomogeneousFinite target X q := by
  rcases q with ⟨m, b⟩
  simp only [HomogeneousFinite] at h ⊢
  rcases h with hsub | hdis
  · exact Or.inl ((S.neighborhood_mono hXY).trans hsub)
  · apply Or.inr
    rw [Set.disjoint_left] at hdis ⊢
    intro Z hZX hZt
    exact hdis (S.neighborhood_mono hXY hZX) hZt

/-- Finitely many approximations of one protected depth can simultaneously be
made homogeneous for one Ramsey target. -/
theorem exists_refinement_homogeneous_finite
    (R : AbstractRamseySpace S) {target : Set S.Point}
    (hRamsey : IsRamsey R target)
    (t : Set S.FiniteApprox) (ht : t.Finite)
    {Y : S.Point} {d : ℕ}
    (hdepth : t ⊆ R.fin.depthApproximations Y d) :
    ∃ X, X ∈ S.levelNeighborhood d Y ∧
      ∀ q ∈ t, HomogeneousFinite target X q := by
  induction t, ht using Set.Finite.induction_on generalizing Y with
  | empty =>
      refine ⟨Y, S.self_mem_levelNeighborhood d Y, ?_⟩
      simp
  | @insert q t hqt ht ih =>
      have htdepth : t ⊆ R.fin.depthApproximations Y d := by
        intro p hp
        exact hdepth (by simp [hp])
      rcases ih htdepth with ⟨X, hXY, hhomX⟩
      have hqdepthSigma : q ∈ R.fin.depthApproximations Y d :=
        hdepth (by simp)
      rcases q with ⟨m, b⟩
      have hqdepthY : R.fin.HasDepth b Y d :=
        (R.fin.mem_depthApproximations).1 hqdepthSigma
      have hqdepthX : R.fin.HasDepth b X d :=
        (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hqdepthY
      rcases hRamsey b X hqdepthX with ⟨Z, hZX, hhomZ⟩
      have hZY : Z ∈ S.levelNeighborhood d Y :=
        S.levelNeighborhood_mono hXY hZX
      refine ⟨Z, hZY, ?_⟩
      intro p hp
      rcases Set.mem_insert_iff.mp hp with hp | hp
      · subst p
        simpa [HomogeneousFinite] using hhomZ
      · exact homogeneousFinite_mono (hhomX p hp) hZX.1

/-- Simultaneously homogenize a finite depth layer for targets 0,...,k. -/
theorem exists_refinement_homogeneous_upTo
    (R : AbstractRamseySpace S)
    (targets : ℕ → Set S.Point)
    (hRamsey : ∀ i, IsRamsey R (targets i))
    (t : Set S.FiniteApprox) (ht : t.Finite)
    {Y : S.Point} {d : ℕ}
    (hdepth : t ⊆ R.fin.depthApproximations Y d)
    (k : ℕ) :
    ∃ X, X ∈ S.levelNeighborhood d Y ∧
      ∀ i, i ≤ k → ∀ q ∈ t, HomogeneousFinite (targets i) X q := by
  induction k generalizing Y with
  | zero =>
      rcases exists_refinement_homogeneous_finite R (hRamsey 0) t ht hdepth with
        ⟨X, hXY, hhom⟩
      refine ⟨X, hXY, ?_⟩
      intro i hi q hq
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      exact hhom q hq
  | succ k ih =>
      rcases ih hdepth with ⟨X, hXY, hhomX⟩
      have hdepthX : t ⊆ R.fin.depthApproximations X d := by
        intro q hq
        rcases q with ⟨m, b⟩
        have hdY : R.fin.HasDepth b Y d :=
          (R.fin.mem_depthApproximations).1 (hdepth hq)
        have hdX : R.fin.HasDepth b X d :=
          (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hdY
        exact (R.fin.mem_depthApproximations).2 hdX
      rcases exists_refinement_homogeneous_finite
          R (hRamsey (k + 1)) t ht hdepthX with
        ⟨Z, hZX, hhomZ⟩
      have hZY : Z ∈ S.levelNeighborhood d Y :=
        S.levelNeighborhood_mono hXY hZX
      refine ⟨Z, hZY, ?_⟩
      intro i hi q hq
      by_cases hik : i ≤ k
      · exact homogeneousFinite_mono (hhomX i hik q hq) hZX.1
      · have hiEq : i = k + 1 := by omega
        subst i
        exact hhomZ q hq

/-- Homogenize the whole finite layer of approximations of depth d. -/
theorem exists_refinement_homogeneous_stage
    (R : AbstractRamseySpace S)
    (targets : ℕ → Set S.Point)
    (hRamsey : ∀ i, IsRamsey R (targets i))
    (Y : S.Point) (d k : ℕ) :
    ∃ X, X ∈ S.levelNeighborhood d Y ∧
      ∀ i, i ≤ k →
        ∀ q ∈ R.fin.depthApproximations Y d,
          HomogeneousFinite (targets i) X q := by
  exact exists_refinement_homogeneous_upTo R targets hRamsey
    (R.fin.depthApproximations Y d)
    (R.fin.depthApproximations_finite Y d)
    (fun _ h => h) k

/-- Canonical stage of the countable-union fusion. -/
noncomputable def unionStep
    (R : AbstractRamseySpace S)
    (targets : ℕ → Set S.Point)
    (hRamsey : ∀ i, IsRamsey R (targets i))
    (k d : ℕ) (Y : S.Point) : S.Point :=
  Classical.choose
    (exists_refinement_homogeneous_stage R targets hRamsey Y d k)

theorem unionStep_mem
    (R : AbstractRamseySpace S)
    (targets : ℕ → Set S.Point)
    (hRamsey : ∀ i, IsRamsey R (targets i))
    (k d : ℕ) (Y : S.Point) :
    unionStep R targets hRamsey k d Y ∈ S.levelNeighborhood d Y :=
  (Classical.choose_spec
    (exists_refinement_homogeneous_stage R targets hRamsey Y d k)).1

theorem unionStep_homogeneous
    (R : AbstractRamseySpace S)
    (targets : ℕ → Set S.Point)
    (hRamsey : ∀ i, IsRamsey R (targets i))
    (k d : ℕ) (Y : S.Point)
    {i : ℕ} (hi : i ≤ k) {q : S.FiniteApprox}
    (hq : q ∈ R.fin.depthApproximations Y d) :
    HomogeneousFinite (targets i)
      (unionStep R targets hRamsey k d Y) q :=
  (Classical.choose_spec
    (exists_refinement_homogeneous_stage R targets hRamsey Y d k)).2
      i hi q hq

/-- Fusion used for closure of Ramsey sets under countable unions. -/
noncomputable def unionFusion
    (R : AbstractRamseySpace S)
    (targets : ℕ → Set S.Point)
    (hRamsey : ∀ i, IsRamsey R (targets i))
    (n0 : ℕ) (Y0 : S.Point) : ℕ → S.Point
  | 0 => Y0
  | k + 1 =>
      unionStep R targets hRamsey k (n0 + k)
        (unionFusion R targets hRamsey n0 Y0 k)

theorem unionFusion_isFusion
    (R : AbstractRamseySpace S)
    (targets : ℕ → Set S.Point)
    (hRamsey : ∀ i, IsRamsey R (targets i))
    (n0 : ℕ) (Y0 : S.Point) :
    S.IsFusionFrom n0 (unionFusion R targets hRamsey n0 Y0) := by
  intro k
  simpa [unionFusion] using
    unionStep_mem R targets hRamsey k (n0 + k)
      (unionFusion R targets hRamsey n0 Y0 k)

theorem unionFusion_le_start
    (R : AbstractRamseySpace S)
    (targets : ℕ → Set S.Point)
    (hRamsey : ∀ i, IsRamsey R (targets i))
    (n0 : ℕ) (Y0 : S.Point) (k : ℕ) :
    S.le (unionFusion R targets hRamsey n0 Y0 k) Y0 := by
  have hf := unionFusion_isFusion R targets hRamsey n0 Y0
  simpa [unionFusion] using
    S.fusion_le hf (Nat.zero_le k)

theorem unionFusion_succ_homogeneous
    (R : AbstractRamseySpace S)
    (targets : ℕ → Set S.Point)
    (hRamsey : ∀ i, IsRamsey R (targets i))
    (n0 : ℕ) (Y0 : S.Point) (k : ℕ)
    {i : ℕ} (hi : i ≤ k) {q : S.FiniteApprox}
    (hq : q ∈ R.fin.depthApproximations
      (unionFusion R targets hRamsey n0 Y0 k) (n0 + k)) :
    HomogeneousFinite (targets i)
      (unionFusion R targets hRamsey n0 Y0 (k + 1)) q := by
  simpa [unionFusion] using
    unionStep_homogeneous R targets hRamsey k (n0 + k)
      (unionFusion R targets hRamsey n0 Y0 k) hi hq

/-- Todorčević Lemma 4.37: Ramsey sets are closed under countable unions. -/
theorem isRamsey_iUnion
    (R : AbstractRamseySpace S) (C : FusionComplete S)
    (targets : ℕ → Set S.Point)
    (hRamsey : ∀ i, IsRamsey R (targets i)) :
    IsRamsey R (⋃ i, targets i) := by
  intro n a Y d hd
  let U : Set S.Point := ⋃ i, targets i

  rcases exists_global_decider R C U d Y with
    ⟨X, hXY, hdecX⟩
  have hdX : R.fin.HasDepth a X d :=
    (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hd
  have hdecA : Decides R U X a :=
    hdecX a hdX le_rfl

  rcases hdecA with hacc | hrej
  · have hsub : S.neighborhood a X ⊆ U := by
      simpa [Accepts] using hacc
    refine ⟨X, hXY, Or.inl ?_⟩
    simpa [U] using hsub
  · rcases exists_refinement_rejects_endExtensions R C hdX hdecX hrej with
      ⟨Y0, hY0X, hrejectAll⟩
    have hY0Y : Y0 ∈ S.levelNeighborhood d Y :=
      S.levelNeighborhood_mono hXY hY0X

    let Ys := unionFusion R targets hRamsey d Y0
    have hfusion : S.IsFusionFrom d Ys := by
      simpa [Ys] using unionFusion_isFusion R targets hRamsey d Y0
    rcases C.exists_limit hfusion with ⟨Z, hZ⟩

    have hZY0 : Z ∈ S.levelNeighborhood d Y0 := by
      simpa [Ys, unionFusion] using hZ 0
    have hZY : Z ∈ S.levelNeighborhood d Y :=
      S.levelNeighborhood_mono hY0Y hZY0

    refine ⟨Z, hZY, Or.inr ?_⟩
    rw [Set.disjoint_left]
    intro A hAaZ hAU
    rcases Set.mem_iUnion.mp hAU with ⟨i, hAi⟩

    rcases R.fin.exists_hasDepth_ge_of_le hAaZ.1 n (d + i) with
      ⟨l, e, hnl, hde, hdepthZ⟩
    have hde0 : d ≤ e := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hde0
    have hik : i ≤ k := by omega

    let b : S.Approx l := S.approx l A
    have hab : S.IsInitial a b :=
      ⟨hnl, A, hAaZ.2, rfl⟩
    have hZk : Z ∈ S.levelNeighborhood (d + k) (Ys k) :=
      hZ k
    have hdepthYk : R.fin.HasDepth b (Ys k) (d + k) :=
      (R.fin.hasDepth_iff_of_mem_levelNeighborhood hZk).1 hdepthZ
    have hq :
        (⟨l, b⟩ : S.FiniteApprox) ∈
          R.fin.depthApproximations (Ys k) (d + k) :=
      (R.fin.mem_depthApproximations).2 hdepthYk

    have hhom :
        HomogeneousFinite (targets i) (Ys (k + 1))
          (⟨l, b⟩ : S.FiniteApprox) := by
      simpa [Ys] using
        unionFusion_succ_homogeneous R targets hRamsey d Y0 k hik hq

    have hAstage : A ∈ S.neighborhood b (Ys (k + 1)) :=
      ⟨S.le_trans hAaZ.1 (hZ (k + 1)).1, rfl⟩

    have hstageY0 : S.le (Ys (k + 1)) Y0 := by
      simpa [Ys] using
        unionFusion_le_start R targets hRamsey d Y0 (k + 1)
    have hneBY0 : (S.neighborhood b Y0).Nonempty :=
      ⟨A, S.neighborhood_mono hstageY0 hAstage⟩
    have hrejY0 : Rejects R U Y0 b :=
      hrejectAll b hab hneBY0
    have hrejStage : Rejects R U (Ys (k + 1)) b :=
      rejects_mono R hrejY0 hstageY0 ⟨A, hAstage⟩

    simp only [HomogeneousFinite] at hhom
    rcases hhom with hsubi | hdisi
    · have haccStage : Accepts U (Ys (k + 1)) b := by
        unfold Accepts
        intro W hW
        have hWi : W ∈ targets i := hsubi hW
        exact Set.mem_iUnion.2 ⟨i, hWi⟩
      exact (Rejects.not_accepts R hrejStage) haccStage
    · exact Set.disjoint_left.1 hdisi hAstage hAi

end CombinatorialForcing
end RamseySpace
