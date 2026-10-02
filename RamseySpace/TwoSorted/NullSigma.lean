import RamseySpace.TwoSorted.Sigma

/-!
# Countable unions of S-Ramsey-null sets

This is the two-sorted σ-ideal part of Todorčević's Lemma 4.38.
-/

namespace RamseySpace
namespace TwoSorted
namespace CombinatorialForcing

universe uR vR uS vS

variable {P : System.{uR, vR, uS, vS}}

/-- A tagged object approximation avoids a target. -/
def AvoidsFinite (target : Set P.Obj.Point) (Y : P.Red.Point)
    (q : P.Obj.FiniteApprox) : Prop :=
  match q with
  | ⟨_, b⟩ => Disjoint (P.objectNeighborhood b Y) target

theorem avoidsFinite_mono
    (R : AbstractRamseySystem P)
    {target : Set P.Obj.Point} {X Y : P.Red.Point}
    {q : P.Obj.FiniteApprox} (h : AvoidsFinite target Y q)
    (hXY : P.Red.le X Y) :
    AvoidsFinite target X q := by
  rcases q with ⟨m, b⟩
  simp only [AvoidsFinite] at h ⊢
  rw [Set.disjoint_left] at h ⊢
  intro A hAX hAt
  exact h (R.fin.objectNeighborhood_mono hXY hAX) hAt

theorem exists_refinement_avoids_finite
    (R : AbstractRamseySystem P) {target : Set P.Obj.Point}
    (hNull : IsRamseyNull R target)
    (t : Set P.Obj.FiniteApprox) (ht : t.Finite)
    {Y : P.Red.Point} {d : ℕ}
    (hdepth : t ⊆ R.fin.depthApproximations Y d) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ q ∈ t, AvoidsFinite target X q := by
  induction t, ht using Set.Finite.induction_on generalizing Y with
  | empty =>
      refine ⟨Y, P.self_mem_levelNeighborhood d Y, ?_⟩
      simp
  | @insert q t hqt ht ih =>
      have htdepth : t ⊆ R.fin.depthApproximations Y d := by
        intro p hp
        exact hdepth (by simp [hp])
      rcases ih htdepth with ⟨X, hXY, havoidX⟩
      have hqdepthSigma : q ∈ R.fin.depthApproximations Y d :=
        hdepth (by simp)
      rcases q with ⟨m, b⟩
      have hqdepthY : R.fin.HasDepth b Y d :=
        (R.fin.mem_depthApproximations).1 hqdepthSigma
      have hqdepthX : R.fin.HasDepth b X d :=
        (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hqdepthY
      rcases hNull b X hqdepthX with ⟨Z, hZX, hdisZ⟩
      have hZY : Z ∈ P.levelNeighborhood d Y :=
        P.levelNeighborhood_mono hXY hZX
      refine ⟨Z, hZY, ?_⟩
      intro p hp
      rcases Set.mem_insert_iff.mp hp with hp | hp
      · subst p
        simpa [AvoidsFinite] using hdisZ
      · exact avoidsFinite_mono R (havoidX p hp) hZX.1

theorem exists_refinement_avoids_upTo
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNull R (targets i))
    (t : Set P.Obj.FiniteApprox) (ht : t.Finite)
    {Y : P.Red.Point} {d : ℕ}
    (hdepth : t ⊆ R.fin.depthApproximations Y d)
    (k : ℕ) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ i, i ≤ k → ∀ q ∈ t, AvoidsFinite (targets i) X q := by
  induction k generalizing Y with
  | zero =>
      rcases exists_refinement_avoids_finite
          R (hNull 0) t ht hdepth with ⟨X, hXY, havoid⟩
      refine ⟨X, hXY, ?_⟩
      intro i hi q hq
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      exact havoid q hq
  | succ k ih =>
      rcases ih hdepth with ⟨X, hXY, havoidX⟩
      have hdepthX : t ⊆ R.fin.depthApproximations X d := by
        intro q hq
        rcases q with ⟨m, b⟩
        have hdY : R.fin.HasDepth b Y d :=
          (R.fin.mem_depthApproximations).1 (hdepth hq)
        have hdX : R.fin.HasDepth b X d :=
          (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hdY
        exact (R.fin.mem_depthApproximations).2 hdX
      rcases exists_refinement_avoids_finite
          R (hNull (k + 1)) t ht hdepthX with
        ⟨Z, hZX, havoidZ⟩
      have hZY : Z ∈ P.levelNeighborhood d Y :=
        P.levelNeighborhood_mono hXY hZX
      refine ⟨Z, hZY, ?_⟩
      intro i hi q hq
      by_cases hik : i ≤ k
      · exact avoidsFinite_mono R (havoidX i hik q hq) hZX.1
      · have hiEq : i = k + 1 := by omega
        subst i
        exact havoidZ q hq

theorem exists_refinement_avoids_stage
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNull R (targets i))
    (Y : P.Red.Point) (d k : ℕ) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ i, i ≤ k →
        ∀ q ∈ R.fin.depthApproximations Y d,
          AvoidsFinite (targets i) X q :=
  exists_refinement_avoids_upTo R targets hNull
    (R.fin.depthApproximations Y d)
    (R.fin.depthApproximations_finite Y d)
    (fun _ h => h) k

noncomputable def nullStep
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNull R (targets i))
    (k d : ℕ) (Y : P.Red.Point) : P.Red.Point :=
  Classical.choose
    (exists_refinement_avoids_stage R targets hNull Y d k)

theorem nullStep_mem
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNull R (targets i))
    (k d : ℕ) (Y : P.Red.Point) :
    nullStep R targets hNull k d Y ∈ P.levelNeighborhood d Y :=
  (Classical.choose_spec
    (exists_refinement_avoids_stage R targets hNull Y d k)).1

theorem nullStep_avoids
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNull R (targets i))
    (k d : ℕ) (Y : P.Red.Point)
    {i : ℕ} (hi : i ≤ k) {q : P.Obj.FiniteApprox}
    (hq : q ∈ R.fin.depthApproximations Y d) :
    AvoidsFinite (targets i) (nullStep R targets hNull k d Y) q :=
  (Classical.choose_spec
    (exists_refinement_avoids_stage R targets hNull Y d k)).2
      i hi q hq

noncomputable def nullFusion
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNull R (targets i))
    (n0 : ℕ) (Y0 : P.Red.Point) : ℕ → P.Red.Point
  | 0 => Y0
  | k + 1 =>
      nullStep R targets hNull k (n0 + k)
        (nullFusion R targets hNull n0 Y0 k)

theorem nullFusion_isFusion
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNull R (targets i))
    (n0 : ℕ) (Y0 : P.Red.Point) :
    P.Red.IsFusionFrom n0 (nullFusion R targets hNull n0 Y0) := by
  intro k
  simpa [nullFusion] using
    nullStep_mem R targets hNull k (n0 + k)
      (nullFusion R targets hNull n0 Y0 k)

theorem nullFusion_succ_avoids
    (R : AbstractRamseySystem P)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNull R (targets i))
    (n0 : ℕ) (Y0 : P.Red.Point) (k : ℕ)
    {i : ℕ} (hi : i ≤ k) {q : P.Obj.FiniteApprox}
    (hq : q ∈ R.fin.depthApproximations
      (nullFusion R targets hNull n0 Y0 k) (n0 + k)) :
    AvoidsFinite (targets i)
      (nullFusion R targets hNull n0 Y0 (k + 1)) q := by
  simpa [nullFusion] using
    nullStep_avoids R targets hNull k (n0 + k)
      (nullFusion R targets hNull n0 Y0 k) hi hq

/-- S-Ramsey-null sets form a σ-ideal. -/
theorem isRamseyNull_iUnion
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNull R (targets i)) :
    IsRamseyNull R (⋃ i, targets i) := by
  intro n a Y d hd
  let Ys := nullFusion R targets hNull d Y
  have hfusion : P.Red.IsFusionFrom d Ys := by
    simpa [Ys] using nullFusion_isFusion R targets hNull d Y
  rcases C.exists_limit hfusion with ⟨Z, hZ⟩
  have hZY : Z ∈ P.levelNeighborhood d Y := by
    simpa [Ys, nullFusion] using hZ 0
  refine ⟨Z, hZY, ?_⟩
  rw [Set.disjoint_left]
  intro A hAaZ hAU
  rcases Set.mem_iUnion.mp hAU with ⟨i, hAi⟩

  rcases R.fin.exists_hasDepth_ge_of_le0 hAaZ.1 n (d + i) with
    ⟨l, e, hnl, hde, hdepthZ⟩
  have hde0 : d ≤ e := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hde0
  have hik : i ≤ k := by omega

  let b : P.Obj.Approx l := P.Obj.approx l A
  have hZk : Z ∈ P.levelNeighborhood (d + k) (Ys k) := hZ k
  have hdepthYk : R.fin.HasDepth b (Ys k) (d + k) :=
    (R.fin.hasDepth_iff_of_mem_levelNeighborhood hZk).1 hdepthZ
  have hq :
      (⟨l, b⟩ : P.Obj.FiniteApprox) ∈
        R.fin.depthApproximations (Ys k) (d + k) :=
    (R.fin.mem_depthApproximations).2 hdepthYk
  have havoid :
      AvoidsFinite (targets i) (Ys (k + 1))
        (⟨l, b⟩ : P.Obj.FiniteApprox) := by
    simpa [Ys] using
      nullFusion_succ_avoids R targets hNull d Y k hik hq
  have hAstage : A ∈ P.objectNeighborhood b (Ys (k + 1)) := by
    constructor
    · exact R.fin.le0_trans hAaZ.1 (hZ (k + 1)).1
    · rfl
  simp only [AvoidsFinite] at havoid
  exact Set.disjoint_left.1 havoid hAstage hAi

end CombinatorialForcing
end TwoSorted
end RamseySpace
