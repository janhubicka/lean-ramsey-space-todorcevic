import RamseySpace.TwoSorted.Relative
import RamseySpace.TwoSorted.Sigma
import RamseySpace.TwoSorted.NullSigma

/-!
# Relative σ-field and σ-ideal closure

Countable-union closure inside `S(≤ bound)`.  These are the local versions
of Lemmas 4.37 and 4.38 used explicitly in Todorčević's proof of Souslin
closure.
-/

namespace RamseySpace
namespace TwoSorted
namespace CombinatorialForcing

universe uR vR uS vS

variable {P : System.{uR, vR, uS, vS}}

/-- Finitely homogenize one local Ramsey target while staying below the
fixed bound. -/
theorem exists_refinement_homogeneous_finite_below
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    {target : Set P.Obj.Point}
    (hRamsey : IsRamseyBelow R bound target)
    (t : Set P.Obj.FiniteApprox) (ht : t.Finite)
    {Y : P.Red.Point} {d : ℕ} (hY : P.Red.le Y bound)
    (hdepth : t ⊆ R.fin.depthApproximations Y d) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ q ∈ t, HomogeneousFinite target X q := by
  induction t, ht using Set.Finite.induction_on generalizing Y with
  | empty =>
      exact ⟨Y, P.self_mem_levelNeighborhood d Y, by simp⟩
  | @insert q t hqt ht ih =>
      have htdepth : t ⊆ R.fin.depthApproximations Y d := by
        intro p hp
        exact hdepth (by simp [hp])
      rcases ih hY htdepth with ⟨X, hXY, hhomX⟩
      have hXbound : P.Red.le X bound := P.Red.le_trans hXY.1 hY
      have hqdepthSigma : q ∈ R.fin.depthApproximations Y d :=
        hdepth (by simp)
      rcases q with ⟨m, b⟩
      have hqdepthY : R.fin.HasDepth b Y d :=
        (R.fin.mem_depthApproximations).1 hqdepthSigma
      have hqdepthX : R.fin.HasDepth b X d :=
        (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hqdepthY
      rcases hRamsey b X hXbound hqdepthX with ⟨Z, hZX, hhomZ⟩
      have hZY : Z ∈ P.levelNeighborhood d Y :=
        P.levelNeighborhood_mono hXY hZX
      refine ⟨Z, hZY, ?_⟩
      intro p hp
      rcases Set.mem_insert_iff.mp hp with hp | hp
      · subst p
        simpa [HomogeneousFinite] using hhomZ
      · exact homogeneousFinite_mono R (hhomX p hp) hZX.1

theorem exists_refinement_homogeneous_upTo_below
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hRamsey : ∀ i, IsRamseyBelow R bound (targets i))
    (t : Set P.Obj.FiniteApprox) (ht : t.Finite)
    {Y : P.Red.Point} {d : ℕ} (hY : P.Red.le Y bound)
    (hdepth : t ⊆ R.fin.depthApproximations Y d)
    (k : ℕ) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ i, i ≤ k → ∀ q ∈ t, HomogeneousFinite (targets i) X q := by
  induction k generalizing Y with
  | zero =>
      rcases exists_refinement_homogeneous_finite_below
          R bound (hRamsey 0) t ht hY hdepth with ⟨X, hXY, hhom⟩
      exact ⟨X, hXY, fun i hi q hq => by
        have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
        subst i
        exact hhom q hq⟩
  | succ k ih =>
      rcases ih hY hdepth with ⟨X, hXY, hhomX⟩
      have hXbound : P.Red.le X bound := P.Red.le_trans hXY.1 hY
      have hdepthX : t ⊆ R.fin.depthApproximations X d := by
        intro q hq
        rcases q with ⟨m, b⟩
        have hdY : R.fin.HasDepth b Y d :=
          (R.fin.mem_depthApproximations).1 (hdepth hq)
        have hdX : R.fin.HasDepth b X d :=
          (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hdY
        exact (R.fin.mem_depthApproximations).2 hdX
      rcases exists_refinement_homogeneous_finite_below
          R bound (hRamsey (k + 1)) t ht hXbound hdepthX with
        ⟨Z, hZX, hhomZ⟩
      have hZY : Z ∈ P.levelNeighborhood d Y :=
        P.levelNeighborhood_mono hXY hZX
      refine ⟨Z, hZY, ?_⟩
      intro i hi q hq
      by_cases hik : i ≤ k
      · exact homogeneousFinite_mono R (hhomX i hik q hq) hZX.1
      · have hiEq : i = k + 1 := by omega
        subst i
        exact hhomZ q hq

theorem exists_refinement_homogeneous_stage_below
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hRamsey : ∀ i, IsRamseyBelow R bound (targets i))
    {Y : P.Red.Point} (hY : P.Red.le Y bound) (d k : ℕ) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ i, i ≤ k →
        ∀ q ∈ R.fin.depthApproximations Y d,
          HomogeneousFinite (targets i) X q :=
  exists_refinement_homogeneous_upTo_below R bound targets hRamsey
    (R.fin.depthApproximations Y d)
    (R.fin.depthApproximations_finite Y d)
    hY (fun _ h => h) k

/-- One local countable-union fusion step.  Outside the cone below `bound`
we return the input; the actual fusion always stays in the cone. -/
noncomputable def unionStepBelow
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hRamsey : ∀ i, IsRamseyBelow R bound (targets i))
    (k d : ℕ) (Y : P.Red.Point) : P.Red.Point :=
  if hY : P.Red.le Y bound then
    Classical.choose
      (exists_refinement_homogeneous_stage_below
        R bound targets hRamsey hY d k)
  else Y

theorem unionStepBelow_mem
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hRamsey : ∀ i, IsRamseyBelow R bound (targets i))
    (k d : ℕ) {Y : P.Red.Point} (hY : P.Red.le Y bound) :
    unionStepBelow R bound targets hRamsey k d Y ∈
      P.levelNeighborhood d Y := by
  simp only [unionStepBelow, dif_pos hY]
  exact
    (Classical.choose_spec
      (exists_refinement_homogeneous_stage_below
        R bound targets hRamsey hY d k)).1

theorem unionStepBelow_homogeneous
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hRamsey : ∀ i, IsRamseyBelow R bound (targets i))
    (k d : ℕ) {Y : P.Red.Point} (hY : P.Red.le Y bound)
    {i : ℕ} (hi : i ≤ k) {q : P.Obj.FiniteApprox}
    (hq : q ∈ R.fin.depthApproximations Y d) :
    HomogeneousFinite (targets i)
      (unionStepBelow R bound targets hRamsey k d Y) q := by
  simp only [unionStepBelow, dif_pos hY]
  exact
    (Classical.choose_spec
      (exists_refinement_homogeneous_stage_below
        R bound targets hRamsey hY d k)).2 i hi q hq

noncomputable def unionFusionBelow
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hRamsey : ∀ i, IsRamseyBelow R bound (targets i))
    (n0 : ℕ) (Y0 : P.Red.Point) : ℕ → P.Red.Point
  | 0 => Y0
  | k + 1 =>
      unionStepBelow R bound targets hRamsey k (n0 + k)
        (unionFusionBelow R bound targets hRamsey n0 Y0 k)

theorem unionFusionBelow_le_bound
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hRamsey : ∀ i, IsRamseyBelow R bound (targets i))
    (n0 : ℕ) {Y0 : P.Red.Point} (hY0 : P.Red.le Y0 bound) :
    ∀ k, P.Red.le
      (unionFusionBelow R bound targets hRamsey n0 Y0 k) bound := by
  intro k
  induction k with
  | zero => exact hY0
  | succ k ih =>
      have hstep :=
        unionStepBelow_mem R bound targets hRamsey k (n0 + k) ih
      exact P.Red.le_trans hstep.1 ih

theorem unionFusionBelow_isFusion
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hRamsey : ∀ i, IsRamseyBelow R bound (targets i))
    (n0 : ℕ) {Y0 : P.Red.Point} (hY0 : P.Red.le Y0 bound) :
    P.Red.IsFusionFrom n0
      (unionFusionBelow R bound targets hRamsey n0 Y0) := by
  intro k
  simpa [unionFusionBelow] using
    unionStepBelow_mem R bound targets hRamsey k (n0 + k)
      (unionFusionBelow_le_bound R bound targets hRamsey n0 hY0 k)

theorem unionFusionBelow_le_start
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hRamsey : ∀ i, IsRamseyBelow R bound (targets i))
    (n0 : ℕ) (Y0 : P.Red.Point) (k : ℕ) :
    P.Red.le (unionFusionBelow R bound targets hRamsey n0 Y0 k) Y0 := by
  induction k with
  | zero => simpa [unionFusionBelow] using P.Red.le_refl Y0
  | succ k ih =>
      by_cases hY : P.Red.le
          (unionFusionBelow R bound targets hRamsey n0 Y0 k) bound
      · have hstep :=
          unionStepBelow_mem R bound targets hRamsey k (n0 + k) hY
        exact P.Red.le_trans (by simpa [unionFusionBelow] using hstep.1) ih
      · simp [unionFusionBelow, unionStepBelow, hY, ih]

theorem unionFusionBelow_succ_homogeneous
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hRamsey : ∀ i, IsRamseyBelow R bound (targets i))
    (n0 : ℕ) {Y0 : P.Red.Point} (hY0 : P.Red.le Y0 bound) (k : ℕ)
    {i : ℕ} (hi : i ≤ k) {q : P.Obj.FiniteApprox}
    (hq : q ∈ R.fin.depthApproximations
      (unionFusionBelow R bound targets hRamsey n0 Y0 k) (n0 + k)) :
    HomogeneousFinite (targets i)
      (unionFusionBelow R bound targets hRamsey n0 Y0 (k + 1)) q := by
  have hY :=
    unionFusionBelow_le_bound R bound targets hRamsey n0 hY0 k
  simpa [unionFusionBelow] using
    unionStepBelow_homogeneous R bound targets hRamsey k (n0 + k)
      hY hi hq

/-- Relative Lemma 4.37. -/
theorem isRamseyBelow_iUnion
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hRamsey : ∀ i, IsRamseyBelow R bound (targets i)) :
    IsRamseyBelow R bound (⋃ i, targets i) := by
  intro n a Y d hYbound hd
  let U : Set P.Obj.Point := ⋃ i, targets i

  rcases exists_global_decider R C U d Y with ⟨X, hXY, hdecX⟩
  have hXbound : P.Red.le X bound := P.Red.le_trans hXY.1 hYbound
  have hdX : R.fin.HasDepth a X d :=
    (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hd
  have hdecA : Decides R U X a := hdecX a hdX le_rfl
  rcases hdecA with hacc | hrej
  · refine ⟨X, hXY, Or.inl ?_⟩
    simpa [U, Accepts] using hacc
  · rcases exists_refinement_rejects_endExtensions R C hdX hdecX hrej with
      ⟨Y0, hY0X, hrejectAll⟩
    have hY0Y : Y0 ∈ P.levelNeighborhood d Y :=
      P.levelNeighborhood_mono hXY hY0X
    have hY0bound : P.Red.le Y0 bound :=
      P.Red.le_trans hY0Y.1 hYbound

    let Ys := unionFusionBelow R bound targets hRamsey d Y0
    have hfusion : P.Red.IsFusionFrom d Ys := by
      simpa [Ys] using
        unionFusionBelow_isFusion R bound targets hRamsey d hY0bound
    rcases C.exists_limit hfusion with ⟨Z, hZ⟩

    have hZY0 : Z ∈ P.levelNeighborhood d Y0 := by
      simpa [Ys, unionFusionBelow] using hZ 0
    have hZY : Z ∈ P.levelNeighborhood d Y :=
      P.levelNeighborhood_mono hY0Y hZY0

    refine ⟨Z, hZY, Or.inr ?_⟩
    rw [Set.disjoint_left]
    intro A hAaZ hAU
    rcases Set.mem_iUnion.mp hAU with ⟨i, hAi⟩

    rcases R.fin.exists_hasDepth_ge_of_le0 hAaZ.1 n (d + i) with
      ⟨l, e, hnl, hde, hdepthZ⟩
    have hde0 : d ≤ e := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hde0
    have hik : i ≤ k := by omega

    let b : P.Obj.Approx l := P.Obj.approx l A
    have hab : P.Obj.IsInitial a b := ⟨hnl, A, hAaZ.2, rfl⟩
    have hZk : Z ∈ P.levelNeighborhood (d + k) (Ys k) := hZ k
    have hdepthYk : R.fin.HasDepth b (Ys k) (d + k) :=
      (R.fin.hasDepth_iff_of_mem_levelNeighborhood hZk).1 hdepthZ
    have hq :
        (⟨l, b⟩ : P.Obj.FiniteApprox) ∈
          R.fin.depthApproximations (Ys k) (d + k) :=
      (R.fin.mem_depthApproximations).2 hdepthYk
    have hhom :
        HomogeneousFinite (targets i) (Ys (k + 1))
          (⟨l, b⟩ : P.Obj.FiniteApprox) := by
      simpa [Ys] using
        unionFusionBelow_succ_homogeneous
          R bound targets hRamsey d hY0bound k hik hq

    have hAstage : A ∈ P.objectNeighborhood b (Ys (k + 1)) := by
      exact ⟨R.fin.le0_trans hAaZ.1 (hZ (k + 1)).1, rfl⟩
    have hstageY0 : P.Red.le (Ys (k + 1)) Y0 := by
      simpa [Ys] using
        unionFusionBelow_le_start R bound targets hRamsey d Y0 (k + 1)
    have hneBY0 : (P.objectNeighborhood b Y0).Nonempty :=
      ⟨A, R.fin.objectNeighborhood_mono hstageY0 hAstage⟩
    have hrejY0 : Rejects R U Y0 b := hrejectAll b hab hneBY0
    have hrejStage : Rejects R U (Ys (k + 1)) b :=
      rejects_mono R hrejY0 hstageY0 ⟨A, hAstage⟩

    simp only [HomogeneousFinite] at hhom
    rcases hhom with hsubi | hdisi
    · have haccStage : Accepts U (Ys (k + 1)) b := by
        intro W hW
        exact Set.mem_iUnion.2 ⟨i, hsubi hW⟩
      exact (Rejects.not_accepts R hrejStage) haccStage
    · exact Set.disjoint_left.1 hdisi hAstage hAi

/-- Finitely avoid one local null target. -/
theorem exists_refinement_avoids_finite_below
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    {target : Set P.Obj.Point}
    (hNull : IsRamseyNullBelow R bound target)
    (t : Set P.Obj.FiniteApprox) (ht : t.Finite)
    {Y : P.Red.Point} {d : ℕ} (hY : P.Red.le Y bound)
    (hdepth : t ⊆ R.fin.depthApproximations Y d) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ q ∈ t, AvoidsFinite target X q := by
  induction t, ht using Set.Finite.induction_on generalizing Y with
  | empty => exact ⟨Y, P.self_mem_levelNeighborhood d Y, by simp⟩
  | @insert q t hqt ht ih =>
      have htdepth : t ⊆ R.fin.depthApproximations Y d := by
        intro p hp
        exact hdepth (by simp [hp])
      rcases ih hY htdepth with ⟨X, hXY, havoidX⟩
      have hXbound : P.Red.le X bound := P.Red.le_trans hXY.1 hY
      have hqdepthSigma : q ∈ R.fin.depthApproximations Y d :=
        hdepth (by simp)
      rcases q with ⟨m, b⟩
      have hqdepthY : R.fin.HasDepth b Y d :=
        (R.fin.mem_depthApproximations).1 hqdepthSigma
      have hqdepthX : R.fin.HasDepth b X d :=
        (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hqdepthY
      rcases hNull b X hXbound hqdepthX with ⟨Z, hZX, hdisZ⟩
      have hZY : Z ∈ P.levelNeighborhood d Y :=
        P.levelNeighborhood_mono hXY hZX
      refine ⟨Z, hZY, ?_⟩
      intro p hp
      rcases Set.mem_insert_iff.mp hp with hp | hp
      · subst p
        simpa [AvoidsFinite] using hdisZ
      · exact avoidsFinite_mono R (havoidX p hp) hZX.1

theorem exists_refinement_avoids_upTo_below
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNullBelow R bound (targets i))
    (t : Set P.Obj.FiniteApprox) (ht : t.Finite)
    {Y : P.Red.Point} {d : ℕ} (hY : P.Red.le Y bound)
    (hdepth : t ⊆ R.fin.depthApproximations Y d)
    (k : ℕ) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ i, i ≤ k → ∀ q ∈ t, AvoidsFinite (targets i) X q := by
  induction k generalizing Y with
  | zero =>
      rcases exists_refinement_avoids_finite_below
          R bound (hNull 0) t ht hY hdepth with ⟨X, hXY, havoid⟩
      exact ⟨X, hXY, fun i hi q hq => by
        have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
        subst i
        exact havoid q hq⟩
  | succ k ih =>
      rcases ih hY hdepth with ⟨X, hXY, havoidX⟩
      have hXbound : P.Red.le X bound := P.Red.le_trans hXY.1 hY
      have hdepthX : t ⊆ R.fin.depthApproximations X d := by
        intro q hq
        rcases q with ⟨m, b⟩
        have hdY : R.fin.HasDepth b Y d :=
          (R.fin.mem_depthApproximations).1 (hdepth hq)
        have hdX : R.fin.HasDepth b X d :=
          (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hdY
        exact (R.fin.mem_depthApproximations).2 hdX
      rcases exists_refinement_avoids_finite_below
          R bound (hNull (k + 1)) t ht hXbound hdepthX with
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

theorem exists_refinement_avoids_stage_below
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNullBelow R bound (targets i))
    {Y : P.Red.Point} (hY : P.Red.le Y bound) (d k : ℕ) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ i, i ≤ k →
        ∀ q ∈ R.fin.depthApproximations Y d,
          AvoidsFinite (targets i) X q :=
  exists_refinement_avoids_upTo_below R bound targets hNull
    (R.fin.depthApproximations Y d)
    (R.fin.depthApproximations_finite Y d)
    hY (fun _ h => h) k

noncomputable def nullStepBelow
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNullBelow R bound (targets i))
    (k d : ℕ) (Y : P.Red.Point) : P.Red.Point :=
  if hY : P.Red.le Y bound then
    Classical.choose
      (exists_refinement_avoids_stage_below
        R bound targets hNull hY d k)
  else Y

theorem nullStepBelow_mem
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNullBelow R bound (targets i))
    (k d : ℕ) {Y : P.Red.Point} (hY : P.Red.le Y bound) :
    nullStepBelow R bound targets hNull k d Y ∈ P.levelNeighborhood d Y := by
  simp only [nullStepBelow, dif_pos hY]
  exact
    (Classical.choose_spec
      (exists_refinement_avoids_stage_below
        R bound targets hNull hY d k)).1

theorem nullStepBelow_avoids
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNullBelow R bound (targets i))
    (k d : ℕ) {Y : P.Red.Point} (hY : P.Red.le Y bound)
    {i : ℕ} (hi : i ≤ k) {q : P.Obj.FiniteApprox}
    (hq : q ∈ R.fin.depthApproximations Y d) :
    AvoidsFinite (targets i)
      (nullStepBelow R bound targets hNull k d Y) q := by
  simp only [nullStepBelow, dif_pos hY]
  exact
    (Classical.choose_spec
      (exists_refinement_avoids_stage_below
        R bound targets hNull hY d k)).2 i hi q hq

noncomputable def nullFusionBelow
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNullBelow R bound (targets i))
    (n0 : ℕ) (Y0 : P.Red.Point) : ℕ → P.Red.Point
  | 0 => Y0
  | k + 1 =>
      nullStepBelow R bound targets hNull k (n0 + k)
        (nullFusionBelow R bound targets hNull n0 Y0 k)

theorem nullFusionBelow_le_bound
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNullBelow R bound (targets i))
    (n0 : ℕ) {Y0 : P.Red.Point} (hY0 : P.Red.le Y0 bound) :
    ∀ k, P.Red.le
      (nullFusionBelow R bound targets hNull n0 Y0 k) bound := by
  intro k
  induction k with
  | zero => exact hY0
  | succ k ih =>
      have hstep := nullStepBelow_mem R bound targets hNull k (n0 + k) ih
      exact P.Red.le_trans hstep.1 ih

theorem nullFusionBelow_isFusion
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNullBelow R bound (targets i))
    (n0 : ℕ) {Y0 : P.Red.Point} (hY0 : P.Red.le Y0 bound) :
    P.Red.IsFusionFrom n0
      (nullFusionBelow R bound targets hNull n0 Y0) := by
  intro k
  simpa [nullFusionBelow] using
    nullStepBelow_mem R bound targets hNull k (n0 + k)
      (nullFusionBelow_le_bound R bound targets hNull n0 hY0 k)

theorem nullFusionBelow_succ_avoids
    (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNullBelow R bound (targets i))
    (n0 : ℕ) {Y0 : P.Red.Point} (hY0 : P.Red.le Y0 bound) (k : ℕ)
    {i : ℕ} (hi : i ≤ k) {q : P.Obj.FiniteApprox}
    (hq : q ∈ R.fin.depthApproximations
      (nullFusionBelow R bound targets hNull n0 Y0 k) (n0 + k)) :
    AvoidsFinite (targets i)
      (nullFusionBelow R bound targets hNull n0 Y0 (k + 1)) q := by
  have hY := nullFusionBelow_le_bound R bound targets hNull n0 hY0 k
  simpa [nullFusionBelow] using
    nullStepBelow_avoids R bound targets hNull k (n0 + k) hY hi hq

/-- Relative Lemma 4.38: local Ramsey-null sets form a σ-ideal. -/
theorem isRamseyNullBelow_iUnion
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (bound : P.Red.Point)
    (targets : ℕ → Set P.Obj.Point)
    (hNull : ∀ i, IsRamseyNullBelow R bound (targets i)) :
    IsRamseyNullBelow R bound (⋃ i, targets i) := by
  intro n a Y d hYbound hd
  let Ys := nullFusionBelow R bound targets hNull d Y
  have hfusion : P.Red.IsFusionFrom d Ys := by
    simpa [Ys] using
      nullFusionBelow_isFusion R bound targets hNull d hYbound
  rcases C.exists_limit hfusion with ⟨Z, hZ⟩
  have hZY : Z ∈ P.levelNeighborhood d Y := by
    simpa [Ys, nullFusionBelow] using hZ 0
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
      nullFusionBelow_succ_avoids
        R bound targets hNull d hYbound k hik hq
  have hAstage : A ∈ P.objectNeighborhood b (Ys (k + 1)) := by
    exact ⟨R.fin.le0_trans hAaZ.1 (hZ (k + 1)).1, rfl⟩
  simp only [AvoidsFinite] at havoid
  exact Set.disjoint_left.1 havoid hAstage hAi

end CombinatorialForcing
end TwoSorted
end RamseySpace
