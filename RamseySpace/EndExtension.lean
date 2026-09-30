import RamseySpace.Reject

/-!
# Rejection of all end-extensions

This file formalizes Todorčević's Lemma 4.35.  The proof first performs a
finite recursion through the rejected approximations at each protected depth,
then fuses those stages and argues by induction on the length of an
end-extension.
-/

namespace RamseySpace
namespace CombinatorialForcing

universe u v

variable {S : ApproximationSystem.{u, v}}

/-- A tagged finite approximation is rejected by Y together with all of its
one-step extensions compatible with Y. -/
def RejectsOneStepFinite (R : AbstractRamseySpace S) (target : Set S.Point)
    (Y : S.Point) (q : S.FiniteApprox) : Prop :=
  match q with
  | ⟨_, b⟩ =>
      ∀ c, c ∈ S.oneStepApproximations b Y → Rejects R target Y c

/-- Rejected end-extensions of a at one fixed depth. -/
def RejectingExtensionsAtDepth (R : AbstractRamseySpace S)
    (target : Set S.Point) {n : ℕ} (a : S.Approx n)
    (Y : S.Point) (d : ℕ) : Set S.FiniteApprox :=
  {q | q ∈ R.fin.depthApproximations Y d ∧
    match q with
    | ⟨_, b⟩ => S.IsInitial a b ∧ Rejects R target Y b}

theorem rejectingExtensionsAtDepth_finite
    (R : AbstractRamseySpace S) (target : Set S.Point)
    {n : ℕ} (a : S.Approx n) (Y : S.Point) (d : ℕ) :
    (RejectingExtensionsAtDepth R target a Y d).Finite :=
  (R.fin.depthApproximations_finite Y d).subset fun _ h => h.1

theorem rejectsOneStepFinite_mono
    (R : AbstractRamseySpace S) {target : Set S.Point}
    {X Y : S.Point} {q : S.FiniteApprox}
    (h : RejectsOneStepFinite R target Y q) (hXY : S.le X Y) :
    RejectsOneStepFinite R target X q := by
  rcases q with ⟨m, b⟩
  simp only [RejectsOneStepFinite] at h ⊢
  intro c hc
  have hcY : c ∈ S.oneStepApproximations b Y :=
    S.oneStepApproximations_mono hXY hc
  have hrejY : Rejects R target Y c := h c hcY
  have hneCX : (S.neighborhood c X).Nonempty := by
    rcases hc with ⟨W, hWb, hWc⟩
    exact ⟨W, hWb.1, hWc⟩
  exact rejects_mono R hrejY hXY hneCX

/-- Finitely many rejected approximations of the same depth can all have
their rejection propagated one step, while preserving that depth. -/
theorem exists_refinement_propagates_finite
    (R : AbstractRamseySpace S) (C : FusionComplete S)
    {target : Set S.Point} {n : ℕ} (a : S.Approx n)
    (t : Set S.FiniteApprox) (ht : t.Finite)
    {Y : S.Point} {d : ℕ}
    (hsub : t ⊆ RejectingExtensionsAtDepth R target a Y d) :
    ∃ X, X ∈ S.levelNeighborhood d Y ∧
      ∀ q ∈ t, RejectsOneStepFinite R target X q := by
  induction t, ht using Set.Finite.induction_on generalizing Y with
  | empty =>
      refine ⟨Y, S.self_mem_levelNeighborhood d Y, ?_⟩
      simp
  | @insert q t hqt ht ih =>
      have htsub :
          t ⊆ RejectingExtensionsAtDepth R target a Y d := by
        intro p hp
        exact hsub (by simp [hp])
      rcases ih htsub with ⟨X, hXY, hpropX⟩
      have hqinfo :
          q ∈ RejectingExtensionsAtDepth R target a Y d :=
        hsub (by simp)
      rcases q with ⟨m, b⟩
      change
        (⟨m, b⟩ : S.FiniteApprox) ∈ R.fin.depthApproximations Y d ∧
          S.IsInitial a b ∧ Rejects R target Y b at hqinfo
      have hdepthY : R.fin.HasDepth b Y d :=
        (R.fin.mem_depthApproximations).1 hqinfo.1
      have hdepthX : R.fin.HasDepth b X d :=
        (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hdepthY
      have hneBX : (S.neighborhood b X).Nonempty :=
        R.amalgamation_nonempty b Y hdepthY hXY
      have hrejX : Rejects R target X b :=
        rejects_mono R hqinfo.2.2 hXY.1 hneBX
      rcases exists_refinement_rejects_oneStep R C hrejX hdepthX with
        ⟨Z, hZX, hpropZ⟩
      have hZY : Z ∈ S.levelNeighborhood d Y :=
        S.levelNeighborhood_mono hXY hZX
      refine ⟨Z, hZY, ?_⟩
      intro p hp
      rcases Set.mem_insert_iff.mp hp with hp | hp
      · subst p
        simpa [RejectsOneStepFinite] using hpropZ
      · exact rejectsOneStepFinite_mono R (hpropX p hp) hZX.1

/-- Perform one complete finite rejection-propagation stage at depth d. -/
theorem exists_rejection_stage
    (R : AbstractRamseySpace S) (C : FusionComplete S)
    (target : Set S.Point) {n : ℕ} (a : S.Approx n)
    (Y : S.Point) (d : ℕ) :
    ∃ X, X ∈ S.levelNeighborhood d Y ∧
      ∀ q ∈ RejectingExtensionsAtDepth R target a Y d,
        RejectsOneStepFinite R target X q := by
  exact exists_refinement_propagates_finite R C a
    (RejectingExtensionsAtDepth R target a Y d)
    (rejectingExtensionsAtDepth_finite R target a Y d)
    (fun _ h => h)

/-- Canonical finite rejection-propagation stage. -/
noncomputable def rejectionStep
    (R : AbstractRamseySpace S) (C : FusionComplete S)
    (target : Set S.Point) {n : ℕ} (a : S.Approx n)
    (d : ℕ) (Y : S.Point) : S.Point :=
  Classical.choose (exists_rejection_stage R C target a Y d)

theorem rejectionStep_mem
    (R : AbstractRamseySpace S) (C : FusionComplete S)
    (target : Set S.Point) {n : ℕ} (a : S.Approx n)
    (d : ℕ) (Y : S.Point) :
    rejectionStep R C target a d Y ∈ S.levelNeighborhood d Y :=
  (Classical.choose_spec (exists_rejection_stage R C target a Y d)).1

theorem rejectionStep_rejects
    (R : AbstractRamseySpace S) (C : FusionComplete S)
    (target : Set S.Point) {n m : ℕ}
    (a : S.Approx n) (b : S.Approx m)
    (d : ℕ) (Y : S.Point)
    (hdepth : R.fin.HasDepth b Y d)
    (hab : S.IsInitial a b)
    (hrej : Rejects R target Y b) :
    ∀ c, c ∈ S.oneStepApproximations b (rejectionStep R C target a d Y) →
      Rejects R target (rejectionStep R C target a d Y) c := by
  have hq :
      (⟨m, b⟩ : S.FiniteApprox) ∈
        RejectingExtensionsAtDepth R target a Y d := by
    exact ⟨(R.fin.mem_depthApproximations).2 hdepth, hab, hrej⟩
  have h :=
    (Classical.choose_spec
      (exists_rejection_stage R C target a Y d)).2
      (⟨m, b⟩ : S.FiniteApprox) hq
  simpa [RejectsOneStepFinite] using h

/-- Fusion sequence for Lemma 4.35. -/
noncomputable def rejectionFusion
    (R : AbstractRamseySpace S) (C : FusionComplete S)
    (target : Set S.Point) {n : ℕ} (a : S.Approx n)
    (n0 : ℕ) (Y0 : S.Point) : ℕ → S.Point
  | 0 => Y0
  | k + 1 =>
      rejectionStep R C target a (n0 + k)
        (rejectionFusion R C target a n0 Y0 k)

theorem rejectionFusion_isFusion
    (R : AbstractRamseySpace S) (C : FusionComplete S)
    (target : Set S.Point) {n : ℕ} (a : S.Approx n)
    (n0 : ℕ) (Y0 : S.Point) :
    S.IsFusionFrom n0 (rejectionFusion R C target a n0 Y0) := by
  intro k
  simpa [rejectionFusion] using
    rejectionStep_mem R C target a (n0 + k)
      (rejectionFusion R C target a n0 Y0 k)

theorem rejectionFusion_le_start
    (R : AbstractRamseySpace S) (C : FusionComplete S)
    (target : Set S.Point) {n : ℕ} (a : S.Approx n)
    (n0 : ℕ) (Y0 : S.Point) (k : ℕ) :
    S.le (rejectionFusion R C target a n0 Y0 k) Y0 := by
  induction k with
  | zero =>
      simpa [rejectionFusion] using S.le_refl Y0
  | succ k ih =>
      have hstep :
          S.le
            (rejectionFusion R C target a n0 Y0 (k + 1))
            (rejectionFusion R C target a n0 Y0 k) := by
        simpa [rejectionFusion] using
          (rejectionStep_mem R C target a (n0 + k)
            (rejectionFusion R C target a n0 Y0 k)).1
      exact S.le_trans hstep ih

theorem rejectionFusion_succ_rejects
    (R : AbstractRamseySpace S) (C : FusionComplete S)
    (target : Set S.Point) {n m : ℕ}
    (a : S.Approx n) (n0 : ℕ) (Y0 : S.Point) (k : ℕ)
    (b : S.Approx m)
    (hdepth :
      R.fin.HasDepth b (rejectionFusion R C target a n0 Y0 k) (n0 + k))
    (hab : S.IsInitial a b)
    (hrej :
      Rejects R target (rejectionFusion R C target a n0 Y0 k) b) :
    ∀ c,
      c ∈ S.oneStepApproximations b
        (rejectionFusion R C target a n0 Y0 (k + 1)) →
      Rejects R target
        (rejectionFusion R C target a n0 Y0 (k + 1)) c := by
  simpa [rejectionFusion] using
    rejectionStep_rejects R C target a b (n0 + k)
      (rejectionFusion R C target a n0 Y0 k)
      hdepth hab hrej

/-- Todorčević Lemma 4.35. If Y already decides every approximation at
depth at least depth_Y(a) and rejects a, then a same-depth refinement rejects
every compatible end-extension of a. -/
theorem exists_refinement_rejects_endExtensions
    (R : AbstractRamseySpace S) (C : FusionComplete S)
    {target : Set S.Point} {Y : S.Point}
    {n : ℕ} {a : S.Approx n} {d : ℕ}
    (hd : R.fin.HasDepth a Y d)
    (hdecY :
      ∀ {m : ℕ} (b : S.Approx m) {e : ℕ},
        R.fin.HasDepth b Y e → d ≤ e → Decides R target Y b)
    (hY : Rejects R target Y a) :
    ∃ X, X ∈ S.levelNeighborhood d Y ∧
      ∀ {m : ℕ} (b : S.Approx m),
        S.IsInitial a b →
        (S.neighborhood b X).Nonempty →
        Rejects R target X b := by
  let Ys := rejectionFusion R C target a d Y
  have hfusion : S.IsFusionFrom d Ys :=
    rejectionFusion_isFusion R C target a d Y
  rcases C.exists_limit hfusion with ⟨X, hX⟩
  have hXY : X ∈ S.levelNeighborhood d Y := by
    simpa [Ys, rejectionFusion] using hX 0
  have hdX : R.fin.HasDepth a X d :=
    (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hd
  have hrejX : Rejects R target X a :=
    rejects_of_mem_levelNeighborhood R hY hd hXY
  refine ⟨X, hXY, ?_⟩
  intro m
  refine Nat.strong_induction_on m ?_
  intro m ih b hab hne
  by_cases hmn : m = n
  · subst m
    have habEq : a = b := S.isInitial_eq_sameLevel hab
    subst b
    exact hrejX
  · have hnm : n < m := by omega
    have hmpos : 0 < m := by omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hmpos
    rcases hne with ⟨D, hDbX⟩
    have hDaX : D ∈ S.neighborhood a X :=
      S.neighborhood_initial_subset hab hDbX
    let c : S.Approx j := S.approx j D
    have hac : S.IsInitial a c := by
      refine ⟨?_, D, hDaX.2, rfl⟩
      omega
    have hDcX : D ∈ S.neighborhood c X :=
      ⟨hDbX.1, rfl⟩
    have hrejCX : Rejects R target X c :=
      ih j (by omega) c hac ⟨D, hDcX⟩
    rcases R.fin.exists_hasDepth_of_mem_neighborhood hDcX with
      ⟨e, hdcX⟩
    have hde : d ≤ e :=
      R.fin.hasDepth_le_of_initial hac hdX hdcX
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hde
    subst e
    have hXk :
        X ∈ S.levelNeighborhood (d + k) (Ys k) :=
      hX k
    have hdcYk : R.fin.HasDepth c (Ys k) (d + k) :=
      (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXk).1 hdcX
    have hDcY : D ∈ S.neighborhood c Y :=
      S.neighborhood_mono hXY.1 hDcX
    rcases R.fin.exists_hasDepth_of_mem_neighborhood hDcY with
      ⟨eY, hdcY⟩
    have hdeY : d ≤ eY :=
      R.fin.hasDepth_le_of_initial hac hd hdcY
    have hdec0 : Decides R target Y c :=
      hdecY c hdcY hdeY
    have hYkY : S.le (Ys k) Y := by
      simpa [Ys] using
        rejectionFusion_le_start R C target a d Y k
    have hdecYk : Decides R target (Ys k) c :=
      decides_mono R hdec0 hYkY
    have hnotAccX : ¬ Accepts target X c := by
      intro hacc
      exact hrejCX.2 (d + k) hdcX X
        (S.self_mem_levelNeighborhood (d + k) X) hacc
    have hrejYk : Rejects R target (Ys k) c := by
      rcases hdecYk with hacc | hrej
      · have haccX : Accepts target X c :=
          accepts_mono hacc hXk.1
        exact (hnotAccX haccX).elim
      · exact hrej
    have hstage :
        ∀ q, q ∈ S.oneStepApproximations c (Ys (k + 1)) →
          Rejects R target (Ys (k + 1)) q := by
      simpa [Ys] using
        rejectionFusion_succ_rejects R C target a d Y k c
          hdcYk hac hrejYk
    have hbStep : b ∈ S.oneStepApproximations c (Ys (k + 1)) := by
      refine ⟨D, ?_, hDbX.2⟩
      exact ⟨S.le_trans hDbX.1 (hX (k + 1)).1, rfl⟩
    have hrejStage : Rejects R target (Ys (k + 1)) b :=
      hstage b hbStep
    exact rejects_mono R hrejStage (hX (k + 1)).1 ⟨D, hDbX⟩

end CombinatorialForcing
end RamseySpace
