import RamseySpace.TwoSorted.Reject

/-!
# Rejection of all object end-extensions

Two-sorted version of Todorčević's end-extension rejection lemma.
-/

namespace RamseySpace
namespace TwoSorted
namespace CombinatorialForcing

universe uR vR uS vS

variable {P : System.{uR, vR, uS, vS}}

def RejectsOneStepFinite
    (R : AbstractRamseySystem P) (target : Set P.Obj.Point)
    (Y : P.Red.Point) (q : P.Obj.FiniteApprox) : Prop :=
  match q with
  | ⟨_, b⟩ =>
      ∀ c, c ∈ P.oneStepObjectApproximations b Y →
        Rejects R target Y c

def RejectingExtensionsAtDepth
    (R : AbstractRamseySystem P) (target : Set P.Obj.Point)
    {n : ℕ} (a : P.Obj.Approx n)
    (Y : P.Red.Point) (d : ℕ) : Set P.Obj.FiniteApprox :=
  {q | q ∈ R.fin.depthApproximations Y d ∧
    match q with
    | ⟨_, b⟩ => P.Obj.IsInitial a b ∧ Rejects R target Y b}

theorem rejectingExtensionsAtDepth_finite
    (R : AbstractRamseySystem P) (target : Set P.Obj.Point)
    {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point) (d : ℕ) :
    (RejectingExtensionsAtDepth R target a Y d).Finite :=
  (R.fin.depthApproximations_finite Y d).subset fun _ h => h.1

theorem rejectsOneStepFinite_mono
    (R : AbstractRamseySystem P) {target : Set P.Obj.Point}
    {X Y : P.Red.Point} {q : P.Obj.FiniteApprox}
    (h : RejectsOneStepFinite R target Y q)
    (hXY : P.Red.le X Y) :
    RejectsOneStepFinite R target X q := by
  rcases q with ⟨m, b⟩
  simp only [RejectsOneStepFinite] at h ⊢
  intro c hc
  have hcY : c ∈ P.oneStepObjectApproximations b Y :=
    R.fin.oneStepObjectApproximations_mono hXY hc
  have hrejY : Rejects R target Y c := h c hcY
  have hneCX : (P.objectNeighborhood c X).Nonempty := by
    rcases hc with ⟨A, hAb, hAc⟩
    exact ⟨A, hAb.1, hAc⟩
  exact rejects_mono R hrejY hXY hneCX

theorem exists_refinement_propagates_finite
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    {target : Set P.Obj.Point} {n : ℕ} (a : P.Obj.Approx n)
    (t : Set P.Obj.FiniteApprox) (ht : t.Finite)
    {Y : P.Red.Point} {d : ℕ}
    (hsub : t ⊆ RejectingExtensionsAtDepth R target a Y d) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ q ∈ t, RejectsOneStepFinite R target X q := by
  induction t, ht using Set.Finite.induction_on generalizing Y with
  | empty =>
      refine ⟨Y, P.self_mem_levelNeighborhood d Y, ?_⟩
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
        (⟨m, b⟩ : P.Obj.FiniteApprox) ∈
            R.fin.depthApproximations Y d ∧
          P.Obj.IsInitial a b ∧ Rejects R target Y b at hqinfo
      have hdepthY : R.fin.HasDepth b Y d :=
        (R.fin.mem_depthApproximations).1 hqinfo.1
      have hdepthX : R.fin.HasDepth b X d :=
        (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hdepthY
      have hneBX : (P.objectNeighborhood b X).Nonempty :=
        R.amalgamation_nonempty b Y hdepthY hXY
      have hrejX : Rejects R target X b :=
        rejects_mono R hqinfo.2.2 hXY.1 hneBX
      rcases exists_refinement_rejects_oneStep R C hrejX hdepthX with
        ⟨Z, hZX, hpropZ⟩
      have hZY : Z ∈ P.levelNeighborhood d Y :=
        P.levelNeighborhood_mono hXY hZX
      refine ⟨Z, hZY, ?_⟩
      intro p hp
      rcases Set.mem_insert_iff.mp hp with hp | hp
      · subst p
        simpa [RejectsOneStepFinite] using hpropZ
      · exact rejectsOneStepFinite_mono R (hpropX p hp) hZX.1

theorem exists_rejection_stage
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (target : Set P.Obj.Point) {n : ℕ} (a : P.Obj.Approx n)
    (Y : P.Red.Point) (d : ℕ) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ q ∈ RejectingExtensionsAtDepth R target a Y d,
        RejectsOneStepFinite R target X q :=
  exists_refinement_propagates_finite R C a
    (RejectingExtensionsAtDepth R target a Y d)
    (rejectingExtensionsAtDepth_finite R target a Y d)
    (fun _ h => h)

noncomputable def rejectionStep
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (target : Set P.Obj.Point) {n : ℕ} (a : P.Obj.Approx n)
    (d : ℕ) (Y : P.Red.Point) : P.Red.Point :=
  Classical.choose (exists_rejection_stage R C target a Y d)

theorem rejectionStep_mem
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (target : Set P.Obj.Point) {n : ℕ} (a : P.Obj.Approx n)
    (d : ℕ) (Y : P.Red.Point) :
    rejectionStep R C target a d Y ∈ P.levelNeighborhood d Y :=
  (Classical.choose_spec (exists_rejection_stage R C target a Y d)).1

theorem rejectionStep_rejects
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (target : Set P.Obj.Point) {n m : ℕ}
    (a : P.Obj.Approx n) (b : P.Obj.Approx m)
    (d : ℕ) (Y : P.Red.Point)
    (hdepth : R.fin.HasDepth b Y d)
    (hab : P.Obj.IsInitial a b)
    (hrej : Rejects R target Y b) :
    ∀ c,
      c ∈ P.oneStepObjectApproximations b
        (rejectionStep R C target a d Y) →
      Rejects R target (rejectionStep R C target a d Y) c := by
  have hq :
      (⟨m, b⟩ : P.Obj.FiniteApprox) ∈
        RejectingExtensionsAtDepth R target a Y d :=
    ⟨(R.fin.mem_depthApproximations).2 hdepth, hab, hrej⟩
  have h :=
    (Classical.choose_spec
      (exists_rejection_stage R C target a Y d)).2
      (⟨m, b⟩ : P.Obj.FiniteApprox) hq
  simpa [RejectsOneStepFinite, rejectionStep] using h

noncomputable def rejectionFusion
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (target : Set P.Obj.Point) {n : ℕ} (a : P.Obj.Approx n)
    (n0 : ℕ) (Y0 : P.Red.Point) : ℕ → P.Red.Point
  | 0 => Y0
  | k + 1 =>
      rejectionStep R C target a (n0 + k)
        (rejectionFusion R C target a n0 Y0 k)

theorem rejectionFusion_isFusion
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (target : Set P.Obj.Point) {n : ℕ} (a : P.Obj.Approx n)
    (n0 : ℕ) (Y0 : P.Red.Point) :
    P.Red.IsFusionFrom n0 (rejectionFusion R C target a n0 Y0) := by
  intro k
  simpa [rejectionFusion] using
    rejectionStep_mem R C target a (n0 + k)
      (rejectionFusion R C target a n0 Y0 k)

theorem rejectionFusion_le_start
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (target : Set P.Obj.Point) {n : ℕ} (a : P.Obj.Approx n)
    (n0 : ℕ) (Y0 : P.Red.Point) (k : ℕ) :
    P.Red.le (rejectionFusion R C target a n0 Y0 k) Y0 := by
  induction k with
  | zero =>
      simpa [rejectionFusion] using P.Red.le_refl Y0
  | succ k ih =>
      have hstep :
          P.Red.le
            (rejectionFusion R C target a n0 Y0 (k + 1))
            (rejectionFusion R C target a n0 Y0 k) := by
        simpa [rejectionFusion] using
          (rejectionStep_mem R C target a (n0 + k)
            (rejectionFusion R C target a n0 Y0 k)).1
      exact P.Red.le_trans hstep ih

theorem rejectionFusion_succ_rejects
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (target : Set P.Obj.Point) {n m : ℕ}
    (a : P.Obj.Approx n) (n0 : ℕ) (Y0 : P.Red.Point) (k : ℕ)
    (b : P.Obj.Approx m)
    (hdepth :
      R.fin.HasDepth b
        (rejectionFusion R C target a n0 Y0 k) (n0 + k))
    (hab : P.Obj.IsInitial a b)
    (hrej :
      Rejects R target
        (rejectionFusion R C target a n0 Y0 k) b) :
    ∀ c,
      c ∈ P.oneStepObjectApproximations b
        (rejectionFusion R C target a n0 Y0 (k + 1)) →
      Rejects R target
        (rejectionFusion R C target a n0 Y0 (k + 1)) c := by
  simpa [rejectionFusion] using
    rejectionStep_rejects R C target a b (n0 + k)
      (rejectionFusion R C target a n0 Y0 k)
      hdepth hab hrej

/-- If Y decides all sufficiently deep object approximations and rejects a,
then a same-depth refinement rejects every compatible end-extension of a. -/
theorem exists_refinement_rejects_endExtensions
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    {target : Set P.Obj.Point} {Y : P.Red.Point}
    {n : ℕ} {a : P.Obj.Approx n} {d : ℕ}
    (hd : R.fin.HasDepth a Y d)
    (hdecY :
      ∀ {m : ℕ} (b : P.Obj.Approx m) {e : ℕ},
        R.fin.HasDepth b Y e → d ≤ e → Decides R target Y b)
    (hY : Rejects R target Y a) :
    ∃ X, X ∈ P.levelNeighborhood d Y ∧
      ∀ {m : ℕ} (b : P.Obj.Approx m),
        P.Obj.IsInitial a b →
        (P.objectNeighborhood b X).Nonempty →
        Rejects R target X b := by
  let Ys := rejectionFusion R C target a d Y
  have hfusion : P.Red.IsFusionFrom d Ys :=
    rejectionFusion_isFusion R C target a d Y
  rcases C.exists_limit hfusion with ⟨X, hX⟩
  have hXY : X ∈ P.levelNeighborhood d Y := by
    simpa [Ys, rejectionFusion] using hX 0
  have hdX : R.fin.HasDepth a X d :=
    (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hd
  have hrejX : Rejects R target X a :=
    rejects_of_mem_levelNeighborhood R hY hd hXY
  refine ⟨X, hXY, ?_⟩
  intro m
  refine Nat.strong_induction_on m ?_
  intro m ih b hab hne
  have hle_nm : n ≤ m := hab.1
  by_cases hmn : m = n
  · subst m
    have habEq : a = b := P.Obj.isInitial_eq_sameLevel hab
    subst b
    exact hrejX
  · have hnm : n < m :=
      lt_of_le_of_ne hle_nm (Ne.symm hmn)
    have hmpos : 0 < m := Nat.zero_lt_of_lt hnm
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hmpos
    rcases hne with ⟨A, hAbX⟩
    have hAaX : A ∈ P.objectNeighborhood a X :=
      P.objectNeighborhood_initial_subset hab hAbX
    let c : P.Obj.Approx j := P.Obj.approx j A
    have hac : P.Obj.IsInitial a c := by
      refine ⟨?_, A, hAaX.2, rfl⟩
      omega
    have hAcX : A ∈ P.objectNeighborhood c X :=
      ⟨hAbX.1, rfl⟩
    have hrejCX : Rejects R target X c :=
      ih j (by omega) c hac ⟨A, hAcX⟩
    rcases R.fin.exists_hasDepth_of_mem_objectNeighborhood hAcX with
      ⟨e, hdcX⟩
    have hde : d ≤ e :=
      R.fin.hasDepth_le_of_initial hac hdX hdcX
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hde
    subst e
    have hXk :
        X ∈ P.levelNeighborhood (d + k) (Ys k) :=
      hX k
    have hdcYk : R.fin.HasDepth c (Ys k) (d + k) :=
      (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXk).1 hdcX
    have hAcY : A ∈ P.objectNeighborhood c Y :=
      R.fin.objectNeighborhood_mono hXY.1 hAcX
    rcases R.fin.exists_hasDepth_of_mem_objectNeighborhood hAcY with
      ⟨eY, hdcY⟩
    have hdeY : d ≤ eY :=
      R.fin.hasDepth_le_of_initial hac hd hdcY
    have hdec0 : Decides R target Y c :=
      hdecY c hdcY hdeY
    have hYkY : P.Red.le (Ys k) Y := by
      simpa [Ys] using
        rejectionFusion_le_start R C target a d Y k
    have hdecYk : Decides R target (Ys k) c :=
      decides_mono R hdec0 hYkY
    have hnotAccX : ¬ Accepts target X c := by
      intro hacc
      exact hrejCX.2 (d + k) hdcX X
        (P.self_mem_levelNeighborhood (d + k) X) hacc
    have hrejYk : Rejects R target (Ys k) c := by
      rcases hdecYk with hacc | hrej
      · have haccX : Accepts target X c :=
          accepts_mono R.fin hacc hXk.1
        exact (hnotAccX haccX).elim
      · exact hrej
    have hstage :
        ∀ q, q ∈ P.oneStepObjectApproximations c (Ys (k + 1)) →
          Rejects R target (Ys (k + 1)) q := by
      simpa [Ys] using
        rejectionFusion_succ_rejects R C target a d Y k c
          hdcYk hac hrejYk
    have hbStep :
        b ∈ P.oneStepObjectApproximations c (Ys (k + 1)) := by
      refine ⟨A, ?_, hAbX.2⟩
      exact
        ⟨R.fin.le0_trans hAbX.1 (hX (k + 1)).1, rfl⟩
    have hrejStage : Rejects R target (Ys (k + 1)) b :=
      hstage b hbStep
    have hneBX : (P.objectNeighborhood b X).Nonempty :=
      ⟨A, hAbX⟩
    exact rejects_mono R hrejStage (hX (k + 1)).1 hneBX

end CombinatorialForcing
end TwoSorted
end RamseySpace
