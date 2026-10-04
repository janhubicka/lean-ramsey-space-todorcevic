import RamseySpace.TwoSorted.Baire

/-!
# Ramsey notions relative to a fixed reduction

Todorčević's proof of Souslin closure works inside
`S(≤ X) = {Y : S | Y ≤ X}`.  This file formalizes the four relative notions
and proves the relative form of Lemmas 4.36 and 4.38.  The proofs use exactly
the same forcing machinery as the global theorem, started below the fixed
bound.
-/

namespace RamseySpace
namespace TwoSorted

universe uR vR uS vS

variable {P : System.{uR, vR, uS, vS}}

/-- S(≤ bound)-Ramsey. -/
def IsRamseyBelow (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (target : Set P.Obj.Point) : Prop :=
  ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point) {d : ℕ},
    P.Red.le Y bound →
    R.fin.HasDepth a Y d →
      ∃ X, X ∈ P.levelNeighborhood d Y ∧
        (P.objectNeighborhood a X ⊆ target ∨
          Disjoint (P.objectNeighborhood a X) target)

/-- S(≤ bound)-Ramsey null. -/
def IsRamseyNullBelow (R : AbstractRamseySystem P) (bound : P.Red.Point)
    (target : Set P.Obj.Point) : Prop :=
  ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point) {d : ℕ},
    P.Red.le Y bound →
    R.fin.HasDepth a Y d →
      ∃ X, X ∈ P.levelNeighborhood d Y ∧
        Disjoint (P.objectNeighborhood a X) target

/-- S(≤ bound)-Baire. -/
def IsBaireBelow (bound : P.Red.Point) (target : Set P.Obj.Point) : Prop :=
  ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point),
    P.Red.le Y bound →
    (P.objectNeighborhood a Y).Nonempty →
      ∃ (m : ℕ) (b : P.Obj.Approx m) (X : P.Red.Point),
        P.Obj.IsInitial a b ∧ P.Red.le X Y ∧
          (P.objectNeighborhood b X).Nonempty ∧
          (P.objectNeighborhood b X ⊆ target ∨
            Disjoint (P.objectNeighborhood b X) target)

/-- S(≤ bound)-meagre. -/
def IsMeagreBelow (bound : P.Red.Point) (target : Set P.Obj.Point) : Prop :=
  ∀ {n : ℕ} (a : P.Obj.Approx n) (Y : P.Red.Point),
    P.Red.le Y bound →
    (P.objectNeighborhood a Y).Nonempty →
      ∃ (m : ℕ) (b : P.Obj.Approx m) (X : P.Red.Point),
        P.Obj.IsInitial a b ∧ P.Red.le X Y ∧
          (P.objectNeighborhood b X).Nonempty ∧
          Disjoint (P.objectNeighborhood b X) target

theorem IsRamsey.isRamseyBelow (R : AbstractRamseySystem P)
    {target : Set P.Obj.Point} (h : IsRamsey R target)
    (bound : P.Red.Point) :
    IsRamseyBelow R bound target := by
  intro n a Y d hY hd
  exact h a Y hd

theorem IsRamseyNull.isRamseyNullBelow (R : AbstractRamseySystem P)
    {target : Set P.Obj.Point} (h : IsRamseyNull R target)
    (bound : P.Red.Point) :
    IsRamseyNullBelow R bound target := by
  intro n a Y d hY hd
  exact h a Y hd

theorem IsRamseyBelow.mono_bound (R : AbstractRamseySystem P)
    {X Y : P.Red.Point} {target : Set P.Obj.Point}
    (h : IsRamseyBelow R Y target) (hXY : P.Red.le X Y) :
    IsRamseyBelow R X target := by
  intro n a Z d hZX hd
  exact h a Z (P.Red.le_trans hZX hXY) hd

theorem IsRamseyNullBelow.mono_bound (R : AbstractRamseySystem P)
    {X Y : P.Red.Point} {target : Set P.Obj.Point}
    (h : IsRamseyNullBelow R Y target) (hXY : P.Red.le X Y) :
    IsRamseyNullBelow R X target := by
  intro n a Z d hZX hd
  exact h a Z (P.Red.le_trans hZX hXY) hd

theorem IsRamseyBelow.isBaireBelow (R : AbstractRamseySystem P)
    {bound : P.Red.Point} {target : Set P.Obj.Point}
    (h : IsRamseyBelow R bound target) :
    IsBaireBelow bound target := by
  intro n a Y hY hne
  rcases hne with ⟨A, hAY⟩
  rcases R.fin.exists_hasDepth_of_mem_objectNeighborhood hAY with ⟨d, hd⟩
  rcases h a Y hY hd with ⟨X, hXY, hhom⟩
  refine ⟨n, a, X, P.Obj.isInitial_refl a, hXY.1, ?_, hhom⟩
  exact R.amalgamation_nonempty a Y hd hXY

theorem IsRamseyNullBelow.isMeagreBelow (R : AbstractRamseySystem P)
    {bound : P.Red.Point} {target : Set P.Obj.Point}
    (h : IsRamseyNullBelow R bound target) :
    IsMeagreBelow bound target := by
  intro n a Y hY hne
  rcases hne with ⟨A, hAY⟩
  rcases R.fin.exists_hasDepth_of_mem_objectNeighborhood hAY with ⟨d, hd⟩
  rcases h a Y hY hd with ⟨X, hXY, hdis⟩
  refine ⟨n, a, X, P.Obj.isInitial_refl a, hXY.1, ?_, hdis⟩
  exact R.amalgamation_nonempty a Y hd hXY

theorem IsMeagreBelow.isBaireBelow
    {bound : P.Red.Point} {target : Set P.Obj.Point}
    (h : IsMeagreBelow (P := P) bound target) :
    IsBaireBelow bound target := by
  intro n a Y hY hne
  rcases h a Y hY hne with ⟨m, b, X, hab, hXY, hnon, hdis⟩
  exact ⟨m, b, X, hab, hXY, hnon, Or.inr hdis⟩

open CombinatorialForcing

/-- Relative form of Lemma 4.36: S(≤ bound)-Baire implies
S(≤ bound)-Ramsey. -/
theorem IsBaireBelow.isRamseyBelow
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    {bound : P.Red.Point} {target : Set P.Obj.Point}
    (hBaire : IsBaireBelow (P := P) bound target) :
    IsRamseyBelow R bound target := by
  intro n a Y d hYbound hd

  rcases exists_global_decider R C target d Y with
    ⟨X, hXY, hdecX⟩
  have hXbound : P.Red.le X bound :=
    P.Red.le_trans hXY.1 hYbound
  have hdX : R.fin.HasDepth a X d :=
    (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hd
  have hdecA : Decides R target X a :=
    hdecX a hdX le_rfl

  rcases hdecA with hacc | hrej
  · have hsub : P.objectNeighborhood a X ⊆ target := by
      simpa [Accepts] using hacc
    exact ⟨X, hXY, Or.inl hsub⟩
  · rcases exists_refinement_rejects_endExtensions R C hdX hdecX hrej with
      ⟨Z, hZX, hrejectTargetZ⟩
    have hZY : Z ∈ P.levelNeighborhood d Y :=
      P.levelNeighborhood_mono hXY hZX
    have hdZ : R.fin.HasDepth a Z d :=
      (R.fin.hasDepth_iff_of_mem_levelNeighborhood hZX).2 hdX

    rcases exists_global_decider R C targetᶜ d Z with
      ⟨W, hWZ, hdecComplW⟩
    have hWY : W ∈ P.levelNeighborhood d Y :=
      P.levelNeighborhood_mono hZY hWZ
    have hdW : R.fin.HasDepth a W d :=
      (R.fin.hasDepth_iff_of_mem_levelNeighborhood hWZ).2 hdZ
    have hdecComplA : Decides R targetᶜ W a :=
      hdecComplW a hdW le_rfl

    rcases hdecComplA with haccCompl | hrejCompl
    · have hsubCompl : P.objectNeighborhood a W ⊆ targetᶜ := by
        simpa [Accepts] using haccCompl
      exact ⟨W, hWY, Or.inr
        (Set.subset_compl_iff_disjoint_right.mp hsubCompl)⟩
    · rcases exists_refinement_rejects_endExtensions
        R C hdW hdecComplW hrejCompl with
        ⟨V, hVW, hrejectComplV⟩
      have hVZ : V ∈ P.levelNeighborhood d Z :=
        P.levelNeighborhood_mono hWZ hVW
      have hVY : V ∈ P.levelNeighborhood d Y :=
        P.levelNeighborhood_mono hZY hVZ
      have hVbound : P.Red.le V bound :=
        P.Red.le_trans hVY.1 hYbound
      have hneAV : (P.objectNeighborhood a V).Nonempty :=
        R.amalgamation_nonempty a W hdW hVW

      rcases hBaire a V hVbound hneAV with
        ⟨m, b, Z0, hab, hZ0V, hneBZ0, hhom⟩

      have hneBV : (P.objectNeighborhood b V).Nonempty := by
        rcases hneBZ0 with ⟨A, hA⟩
        exact ⟨A, R.fin.objectNeighborhood_mono hZ0V hA⟩
      have hneBZ : (P.objectNeighborhood b Z).Nonempty := by
        rcases hneBV with ⟨A, hA⟩
        exact ⟨A, R.fin.objectNeighborhood_mono hVZ.1 hA⟩

      have hrejectTargetV : Rejects R target V b := by
        have hrejectTargetZ : Rejects R target Z b :=
          hrejectTargetZ b hab hneBZ
        exact rejects_mono R hrejectTargetZ hVZ.1 hneBV

      have hrejectCompl : Rejects R targetᶜ V b :=
        hrejectComplV b hab hneBV

      rcases hneBV with ⟨A, hAbV⟩
      rcases R.fin.exists_hasDepth_of_mem_objectNeighborhood hAbV with
        ⟨e, hdbV⟩
      rcases R.amalgamation_refine b V hdbV hZ0V hneBZ0 with
        ⟨Z', hZ'depth, hsub⟩

      exfalso
      rcases hhom with hsubTarget | hdisTarget
      · have haccTarget : Accepts target Z' b :=
          hsub.trans hsubTarget
        exact (hrejectTargetV.2 e hdbV Z' hZ'depth) haccTarget
      · have hsubCompl : P.objectNeighborhood b Z0 ⊆ targetᶜ :=
          Set.subset_compl_iff_disjoint_right.mpr hdisTarget
        have haccCompl : Accepts targetᶜ Z' b :=
          hsub.trans hsubCompl
        exact (hrejectCompl.2 e hdbV Z' hZ'depth) haccCompl

theorem isBaireBelow_iff_isRamseyBelow
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (bound : P.Red.Point) (target : Set P.Obj.Point) :
    IsBaireBelow (P := P) bound target ↔ IsRamseyBelow R bound target :=
  ⟨fun h => h.isRamseyBelow R C, fun h => h.isBaireBelow R⟩

theorem IsMeagreBelow.isRamseyNullBelow
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    {bound : P.Red.Point} {target : Set P.Obj.Point}
    (hMeagre : IsMeagreBelow (P := P) bound target) :
    IsRamseyNullBelow R bound target := by
  have hBaire : IsBaireBelow (P := P) bound target :=
    hMeagre.isBaireBelow
  have hRamsey : IsRamseyBelow R bound target :=
    hBaire.isRamseyBelow R C
  intro n a Y d hYbound hd
  rcases hRamsey a Y hYbound hd with ⟨X, hXY, hhom⟩
  rcases hhom with hsub | hdis
  · have hXbound : P.Red.le X bound :=
      P.Red.le_trans hXY.1 hYbound
    have hneAX : (P.objectNeighborhood a X).Nonempty :=
      R.amalgamation_nonempty a Y hd hXY
    rcases hMeagre a X hXbound hneAX with
      ⟨m, b, Z, hab, hZX, hneBZ, hdisBZ⟩
    exfalso
    rcases hneBZ with ⟨A, hAbZ⟩
    have hAbX : A ∈ P.objectNeighborhood b X :=
      R.fin.objectNeighborhood_mono hZX hAbZ
    have hAaX : A ∈ P.objectNeighborhood a X :=
      P.objectNeighborhood_initial_subset hab hAbX
    exact Set.disjoint_left.1 hdisBZ hAbZ (hsub hAaX)
  · exact ⟨X, hXY, hdis⟩

theorem isMeagreBelow_iff_isRamseyNullBelow
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (bound : P.Red.Point) (target : Set P.Obj.Point) :
    IsMeagreBelow (P := P) bound target ↔
      IsRamseyNullBelow R bound target :=
  ⟨fun h => h.isRamseyNullBelow R C,
   fun h => h.isMeagreBelow R⟩

theorem IsRamseyBelow.compl
    (R : AbstractRamseySystem P) {bound : P.Red.Point}
    {target : Set P.Obj.Point}
    (h : IsRamseyBelow R bound target) :
    IsRamseyBelow R bound targetᶜ := by
  intro n a Y d hY hd
  rcases h a Y hY hd with ⟨X, hXY, hhom⟩
  refine ⟨X, hXY, ?_⟩
  rcases hhom with hsub | hdis
  · exact Or.inr (Set.disjoint_compl_right_iff_subset.mpr hsub)
  · exact Or.inl (Set.subset_compl_iff_disjoint_right.mpr hdis)

theorem IsRamseyNullBelow.mono
    (R : AbstractRamseySystem P) {bound : P.Red.Point}
    {target subset : Set P.Obj.Point}
    (h : IsRamseyNullBelow R bound target) (hsub : subset ⊆ target) :
    IsRamseyNullBelow R bound subset := by
  intro n a Y d hY hd
  rcases h a Y hY hd with ⟨X, hXY, hdis⟩
  exact ⟨X, hXY, hdis.mono_right hsub⟩


theorem IsRamseyBelow.inter
    (R : AbstractRamseySystem P) {bound : P.Red.Point}
    {A B : Set P.Obj.Point}
    (hA : IsRamseyBelow R bound A)
    (hB : IsRamseyBelow R bound B) :
    IsRamseyBelow R bound (A ∩ B) := by
  intro n a Y d hY hd
  rcases hA a Y hY hd with ⟨X, hXY, hhomA⟩
  rcases hhomA with hsubA | hdisA
  · have hXbound : P.Red.le X bound := P.Red.le_trans hXY.1 hY
    have hdX : R.fin.HasDepth a X d :=
      (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hd
    rcases hB a X hXbound hdX with ⟨Z, hZX, hhomB⟩
    have hZY : Z ∈ P.levelNeighborhood d Y :=
      P.levelNeighborhood_mono hXY hZX
    refine ⟨Z, hZY, ?_⟩
    rcases hhomB with hsubB | hdisB
    · apply Or.inl
      intro W hW
      exact ⟨hsubA (R.fin.objectNeighborhood_mono hZX.1 hW), hsubB hW⟩
    · apply Or.inr
      rw [Set.disjoint_left] at hdisB ⊢
      intro W hW hAB
      exact hdisB hW hAB.2
  · refine ⟨X, hXY, Or.inr ?_⟩
    rw [Set.disjoint_left] at hdisA ⊢
    intro W hW hAB
    exact hdisA hW hAB.1

theorem IsRamseyBelow.union
    (R : AbstractRamseySystem P) {bound : P.Red.Point}
    {A B : Set P.Obj.Point}
    (hA : IsRamseyBelow R bound A)
    (hB : IsRamseyBelow R bound B) :
    IsRamseyBelow R bound (A ∪ B) := by
  intro n a Y d hY hd
  rcases hA a Y hY hd with ⟨X, hXY, hhomA⟩
  have hXbound : P.Red.le X bound :=
    P.Red.le_trans hXY.1 hY
  have hdX : R.fin.HasDepth a X d :=
    (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hd
  rcases hB a X hXbound hdX with ⟨Z, hZX, hhomB⟩
  have hZY : Z ∈ P.levelNeighborhood d Y :=
    P.levelNeighborhood_mono hXY hZX
  refine ⟨Z, hZY, ?_⟩
  rcases hhomA with hsubA | hdisA
  · exact Or.inl (fun W hW =>
      Or.inl (hsubA (R.fin.objectNeighborhood_mono hZX.1 hW)))
  · rcases hhomB with hsubB | hdisB
    · exact Or.inl (fun W hW => Or.inr (hsubB hW))
    · apply Or.inr
      rw [Set.disjoint_left] at hdisA hdisB ⊢
      intro W hW hAB
      rcases hAB with hWA | hWB
      · exact hdisA (R.fin.objectNeighborhood_mono hZX.1 hW) hWA
      · exact hdisB hW hWB


theorem IsRamseyBelow.diff
    (R : AbstractRamseySystem P) {bound : P.Red.Point}
    {A B : Set P.Obj.Point}
    (hA : IsRamseyBelow R bound A)
    (hB : IsRamseyBelow R bound B) :
    IsRamseyBelow R bound (A \ B) := by
  intro n a Y d hY hd
  rcases hA a Y hY hd with ⟨X, hXY, hhomA⟩
  rcases hhomA with hsubA | hdisA
  · have hXbound : P.Red.le X bound :=
      P.Red.le_trans hXY.1 hY
    have hdX : R.fin.HasDepth a X d :=
      (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hd
    rcases hB a X hXbound hdX with ⟨Z, hZX, hhomB⟩
    have hZY : Z ∈ P.levelNeighborhood d Y :=
      P.levelNeighborhood_mono hXY hZX
    refine ⟨Z, hZY, ?_⟩
    rcases hhomB with hsubB | hdisB
    · apply Or.inr
      rw [Set.disjoint_left]
      intro W hW hdiff
      exact hdiff.2 (hsubB hW)
    · apply Or.inl
      intro W hW
      refine ⟨hsubA (R.fin.objectNeighborhood_mono hZX.1 hW), ?_⟩
      intro hWB
      exact Set.disjoint_left.1 hdisB hW hWB
  · refine ⟨X, hXY, Or.inr ?_⟩
    rw [Set.disjoint_left]
    intro W hW hdiff
    exact Set.disjoint_left.1 hdisA hW hdiff.1

end TwoSorted
end RamseySpace
