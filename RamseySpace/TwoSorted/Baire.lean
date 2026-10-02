import RamseySpace.TwoSorted.EndExtension
import RamseySpace.TwoSorted.Ramsey

/-!
# The Abstract Ramsey Theorem: Baire and meagre sets
-/

namespace RamseySpace
namespace TwoSorted

universe uR vR uS vS

variable {P : System.{uR, vR, uS, vS}}

open CombinatorialForcing

theorem IsRamsey.isBaire (R : AbstractRamseySystem P)
    {target : Set P.Obj.Point} (h : IsRamsey R target) :
    IsBaire target := by
  intro n a Y hne
  rcases hne with ⟨A, hAY⟩
  rcases R.fin.exists_hasDepth_of_mem_objectNeighborhood hAY with ⟨d, hd⟩
  rcases h a Y hd with ⟨X, hXY, hhom⟩
  refine ⟨n, a, X, P.Obj.isInitial_refl a, hXY.1, ?_, hhom⟩
  exact R.amalgamation_nonempty a Y hd hXY

theorem IsRamseyNull.isMeagre (R : AbstractRamseySystem P)
    {target : Set P.Obj.Point} (h : IsRamseyNull R target) :
    IsMeagre target := by
  intro n a Y hne
  rcases hne with ⟨A, hAY⟩
  rcases R.fin.exists_hasDepth_of_mem_objectNeighborhood hAY with ⟨d, hd⟩
  rcases h a Y hd with ⟨X, hXY, hdis⟩
  refine ⟨n, a, X, P.Obj.isInitial_refl a, hXY.1, ?_, hdis⟩
  exact R.amalgamation_nonempty a Y hd hXY

theorem IsMeagre.isBaire {target : Set P.Obj.Point}
    (h : IsMeagre target) :
    IsBaire target := by
  intro n a Y hne
  rcases h a Y hne with ⟨m, b, X, hab, hXY, hnon, hdis⟩
  exact ⟨m, b, X, hab, hXY, hnon, Or.inr hdis⟩

/-- Nontrivial direction of Todorčević's Abstract Ramsey Theorem:
S-Baire implies S-Ramsey. -/
theorem IsBaire.isRamsey
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    {target : Set P.Obj.Point}
    (hBaire : IsBaire target) :
    IsRamsey R target := by
  intro n a Y d hd

  rcases exists_global_decider R C target d Y with
    ⟨X, hXY, hdecX⟩
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
      have hneAV : (P.objectNeighborhood a V).Nonempty :=
        R.amalgamation_nonempty a W hdW hVW

      rcases hBaire a V hneAV with
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
      · have haccTarget : Accepts target Z' b := by
          exact hsub.trans hsubTarget
        exact (hrejectTargetV.2 e hdbV Z' hZ'depth) haccTarget
      · have hsubCompl : P.objectNeighborhood b Z0 ⊆ targetᶜ :=
          Set.subset_compl_iff_disjoint_right.mpr hdisTarget
        have haccCompl : Accepts targetᶜ Z' b := by
          exact hsub.trans hsubCompl
        exact (hrejectCompl.2 e hdbV Z' hZ'depth) haccCompl

theorem isBaire_iff_isRamsey
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (target : Set P.Obj.Point) :
    IsBaire target ↔ IsRamsey R target :=
  ⟨fun h => h.isRamsey R C, fun h => h.isBaire R⟩

theorem IsMeagre.isRamseyNull
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    {target : Set P.Obj.Point}
    (hMeagre : IsMeagre target) :
    IsRamseyNull R target := by
  have hBaire : IsBaire target :=
    IsMeagre.isBaire hMeagre
  have hRamsey : IsRamsey R target :=
    IsBaire.isRamsey R C hBaire
  intro n a Y d hd
  rcases hRamsey a Y hd with ⟨X, hXY, hhom⟩
  rcases hhom with hsub | hdis
  · have hneAX : (P.objectNeighborhood a X).Nonempty :=
      R.amalgamation_nonempty a Y hd hXY
    rcases hMeagre a X hneAX with
      ⟨m, b, Z, hab, hZX, hneBZ, hdisBZ⟩
    exfalso
    rcases hneBZ with ⟨A, hAbZ⟩
    have hAbX : A ∈ P.objectNeighborhood b X :=
      R.fin.objectNeighborhood_mono hZX hAbZ
    have hAaX : A ∈ P.objectNeighborhood a X :=
      P.objectNeighborhood_initial_subset hab hAbX
    have hAtarget : A ∈ target := hsub hAaX
    exact Set.disjoint_left.1 hdisBZ hAbZ hAtarget
  · exact ⟨X, hXY, hdis⟩

theorem isMeagre_iff_isRamseyNull
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (target : Set P.Obj.Point) :
    IsMeagre target ↔ IsRamseyNull R target :=
  ⟨fun h => h.isRamseyNull R C, fun h => h.isMeagre R⟩

end TwoSorted
end RamseySpace
