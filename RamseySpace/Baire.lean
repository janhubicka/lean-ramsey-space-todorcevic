import RamseySpace.EndExtension
import RamseySpace.Ramsey

/-!
# Abstract Baire and meagre sets

This file formalizes Todorčević's S-Baire and S-meagre notions in the
single-space case relevant to the Abstract Ellentuck Theorem, together with
Lemmas 4.36 and 4.38.
-/

namespace RamseySpace

universe u v

variable {S : ApproximationSystem.{u, v}}

open CombinatorialForcing

/-- The abstract Baire property: every nonempty basic neighborhood contains a
nonempty homogeneous basic neighborhood, possibly after end-extending the
finite approximation. -/
def IsAbstractBaire (target : Set S.Point) : Prop :=
  ∀ {n : ℕ} (a : S.Approx n) (Y : S.Point),
    (S.neighborhood a Y).Nonempty →
      ∃ (m : ℕ) (b : S.Approx m) (Z : S.Point),
        S.IsInitial a b ∧ S.le Z Y ∧
          (S.neighborhood b Z).Nonempty ∧
          (S.neighborhood b Z ⊆ target ∨
            Disjoint (S.neighborhood b Z) target)

/-- The abstract meagre property: every nonempty basic neighborhood contains
a nonempty basic neighborhood disjoint from the target, again allowing an
end-extension of the finite approximation. -/
def IsAbstractMeagre (target : Set S.Point) : Prop :=
  ∀ {n : ℕ} (a : S.Approx n) (Y : S.Point),
    (S.neighborhood a Y).Nonempty →
      ∃ (m : ℕ) (b : S.Approx m) (Z : S.Point),
        S.IsInitial a b ∧ S.le Z Y ∧
          (S.neighborhood b Z).Nonempty ∧
          Disjoint (S.neighborhood b Z) target

theorem IsRamsey.isAbstractBaire (R : AbstractRamseySpace S)
    {target : Set S.Point} (h : IsRamsey R target) :
    IsAbstractBaire target := by
  intro n a Y hne
  rcases hne with ⟨A, hAY⟩
  rcases R.fin.exists_hasDepth_of_mem_neighborhood hAY with ⟨d, hd⟩
  rcases h a Y hd with ⟨Z, hZY, hhom⟩
  refine ⟨n, a, Z, S.isInitial_refl a, hZY.1, ?_, hhom⟩
  exact R.amalgamation_nonempty a Y hd hZY

theorem IsRamseyNull.isAbstractMeagre (R : AbstractRamseySpace S)
    {target : Set S.Point} (h : IsRamseyNull R target) :
    IsAbstractMeagre target := by
  intro n a Y hne
  rcases hne with ⟨A, hAY⟩
  rcases R.fin.exists_hasDepth_of_mem_neighborhood hAY with ⟨d, hd⟩
  rcases h a Y hd with ⟨Z, hZY, hdis⟩
  refine ⟨n, a, Z, S.isInitial_refl a, hZY.1, ?_, hdis⟩
  exact R.amalgamation_nonempty a Y hd hZY

theorem IsAbstractMeagre.isAbstractBaire {target : Set S.Point}
    (h : IsAbstractMeagre target) :
    IsAbstractBaire target := by
  intro n a Y hne
  rcases h a Y hne with ⟨m, b, Z, hab, hZY, hnon, hdis⟩
  exact ⟨m, b, Z, hab, hZY, hnon, Or.inr hdis⟩

/-- Todorčević Lemma 4.36, nontrivial direction: abstract Baire implies Ramsey. -/
theorem IsAbstractBaire.isRamsey (R : AbstractRamseySpace S)
    (C : FusionComplete S) {target : Set S.Point}
    (hBaire : IsAbstractBaire target) :
    IsRamsey R target := by
  intro n a Y d hd

  rcases exists_global_decider R C target d Y with
    ⟨X, hXY, hdecX⟩
  have hdX : R.fin.HasDepth a X d :=
    (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hd
  have hdecA : Decides R target X a :=
    hdecX a hdX le_rfl

  rcases hdecA with hacc | hrej
  · have hsub : S.neighborhood a X ⊆ target := by
      simpa [Accepts] using hacc
    exact ⟨X, hXY, Or.inl hsub⟩
  · rcases exists_refinement_rejects_endExtensions R C hdX hdecX hrej with
      ⟨Z, hZX, hrejectTargetZ⟩
    have hZY : Z ∈ S.levelNeighborhood d Y :=
      S.levelNeighborhood_mono hXY hZX
    have hdZ : R.fin.HasDepth a Z d :=
      (R.fin.hasDepth_iff_of_mem_levelNeighborhood hZX).2 hdX

    rcases exists_global_decider R C targetᶜ d Z with
      ⟨W, hWZ, hdecComplW⟩
    have hWY : W ∈ S.levelNeighborhood d Y :=
      S.levelNeighborhood_mono hZY hWZ
    have hdW : R.fin.HasDepth a W d :=
      (R.fin.hasDepth_iff_of_mem_levelNeighborhood hWZ).2 hdZ
    have hdecComplA : Decides R targetᶜ W a :=
      hdecComplW a hdW le_rfl

    rcases hdecComplA with haccCompl | hrejCompl
    · have hsubCompl : S.neighborhood a W ⊆ targetᶜ := by
        simpa [Accepts] using haccCompl
      exact ⟨W, hWY, Or.inr
        (Set.subset_compl_iff_disjoint_right.mp hsubCompl)⟩
    · rcases exists_refinement_rejects_endExtensions
        R C hdW hdecComplW hrejCompl with
        ⟨V, hVW, hrejectComplV⟩
      have hVZ : V ∈ S.levelNeighborhood d Z :=
        S.levelNeighborhood_mono hWZ hVW
      have hVY : V ∈ S.levelNeighborhood d Y :=
        S.levelNeighborhood_mono hZY hVZ
      have hneAV : (S.neighborhood a V).Nonempty :=
        R.amalgamation_nonempty a W hdW hVW

      rcases hBaire a V hneAV with
        ⟨m, b, Z0, hab, hZ0V, hneBZ0, hhom⟩

      have hneBV : (S.neighborhood b V).Nonempty := by
        rcases hneBZ0 with ⟨D, hD⟩
        exact ⟨D, S.neighborhood_mono hZ0V hD⟩
      have hneBZ : (S.neighborhood b Z).Nonempty := by
        rcases hneBV with ⟨D, hD⟩
        exact ⟨D, S.neighborhood_mono hVZ.1 hD⟩

      have hrejectTargetV : Rejects R target V b := by
        have hrejectTargetZ : Rejects R target Z b :=
          hrejectTargetZ b hab hneBZ
        exact rejects_mono R hrejectTargetZ hVZ.1 hneBV

      have hrejectCompl : Rejects R targetᶜ V b :=
        hrejectComplV b hab hneBV

      rcases hneBV with ⟨D, hDbV⟩
      rcases R.fin.exists_hasDepth_of_mem_neighborhood hDbV with
        ⟨e, hdbV⟩
      rcases R.amalgamation_refine b V hdbV hZ0V hneBZ0 with
        ⟨Z', hZ'depth, hsub⟩

      exfalso
      rcases hhom with hsubTarget | hdisTarget
      · have haccTarget : Accepts target Z' b := by
          unfold Accepts
          exact hsub.trans hsubTarget
        exact (hrejectTargetV.2 e hdbV Z' hZ'depth) haccTarget
      · have hsubCompl : S.neighborhood b Z0 ⊆ targetᶜ :=
          Set.subset_compl_iff_disjoint_right.mpr hdisTarget
        have haccCompl : Accepts targetᶜ Z' b := by
          unfold Accepts
          exact hsub.trans hsubCompl
        exact (hrejectCompl.2 e hdbV Z' hZ'depth) haccCompl

/-- Todorčević Lemma 4.36. -/
theorem isAbstractBaire_iff_isRamsey (R : AbstractRamseySpace S)
    (C : FusionComplete S) (target : Set S.Point) :
    IsAbstractBaire target ↔ IsRamsey R target :=
  ⟨fun h => h.isRamsey R C, fun h => h.isAbstractBaire R⟩

/-- Todorčević Lemma 4.38, nontrivial direction: abstract meagre implies
Ramsey null. -/
theorem IsAbstractMeagre.isRamseyNull (R : AbstractRamseySpace S)
    (C : FusionComplete S) {target : Set S.Point}
    (hMeagre : IsAbstractMeagre target) :
    IsRamseyNull R target := by
  have hBaire : IsAbstractBaire target :=
    IsAbstractMeagre.isAbstractBaire hMeagre
  have hRamsey : IsRamsey R target :=
    IsAbstractBaire.isRamsey R C hBaire
  intro n a Y d hd
  rcases hRamsey a Y hd with ⟨X, hXY, hhom⟩
  rcases hhom with hsub | hdis
  · have hneAX : (S.neighborhood a X).Nonempty :=
      R.amalgamation_nonempty a Y hd hXY
    rcases hMeagre a X hneAX with
      ⟨m, b, Z, hab, hZX, hneBZ, hdisBZ⟩
    exfalso
    rcases hneBZ with ⟨D, hDbZ⟩
    have hDbX : D ∈ S.neighborhood b X :=
      S.neighborhood_mono hZX hDbZ
    have hDaX : D ∈ S.neighborhood a X :=
      S.neighborhood_initial_subset hab hDbX
    have hDtarget : D ∈ target := hsub hDaX
    exact Set.disjoint_left.1 hdisBZ hDbZ hDtarget
  · exact ⟨X, hXY, hdis⟩

/-- Todorčević Lemma 4.38. -/
theorem isAbstractMeagre_iff_isRamseyNull (R : AbstractRamseySpace S)
    (C : FusionComplete S) (target : Set S.Point) :
    IsAbstractMeagre target ↔ IsRamseyNull R target :=
  ⟨fun h => h.isRamseyNull R C, fun h => h.isAbstractMeagre R⟩

end RamseySpace
