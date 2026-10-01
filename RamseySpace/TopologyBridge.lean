import RamseySpace.Ellentuck
import RamseySpace.NullSigma

/-!
# Bridge from the Ellentuck topology to abstract Ramsey notions

This file translates ordinary topological nowhere-dense, meagre, and Baire
measurable sets for the Ellentuck topology into the combinatorial notions
proved in the preceding files.
-/

namespace RamseySpace

universe u v

open CombinatorialForcing

namespace ApproximationSystem

variable {S : ApproximationSystem.{u, v}}

/-- A nowhere-dense set in the Ellentuck topology is abstract meagre. -/
theorem isAbstractMeagre_of_isNowhereDense_ellentuck
    {target : Set S.Point}
    (hnd : @IsNowhereDense S.Point S.ellentuckTopology target) :
    IsAbstractMeagre target := by
  letI : TopologicalSpace S.Point := S.ellentuckTopology
  intro n a Y hne

  have hndClosure : IsNowhereDense (closure target) :=
    hnd.closure
  have hopenDense :
      IsOpen (closure target)ᶜ ∧ Dense (closure target)ᶜ :=
    isClosed_isNowhereDense_iff_compl.mp
      ⟨isClosed_closure, hndClosure⟩
  have hbasicOpen : IsOpen (S.neighborhood a Y) :=
    S.isOpen_neighborhood a Y
  rcases hopenDense.2.inter_open_nonempty
      (S.neighborhood a Y) hbasicOpen hne with
    ⟨X, hXaY, hXcomp⟩

  have hcompEll : S.IsEllentuckOpen (closure target)ᶜ :=
    (S.isOpen_ellentuck_iff _).1 hopenDense.1
  rcases hcompEll hXcomp with
    ⟨m, c, B, hXcB, hcBcomp⟩

  let l := max n m
  let b : S.Approx l := S.approx l X
  have hab : S.IsInitial a b :=
    ⟨Nat.le_max_left n m, X, hXaY.2, rfl⟩
  have hcb : S.IsInitial c b :=
    ⟨Nat.le_max_right n m, X, hXcB.2, rfl⟩
  have hsubComp : S.neighborhood b X ⊆ (closure target)ᶜ := by
    intro Z hZ
    apply hcBcomp
    apply S.neighborhood_mono hXcB.1
    exact S.neighborhood_initial_subset hcb hZ
  have hdis : Disjoint (S.neighborhood b X) target := by
    rw [Set.disjoint_left]
    intro Z hZ hZtarget
    exact (hsubComp hZ) (subset_closure hZtarget)

  refine ⟨l, b, X, hab, hXaY.1, ?_, hdis⟩
  exact ⟨X, S.le_refl X, rfl⟩

end ApproximationSystem

/-- A nowhere-dense Ellentuck set is Ramsey null. -/
theorem isRamseyNull_of_isNowhereDense_ellentuck
    {S : ApproximationSystem.{u, v}}
    (R : AbstractRamseySpace S) (C : FusionComplete S)
    {target : Set S.Point}
    (hnd : @IsNowhereDense S.Point S.ellentuckTopology target) :
    IsRamseyNull R target :=
  IsAbstractMeagre.isRamseyNull R C
    (ApproximationSystem.isAbstractMeagre_of_isNowhereDense_ellentuck hnd)

/-- A meagre set in the Ellentuck topology is Ramsey null. -/
theorem isRamseyNull_of_isMeagre_ellentuck
    {S : ApproximationSystem.{u, v}}
    (R : AbstractRamseySpace S) (C : FusionComplete S)
    {target : Set S.Point}
    (hM : @IsMeagre S.Point S.ellentuckTopology target) :
    IsRamseyNull R target := by
  letI : TopologicalSpace S.Point := S.ellentuckTopology
  rcases isMeagre_iff_eq_countable_union_isNowhereDense.mp hM with
    ⟨T, hTnd, hTc, hEq⟩
  rcases Set.eq_empty_or_nonempty T with rfl | hTne
  · rw [hEq]
    intro n a B d hd
    exact ⟨B, S.self_mem_levelNeighborhood d B, by simp⟩
  · obtain ⟨f, hf⟩ :
        ∃ f : ℕ → Set S.Point, T = Set.range f :=
      Set.Countable.exists_eq_range hTc hTne
    have hNull : ∀ i, IsRamseyNull R (f i) := by
      intro i
      apply isRamseyNull_of_isNowhereDense_ellentuck R C
      apply hTnd
      rw [hf]
      exact Set.mem_range_self i
    have hUnionNull : IsRamseyNull R (⋃ i, f i) :=
      isRamseyNull_iUnion R C f hNull
    rw [hEq, hf, Set.sUnion_range]
    intro n a B d hd
    exact hUnionNull a B hd

/-- Baire-measurable subsets of the Ellentuck topology are Ramsey. -/
theorem isRamsey_of_baireMeasurableSet_ellentuck
    {S : ApproximationSystem.{u, v}}
    (R : AbstractRamseySpace S) (C : FusionComplete S)
    {target : Set S.Point}
    (hB :
      @BaireMeasurableSet S.Point S.ellentuckTopology target) :
    IsRamsey R target := by
  letI : TopologicalSpace S.Point := S.ellentuckTopology
  rcases hB.residualEq_isOpen with ⟨U, hUopen, hEq⟩

  let M : Set S.Point :=
    {x | ¬ (x ∈ target ↔ x ∈ U)}

  have hM : IsMeagre M := by
    unfold IsMeagre
    rw [Filter.eventuallyEqSet_iff] at hEq
    have hcompl :
        Mᶜ = {x : S.Point | x ∈ target ↔ x ∈ U} := by
      ext x
      simp [M]
    rw [hcompl]
    exact hEq

  have hMnull : IsRamseyNull R M :=
    isRamseyNull_of_isMeagre_ellentuck R C hM

  have hUEll : S.IsEllentuckOpen U :=
    (S.isOpen_ellentuck_iff U).1 hUopen
  have hURamsey : IsRamsey R U :=
    isRamsey_of_isEllentuckOpen R C hUEll

  have hAgree : ∀ {x : S.Point}, x ∉ M → (x ∈ target ↔ x ∈ U) := by
    intro x hx
    simpa [M] using hx

  intro n a Y d hd
  rcases hURamsey a Y hd with ⟨X, hXY, hhomU⟩
  have hdX : R.fin.HasDepth a X d :=
    (R.fin.hasDepth_iff_of_mem_levelNeighborhood hXY).2 hd
  rcases hMnull a X hdX with ⟨Z, hZX, hdisM⟩
  have hZY : Z ∈ S.levelNeighborhood d Y :=
    S.levelNeighborhood_mono hXY hZX

  refine ⟨Z, hZY, ?_⟩
  rcases hhomU with hsubU | hdisU
  · apply Or.inl
    intro W hWaZ
    have hWaX : W ∈ S.neighborhood a X :=
      S.neighborhood_mono hZX.1 hWaZ
    have hnotM : W ∉ M := by
      intro hWM
      exact Set.disjoint_left.1 hdisM hWaZ hWM
    exact (hAgree hnotM).2 (hsubU hWaX)
  · apply Or.inr
    rw [Set.disjoint_left]
    intro W hWaZ hWt
    have hWaX : W ∈ S.neighborhood a X :=
      S.neighborhood_mono hZX.1 hWaZ
    have hnotM : W ∉ M := by
      intro hWM
      exact Set.disjoint_left.1 hdisM hWaZ hWM
    have hWU : W ∈ U :=
      (hAgree hnotM).1 hWt
    exact Set.disjoint_left.1 hdisU hWaX hWU

end RamseySpace
