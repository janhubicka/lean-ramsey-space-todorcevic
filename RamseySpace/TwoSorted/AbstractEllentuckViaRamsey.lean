import RamseySpace.TwoSorted.Diagonal
import RamseySpace.TopologicalRamsey
import RamseySpace.TopologyBridge
import RamseySpace.NullSigma

/-!
# Abstract Ellentuck from the Abstract Ramsey Theorem

This file proves the Chapter 5 Abstract Ellentuck conclusion through the
Chapter 4 two-sorted Abstract Ramsey Theorem.  The proof does not invoke
`abstractEllentuck`; it uses the diagonal specialization, the direct
topological-to-abstract bridges for open/nowhere-dense sets, and the
Ramsey-null sigma ideal.
-/

namespace RamseySpace
namespace TwoSorted

universe u v

open RamseySpace.CombinatorialForcing

/-- Ellentuck-open sets are Ramsey as a direct consequence of the diagonal
Abstract Ramsey Theorem. -/
theorem isRamsey_of_isEllentuckOpen_via_abstractRamsey
    {S : ApproximationSystem.{u, v}}
    (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed)
    {U : Set S.Point}
    (hU : S.IsEllentuckOpen U) :
    RamseySpace.IsRamsey R U := by
  apply
    (abstractBaire_iff_isRamsey_via_abstractRamsey
      R hclosed U).1
  exact
    ApproximationSystem.IsEllentuckOpen.isAbstractBaire
      S hU

/-- Nowhere-dense Ellentuck sets are Ramsey null, via the diagonal Abstract
Ramsey Theorem. -/
theorem isRamseyNull_of_isNowhereDense_via_abstractRamsey
    {S : ApproximationSystem.{u, v}}
    (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed)
    {target : Set S.Point}
    (hnd : @IsNowhereDense S.Point S.ellentuckTopology target) :
    RamseySpace.IsRamseyNull R target := by
  apply
    (abstractMeagre_iff_isRamseyNull_via_abstractRamsey
      R hclosed target).1
  exact
    ApproximationSystem.isAbstractMeagre_of_isNowhereDense_ellentuck
      hnd

/-- Meagre Ellentuck sets are Ramsey null, using the Ramsey-null sigma ideal. -/
theorem isRamseyNull_of_isMeagre_via_abstractRamsey
    {S : ApproximationSystem.{u, v}}
    (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed)
    {target : Set S.Point}
    (hM : @_root_.IsMeagre S.Point S.ellentuckTopology target) :
    RamseySpace.IsRamseyNull R target := by
  letI : TopologicalSpace S.Point := S.ellentuckTopology
  let C : FusionComplete S :=
    RamseySpace.fusionComplete_of_isMetricallyClosed R hclosed
  rcases isMeagre_iff_eq_countable_union_isNowhereDense.mp hM with
    ⟨T, hTnd, hTc, hEq⟩
  rcases Set.eq_empty_or_nonempty T with rfl | hTne
  · rw [hEq]
    exact isRamseyNull_empty R
  · obtain ⟨f, hf⟩ :
        ∃ f : ℕ → Set S.Point, T = Set.range f :=
      Set.Countable.exists_eq_range hTc hTne
    have hNull : ∀ i, RamseySpace.IsRamseyNull R (f i) := by
      intro i
      apply
        isRamseyNull_of_isNowhereDense_via_abstractRamsey
          R hclosed
      apply hTnd
      rw [hf]
      exact Set.mem_range_self i
    have hUnionNull : RamseySpace.IsRamseyNull R (⋃ i, f i) :=
      RamseySpace.CombinatorialForcing.isRamseyNull_iUnion
        R C f hNull
    rw [hEq, hf, Set.sUnion_range]
    exact hUnionNull

/-- Baire-property sets in the Ellentuck topology are Ramsey, derived through
the Abstract Ramsey Theorem rather than the standalone Abstract Ellentuck
proof. -/
theorem isRamsey_of_baireMeasurableSet_via_abstractRamsey
    {S : ApproximationSystem.{u, v}}
    (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed)
    {target : Set S.Point}
    (hB :
      @BaireMeasurableSet S.Point S.ellentuckTopology target) :
    RamseySpace.IsRamsey R target := by
  letI : TopologicalSpace S.Point := S.ellentuckTopology
  rcases hB.residualEq_isOpen with ⟨U, hUopen, hEq⟩

  let M : Set S.Point :=
    {x | ¬ (x ∈ target ↔ x ∈ U)}

  have hM : _root_.IsMeagre M := by
    unfold _root_.IsMeagre
    rw [Filter.eventuallyEqSet_iff] at hEq
    have hcompl :
        Mᶜ = {x : S.Point | x ∈ target ↔ x ∈ U} := by
      ext x
      simp [M]
    rw [hcompl]
    exact hEq

  have hMnull : RamseySpace.IsRamseyNull R M :=
    isRamseyNull_of_isMeagre_via_abstractRamsey
      R hclosed hM

  have hUEll : S.IsEllentuckOpen U :=
    (S.isOpen_ellentuck_iff U).1 hUopen
  have hURamsey : RamseySpace.IsRamsey R U :=
    isRamsey_of_isEllentuckOpen_via_abstractRamsey
      R hclosed hUEll

  have hAgree :
      ∀ {x : S.Point}, x ∉ M → (x ∈ target ↔ x ∈ U) := by
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

/-- The full Abstract Ellentuck Theorem obtained as a consequence of the
two-sorted Abstract Ramsey Theorem. -/
theorem abstractEllentuck_via_abstractRamsey
    {S : ApproximationSystem.{u, v}}
    (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed) :
    RamseySpace.IsTopologicalRamseySpace R := by
  constructor
  · intro target hB
    exact
      isRamsey_of_baireMeasurableSet_via_abstractRamsey
        R hclosed hB
  · intro target hM
    exact
      isRamseyNull_of_isMeagre_via_abstractRamsey
        R hclosed hM

/-- Source-facing basic-neighborhood formulation, again derived through the
Abstract Ramsey Theorem. -/
theorem abstractEllentuck_onBasicNeighborhoods_via_abstractRamsey
    {S : ApproximationSystem.{u, v}}
    (R : AbstractRamseySpace S)
    (hclosed : S.IsMetricallyClosed) :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods (S := S) := by
  constructor
  · intro target hB
    exact
      (isRamsey_iff_onBasicNeighborhoods R target).1
        ((abstractEllentuck_via_abstractRamsey R hclosed).1 target hB)
  · intro target hM
    exact
      (isRamseyNull_iff_onBasicNeighborhoods R target).1
        ((abstractEllentuck_via_abstractRamsey R hclosed).2 target hM)

end TwoSorted
end RamseySpace
