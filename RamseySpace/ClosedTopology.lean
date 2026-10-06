import RamseySpace.Closed
import Mathlib.Topology.Constructions

/-!
# Product-topological form of closedness

Todorčević defines a closed Ramsey triple by identifying each point with its
approximation code and asking that the image be closed in the Tychonoff
product of the discrete approximation levels.

The forcing development uses the equivalent finite-prefix realization
criterion.  This file proves the equivalence in Lean.
-/

namespace RamseySpace
namespace ApproximationSystem

universe u v

variable (S : ApproximationSystem.{u, v})

section Tychonoff

/-- Each approximation level is given its discrete topology, and full codes
carry the resulting Tychonoff product topology. -/
local instance levelTopology (n : ℕ) : TopologicalSpace (S.Approx n) := ⊥
local instance codeTopology : TopologicalSpace S.ApproximationCode :=
  Pi.topologicalSpace

/-- Literal topological closedness of the approximation-code image in the
Tychonoff product of the discrete level spaces. -/
def IsTychonoffClosed : Prop :=
  IsClosed (Set.range S.code)

/-- Closedness in the discrete Tychonoff product is equivalent to the
finite-prefix realization criterion used by the fusion proof. -/
theorem isTychonoffClosed_iff_isClosedApproximationImage :
    S.IsTychonoffClosed ↔ S.IsClosedApproximationImage := by
  constructor
  · intro hclosed c hpref
    have hcclosure : c ∈ closure (Set.range S.code) := by
      rw [mem_closure_iff]
      intro o ho hco
      rcases (isOpen_pi_iff.mp ho) c hco with
        ⟨I, U, hIU, hsub⟩
      rcases I.exists_nat_subset_range with ⟨N, hIN⟩
      rcases hpref N with ⟨X, hX⟩
      have hcodePi : S.code X ∈ (↑I : Set ℕ).pi U := by
        intro i hiI
        have hiN : i < N := Finset.mem_range.mp (hIN hiI)
        have hEq : S.code X i = c i := by
          exact hX i (Nat.le_of_lt hiN)
        have hci : c i ∈ U i := (hIU i hiI).2
        simpa [hEq] using hci
      exact ⟨S.code X, hsub hcodePi, ⟨X, rfl⟩⟩
    have hcrange : c ∈ Set.range S.code := by
      rwa [hclosed.closure_eq] at hcclosure
    rcases hcrange with ⟨X, hX⟩
    refine ⟨X, ?_⟩
    intro n
    exact congrFun hX n
  · intro hprefClosed
    change IsClosed (Set.range S.code)
    rw [← isOpen_compl_iff]
    rw [isOpen_pi_iff]
    intro c hc
    have hnotrange : c ∉ Set.range S.code := hc
    have hfail : ∃ N, ¬ S.PrefixRealizable c N := by
      by_contra h
      push_neg at h
      rcases hprefClosed c h with ⟨X, hX⟩
      apply hnotrange
      refine ⟨X, ?_⟩
      funext n
      exact hX n
    rcases hfail with ⟨N, hN⟩
    refine ⟨Finset.range (N + 1), (fun i => {c i}), ?_, ?_⟩
    · intro i hi
      constructor
      · exact isOpen_discrete _
      · simp
    · intro d hd
      show d ∈ (Set.range S.code)ᶜ
      intro hdrange
      rcases hdrange with ⟨X, rfl⟩
      apply hN
      refine ⟨X, ?_⟩
      intro n hn
      have hnI : n ∈ Finset.range (N + 1) := by
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn)
      have hm := hd n hnI
      simpa using hm

end Tychonoff

end ApproximationSystem
end RamseySpace
