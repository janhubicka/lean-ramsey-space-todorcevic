import RamseySpace.Closed
import Mathlib.Topology.Constructions

/-!
# Product-topological form of closedness

Todorčević defines a closed Ramsey triple by identifying each point with the
sequence of its finite approximations and asking that the image be closed in
the Tychonoff power `AR^ℕ`, where `AR` (the set of all finite
approximations) is discrete.

The source-facing ambient space is the literal power
`FiniteApprox^ℕ`, where `FiniteApprox = Σ n, Approx n` represents the
book's union of finite approximations.
-/

namespace RamseySpace
namespace ApproximationSystem

universe u v

variable (S : ApproximationSystem.{u, v})

section PublishedTychonoff

/-- A code in the literal ambient power `AR^ℕ` of the book.  Here
`FiniteApprox = Σ n, Approx n` is the typed disjoint union representing
`AR = ⋃ₙ ARₙ`. -/
abbrev PublishedApproximationCode := ℕ → S.FiniteApprox

/-- The literal `AR^ℕ` code of an infinite object. -/
def publishedCode (X : S.Point) : S.PublishedApproximationCode :=
  fun n => S.finiteApprox n X

local instance finiteApproxTopology : TopologicalSpace S.FiniteApprox := ⊥
local instance finiteApproxDiscreteTopology :
    DiscreteTopology S.FiniteApprox := ⟨rfl⟩
local instance publishedCodeTopology :
    TopologicalSpace S.PublishedApproximationCode :=
  Pi.topologicalSpace

/-- Literal published closedness: the image of the approximation sequence is
closed in the Tychonoff power `AR^ℕ`, with `AR` discrete. -/
def IsTychonoffClosed : Prop :=
  IsClosed (Set.range S.publishedCode)

/-- Todorčević's literal Tychonoff closedness is equivalent to the
finite-prefix realization criterion used by the implementation. -/
theorem isTychonoffClosed_iff_isClosedApproximationImage :
    S.IsTychonoffClosed ↔ S.IsClosedApproximationImage := by
  constructor
  · intro hclosed c hpref
    let d : S.PublishedApproximationCode :=
      fun n => (⟨n, c n⟩ : S.FiniteApprox)
    have hdclosure : d ∈ closure (Set.range S.publishedCode) := by
      rw [mem_closure_iff]
      intro o ho hdo
      rcases (isOpen_pi_iff.mp ho) d hdo with
        ⟨I, U, hIU, hsub⟩
      rcases I.exists_nat_subset_range with ⟨N, hIN⟩
      rcases hpref N with ⟨X, hX⟩
      have hcodePi :
          S.publishedCode X ∈ (↑I : Set ℕ).pi U := by
        intro i hiI
        have hiN : i < N := Finset.mem_range.mp (hIN hiI)
        have hEq : S.publishedCode X i = d i := by
          refine Sigma.ext rfl ?_
          exact heq_of_eq (hX i (Nat.le_of_lt hiN))
        rw [hEq]
        exact (hIU i hiI).2
      exact ⟨S.publishedCode X, hsub hcodePi, ⟨X, rfl⟩⟩
    have hdrange : d ∈ Set.range S.publishedCode := by
      rwa [hclosed.closure_eq] at hdclosure
    rcases hdrange with ⟨X, hX⟩
    refine ⟨X, ?_⟩
    intro n
    have hn := congrFun hX n
    change
      (⟨n, S.approx n X⟩ : S.FiniteApprox) =
        (⟨n, c n⟩ : S.FiniteApprox) at hn
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hn
  · intro hprefClosed
    change IsClosed (Set.range S.publishedCode)
    rw [← isOpen_compl_iff]
    rw [isOpen_pi_iff]
    intro d hd
    have hnotrange : d ∉ Set.range S.publishedCode := hd
    by_cases hlevel : ∀ n, (d n).1 = n
    · let c : S.ApproximationCode :=
        fun n =>
          cast (congrArg S.Approx (hlevel n)) (d n).2
      have htag :
          ∀ n, (⟨n, c n⟩ : S.FiniteApprox) = d n := by
        intro n
        refine Sigma.ext (hlevel n).symm ?_
        exact cast_heq (congrArg S.Approx (hlevel n)) (d n).2
      have hfail : ∃ N, ¬ S.PrefixRealizable c N := by
        by_contra h
        push Not at h
        rcases hprefClosed c h with ⟨X, hX⟩
        apply hnotrange
        refine ⟨X, ?_⟩
        funext n
        calc
          S.publishedCode X n =
              (⟨n, c n⟩ : S.FiniteApprox) := by
            refine Sigma.ext rfl ?_
            exact heq_of_eq (hX n)
          _ = d n := htag n
      rcases hfail with ⟨N, hN⟩
      refine
        ⟨Finset.range (N + 1), (fun i => {d i}), ?_, ?_⟩
      · intro i hi
        constructor
        · exact isOpen_discrete _
        · simp
      · intro q hq
        show q ∈ (Set.range S.publishedCode)ᶜ
        intro hqrange
        rcases hqrange with ⟨X, rfl⟩
        apply hN
        refine ⟨X, ?_⟩
        intro n hn
        have hnI : n ∈ Finset.range (N + 1) := by
          exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn)
        have hm := hq n hnI
        have heq : S.publishedCode X n = d n := by
          simpa using hm
        rw [← htag n] at heq
        change
          (⟨n, S.approx n X⟩ : S.FiniteApprox) =
            (⟨n, c n⟩ : S.FiniteApprox) at heq
        simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using heq
    · push Not at hlevel
      rcases hlevel with ⟨n, hn⟩
      refine ⟨{n}, (fun i => {d i}), ?_, ?_⟩
      · intro i hi
        constructor
        · exact isOpen_discrete _
        · simp
      · intro q hq
        show q ∈ (Set.range S.publishedCode)ᶜ
        intro hqrange
        rcases hqrange with ⟨X, rfl⟩
        have hm := hq n (by simp)
        have heq : S.publishedCode X n = d n := by
          simpa using hm
        have hf := congrArg Sigma.fst heq
        change n = (d n).1 at hf
        exact hn hf.symm

end PublishedTychonoff

end ApproximationSystem
end RamseySpace
