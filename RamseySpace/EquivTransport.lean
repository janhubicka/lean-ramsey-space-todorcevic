import RamseySpace.AbstractEllentuck

/-!
# Reindexing a Ramsey space by a bijection of its infinite objects

This is the reusable transport interface for copy spaces such as the three
Hrushovski spaces. Only the *points* are renamed: the actual approximation
types, the refinement order, and the finite approximation map are pulled
back. Consequently every published A.1--A.4 obligation, as well as
Tychonoff closedness, is inherited without any additional hypothesis.

This theorem does not construct an equivalence between a concrete space
of Hrushovski copies and an existing Ramsey space. That identification,
including the approximation map, is an independent mathematical task.
-/

namespace RamseySpace

universe u v w

variable {α : Type w}

namespace ApproximationSystem

/-- Rename points along a bijection, retaining all original approximation
types. An order isomorphism alone is not sufficient: the approximations
must be transported too. -/
def reindex (S : ApproximationSystem.{u, v})
    (e : α ≃ S.Point) : ApproximationSystem.{w, v} where
  Point := α
  Approx := S.Approx
  le := fun X Y => S.le (e X) (e Y)
  le_refl := fun X => S.le_refl (e X)
  le_trans := fun hXY hYZ => S.le_trans hXY hYZ
  approx := fun n X => S.approx n (e X)
  approx_surjective := by
    intro n a
    rcases S.approx_surjective n a with ⟨Y, hY⟩
    exact ⟨e.symm Y, by simpa using hY⟩
  empty := S.empty
  approx_zero := fun X => S.approx_zero (e X)
  separated := by
    intro X Y h
    apply e.injective
    apply S.separated
    exact h
  coherent := by
    intro X Y n h m hm
    exact S.coherent h m hm

@[simp] theorem reindex_mem_neighborhood
    (S : ApproximationSystem.{u, v}) (e : α ≃ S.Point)
    {n : ℕ} {a : S.Approx n} {X Y : α} :
    X ∈ (S.reindex e).neighborhood a Y ↔
      e X ∈ S.neighborhood a (e Y) :=
  Iff.rfl

@[simp] theorem reindex_mem_levelNeighborhood
    (S : ApproximationSystem.{u, v}) (e : α ≃ S.Point)
    {n : ℕ} {X Y : α} :
    X ∈ (S.reindex e).levelNeighborhood n Y ↔
      e X ∈ S.levelNeighborhood n (e Y) :=
  Iff.rfl

/-- Exact copy-space identification also preserves the *Ellentuck open*
sets, not only the four axioms. This is the topology comparison required
for transport of the actual manuscript neighbourhoods. -/
theorem reindex_isEllentuckOpen_iff
    (S : ApproximationSystem.{u, v}) (e : α ≃ S.Point)
    (U : Set S.Point) :
    (S.reindex e).IsEllentuckOpen (e ⁻¹' U) ↔
      S.IsEllentuckOpen U := by
  constructor
  · intro h X hX
    have hpre : e.symm X ∈ e ⁻¹' U := by simpa using hX
    rcases h hpre with ⟨n, a, B, hXB, hsub⟩
    refine ⟨n, a, e B, ?_, ?_⟩
    · simpa using (S.reindex_mem_neighborhood e).mp hXB
    · intro Z hZ
      have hZ' : e.symm Z ∈ (S.reindex e).neighborhood a B :=
        (S.reindex_mem_neighborhood e).mpr (by simpa using hZ)
      simpa only [Set.mem_preimage, Equiv.apply_symm_apply] using (hsub hZ')
  · intro h X hX
    rcases h hX with ⟨n, a, B, hXB, hsub⟩
    refine ⟨n, a, e.symm B, ?_, ?_⟩
    · apply (S.reindex_mem_neighborhood e).mpr
      simpa using hXB
    · intro Y hY
      have htransport : e Y ∈ S.neighborhood a (e (e.symm B)) :=
        (S.reindex_mem_neighborhood e).mp hY
      have hYB : e Y ∈ S.neighborhood a B := by
        simpa only [Equiv.apply_symm_apply] using htransport
      exact hsub hYB

theorem reindex_oneStepApproximations
    (S : ApproximationSystem.{u, v}) (e : α ≃ S.Point)
    {n : ℕ} (a : S.Approx n) (Y : α) :
    (S.reindex e).oneStepApproximations a Y =
      S.oneStepApproximations a (e Y) := by
  ext b
  constructor
  · rintro ⟨X, hX, hXb⟩
    exact ⟨e X, (S.reindex_mem_neighborhood e).mp hX, hXb⟩
  · rintro ⟨X, hX, hXb⟩
    refine ⟨e.symm X, ?_, ?_⟩
    · apply (S.reindex_mem_neighborhood e).mpr
      simpa using hX
    · change S.approx (n + 1) (e (e.symm X)) = b
      simpa using hXb

/-- Finite-prefix realizability is invariant under reindexing of points. -/
theorem reindex_isClosedApproximationImage
    (S : ApproximationSystem.{u, v}) (e : α ≃ S.Point)
    (hclosed : S.IsClosedApproximationImage) :
    (S.reindex e).IsClosedApproximationImage := by
  intro c hreal
  have hrealS : ∀ N, S.PrefixRealizable c N := by
    intro N
    rcases hreal N with ⟨X, hX⟩
    exact ⟨e X, hX⟩
  rcases hclosed c hrealS with ⟨Y, hY⟩
  refine ⟨e.symm Y, ?_⟩
  intro n
  change S.approx n (e (e.symm Y)) = c n
  simpa using hY n

/-- The precise published Tychonoff closedness hypothesis is preserved. -/
theorem reindex_isTychonoffClosed
    (S : ApproximationSystem.{u, v}) (e : α ≃ S.Point)
    (hclosed : S.IsTychonoffClosed) :
    (S.reindex e).IsTychonoffClosed :=
  ((S.reindex e).isTychonoffClosed_iff_isClosedApproximationImage).2
    (S.reindex_isClosedApproximationImage e
      ((S.isTychonoffClosed_iff_isClosedApproximationImage).1 hclosed))

end ApproximationSystem

namespace Finitization

/-- The complete A.2 structure survives the same reindexing. -/
def reindex {S : ApproximationSystem.{u, v}}
    (F : Finitization S) (e : α ≃ S.Point) :
    Finitization (S.reindex e) where
  leFin := F.leFin
  leFin_refl := F.leFin_refl
  leFin_trans := fun hXY hYZ => F.leFin_trans hXY hYZ
  lowerFinite := F.lowerFinite
  realizesOrder := by
    intro X Y
    exact F.realizesOrder (e X) (e Y)
  prefix_leFin := by
    intro n m k a b c hab hbc
    rcases hab with ⟨hnm, X, hXa, hXb⟩
    have habS : S.IsInitial a b := ⟨hnm, e X, hXa, hXb⟩
    rcases F.prefix_leFin habS hbc with ⟨j, d, hd, hfin⟩
    rcases hd with ⟨hjk, Y, hYd, hYc⟩
    refine ⟨j, d, ⟨hjk, e.symm Y, ?_, ?_⟩, hfin⟩
    · change S.approx j (e (e.symm Y)) = d
      simpa using hYd
    · change S.approx k (e (e.symm Y)) = c
      simpa using hYc

end Finitization

namespace AbstractRamseySpace

/-- A.1--A.4 transported to an exactly identified concrete copy space. -/
def reindex {S : ApproximationSystem.{u, v}}
    (R : AbstractRamseySpace S) (e : α ≃ S.Point) :
    AbstractRamseySpace (S.reindex e) where
  fin := R.fin.reindex e
  amalgamation_nonempty := by
    intro n a B d hd A hAB
    rcases R.amalgamation_nonempty a (e B) hd
      (A := e A) ((S.reindex_mem_levelNeighborhood e).mp hAB) with
      ⟨X, hX⟩
    exact ⟨e.symm X, (S.reindex_mem_neighborhood e).mpr (by simpa using hX)⟩
  amalgamation_refine := by
    intro n a B d hd A hAB hne
    have hneS : (S.neighborhood a (e A)).Nonempty := by
      rcases hne with ⟨X, hX⟩
      exact ⟨e X, (S.reindex_mem_neighborhood e).mp hX⟩
    rcases R.amalgamation_refine a (e B) hd hAB hneS with
      ⟨A', hA', hsub⟩
    refine ⟨e.symm A', ?_, ?_⟩
    · apply (S.reindex_mem_levelNeighborhood e).mpr
      simpa using hA'
    · intro X hX
      have hX' : e X ∈ S.neighborhood a A' := by
        simpa using (S.reindex_mem_neighborhood e).mp hX
      exact (S.reindex_mem_neighborhood e).mpr (hsub hX')
  pigeonhole := by
    intro n a B d hd O
    rcases R.pigeonhole a (e B) hd O with ⟨A', hA', hhom⟩
    refine ⟨e.symm A', ?_, ?_⟩
    · apply (S.reindex_mem_levelNeighborhood e).mpr
      simpa using hA'
    · have hs :
          (S.reindex e).oneStepApproximations a (e.symm A') =
            S.oneStepApproximations a A' := by
        simpa using S.reindex_oneStepApproximations e a (e.symm A')
      rw [hs]
      exact hhom

end AbstractRamseySpace

/-- The textbook Ellentuck conclusion is transported only when a bijection
preserves all concrete approximations and refinements by construction. -/
theorem abstractEllentuck_reindex
    {S : ApproximationSystem.{u, v}}
    (R : AbstractRamseySpace S) (hclosed : S.IsTychonoffClosed)
    (e : α ≃ S.Point) :
    IsTopologicalRamseySpaceTextbook (S := S.reindex e) :=
  abstractEllentuck_textbook (R.reindex e)
    (S.reindex_isTychonoffClosed e hclosed)

end RamseySpace
