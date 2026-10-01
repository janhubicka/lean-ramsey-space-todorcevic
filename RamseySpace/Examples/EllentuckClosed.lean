import RamseySpace.Examples.EllentuckAxioms
import RamseySpace.Closed

/-!
# Closedness of the classical Ellentuck space

A coherent full sequence of finite approximations determines its unique
increasing enumeration by reading the kth value from level k+1. Prefix
realizability makes this enumeration strictly increasing and shows that it
has exactly the prescribed approximation code.
-/

namespace RamseySpace
namespace Examples
namespace Ellentuck

/-- Read the kth value of a full approximation code from its (k+1)st
approximation. -/
def codeValue (c : S.ApproximationCode) (k : ℕ) : ℕ :=
  (c (k + 1)).1 ⟨k, Nat.lt_succ_self k⟩

/-- A prefix-realizable full code determines an infinite increasing
enumeration. -/
def pointOfCode (c : S.ApproximationCode)
    (h : ∀ N, S.PrefixRealizable c N) : Point :=
  OrderEmbedding.ofStrictMono (codeValue c) (by
    intro k l hkl
    rcases h (l + 1) with ⟨Y, hY⟩
    have hk := congrArg
      (fun q : Approx (k + 1) => q.1 ⟨k, Nat.lt_succ_self k⟩)
      (hY (k + 1) (by omega))
    have hl := congrArg
      (fun q : Approx (l + 1) => q.1 ⟨l, Nat.lt_succ_self l⟩)
      (hY (l + 1) le_rfl)
    change Y k = codeValue c k at hk
    change Y l = codeValue c l at hl
    rw [← hk, ← hl]
    exact Y.strictMono hkl)

theorem approx_pointOfCode (c : S.ApproximationCode)
    (h : ∀ N, S.PrefixRealizable c N) (n : ℕ) :
    approx n (pointOfCode c h) = c n := by
  apply Subtype.ext
  apply DFunLike.ext _ _
  intro i
  rcases h n with ⟨Y, hY⟩
  have hsmall := congrArg
    (fun q : Approx (i.1 + 1) =>
      q.1 ⟨i.1, Nat.lt_succ_self i.1⟩)
    (hY (i.1 + 1) (by omega))
  have hbig := congrArg (fun q : Approx n => q.1 i)
    (hY n le_rfl)
  change Y i.1 = codeValue c i.1 at hsmall
  change Y i.1 = (c n).1 i at hbig
  change codeValue c i.1 = (c n).1 i
  exact hsmall.symm.trans hbig

/-- The approximation image of the classical Ellentuck space is closed in
the first-difference/product topology. -/
theorem isMetricallyClosed : S.IsMetricallyClosed := by
  intro c h
  refine ⟨pointOfCode c h, ?_⟩
  intro n
  exact approx_pointOfCode c h n

end Ellentuck
end Examples
end RamseySpace
