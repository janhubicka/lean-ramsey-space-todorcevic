import RamseySpace.TwoSorted.Axioms
import RamseySpace.Closed

/-!
# Closedness and fusion for the reduction sort

Only the reduction sort `S` is required to be metrically closed in
Todorčević's Abstract Ramsey Theorem.
-/

namespace RamseySpace
namespace TwoSorted

universe uR vR uS vS

variable {P : System.{uR, vR, uS, vS}}

/-- Metric closedness of the reduction sort gives exactly the fusion
completeness used by the two-sorted forcing proof. -/
theorem fusionComplete_of_isMetricallyClosed
    (R : AbstractRamseySystem P)
    (hclosed : P.Red.IsMetricallyClosed) :
    RamseySpace.FusionComplete P.Red := by
  refine ⟨?_⟩
  intro n0 Y hY
  let c : P.Red.ApproximationCode :=
    fun n => P.Red.approx n (Y (n + 1))

  have hpref : ∀ N, P.Red.PrefixRealizable c N := by
    intro N
    refine ⟨Y (N + 1), ?_⟩
    intro n hn
    have hstab :
        P.Red.approx n (Y (N + 1)) =
          P.Red.approx n (Y (n + 1)) :=
      P.Red.fusion_approx_eq hY (by omega) (by omega)
    simpa [c] using hstab

  rcases hclosed c hpref with ⟨X, hXcode⟩
  refine ⟨X, ?_⟩
  intro k
  constructor
  · apply (R.fin.redFin.realizesOrder X (Y k)).2
    intro n
    let j : ℕ := max k (n + 1)
    have hkj : k ≤ j := Nat.le_max_left _ _
    have hnj : n + 1 ≤ j := Nat.le_max_right _ _
    have hYjYk : P.Red.le (Y j) (Y k) :=
      P.Red.fusion_le hY hkj
    rcases (R.fin.redFin.realizesOrder (Y j) (Y k)).1 hYjYk n with
      ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hstab :
        P.Red.approx n (Y j) =
          P.Red.approx n (Y (n + 1)) :=
      P.Red.fusion_approx_eq hY hnj (by omega)
    have hXj : P.Red.approx n X = P.Red.approx n (Y j) :=
      (hXcode n).trans hstab.symm
    simpa only [ApproximationSystem.finiteApprox, hXj] using hm
  · have hx :
        P.Red.approx (n0 + k) X =
          P.Red.approx (n0 + k) (Y (n0 + k + 1)) :=
      hXcode (n0 + k)
    have hstab :
        P.Red.approx (n0 + k) (Y (n0 + k + 1)) =
          P.Red.approx (n0 + k) (Y k) :=
      P.Red.fusion_approx_eq hY (by omega) (by omega)
    exact hx.trans hstab

end TwoSorted
end RamseySpace
