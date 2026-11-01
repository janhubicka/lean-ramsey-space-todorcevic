import RamseySpace.ProperPrefixTransport
import RamseySpace.Examples.EllentuckProperA2
import RamseySpace.Examples.SupportedEllentuck

/-!
# Published A.2(3) for finite-support Ellentuck copy domains

The space of synthetic complete-support domains admits the actual strict
A.2(3), not just the reflexive-prefix interface used by the general
abstract Ramsey theorem. This result remains conditional on the
singleton-support witnesses. The manuscript's functional-copy instance
additionally requires exact range recognition from Track B.
-/

namespace RamseySpace.Examples.Ellentuck

/-- The classical Ellentuck finitization meets literal A.2(3). -/
theorem finitization_hasProperPrefixA2 :
    finitization.HasProperPrefixA2 := by
  intro n m k a b c hab hnm hbc
  exact prefix_leFin_proper hab hnm hbc

end RamseySpace.Examples.Ellentuck

namespace RamseySpace.Examples.SupportedEllentuck

universe u

variable {Vertex : Type u}

/-- Under a genuine singleton-level witness, the synthetic copy space
also meets the *proper-prefix* A.2(3) formulation of the manuscript. -/
theorem hasProperPrefixA2
    (support : Vertex → Finset ℕ) (singleton : ℕ → Vertex)
    (hsingle : ∀ n, support (singleton n) = {n}) :
    (ramseySpace support singleton hsingle).fin.HasProperPrefixA2 := by
  change
    (Ellentuck.finitization.reindex
      (decode support singleton hsingle)).HasProperPrefixA2
  exact Ellentuck.finitization.reindex_hasProperPrefixA2
    (decode support singleton hsingle)
    Ellentuck.finitization_hasProperPrefixA2

end RamseySpace.Examples.SupportedEllentuck
