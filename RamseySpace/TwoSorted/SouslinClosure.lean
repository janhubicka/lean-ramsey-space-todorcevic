import RamseySpace.TwoSorted.SouslinEnvelope

/-!
# Souslin closure of the two-sorted Ramsey field

This file completes Todorčević's Lemma 4.39.  The normalized scheme has exact
tail recursion, so the source proof can be organized around the residual set

  Phi_s \ union_k Phi_{s^[k]}.

Each residual is Ramsey null below the common decision fusion.  A branch
argument then shows that every point of the root envelope outside the Souslin
set belongs to one residual.
-/

namespace RamseySpace
namespace TwoSorted
namespace CombinatorialForcing

universe uR vR uS vS

variable {P : System.{uR, vR, uS, vS}}

/-- The part of one local envelope not covered by any immediate child
envelope.  This is the source's Y_s after normalizing the Souslin scheme. -/
def souslinResidual
    (R : AbstractRamseySystem P)
    (A : Souslin.Scheme P.Obj.Point)
    {n : ℕ} (a : P.Obj.Approx n)
    (X : P.Red.Point) (s : List ℕ) : Set P.Obj.Point :=
  souslinEnvelope R A a X s \
    ⋃ k : ℕ, souslinEnvelope R A a X (s ++ [k])

/-- A residual point lies in the current envelope but outside the normalized
Souslin tail.  Otherwise tail recursion would put it into a child envelope. -/
theorem souslinResidual_subset_envelope_diff_tail
    (R : AbstractRamseySystem P)
    (A : Souslin.Scheme P.Obj.Point)
    {n : ℕ} (a : P.Obj.Approx n)
    (X : P.Red.Point) (s : List ℕ) :
    souslinResidual R A a X s ⊆
      souslinEnvelope R A a X s \
        Souslin.tail (Souslin.normalize A) s := by
  intro B hB
  change
    B ∈ souslinEnvelope R A a X s ∧
      B ∉ ⋃ k : ℕ, souslinEnvelope R A a X (s ++ [k]) at hB
  refine ⟨hB.1, ?_⟩
  intro htail
  rw [Souslin.tail_normalize_eq_iUnion A s] at htail
  rcases Set.mem_iUnion.1 htail with ⟨k, hchildTail⟩
  have hbase : B ∈ P.objectNeighborhood a X := by
    have henv := hB.1
    change
      B ∈
        (P.objectNeighborhood a X ∩ Souslin.normalize A s) \
          acceptedUnion R
            (Souslin.tail (Souslin.normalize A) s)ᶜ X at henv
    exact henv.1.1
  have hchildEnv :
      B ∈ souslinEnvelope R A a X (s ++ [k]) :=
    tail_subset_souslinEnvelope R A a X (s ++ [k])
      ⟨hbase, hchildTail⟩
  exact hB.2 (Set.mem_iUnion.2 ⟨k, hchildEnv⟩)

/-- Residuals are Ramsey below the common upper reduction. -/
theorem souslinResidual_isRamseyBelow
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (A : Souslin.Scheme P.Obj.Point)
    (hA : ∀ s, IsRamsey R (A s))
    {n : ℕ} (a : P.Obj.Approx n)
    (X : P.Red.Point) (s : List ℕ) :
    IsRamseyBelow R X (souslinResidual R A a X s) := by
  have hparent :
      IsRamseyBelow R X (souslinEnvelope R A a X s) :=
    souslinEnvelope_isRamseyBelow R C A hA a X s
  have hchildren :
      IsRamseyBelow R X
        (⋃ k : ℕ, souslinEnvelope R A a X (s ++ [k])) :=
    isRamseyBelow_iUnion R C X
      (fun k => souslinEnvelope R A a X (s ++ [k]))
      (fun k => souslinEnvelope_isRamseyBelow R C A hA a X (s ++ [k]))
  change
    IsRamseyBelow R X
      (souslinEnvelope R A a X s \
        ⋃ k : ℕ, souslinEnvelope R A a X (s ++ [k]))
  exact IsRamseyBelow.diff R hparent hchildren

/-- Under the common decision schedule, every residual is Ramsey null below X.
This is the direct application of Claim 4.39.1 to the source's Y_s. -/
theorem souslinResidual_isRamseyNullBelow
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (A : Souslin.Scheme P.Obj.Point)
    (hA : ∀ s, IsRamsey R (A s))
    {n : ℕ} (a : P.Obj.Approx n)
    (X : P.Red.Point) (s : List ℕ) (n0 : ℕ)
    (hdec :
      ∀ {m : ℕ} (b : P.Obj.Approx m) {d : ℕ},
        R.fin.HasDepth b X d →
        n0 + Encodable.encode s ≤ d →
        Decides R
          (Souslin.tail (Souslin.normalize A) s)ᶜ X b) :
    IsRamseyNullBelow R X (souslinResidual R A a X s) := by
  have hRamsey :
      IsRamseyBelow R X (souslinResidual R A a X s) :=
    souslinResidual_isRamseyBelow R C A hA a X s
  have hBaire :
      IsBaireBelow (P := P) X (souslinResidual R A a X s) :=
    IsRamseyBelow.isBaireBelow R hRamsey
  have hMeagre :
      IsMeagreBelow (P := P) X (souslinResidual R A a X s) :=
    baireSubset_souslinEnvelope_diff_tail_isMeagreBelow
      R A a X s n0 hdec hBaire
      (souslinResidual_subset_envelope_diff_tail R A a X s)
  change
    IsRamseyNullBelow R X
      (souslinEnvelope R A a X s \
        ⋃ k : ℕ, souslinEnvelope R A a X (s ++ [k]))
  exact IsMeagreBelow.isRamseyNullBelow R C hMeagre

end CombinatorialForcing
end TwoSorted
end RamseySpace
