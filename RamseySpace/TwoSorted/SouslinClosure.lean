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


/-- The union of all source residuals, using the fixed Encodable enumeration
of finite sequences. -/
def souslinResidualUnion
    (R : AbstractRamseySystem P)
    (A : Souslin.Scheme P.Obj.Point)
    {n : ℕ} (a : P.Obj.Approx n)
    (X : P.Red.Point) : Set P.Obj.Point :=
  ⋃ i : ℕ, souslinResidual R A a X (souslinSeq i)

/-- The countable union of the residuals is Ramsey null below X. -/
theorem souslinResidualUnion_isRamseyNullBelow
    (R : AbstractRamseySystem P)
    (C : RamseySpace.FusionComplete P.Red)
    (A : Souslin.Scheme P.Obj.Point)
    (hA : ∀ s, IsRamsey R (A s))
    {n : ℕ} (a : P.Obj.Approx n)
    (X : P.Red.Point) (n0 : ℕ)
    (hdec :
      ∀ (s : List ℕ) {m : ℕ} (b : P.Obj.Approx m) {d : ℕ},
        R.fin.HasDepth b X d →
        n0 + Encodable.encode s ≤ d →
        Decides R
          (Souslin.tail (Souslin.normalize A) s)ᶜ X b) :
    IsRamseyNullBelow R X (souslinResidualUnion R A a X) := by
  change
    IsRamseyNullBelow R X
      (⋃ i : ℕ, souslinResidual R A a X (souslinSeq i))
  exact isRamseyNullBelow_iUnion R C X
    (fun i => souslinResidual R A a X (souslinSeq i))
    (fun i =>
      souslinResidual_isRamseyNullBelow
        R C A hA a X (souslinSeq i) n0
        (fun {m} b {d} hdepth hsched =>
          hdec (souslinSeq i) b hdepth hsched))

/-- Deterministically choose a child envelope containing B whenever one
exists.  The default value is irrelevant when there is no such child. -/
noncomputable def souslinEnvelopeNext
    (R : AbstractRamseySystem P)
    (A : Souslin.Scheme P.Obj.Point)
    {n : ℕ} (a : P.Obj.Approx n)
    (X : P.Red.Point) (B : P.Obj.Point)
    (s : List ℕ) : ℕ := by
  classical
  exact
    if h : ∃ k : ℕ, B ∈ souslinEnvelope R A a X (s ++ [k]) then
      Classical.choose h
    else
      0

theorem souslinEnvelopeNext_mem
    (R : AbstractRamseySystem P)
    (A : Souslin.Scheme P.Obj.Point)
    {n : ℕ} (a : P.Obj.Approx n)
    (X : P.Red.Point) (B : P.Obj.Point)
    (s : List ℕ)
    (h : ∃ k : ℕ, B ∈ souslinEnvelope R A a X (s ++ [k])) :
    B ∈ souslinEnvelope R A a X
      (s ++ [souslinEnvelopeNext R A a X B s]) := by
  unfold souslinEnvelopeNext
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The path obtained by repeatedly following the chosen child envelope. -/
noncomputable def souslinEnvelopePath
    (R : AbstractRamseySystem P)
    (A : Souslin.Scheme P.Obj.Point)
    {n : ℕ} (a : P.Obj.Approx n)
    (X : P.Red.Point) (B : P.Obj.Point) :
    ℕ → List ℕ
  | 0 => []
  | k + 1 =>
      let s := souslinEnvelopePath R A a X B k
      s ++ [souslinEnvelopeNext R A a X B s]

/-- The corresponding infinite branch. -/
noncomputable def souslinEnvelopeBranch
    (R : AbstractRamseySystem P)
    (A : Souslin.Scheme P.Obj.Point)
    {n : ℕ} (a : P.Obj.Approx n)
    (X : P.Red.Point) (B : P.Obj.Point) :
    ℕ → ℕ :=
  fun k =>
    souslinEnvelopeNext R A a X B
      (souslinEnvelopePath R A a X B k)

theorem souslinEnvelopePath_eq_branchPrefix
    (R : AbstractRamseySystem P)
    (A : Souslin.Scheme P.Obj.Point)
    {n : ℕ} (a : P.Obj.Approx n)
    (X : P.Red.Point) (B : P.Obj.Point) :
    ∀ k : ℕ,
      souslinEnvelopePath R A a X B k =
        Souslin.branchPrefix
          (souslinEnvelopeBranch R A a X B) k := by
  intro k
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      simp [souslinEnvelopePath, Souslin.branchPrefix_succ,
        souslinEnvelopeBranch, List.concat_eq_append, ih]

/-- If B starts in the root envelope and belongs to no residual, the chosen
path remains inside an envelope at every stage. -/
theorem souslinEnvelopePath_mem_of_no_residual
    (R : AbstractRamseySystem P)
    (A : Souslin.Scheme P.Obj.Point)
    {n : ℕ} (a : P.Obj.Approx n)
    (X : P.Red.Point) (B : P.Obj.Point)
    (hroot : B ∈ souslinEnvelope R A a X [])
    (hno :
      ∀ s : List ℕ, B ∉ souslinResidual R A a X s) :
    ∀ k : ℕ,
      B ∈ souslinEnvelope R A a X
        (souslinEnvelopePath R A a X B k) := by
  intro k
  induction k with
  | zero =>
      simpa [souslinEnvelopePath] using hroot
  | succ k ih =>
      let s := souslinEnvelopePath R A a X B k
      have hchildren :
          B ∈ ⋃ j : ℕ, souslinEnvelope R A a X (s ++ [j]) := by
        by_contra hnot
        apply hno s
        change
          B ∈ souslinEnvelope R A a X s ∧
            B ∉ ⋃ j : ℕ, souslinEnvelope R A a X (s ++ [j])
        exact ⟨by simpa [s] using ih, hnot⟩
      rcases Set.mem_iUnion.1 hchildren with ⟨j, hj⟩
      have hex :
          ∃ j : ℕ, B ∈ souslinEnvelope R A a X (s ++ [j]) :=
        ⟨j, hj⟩
      have hnext :=
        souslinEnvelopeNext_mem R A a X B s hex
      simpa [s, souslinEnvelopePath] using hnext

end CombinatorialForcing
end TwoSorted
end RamseySpace
