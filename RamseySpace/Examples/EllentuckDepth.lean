import RamseySpace.Examples.EllentuckFinitization

/-!
# Depth in the classical Ellentuck space

For the standard finitization by finite-set inclusion, depth has its familiar
meaning: depth zero is exactly the empty approximation, while a nonempty
approximation of depth d has its last element equal to the last element of the
protected prefix r_d(B).
-/

namespace RamseySpace
namespace Examples
namespace Ellentuck

theorem value_not_mem_prefix (X : Point) (d : ℕ) :
    X d ∉ finiteRange (S.finiteApprox d X) := by
  intro h
  change X d ∈ Set.range (approx d X).1 at h
  rcases h with ⟨i, hi⟩
  change X i.1 = X d at hi
  have hid : i.1 = d := X.injective hi
  exact (Nat.ne_of_lt i.2) hid

theorem eq_last_of_mem_succ_not_mem_prefix
    (X : Point) (d : ℕ) {x : ℕ}
    (hsucc : x ∈ finiteRange (S.finiteApprox (d + 1) X))
    (hprev : x ∉ finiteRange (S.finiteApprox d X)) :
    x = X d := by
  change x ∈ Set.range (approx (d + 1) X).1 at hsucc
  rcases hsucc with ⟨i, hi⟩
  change X i.1 = x at hi
  have hid : i.1 = d := by
    by_contra hne
    have hlt : i.1 < d := by omega
    apply hprev
    change x ∈ Set.range (approx d X).1
    refine ⟨⟨i.1, hlt⟩, ?_⟩
    change X i.1 = x
    exact hi
  calc
    x = X i.1 := hi.symm
    _ = X d := congrArg X hid

theorem depth_zero_of_empty (a : Approx 0) (B : Point) {d : ℕ}
    (hd : finitization.HasDepth a B d) :
    d = 0 := by
  by_contra hne
  have hdpos : 0 < d := Nat.pos_of_ne_zero hne
  apply hd.2 0 hdpos
  change leFin (⟨0, a⟩ : S.FiniteApprox) (S.finiteApprox 0 B)
  intro x hx
  change x ∈ Set.range a.1 at hx
  rcases hx with ⟨i, _⟩
  exact Fin.elim0 i

/-- If a nonempty approximation a has depth d in B, then d=e+1 and the
last element of a is exactly B(e). -/
theorem depth_succ_last {n : ℕ} (a : Approx n) (B : Point) {d : ℕ}
    (hn : 0 < n) (hd : finitization.HasDepth a B d) :
    ∃ e, d = e + 1 ∧
      a.1 ⟨n - 1, by omega⟩ = B e := by
  let last : Fin n := ⟨n - 1, by omega⟩
  have hlastA :
      a.1 last ∈ finiteRange (⟨n, a⟩ : S.FiniteApprox) := by
    change a.1 last ∈ Set.range a.1
    exact ⟨last, rfl⟩
  have hsubD :
      leFin (⟨n, a⟩ : S.FiniteApprox) (S.finiteApprox d B) :=
    hd.1
  have hlastD := hsubD hlastA
  have hdpos : 0 < d := by
    rcases hlastD with ⟨j, _⟩
    exact lt_of_le_of_lt (Nat.zero_le j.1) j.2
  obtain ⟨e, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)

  have hnot :
      ¬ leFin (⟨n, a⟩ : S.FiniteApprox) (S.finiteApprox e B) :=
    hd.2 e (by omega)
  change
    ¬ finiteRange (⟨n, a⟩ : S.FiniteApprox) ⊆
      finiteRange (S.finiteApprox e B) at hnot
  rcases Set.not_subset.mp hnot with ⟨x, hxa, hxnot⟩
  have hxd :
      x ∈ finiteRange (S.finiteApprox (e + 1) B) :=
    hsubD hxa
  have hxlast : x = B e :=
    eq_last_of_mem_succ_not_mem_prefix B e hxd hxnot

  have hlastD' :
      a.1 last ∈ finiteRange (S.finiteApprox (e + 1) B) :=
    hsubD hlastA
  rcases hlastD' with ⟨j, hj⟩
  change B j.1 = a.1 last at hj
  have hlast_le : a.1 last ≤ B e := by
    rw [← hj]
    exact B.monotone (by omega)

  rcases hxa with ⟨i, hi⟩
  change a.1 i = x at hi
  have hilast : i.1 ≤ last.1 := by
    dsimp [last]
    omega
  have hx_le : x ≤ a.1 last := by
    rw [← hi]
    exact a.1.monotone hilast
  have hlast_ge : B e ≤ a.1 last := by
    rw [← hxlast]
    exact hx_le

  exact ⟨e, rfl, le_antisymm hlast_le hlast_ge⟩

end Ellentuck
end Examples
end RamseySpace
