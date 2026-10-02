import Mathlib

/-!
# The Souslin operation

A source-facing implementation of Definition 4.6 in Todorčević's book.
Schemes are indexed by finite sequences of natural numbers.

We also define the standard decreasing normalization of a scheme.  The
normalization has the same Souslin result and is convenient in the envelope
proof because its tails satisfy the exact recursion
`tail s = ⋃ n, tail (s ++ [n])`.
-/

namespace RamseySpace
namespace Souslin

universe u

/-- A Souslin scheme on X. -/
abbrev Scheme (X : Type u) := List ℕ → Set X

/-- First n values of an infinite branch. -/
def branchPrefix (f : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => (branchPrefix f n).concat (f n)

@[simp] theorem branchPrefix_zero (f : ℕ → ℕ) : branchPrefix f 0 = [] := rfl

@[simp] theorem branchPrefix_succ (f : ℕ → ℕ) (n : ℕ) :
    branchPrefix f (n + 1) = (branchPrefix f n).concat (f n) := rfl

@[simp] theorem length_branchPrefix (f : ℕ → ℕ) (n : ℕ) :
    (branchPrefix f n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [branchPrefix_succ, ih]

/-- Earlier branch prefixes are obtained by taking an initial segment. -/
theorem take_branchPrefix (f : ℕ → ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (branchPrefix f n).take m = branchPrefix f m := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      rfl
  | succ n ih =>
      by_cases hmn' : m ≤ n
      · rw [branchPrefix_succ, List.concat_eq_append]
        rw [List.take_append_of_le_length]
        · exact ih hmn'
        · simpa [length_branchPrefix] using hmn'
      · have hm : m = n + 1 := by omega
        subst m
        simp [branchPrefix_succ]

/-- A branch extends a finite sequence. -/
def Extends (f : ℕ → ℕ) (s : List ℕ) : Prop :=
  branchPrefix f s.length = s

/-- The result of the Souslin operation. -/
def operation {X : Type u} (A : Scheme X) : Set X :=
  {x | ∃ f : ℕ → ℕ, ∀ n, x ∈ A (branchPrefix f n)}

/-- Tail of a scheme above a finite sequence. -/
def tail {X : Type u} (A : Scheme X) (s : List ℕ) : Set X :=
  {x | ∃ f : ℕ → ℕ, Extends f s ∧
      ∀ n, s.length ≤ n → x ∈ A (branchPrefix f n)}

theorem tail_nil {X : Type u} (A : Scheme X) :
    tail A [] = operation A := by
  ext x
  constructor
  · rintro ⟨f, hf, hmem⟩
    exact ⟨f, fun n => hmem n (Nat.zero_le n)⟩
  · rintro ⟨f, hmem⟩
    exact ⟨f, rfl, fun n hn => hmem n⟩

/-- Decreasing normalization: membership at s means membership in the
original scheme at every prefix of s. -/
def normalize {X : Type u} (A : Scheme X) : Scheme X :=
  fun s => {x | ∀ n, n ≤ s.length → x ∈ A (s.take n)}

theorem normalize_subset {X : Type u} (A : Scheme X) (s : List ℕ) :
    normalize A s ⊆ A s := by
  intro x hx
  simpa using hx s.length le_rfl

/-- One-step monotonicity of the normalized scheme. -/
theorem normalize_append_subset {X : Type u} (A : Scheme X)
    (s : List ℕ) (k : ℕ) :
    normalize A (s ++ [k]) ⊆ normalize A s := by
  intro x hx n hn
  have hn' : n ≤ (s ++ [k]).length := by simp; omega
  have hmem := hx n hn'
  have htake : (s ++ [k]).take n = s.take n := by
    rw [List.take_append_of_le_length hn]
  simpa [htake] using hmem

/-- Normalization does not change the Souslin result. -/
theorem operation_normalize {X : Type u} (A : Scheme X) :
    operation (normalize A) = operation A := by
  ext x
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    intro n
    have h := hf n n (by simp)
    have hlen : (branchPrefix f n).length ≤ n := by
      rw [length_branchPrefix]
    have htake :
        (branchPrefix f n).take n = branchPrefix f n :=
      List.take_of_length_le hlen
    rw [htake] at h
    exact h
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    intro n m hmn
    have hmem := hf m
    have hmn' : m ≤ n := by
      simpa [length_branchPrefix] using hmn
    have htake := take_branchPrefix f hmn'
    rw [htake]
    exact hmem

/-- The tail of a normalized scheme is contained in its node. -/
theorem tail_normalize_subset {X : Type u} (A : Scheme X) (s : List ℕ) :
    tail (normalize A) s ⊆ normalize A s := by
  rintro x ⟨f, hfs, hmem⟩
  have hs := hmem s.length le_rfl
  unfold Extends at hfs
  rw [hfs] at hs
  exact hs

/-- Exact tail recursion for a normalized scheme. -/
theorem tail_normalize_eq_iUnion {X : Type u} (A : Scheme X)
    (s : List ℕ) :
    tail (normalize A) s =
      ⋃ k : ℕ, tail (normalize A) (s ++ [k]) := by
  ext x
  constructor
  · rintro ⟨f, hfs, hmem⟩
    let k := f s.length
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    refine ⟨f, ?_, ?_⟩
    · unfold Extends at hfs ⊢
      simp [branchPrefix_succ, hfs, k]
    · intro n hn
      exact hmem n (by simp at hn; omega)
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨k, f, hfs, hmem⟩
    have hfs0 : Extends f s := by
      unfold Extends at hfs ⊢
      have ht := congrArg (fun l : List ℕ => l.take s.length) hfs
      have htake :
          (s ++ [k]).take s.length = s := by
        simpa using List.take_append_of_le_length (l₂ := [k]) (le_rfl : s.length ≤ s.length)
      rw [htake] at ht
      simpa [length_branchPrefix] using ht
    refine ⟨f, hfs0, ?_⟩
    intro n hn
    by_cases hEq : n = s.length
    · subst n
      have hnode :
          x ∈ normalize A (s ++ [k]) :=
        tail_normalize_subset A (s ++ [k]) ⟨f, hfs, hmem⟩
      have hsnode : x ∈ normalize A s :=
        normalize_append_subset A s k hnode
      unfold Extends at hfs0
      rw [hfs0]
      exact hsnode
    · exact hmem n (by simp; omega)

end Souslin
end RamseySpace
