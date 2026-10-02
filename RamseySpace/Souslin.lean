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
def prefix (f : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => (prefix f n).concat (f n)

@[simp] theorem prefix_zero (f : ℕ → ℕ) : prefix f 0 = [] := rfl

@[simp] theorem prefix_succ (f : ℕ → ℕ) (n : ℕ) :
    prefix f (n + 1) = (prefix f n).concat (f n) := rfl

@[simp] theorem length_prefix (f : ℕ → ℕ) (n : ℕ) :
    (prefix f n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prefix, ih]

/-- Earlier branch prefixes are obtained by taking an initial segment. -/
theorem take_prefix (f : ℕ → ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (prefix f n).take m = prefix f m := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      rfl
  | succ n ih =>
      by_cases hmn' : m ≤ n
      · rw [prefix_succ, List.take_concat_of_le_length]
        · exact ih hmn'
        · simpa using hmn'
      · have hm : m = n + 1 := by omega
        subst m
        simp [prefix_succ]

/-- A branch extends a finite sequence. -/
def Extends (f : ℕ → ℕ) (s : List ℕ) : Prop :=
  prefix f s.length = s

/-- The result of the Souslin operation. -/
def operation {X : Type u} (A : Scheme X) : Set X :=
  {x | ∃ f : ℕ → ℕ, ∀ n, x ∈ A (prefix f n)}

/-- Tail of a scheme above a finite sequence. -/
def tail {X : Type u} (A : Scheme X) (s : List ℕ) : Set X :=
  {x | ∃ f : ℕ → ℕ, Extends f s ∧
      ∀ n, s.length ≤ n → x ∈ A (prefix f n)}

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
    simpa [length_prefix] using h
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    intro n m hmn
    have hmem := hf m
    have htake := take_prefix f hmn
    simpa [htake] using hmem

/-- The tail of a normalized scheme is contained in its node. -/
theorem tail_normalize_subset {X : Type u} (A : Scheme X) (s : List ℕ) :
    tail (normalize A) s ⊆ normalize A s := by
  rintro x ⟨f, hfs, hmem⟩
  have hs := hmem s.length le_rfl
  simpa [Extends, hfs] using hs

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
      simp [prefix_succ, hfs, k]
    · intro n hn
      exact hmem n (by simp at hn; omega)
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨k, f, hfs, hmem⟩
    refine ⟨f, ?_, ?_⟩
    · unfold Extends at hfs ⊢
      have ht := congrArg (List.take s.length) hfs
      simpa using ht
    · intro n hn
      by_cases hEq : n = s.length
      · subst n
        have hnode :
            x ∈ normalize A (s ++ [k]) :=
          tail_normalize_subset A (s ++ [k]) ⟨f, hfs, hmem⟩
        exact normalize_append_subset A s k hnode
      · exact hmem n (by simp; omega)

end Souslin
end RamseySpace
