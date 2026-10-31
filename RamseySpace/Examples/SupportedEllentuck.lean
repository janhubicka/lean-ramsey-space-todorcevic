import RamseySpace.EquivTransport
import RamseySpace.Examples.EllentuckTheorem

/-!
# Finite-support copy domains with ordinary Ellentuck approximation

This is the abstract source-free part of the omega-level case of the
Hrushovski paper. Given a finite support for every vertex and a genuine
singleton-support witness at every natural-number level, the set of all
support-saturated domains arising from increasing level sets is in bijection
with the classical Ellentuck space.

The construction deliberately defines a *synthetic* space of support
domains. Identifying this family with the ranges of every functional
self-embedding of the Hrushovski presentation requires the unique
finite/countable level-lifting theorem of Track B. No such identification
is postulated here.
-/

namespace RamseySpace.Examples.SupportedEllentuck

universe u

variable {Vertex : Type u}

/-- Keep precisely those vertices whose *entire finite closure support*
is represented by the increasing level set. -/
def domain (support : Vertex → Finset ℕ)
    (X : Ellentuck.Point) : Set Vertex :=
  {v | ∀ q ∈ support v, q ∈ Set.range X}

theorem singleton_mem_domain
    (support : Vertex → Finset ℕ) (singleton : ℕ → Vertex)
    (hsingle : ∀ n, support (singleton n) = {n})
    (X : Ellentuck.Point) (n : ℕ) :
    singleton n ∈ domain support X ↔ n ∈ Set.range X := by
  simp [domain, hsingle n]

theorem domain_subset_iff
    (support : Vertex → Finset ℕ) (singleton : ℕ → Vertex)
    (hsingle : ∀ n, support (singleton n) = {n})
    (X Y : Ellentuck.Point) :
    domain support X ⊆ domain support Y ↔
      Set.range X ⊆ Set.range Y := by
  constructor
  · intro h n hn
    apply (singleton_mem_domain support singleton hsingle Y n).mp
    exact h ((singleton_mem_domain support singleton hsingle X n).mpr hn)
  · intro h v hv q hq
    exact h (hv q hq)

/-- If singletons are represented, the complete-supported domain uniquely
determines its increasing level enumeration. -/
theorem domain_injective
    (support : Vertex → Finset ℕ) (singleton : ℕ → Vertex)
    (hsingle : ∀ n, support (singleton n) = {n}) :
    Function.Injective (domain support) := by
  intro X Y h
  apply OrderEmbedding.eq_of_range_eq
  ext n
  have hn := congrArg (fun D : Set Vertex => singleton n ∈ D) h
  simpa only [singleton_mem_domain support singleton hsingle] using hn

/-- Exactly the domains represented by strictly increasing infinite
level enumerations, with no assertion about functional embeddings. -/
def Copy (support : Vertex → Finset ℕ) : Type u :=
  {D : Set Vertex // ∃ X : Ellentuck.Point, domain support X = D}

def ofPoint (support : Vertex → Finset ℕ)
    (X : Ellentuck.Point) : Copy support :=
  ⟨domain support X, ⟨X, rfl⟩⟩

theorem ofPoint_bijective
    (support : Vertex → Finset ℕ) (singleton : ℕ → Vertex)
    (hsingle : ∀ n, support (singleton n) = {n}) :
    Function.Bijective (ofPoint support) := by
  constructor
  · intro X Y h
    exact domain_injective support singleton hsingle
      (congrArg Subtype.val h)
  · intro D
    rcases D.2 with ⟨X, hX⟩
    refine ⟨X, ?_⟩
    apply Subtype.ext
    exact hX

/-- Exact equivalence, rather than an order-isomorphism lacking the finite
approximation map. -/
def encode (support : Vertex → Finset ℕ) (singleton : ℕ → Vertex)
    (hsingle : ∀ n, support (singleton n) = {n}) :
    Ellentuck.Point ≃ Copy support :=
  Equiv.ofBijective (ofPoint support)
    (ofPoint_bijective support singleton hsingle)

def decode (support : Vertex → Finset ℕ) (singleton : ℕ → Vertex)
    (hsingle : ∀ n, support (singleton n) = {n}) :
    Copy support ≃ Ellentuck.Point :=
  (encode support singleton hsingle).symm

/-- Decoding and re-encoding recovers the *entire* vertex domain,
not merely the set of represented levels. -/
theorem domain_decode
    (support : Vertex → Finset ℕ) (singleton : ℕ → Vertex)
    (hsingle : ∀ n, support (singleton n) = {n})
    (D : Copy support) :
    domain support (decode support singleton hsingle D) = D.1 := by
  have h := (encode support singleton hsingle).apply_symm_apply D
  exact congrArg Subtype.val h

/-- The transferred quasi-order is exactly inclusion of complete
support-saturated vertex domains. -/
theorem le_iff_domain_subset
    (support : Vertex → Finset ℕ) (singleton : ℕ → Vertex)
    (hsingle : ∀ n, support (singleton n) = {n})
    (D E : Copy support) :
    (Ellentuck.S.reindex (decode support singleton hsingle)).le D E ↔
      D.1 ⊆ E.1 := by
  change Set.range (decode support singleton hsingle D) ⊆
    Set.range (decode support singleton hsingle E) ↔ D.1 ⊆ E.1
  rw [← domain_decode support singleton hsingle D,
      ← domain_decode support singleton hsingle E]
  exact (domain_subset_iff support singleton hsingle _ _).symm

/-- A copy represented by X has precisely X's classical first-n
approximation. -/
theorem approx_ofPoint
    (support : Vertex → Finset ℕ) (singleton : ℕ → Vertex)
    (hsingle : ∀ n, support (singleton n) = {n})
    (X : Ellentuck.Point) (n : ℕ) :
    (Ellentuck.S.reindex (decode support singleton hsingle)).approx n
      (ofPoint support X) = Ellentuck.approx n X := by
  change Ellentuck.approx n
    (decode support singleton hsingle (ofPoint support X)) =
      Ellentuck.approx n X
  have h := (encode support singleton hsingle).symm_apply_apply X
  change decode support singleton hsingle (ofPoint support X) = X at h
  rw [h]

/-- The finite approximations are literally the first n image levels. -/
def approximationSystem
    (support : Vertex → Finset ℕ) (singleton : ℕ → Vertex)
    (hsingle : ∀ n, support (singleton n) = {n}) :
    ApproximationSystem :=
  Ellentuck.S.reindex (decode support singleton hsingle)

/-- The published A.1–A.4 interface is transported without any additional
Ramsey assumption about the finite closure diagrams. -/
def ramseySpace
    (support : Vertex → Finset ℕ) (singleton : ℕ → Vertex)
    (hsingle : ∀ n, support (singleton n) = {n}) :
    AbstractRamseySpace (approximationSystem support singleton hsingle) :=
  Ellentuck.ramseySpace.reindex (decode support singleton hsingle)

/-- Closure of the approximation-code image, not closure of the domains
inside the Cantor cube of all vertex subsets. -/
theorem isTychonoffClosed
    (support : Vertex → Finset ℕ) (singleton : ℕ → Vertex)
    (hsingle : ∀ n, support (singleton n) = {n}) :
    (approximationSystem support singleton hsingle).IsTychonoffClosed :=
  Ellentuck.S.reindex_isTychonoffClosed
    (decode support singleton hsingle)
    Ellentuck.isTychonoffClosed

/-- The classical Ellentuck theorem on synthetic support-saturated copy
domains. The manuscript instance remains conditional on the actual
unique lifting/recognition theorem. -/
theorem supportedEllentuck
    (support : Vertex → Finset ℕ) (singleton : ℕ → Vertex)
    (hsingle : ∀ n, support (singleton n) = {n}) :
    IsTopologicalRamseySpaceTextbook
      (S := approximationSystem support singleton hsingle) :=
  abstractEllentuck_reindex Ellentuck.ramseySpace
    Ellentuck.isTychonoffClosed (decode support singleton hsingle)

end RamseySpace.Examples.SupportedEllentuck
