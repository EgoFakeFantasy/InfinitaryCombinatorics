import InfinitaryCombinatorics

/-! Consumer checks: these statements deliberately spell out the intended public semantics. -/
open Set Cardinal InfinitaryCombinatorics

example {X : Type*} (A : Set (Set X)) : MAD A ↔
    R0.AlmostDisjoint A ∧ ∀ B,
      ((∀ a ∈ B, a.Infinite) ∧ ∀ a ∈ B, ∀ b ∈ B, a ≠ b → (a ∩ b).Finite) →
      A ⊆ B → B = A := mad_iff_maximal A

example {X : Type*} (A : Set (Set X)) (hA : R0.AlmostDisjoint A) :
    ¬ InIdeal A Set.univ := ideal_proper_of_infinite_ad hA

example : ADFamily ({Set.univ} : Set (Set ℕ)) := by
  constructor
  · intro a ha
    have : a = Set.univ := mem_singleton_iff.mp ha
    simpa [this] using (infinite_univ : (Set.univ : Set ℕ).Infinite)
  · intro a ha b hb hab
    exact (hab ((mem_singleton_iff.mp ha).trans (mem_singleton_iff.mp hb).symm)).elim

example : ¬ R0.AlmostDisjoint ({Set.univ} : Set (Set ℕ)) :=
  fun h => h.1 (finite_singleton Set.univ)

example (c : PairColoring ℕ ℕ) (hc : c.TriangleFree) :
    (∀ d : ℕ → ℕ, ∃ x y, x ≠ y ∧ c.color x y = d x ∧ d x = d y) ↔
    ∀ d, ¬ (c.extend d 0).TriangleFree := c.blocksExtensions_iff hc 0

example : ¬ (PairColoring.mk (fun _ _ : ℕ => ()) (fun _ _ => rfl)).TriangleFree := by
  intro h
  exact h 0 1 2 (by decide) (by decide) (by decide) () ⟨rfl, rfl, rfl⟩

example {V K : Type*} {c : PairColoring V K} {s : Set V} {k : K}
    (hs : s.Infinite) (hc : c.Monochromatic s k) : c.HasClique 4 :=
  monochromatic_hasClique hs hc 4

example {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] (x y : ι → Bool) (hxy : x ≠ y) :
    x (delta x y hxy) ≠ y (delta x y hxy) ∧
      ∀ γ < delta x y hxy, x γ = y γ := delta_spec x y hxy

example (n : ℕ) : (DisjointType.separated (n + 1)).depth = 0 :=
  DisjointType.separated_depth n

example : ∃ (width : ℕ → ℕ) (t : ∀ k, DisjointType (width k + 1)),
    BoundedTypeDepth width t ∧ ¬ BoundedTypeWidth width :=
  exists_boundedDepth_unboundedWidth

example : Directed.Acyclic (⟨fun _ _ : ℕ => False⟩ : Digraph ℕ) := by
  rintro n ⟨p⟩
  exact p.edge ⟨0, p.positive⟩

example {V K : Type*} (D : Digraph V) (c : V → K) :
    Directed.IsDicoloring D c ↔
      ∀ k, Directed.Acyclic (Directed.pullback D (fun x : {v // c v = k} => x.val)) :=
  Directed.isDicoloring_iff_fibers D c

example {X : Type*} {A B : Set (Set X)} (hA : ¬ R0.FinIntersecting A)
    (hAB : A ⊆ B) (hB : MAD B) : MAD B ∧ ¬ R0.FinIntersecting B :=
  nonFI_mad_extension hA hAB hB

example : ∃ A : Set (Set ℕ), R0.AlmostDisjoint A ∧
    ¬ R0.FinIntersecting A ∧ #A = R0.splittingNumber :=
  R0.exists_non_finIntersecting_ad_of_size_splittingNumber

#check Pr1Witness
#check TypeGuessing
#check DeltaRegressive
#check HasChromaticNumber
#check Directed.HasDichromaticNumber
#check R0.nonFinIntersectingNumber_eq_splittingNumber


example (S : Set (Set ℕ)) (hS : S.Countable) :
    ∃ i : Set ℕ, i.Infinite ∧ ∀ s ∈ S, ¬ ((i ∩ s).Infinite ∧ (i \ s).Infinite) :=
  exists_unsplit_of_countable S hS

example {X : Type*} (A : Set (Set X)) (hA : A.Countable) : R0.FinIntersecting A :=
  finIntersecting_of_countable A hA

example : ℵ₁ ≤ R0.splittingNumber ∧ R0.splittingNumber ≤ 2 ^ ℵ₀ :=
  ⟨aleph_one_le_splittingNumber, splittingNumber_le_continuum⟩
