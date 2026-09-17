import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

/-! Total symmetric pair colourings. Diagonal values are ignored by every predicate. -/
namespace InfinitaryCombinatorics
open Set
universe u v w

structure PairColoring (V : Type u) (K : Type v) where
  color : V → V → K
  symm : ∀ x y, color x y = color y x

namespace PairColoring
variable {V : Type u} {W : Type w} {K : Type v}

def Monochromatic (c : PairColoring V K) (s : Set V) (k : K) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → c.color x y = k

def HasClique (c : PairColoring V K) (n : ℕ) : Prop :=
  ∃ e : Fin n ↪ V, ∃ k, ∀ i j, i ≠ j → c.color (e i) (e j) = k

def pullback (c : PairColoring V K) (f : W → V) : PairColoring W K where
  color x y := c.color (f x) (f y)
  symm x y := c.symm (f x) (f y)

def recolor {L : Type*} (c : PairColoring V K) (f : K → L) : PairColoring V L where
  color x y := f (c.color x y)
  symm x y := congrArg f (c.symm x y)

theorem Monochromatic.mono {c : PairColoring V K} {s t : Set V} {k : K}
    (h : c.Monochromatic t k) (hst : s ⊆ t) : c.Monochromatic s k :=
  fun x hx y hy => h x (hst hx) y (hst hy)

theorem monochromatic_pullback (c : PairColoring V K) (e : W ↪ V) (s : Set W) (k : K) :
    (c.pullback e).Monochromatic s k ↔ c.Monochromatic (e '' s) k := by
  constructor
  · intro h x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact h a ha b hb (fun hab => hxy (congrArg e hab))
  · intro h x hx y hy hxy
    exact h (e x) (mem_image_of_mem _ hx) (e y) (mem_image_of_mem _ hy)
      (fun he => hxy (e.injective he))

def colorGraph (c : PairColoring V K) (k : K) : SimpleGraph V where
  Adj x y := x ≠ y ∧ c.color x y = k
  symm := by
    intro x y h
    exact ⟨h.1.symm, (c.symm y x).trans h.2⟩
  loopless := ⟨fun x h => h.1 rfl⟩

def TriangleFree (c : PairColoring V K) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    ∀ k, ¬ (c.color x y = k ∧ c.color y z = k ∧ c.color x z = k)

theorem triangleFree_pullback {c : PairColoring V K} (hc : c.TriangleFree) (e : W ↪ V) :
    (c.pullback e).TriangleFree := by
  intro x y z hxy hyz hxz k h
  exact hc (e x) (e y) (e z) (e.injective.ne hxy) (e.injective.ne hyz)
    (e.injective.ne hxz) k h

/-- Every assignment of colours to edges from a new point creates a triangle. -/
def BlocksExtensions (c : PairColoring V K) : Prop :=
  ∀ d : V → K, ∃ x y, x ≠ y ∧ c.color x y = d x ∧ d x = d y

/-- The new point is `none`; `k₀` fills its irrelevant diagonal. -/
def extend (c : PairColoring V K) (d : V → K) (k₀ : K) : PairColoring (Option V) K where
  color
    | none, none => k₀
    | none, some y => d y
    | some x, none => d x
    | some x, some y => c.color x y
  symm x y := by cases x <;> cases y <;> simp [c.symm]

theorem triangleFree_extend_iff (c : PairColoring V K) (d : V → K) (k₀ : K) :
    (c.extend d k₀).TriangleFree ↔ c.TriangleFree ∧
      ∀ x y, x ≠ y → ¬ (c.color x y = d x ∧ d x = d y) := by
  constructor
  · intro h
    constructor
    · intro x y z hxy hyz hxz k ht
      exact h (some x) (some y) (some z) (by simpa) (by simpa) (by simpa) k ht
    · intro x y hxy ⟨hc, hd⟩
      exact h (some x) (some y) none (by simpa) (by simp) (by simp) (d x)
        ⟨hc, hd.symm, rfl⟩
  · rintro ⟨h, hd⟩ x y z hxy hyz hxz k ht
    cases x with
    | none =>
      cases y with
      | none => exact hxy rfl
      | some y =>
        cases z with
        | none => exact hxz rfl
        | some z =>
            exact hd y z (by simpa using hyz)
              ⟨ht.2.1.trans ht.1.symm, ht.1.trans ht.2.2.symm⟩
    | some x =>
      cases y with
      | none =>
        cases z with
        | none => exact hyz rfl
        | some z =>
            exact hd x z (by simpa using hxz)
              ⟨ht.2.2.trans ht.1.symm, ht.1.trans ht.2.1.symm⟩
      | some y =>
        cases z with
        | none =>
            exact hd x y (by simpa using hxy)
              ⟨ht.1.trans ht.2.2.symm, ht.2.2.trans ht.2.1.symm⟩
        | some z =>
            exact h x y z (by simpa using hxy) (by simpa using hyz)
              (by simpa using hxz) k ht

theorem blocksExtensions_iff (c : PairColoring V K) (hc : c.TriangleFree) (k₀ : K) :
    c.BlocksExtensions ↔ ∀ d, ¬ (c.extend d k₀).TriangleFree := by
  constructor
  · intro h d he
    obtain ⟨x, y, hxy, hcx, hdy⟩ := h d
    exact ((triangleFree_extend_iff c d k₀).mp he).2 x y hxy ⟨hcx, hdy⟩
  · intro h d
    by_contra hn
    apply h d
    apply (triangleFree_extend_iff c d k₀).mpr
    refine ⟨hc, ?_⟩
    intro x y hxy ht
    exact hn ⟨x, y, hxy, ht⟩

end PairColoring
end InfinitaryCombinatorics

