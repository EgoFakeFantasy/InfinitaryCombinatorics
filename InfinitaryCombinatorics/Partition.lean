import InfinitaryCombinatorics.PairColoring
import Mathlib.SetTheory.Cardinal.Pigeonhole

namespace InfinitaryCombinatorics
open Set Cardinal
universe u v

/-- The pair partition relation for a specified vertex and colour type. -/
def PairPartition (V : Type u) (K : Type v) (μ : Cardinal.{u}) : Prop :=
  ∀ c : PairColoring V K, ∃ s : Set V, ∃ k : K, #s = μ ∧ c.Monochromatic s k

theorem monochromatic_hasClique {V : Type u} {K : Type v} {c : PairColoring V K}
    {s : Set V} {k : K} (hs : s.Infinite) (hc : c.Monochromatic s k) (n : ℕ) :
    c.HasClique n := by
  let e : ℕ ↪ s := hs.natEmbedding s
  let f : Fin n ↪ V :=
    ⟨fun i => (e i.val).val, fun i j h => Fin.ext (e.injective (Subtype.ext h))⟩
  refine ⟨f, k, ?_⟩
  intro i j hij
  exact hc (f i) (e i.val).property (f j) (e j.val).property (f.injective.ne hij)

theorem monochromatic_recolor {V : Type u} {K L : Type v} {c : PairColoring V K}
    {s : Set V} {k : K} (hc : c.Monochromatic s k) (q : K → L) :
    (c.recolor q).Monochromatic s (q k) :=
  fun x hx y hy hxy => congrArg q (hc x hx y hy hxy)

/-- A colour class retains the size of the entire infinite domain below its cofinality. -/
theorem full_size_fiber {V K : Type u} (c : V → K)
    (hV : ℵ₀ ≤ #V) (hK : #K < (#V).ord.cof) :
    ∃ k : K, #(c ⁻¹' {k}) = #V := Cardinal.infinite_pigeonhole c hV hK

/-- Cardinal-valued graph colouring; distinguishes different infinite cardinals. -/
def HasChromaticNumber {V : Type u} (G : SimpleGraph V) (κ : Cardinal.{u}) : Prop :=
  (∃ K : Type u, #K = κ ∧ Nonempty (G.Coloring K)) ∧
  ∀ K : Type u, Nonempty (G.Coloring K) → κ ≤ #K

end InfinitaryCombinatorics
