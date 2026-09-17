import Formalizations.A1.Principles

/-!
# Local numbering on empty club intervals

The least point of D strictly above x determines a countable convex fibre.
Classical choice selects an injection from each countable initial segment to
Nat. This is one common numbering for the whole ordinal, not a global injection.
-/

namespace InfinitaryCombinatorics.Formalizations.A1
open Set Order
noncomputable section

/-- Cofinality supplies a D-point strictly above every point. -/
theorem exists_next (D : Set Point) (hD : IsCofinal D) (x : Point) :
    {d : Point | d ∈ D ∧ x < d}.Nonempty := by
  obtain ⟨y, hxy⟩ := point_exists_gt x
  obtain ⟨d, hd, hyd⟩ := hD y
  exact ⟨d, hd, hxy.trans_le hyd⟩

/-- The least D-point strictly after x. Only cofinality is needed. -/
def nextD (D : Set Point) (hD : IsCofinal D) (x : Point) : Point :=
  wellFounded_lt.min {d | d ∈ D ∧ x < d} (exists_next D hD x)

theorem nextD_spec (D : Set Point) (hD : IsCofinal D) (x : Point) :
    nextD D hD x ∈ D ∧ x < nextD D hD x :=
  wellFounded_lt.min_mem _ (exists_next D hD x)

theorem nextD_le (D : Set Point) (hD : IsCofinal D) {x d : Point}
    (hd : d ∈ D) (hxd : x < d) : nextD D hD x ≤ d :=
  wellFounded_lt.min_le (s := {d : Point | d ∈ D ∧ x < d}) ⟨hd, hxd⟩

theorem nextD_monotone (D : Set Point) (hD : IsCofinal D) : Monotone (nextD D hD) := by
  intro x y hxy
  exact nextD_le D hD (nextD_spec D hD y).1 (hxy.trans_lt (nextD_spec D hD y).2)

/-- The next-point map is constant throughout an empty half-open interval. -/
theorem nextD_eq_of_empty (D : Set Point) (hD : IsCofinal D) {u v x y : Point}
    (hempty : ∀ z ∈ D, u ≤ z → z < v → False)
    (hx : x ∈ Ico u v) (hy : y ∈ Ico u v) : nextD D hD x = nextD D hD y := by
  suffices h : ∀ a ∈ Ico u v, ∀ b ∈ Ico u v, nextD D hD a ≤ nextD D hD b from
    le_antisymm (h x hx y hy) (h y hy x hx)
  intro a ha b hb
  apply nextD_le D hD (nextD_spec D hD b).1
  by_contra h
  have hle : nextD D hD b ≤ a := le_of_not_gt h
  exact hempty _ (nextD_spec D hD b).1
    (hb.1.trans (nextD_spec D hD b).2.le) (hle.trans_lt ha.2)

/-- An injection is chosen separately for each proper initial segment. -/
def initialEmbedding (d : Point) : Set.Iio d.val ↪ ℕ := by
  letI := countable_initialSegment d
  exact ⟨Classical.choose (Countable.exists_injective_nat (Set.Iio d.val)),
    Classical.choose_spec (Countable.exists_injective_nat (Set.Iio d.val))⟩

def localNumbering (D : Set Point) (hD : IsCofinal D) (x : Point) : ℕ :=
  initialEmbedding (nextD D hD x) ⟨x.val, (nextD_spec D hD x).2⟩

/-- The common numbering is injective on each next-point fibre. -/
theorem localNumbering_injective_fiber (D : Set Point) (hD : IsCofinal D)
    {x y : Point} (hnext : nextD D hD x = nextD D hD y)
    (he : localNumbering D hD x = localNumbering D hD y) : x = y := by
  have hinj (d d' : Point) (hd : d = d') (hx : x.val < d.val) (hy : y.val < d'.val)
      (h : initialEmbedding d ⟨x.val, hx⟩ = initialEmbedding d' ⟨y.val, hy⟩) :
      x.val = y.val := by
    subst d'
    exact congrArg (fun z : Set.Iio d.val => z.val) ((initialEmbedding d).injective h)
  exact Subtype.ext (hinj _ _ hnext _ _ he)

theorem localNumbering_injOn_empty (D : Set Point) (hD : IsCofinal D) {u v : Point}
    (hempty : ∀ z ∈ D, u ≤ z → z < v → False) :
    Set.InjOn (localNumbering D hD) (Ico u v) := by
  intro x hx y hy he
  exact localNumbering_injective_fiber D hD (nextD_eq_of_empty D hD hempty hx hy) he

/-- Two disjoint open gaps in one injectively numbered interval cannot both contain a label q. -/
theorem two_gaps {α : Type*} [LinearOrder α] (e : α → ℕ) {u₀ u₁ u₂ v : α}
    (h01 : u₀ < u₁) (h12 : u₁ < u₂) (h2v : u₂ < v)
    (hinj : Set.InjOn e (Ico u₀ v)) (q : ℕ) :
    (∀ x, u₀ < x → x < u₁ → e x ≠ q) ∨
    (∀ x, u₁ < x → x < u₂ → e x ≠ q) := by
  classical
  by_cases h : ∀ x, u₀ < x → x < u₁ → e x ≠ q
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨x, h0x, hx1, hxq⟩ := h
    intro y h1y hy2 hyq
    have hxy : x = y := hinj ⟨h0x.le, hx1.trans (h12.trans h2v)⟩
      ⟨(h01.trans h1y).le, hy2.trans h2v⟩ (hxq.trans hyq.symm)
    exact (ne_of_lt (hx1.trans h1y)) hxy

end
end InfinitaryCombinatorics.Formalizations.A1
