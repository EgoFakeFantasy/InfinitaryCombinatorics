import Formalizations.A1.LocalNumbering

/-! # The countable convex partition behind local numbering -/

namespace InfinitaryCombinatorics.Formalizations.A1
open Set Order
noncomputable section

theorem nextD_fiber_injOn (D : Set Point) (hD : IsCofinal D) (d : Point) :
    Set.InjOn (localNumbering D hD) {x | nextD D hD x = d} := by
  intro x hx y hy he
  exact localNumbering_injective_fiber D hD (hx.trans hy.symm) he

theorem nextD_fiber_countable (D : Set Point) (hD : IsCofinal D) (d : Point) :
    {x | nextD D hD x = d}.Countable :=
  Set.countable_iff_exists_injOn.mpr ⟨localNumbering D hD, nextD_fiber_injOn D hD d⟩

theorem nextD_fiber_ordConnected (D : Set Point) (hD : IsCofinal D) (d : Point) :
    Set.OrdConnected {x | nextD D hD x = d} := by
  constructor
  intro x hx y hy z hz
  change nextD D hD z = d
  apply le_antisymm
  · exact (nextD_monotone D hD hz.2).trans_eq hy
  · exact hx.symm.trans_le (nextD_monotone D hD hz.1)

/-- Use only the nonempty fibres, indexed by an arbitrary point in each fibre. -/
def clubPartition (D : Set Point) (hD : IsCofinal D) : Set (Set Point) :=
  Set.range fun x : Point => {y | nextD D hD y = nextD D hD x}

/-- Lemma 4.1: a countable convex partition with a common local numbering.
The final clause places an entire empty half-open interval in one member. -/
theorem countable_convex_partition (D : Set Point) (hD : IsClub D) :
    ∃ (I : Set (Set Point)) (e : Point → ℕ),
      (∀ S ∈ I, S.Nonempty ∧ S.Countable ∧ S.OrdConnected ∧ Set.InjOn e S) ∧
      (∀ x : Point, ∃! S : Set Point, S ∈ I ∧ x ∈ S) ∧
      (∀ u v : Point, u < v → (∀ z ∈ D, u ≤ z → z < v → False) →
        ∃ S ∈ I, Set.Ico u v ⊆ S) := by
  refine ⟨clubPartition D hD.isCofinal, localNumbering D hD.isCofinal, ?_, ?_, ?_⟩
  · rintro S ⟨x, rfl⟩
    exact ⟨⟨x, rfl⟩, nextD_fiber_countable D hD.isCofinal _,
      nextD_fiber_ordConnected D hD.isCofinal _, nextD_fiber_injOn D hD.isCofinal _⟩
  · intro x
    refine ⟨{y | nextD D hD.isCofinal y = nextD D hD.isCofinal x},
      ⟨⟨x, rfl⟩, rfl⟩, ?_⟩
    rintro S ⟨⟨y, rfl⟩, hx⟩
    ext z
    change (nextD D hD.isCofinal z = nextD D hD.isCofinal y ↔
      nextD D hD.isCofinal z = nextD D hD.isCofinal x)
    change nextD D hD.isCofinal x = nextD D hD.isCofinal y at hx
    rw [hx]
  · intro u v huv hempty
    refine ⟨{y | nextD D hD.isCofinal y = nextD D hD.isCofinal u}, ⟨u, rfl⟩, ?_⟩
    intro x hx
    exact nextD_eq_of_empty D hD.isCofinal hempty hx ⟨le_rfl, huv⟩

end
end InfinitaryCombinatorics.Formalizations.A1
