import InfinitaryCombinatorics.PairColoring
import Mathlib.SetTheory.Ordinal.Basic

/-! Strong colourings over partitions. Sets are arbitrary order-type blocks, not Finsets. -/
namespace InfinitaryCombinatorics
open Set Cardinal
universe u v w
variable {V : Type u} [LinearOrder V]

def Separated (a b : Set V) : Prop := ∀ x ∈ a, ∀ y ∈ b, x < y

theorem Separated.disjoint {a b : Set V} (h : Separated a b) : Disjoint a b := by
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  exact lt_irrefl x (h x hxa x hxb)

/-- All members have one fixed ordinal order type; empty blocks are permitted. -/
def UniformDisjoint (A : Set (Set V)) (σ : Ordinal.{u}) : Prop :=
  (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Disjoint a b) ∧
  ∀ a ∈ A, ∃ r : IsWellOrder a (· < ·), @Ordinal.type a (· < ·) r = σ

def RealizesRectangle {P : Type v} {K : Type w}
    (p : PairColoring V P) (c : PairColoring V K) (τ : P → K) (a b : Set V) : Prop :=
  ∀ x ∈ a, ∀ y ∈ b, c.color x y = τ (p.color x y)

/-- Witness-level Pr₁. Both family size and block-size bound remain explicit. -/
def Pr1Witness {P : Type v} {K : Type w} (κ χ : Cardinal.{u})
    (p : PairColoring V P) (c : PairColoring V K) : Prop :=
  ∀ σ : Ordinal.{u}, σ.card < χ → ∀ A : Set (Set V),
    Cardinal.mk A = κ → UniformDisjoint A σ → ∀ τ : P → K,
      ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ Separated a b ∧ RealizesRectangle p c τ a b

/-- Surjective recolouring lowers the number of colours without changing block parameters. -/
theorem pr1Witness_recolor {P : Type v} {K L : Type w} {κ χ : Cardinal.{u}}
    {p : PairColoring V P} {c : PairColoring V K} (hc : Pr1Witness κ χ p c)
    (q : K → L) (hq : Function.Surjective q) : Pr1Witness κ χ p (c.recolor q) := by
  classical
  intro σ hσ A hA hAD τ
  let τ' : P → K := fun z => Classical.choose (hq (τ z))
  obtain ⟨a, ha, b, hb, hab, hsep, hr⟩ := hc σ hσ A hA hAD τ'
  refine ⟨a, ha, b, hb, hab, hsep, ?_⟩
  intro x hx y hy
  change q (c.color x y) = τ (p.color x y)
  rw [hr x hx y hy]
  exact Classical.choose_spec (hq _)

theorem pr1Witness_mono_bound {P : Type v} {K : Type w} {κ χ χ' : Cardinal.{u}}
    {p : PairColoring V P} {c : PairColoring V K} (hc : Pr1Witness κ χ p c)
    (hχ : χ' ≤ χ) : Pr1Witness κ χ' p c :=
  fun σ hσ => hc σ (hσ.trans_le hχ)

end InfinitaryCombinatorics
