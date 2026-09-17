import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.EquivFin
import Lean.Elab.Tactic.Omega

/-! A disjoint type is a shuffle of two increasing sequences of the same length. -/
namespace InfinitaryCombinatorics

/-- The positions partition the `2*n` places; neither width nor depth is suppressed. -/
structure DisjointType (n : ℕ) where
  left : Fin n ↪o Fin (2 * n)
  right : Fin n ↪o Fin (2 * n)
  disjoint : ∀ i j, left i ≠ right j
  cover : ∀ k, (∃ i, left i = k) ∨ ∃ j, right j = k

namespace DisjointType
variable {n : ℕ}

def swap (t : DisjointType n) : DisjointType n where
  left := t.right
  right := t.left
  disjoint i j := (t.disjoint j i).symm
  cover k := (t.cover k).symm

@[simp] theorem swap_swap (t : DisjointType n) : t.swap.swap = t := rfl

/-- A depth bound says one side is finished before position `k` on the other side. -/
def DepthLE (t : DisjointType n) (k : Fin n) : Prop :=
  (∀ i, t.left i < t.right k) ∨ (∀ i, t.right i < t.left k)

theorem depthLE_mono (t : DisjointType n) {i j : Fin n} (hij : i ≤ j)
    (hi : t.DepthLE i) : t.DepthLE j := by
  rcases hi with hi | hi
  · exact Or.inl fun k => (hi k).trans_le (t.right.monotone hij)
  · exact Or.inr fun k => (hi k).trans_le (t.left.monotone hij)

@[simp] theorem depthLE_swap (t : DisjointType n) (k : Fin n) :
    t.swap.DepthLE k ↔ t.DepthLE k := or_comm

theorem depthLE_last (t : DisjointType (n + 1)) : t.DepthLE (Fin.last n) := by
  rcases lt_or_gt_of_ne (t.disjoint (Fin.last n) (Fin.last n)) with h | h
  · exact Or.inl fun i => (t.left.monotone (Fin.le_last i)).trans_lt h
  · exact Or.inr fun i => (t.right.monotone (Fin.le_last i)).trans_lt h

private theorem depth_exists (t : DisjointType (n + 1)) :
    ∃ k : ℕ, ∃ hk : k < n + 1, t.DepthLE ⟨k, hk⟩ :=
  ⟨n, Nat.lt_succ_self n, t.depthLE_last⟩

/-- Least qualifying position, with positivity encoded by width `n+1`. -/
noncomputable def depth (t : DisjointType (n + 1)) : ℕ := by
  classical
  exact Nat.find t.depth_exists

theorem depth_spec (t : DisjointType (n + 1)) :
    ∃ h : t.depth < n + 1, t.DepthLE ⟨t.depth, h⟩ := by
  classical
  exact Nat.find_spec t.depth_exists

theorem depth_le (t : DisjointType (n + 1)) (k : Fin (n + 1)) (h : t.DepthLE k) :
    t.depth ≤ k.val := by
  classical
  exact Nat.find_min' t.depth_exists ⟨k.isLt, h⟩
theorem depth_swap (t : DisjointType (n + 1)) : t.swap.depth = t.depth := by
  apply Nat.le_antisymm
  · exact t.swap.depth_le ⟨t.depth, t.depth_spec.choose⟩
      ((t.depthLE_swap _).mpr t.depth_spec.choose_spec)
  · exact t.depth_le ⟨t.swap.depth, t.swap.depth_spec.choose⟩
      ((t.depthLE_swap _).mp t.swap.depth_spec.choose_spec)

/-- An actual realization by an increasing enumeration of the union. -/
def Realizes {α : Type*} [LinearOrder α] (t : DisjointType n)
    (a b : Fin n → α) : Prop :=
  ∃ e : Fin (2 * n) ↪o α, (∀ i, e (t.left i) = a i) ∧ ∀ i, e (t.right i) = b i

theorem realizes_swap {α : Type*} [LinearOrder α] (t : DisjointType n)
    (a b : Fin n → α) : t.swap.Realizes b a ↔ t.Realizes a b := by
  constructor <;> rintro ⟨e, h₁, h₂⟩ <;> exact ⟨e, h₂, h₁⟩

theorem Realizes.disjoint {α : Type*} [LinearOrder α] {t : DisjointType n}
    {a b : Fin n → α} (h : t.Realizes a b) (i j : Fin n) : a i ≠ b j := by
  obtain ⟨e, ha, hb⟩ := h
  intro hab
  exact t.disjoint i j (e.injective ((ha i).trans (hab.trans (hb j).symm)))

theorem Realizes.strictMono_left {α : Type*} [LinearOrder α] {t : DisjointType n}
    {a b : Fin n → α} (h : t.Realizes a b) : StrictMono a := by
  obtain ⟨e, ha, _⟩ := h
  intro i j hij
  rw [← ha i, ← ha j]
  exact e.strictMono (t.left.strictMono hij)

theorem Realizes.strictMono_right {α : Type*} [LinearOrder α] {t : DisjointType n}
    {a b : Fin n → α} (h : t.Realizes a b) : StrictMono b := by
  exact ((realizes_swap t a b).mpr h).strictMono_left

/-- The realizing enumeration enumerates exactly the union of the two sets. -/
theorem Realizes.exists_range_eq {α : Type*} [LinearOrder α] {t : DisjointType n}
    {a b : Fin n → α} (h : t.Realizes a b) :
    ∃ e : Fin (2 * n) ↪o α, Set.range e = Set.range a ∪ Set.range b := by
  obtain ⟨e, ha, hb⟩ := h
  refine ⟨e, ?_⟩
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    rcases t.cover k with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact Or.inl ⟨i, (ha i).symm.trans (congrArg e hi)⟩
    · exact Or.inr ⟨j, (hb j).symm.trans (congrArg e hj)⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨t.left i, ha i⟩
    · exact ⟨t.right j, hb j⟩

/-- The position-based depth condition agrees with the actual ordered points. -/
theorem Realizes.depthLE_iff {α : Type*} [LinearOrder α] {t : DisjointType n}
    {a b : Fin n → α} (h : t.Realizes a b) (k : Fin n) :
    t.DepthLE k ↔ (∀ i, a i < b k) ∨ (∀ i, b i < a k) := by
  obtain ⟨e, ha, hb⟩ := h
  constructor
  · rintro (h | h)
    · exact Or.inl fun i => by rw [← ha i, ← hb k]; exact e.strictMono (h i)
    · exact Or.inr fun i => by rw [← hb i, ← ha k]; exact e.strictMono (h i)
  · rintro (h | h)
    · exact Or.inl fun i => e.lt_iff_lt.mp (by rw [ha i, hb k]; exact h i)
    · exact Or.inr fun i => e.lt_iff_lt.mp (by rw [hb i, ha k]; exact h i)
/-- The type with every left point before every right point. -/
def separated (n : ℕ) : DisjointType n where
  left := OrderEmbedding.ofStrictMono
    (fun i : Fin n => (⟨i.val, by omega⟩ : Fin (2 * n)))
    (fun _ _ h => h)
  right := OrderEmbedding.ofStrictMono
    (fun i : Fin n => (⟨n + i.val, by omega⟩ : Fin (2 * n)))
    (by intro i j h; change n + i.val < n + j.val; exact Nat.add_lt_add_left h n)
  disjoint i j := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = n + j.val at hv
    omega
  cover k := by
    by_cases hk : k.val < n
    · exact Or.inl ⟨⟨k.val, hk⟩, rfl⟩
    · refine Or.inr ⟨⟨k.val - n, by omega⟩, ?_⟩
      apply Fin.ext
      change n + (k.val - n) = k.val
      omega

theorem separated_depth (n : ℕ) : (separated (n + 1)).depth = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (separated (n + 1)).depth_le (0 : Fin (n + 1))
  left
  intro i
  change i.val < n + 1 + 0
  omega

end DisjointType
end InfinitaryCombinatorics



