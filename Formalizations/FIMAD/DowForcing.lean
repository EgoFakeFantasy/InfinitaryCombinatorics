import Formalizations.FIMAD.DowCardinal
import Mathlib.Order.Antichain

/-! Dow's actual forcing from Definition 2 of *On compact separable radial
spaces*, Canad. Math. Bull. 40 (1997), 422--432. The second coordinate is a
set of forbidden finite stems, not a finite side condition from Solovay forcing.
The results here concern this poset and directed sets meeting stated dense
sets. They do not assert existence of a generic extension or an iteration. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowForcing
open Set

def Tail (a : Set ℕ) (n : ℕ) (t : Finset ℕ) : Prop := ∀ k ∈ t, k ∈ a ∧ n ≤ k

def Admissible (A : Set (Set ℕ)) (S : Set (Finset ℕ)) : Prop :=
  ∀ s, s ∉ S → ∀ a ∈ A, ∃ n, ∀ t, Tail a n t → s ∪ t ∉ S

structure Condition (A : Set (Set ℕ)) where
  stem : Finset ℕ
  forbidden : Set (Finset ℕ)
  allowed : stem ∉ forbidden
  admissible : Admissible A forbidden

variable {A : Set (Set ℕ)}

instance : LE (Condition A) where
  le p q := q.stem ⊆ p.stem ∧ q.forbidden ⊆ p.forbidden ∧ p.stem ∉ q.forbidden

theorem le_def (p q : Condition A) :
    p ≤ q ↔ q.stem ⊆ p.stem ∧ q.forbidden ⊆ p.forbidden ∧ p.stem ∉ q.forbidden := Iff.rfl

instance : PartialOrder (Condition A) where
  le_refl p := ⟨Finset.Subset.refl _, Subset.rfl, p.allowed⟩
  le_trans p q r hpq hqr := ⟨hqr.1.trans hpq.1, hqr.2.1.trans hpq.2.1,
    fun h => hpq.2.2 (hqr.2.1 h)⟩
  le_antisymm p q hpq hqp := by
    have hs := Finset.Subset.antisymm hpq.1 hqp.1
    have hf := Set.Subset.antisymm hpq.2.1 hqp.2.1
    cases p; cases q
    cases hs; cases hf
    rfl

def freeCondition (s : Finset ℕ) : Condition A :=
  ⟨s, ∅, by simp, fun _ _ _ _ => ⟨0, fun _ _ => by simp⟩⟩

theorem admissible_union {S T : Set (Finset ℕ)}
    (hS : Admissible A S) (hT : Admissible A T) : Admissible A (S ∪ T) := by
  intro s hs a ha
  obtain ⟨n, hn⟩ := hS s (fun h => hs (Or.inl h)) a ha
  obtain ⟨m, hm⟩ := hT s (fun h => hs (Or.inr h)) a ha
  refine ⟨max n m, fun t ht => ?_⟩
  exact fun h => h.elim
    (hn t (fun k hk => ⟨(ht k hk).1, (le_max_left n m).trans (ht k hk).2⟩))
    (hm t (fun k hk => ⟨(ht k hk).1, (le_max_right n m).trans (ht k hk).2⟩))

def merge (p q : Condition A) (h : p.stem = q.stem) : Condition A :=
  ⟨p.stem, p.forbidden ∪ q.forbidden,
    fun hbad => hbad.elim p.allowed (fun hb => q.allowed (h ▸ hb)),
    admissible_union p.admissible q.admissible⟩

theorem merge_le_left (p q : Condition A) (h : p.stem = q.stem) : merge p q h ≤ p :=
  ⟨Finset.Subset.refl _, Set.subset_union_left, p.allowed⟩

theorem merge_le_right (p q : Condition A) (h : p.stem = q.stem) : merge p q h ≤ q :=
  ⟨h ▸ Finset.Subset.refl _, Set.subset_union_right, h ▸ q.allowed⟩

/-- A whole finite family with the same stem has a common stronger condition. -/
theorem common_extension (s : Finset ℕ) (P : Finset (Condition A))
    (hP : ∀ p ∈ P, p.stem = s) : ∃ q : Condition A, q.stem = s ∧ ∀ p ∈ P, q ≤ p := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨freeCondition s, rfl, by simp⟩
  | @insert p P hp ih =>
    obtain ⟨q, hq, hqP⟩ := ih (fun r hr => hP r (Finset.mem_insert_of_mem hr))
    have heq : q.stem = p.stem := hq.trans (hP p (Finset.mem_insert_self _ _)).symm
    refine ⟨merge q p heq, hq, fun r hr => ?_⟩
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact merge_le_right _ _ _
    · exact (merge_le_left _ _ _).trans (hqP r hr)

def Compatible (p q : Condition A) : Prop := ∃ r, r ≤ p ∧ r ≤ q

/-- Countably many finite stems cover the poset by centered pieces. -/
theorem sigma_centered :
    ∃ f : Condition A → Finset ℕ, ∀ s (P : Finset (Condition A)), (∀ p ∈ P, f p = s) →
      ∃ q : Condition A, ∀ p ∈ P, q ≤ p := by
  refine ⟨Condition.stem, fun s P hP => ?_⟩
  obtain ⟨q, _, hq⟩ := common_extension s P hP
  exact ⟨q, hq⟩

theorem antichain_countable (B : Set (Condition A))
    (hB : B.Pairwise (fun p q => ¬ Compatible p q)) : B.Countable := by
  apply Set.countable_of_injective_of_countable_image (f := Condition.stem)
  · intro p hp q hq heq
    by_contra hne
    exact hB hp hq hne ⟨merge p q heq, merge_le_left _ _ _, merge_le_right _ _ _⟩
  · exact Set.to_countable _

def Dense (D : Set (Condition A)) : Prop := ∀ p, ∃ q ∈ D, q ≤ p

def hit (a : Set ℕ) (n : ℕ) : Set (Condition A) :=
  {p | ∃ k ∈ p.stem, k ∈ a ∧ n ≤ k}

theorem hit_dense {a : Set ℕ} (ha : a ∈ A) (hi : a.Infinite) (n : ℕ) :
    Dense (hit (A := A) a n) := by
  intro p
  obtain ⟨m, hm⟩ := p.admissible p.stem p.allowed a ha
  obtain ⟨k, hk, hlarge⟩ := infinite_tail_point hi (max n m)
  have ht : Tail a m {k} := by
    intro x hx
    have heq := Finset.mem_singleton.mp hx
    subst x
    exact ⟨hk, (le_max_right n m).trans hlarge⟩
  let q : Condition A := ⟨p.stem ∪ {k}, p.forbidden, hm {k} ht, p.admissible⟩
  exact ⟨q, ⟨k, Finset.mem_union_right _ (Finset.mem_singleton_self _), hk,
    (le_max_left n m).trans hlarge⟩,
    ⟨Finset.subset_union_left, Subset.rfl, hm {k} ht⟩⟩

/-- Blocks exactly the finite stems which acquire a new point of B. -/
def blocker (s : Finset ℕ) (B : Set ℕ) : Set (Finset ℕ) :=
  {t | ∃ k ∈ t, k ∈ B ∧ k ∉ s}

theorem blocker_admissible (s : Finset ℕ) (B : Set ℕ)
    (hB : ∀ a ∈ A, (a ∩ B).Finite) : Admissible A (blocker s B) := by
  intro t ht a ha
  obtain ⟨m, hm⟩ := (hB a ha).bddAbove
  refine ⟨m + 1, fun v hv => ?_⟩
  rintro ⟨k, hk, hkB, hks⟩
  rcases Finset.mem_union.mp hk with hkt | hkv
  · exact ht ⟨k, hkt, hkB, hks⟩
  · have hle := hm ⟨(hv k hkv).1, hkB⟩
    exact (Nat.not_succ_le_self m) ((hv k hkv).2.trans hle)

def avoid (B : Set ℕ) : Set (Condition A) :=
  {p | blocker p.stem B ⊆ p.forbidden}

theorem avoid_dense (B : Set ℕ) (hB : ∀ a ∈ A, (a ∩ B).Finite) :
    Dense (avoid (A := A) B) := by
  intro p
  have hp : p.stem ∉ blocker p.stem B := by rintro ⟨k, hk, _, hkn⟩; exact hkn hk
  let q : Condition A := ⟨p.stem, p.forbidden ∪ blocker p.stem B,
    fun h => h.elim p.allowed hp, admissible_union p.admissible (blocker_admissible _ _ hB)⟩
  exact ⟨q, Set.subset_union_right,
    ⟨Finset.Subset.refl _, Set.subset_union_left, p.allowed⟩⟩

def unionStems (G : Set (Condition A)) : Set ℕ := {k | ∃ p ∈ G, k ∈ p.stem}

theorem unionStems_hits {G : Set (Condition A)} {a : Set ℕ}
    (h : ∀ n, ∃ p ∈ G, p ∈ hit a n) : (a ∩ unionStems G).Infinite := by
  intro hf
  obtain ⟨m, hm⟩ := hf.bddAbove
  obtain ⟨p, hpG, k, hkp, hka, hlarge⟩ := h (m + 1)
  exact (Nat.not_succ_le_self m) (hlarge.trans (hm ⟨hka, p, hpG, hkp⟩))

theorem unionStems_avoids {G : Set (Condition A)}
    (hG : ∀ p ∈ G, ∀ q ∈ G, ∃ r ∈ G, r ≤ p ∧ r ≤ q)
    {B : Set ℕ} {p : Condition A} (hp : p ∈ G) (hpa : p ∈ avoid B) :
    B ∩ unionStems G ⊆ (p.stem : Set ℕ) := by
  rintro k ⟨hkB, q, hqG, hkq⟩
  obtain ⟨r, _, hrp, hrq⟩ := hG p hp q hqG
  by_contra hkp
  exact hrp.2.2 (hpa ⟨k, hrq.1 hkq, hkB, hkp⟩)

/-- Dense-set requirements really produce the weak separator. Existence of
a directed set meeting them is deliberately not asserted here. -/
theorem unionStems_weaklySeparates {B : Set (Set ℕ)} {G : Set (Condition A)}
    (hG : ∀ p ∈ G, ∀ q ∈ G, ∃ r ∈ G, r ≤ p ∧ r ≤ q)
    (hhit : ∀ a ∈ A, ∀ n, ∃ p ∈ G, p ∈ hit a n)
    (havoid : ∀ b ∈ B, ∃ p ∈ G, p ∈ avoid b) : WeaklySeparates (unionStems G) A B := by
  refine ⟨fun a ha => unionStems_hits (hhit a ha), ?_⟩
  intro b hb
  obtain ⟨p, hp, hpa⟩ := havoid b hb
  exact p.stem.finite_toSet.subset (unionStems_avoids hG hp hpa)

/-- The well-founded dense-stem closure underlying Dow's Lemma 1. Each
successor rule has countably many predecessors; the base uses actual D. -/
inductive Reach (D : Set (Condition A)) : Finset ℕ → Prop
  | base (p : Condition A) (hp : p ∈ D) : Reach D p.stem
  | step (s : Finset ℕ) (a : Set ℕ) (ha : a ∈ A) (t : ℕ → Finset ℕ)
      (ht : ∀ n, Tail a n (t n)) (prev : ∀ n, Reach D (s ∪ t n)) : Reach D s

theorem reach_all {D : Set (Condition A)} (hD : Dense D) (s : Finset ℕ) : Reach D s := by
  classical
  by_contra hs
  have had : Admissible A {t | Reach D t} := by
    intro t ht a ha
    by_contra h
    push Not at h
    choose v hv hreach using h
    exact ht (Reach.step t a ha v hv hreach)
  let p : Condition A := ⟨s, {t | Reach D t}, hs, had⟩
  obtain ⟨q, hq, hqp⟩ := hD p
  exact hqp.2.2 (Reach.base q hq)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowForcing
