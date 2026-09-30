import Formalizations.FIMAD.DowForcing

/-! The common-possible-values argument in Dow's Lemma 2. A deciding relation
is supplied explicitly, so this module proves the combinatorial preservation
step without assuming a forcing theorem or a generic model. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowForcing
open Set
variable {A : Set (Set ℕ)}

def Possible (E : Condition A → ℕ → Prop) (s : Finset ℕ) : Set ℕ :=
  {k | ∀ p : Condition A, p.stem = s → ∃ q, q ≤ p ∧ E q k}

def Avoids (E : Condition A → ℕ → Prop) (p : Condition A) (B : Set ℕ) : Prop :=
  ∀ q, q ≤ p → ∀ k ∈ B, ¬ E q k

theorem possible_disjoint {E : Condition A → ℕ → Prop} {p : Condition A} {B : Set ℕ}
    (hp : Avoids E p B) : Disjoint (Possible E p.stem) B := by
  apply Set.disjoint_left.mpr
  intro k hk hkB
  obtain ⟨q, hq, he⟩ := hk p rfl
  exact hp q hq k hkB he

def restem (p : Condition A) (s : Finset ℕ) (hs : s ∉ p.forbidden) : Condition A :=
  ⟨s, p.forbidden, hs, p.admissible⟩

theorem restem_le (p : Condition A) (s : Finset ℕ) (hs : s ∉ p.forbidden)
    (hp : p.stem ⊆ s) : restem p s hs ≤ p := ⟨hp, Subset.rfl, hs⟩

def tailValues (E : Condition A → ℕ → Prop) (s : Finset ℕ) (t : ℕ → Finset ℕ)
    (N : ℕ) : Set ℕ := {k | ∃ n, N ≤ n ∧ k ∈ Possible E (s ∪ t n)}

theorem possible_of_finite_tail {E : Condition A → ℕ → Prop} {s : Finset ℕ}
    {a : Set ℕ} (ha : a ∈ A) (t : ℕ → Finset ℕ) (ht : ∀ n, Tail a n (t n))
    (N : ℕ) (hne : ∀ n, N ≤ n → (Possible E (s ∪ t n)).Nonempty)
    (hf : (tailValues E s t N).Finite) : (Possible E s).Nonempty := by
  classical
  by_contra h
  have hbad : ∀ k, ∃ p : Condition A, p.stem = s ∧ ∀ q, q ≤ p → ¬ E q k := by
    intro k
    have hk : k ∉ Possible E s := fun hk => h ⟨k, hk⟩
    simp only [Possible, Set.mem_setOf_eq] at hk
    push Not at hk
    exact hk
  choose p hp hpbad using hbad
  let P : Finset (Condition A) := hf.toFinset.image p
  obtain ⟨q, hq, hqP⟩ := common_extension s P (by
    intro r hr
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
    exact hp k)
  obtain ⟨m, hm⟩ := q.admissible s (hq ▸ q.allowed) a ha
  let n := max N m
  have hal : s ∪ t n ∉ q.forbidden := hm _ (fun k hk =>
    ⟨(ht n k hk).1, (le_max_right N m).trans (ht n k hk).2⟩)
  let r := restem q (s ∪ t n) hal
  have hrq : r ≤ q := restem_le q _ hal (hq ▸ Finset.subset_union_left)
  obtain ⟨k, hk⟩ := hne n (le_max_left _ _)
  have hkU : k ∈ tailValues E s t N := ⟨n, le_max_left _ _, hk⟩
  have hpP : p k ∈ P := Finset.mem_image.mpr ⟨k, hf.mem_toFinset.mpr hkU, rfl⟩
  obtain ⟨v, hvr, hvk⟩ := hk r rfl
  exact hpbad k v (hvr.trans (hrq.trans (hqP _ hpP))) hvk

/-- Tests may include finite sets; only their infinite members impose a requirement. -/
def MeetsTests (B : Set ℕ) (F : Set (Set ℕ)) : Prop :=
  ∀ X ∈ F, X.Infinite → (X ∩ B).Infinite

theorem meetsTests_mono {B : Set ℕ} {F H : Set (Set ℕ)}
    (hB : MeetsTests B F) (hHF : H ⊆ F) : MeetsTests B H :=
  fun X hX => hB X (hHF hX)

/-- For one reachable stem, a countable collection of tests suffices to
make the common possible-value set nonempty under any avoiding condition. -/
theorem reach_possible_tests {E : Condition A → ℕ → Prop}
    (hmono : ∀ p q, q ≤ p → ∀ k, E p k → E q k)
    {D : Set (Condition A)} (hdec : ∀ p ∈ D, ∃ k, E p k)
    {s : Finset ℕ} (hs : Reach D s) :
    ∃ F : Set (Set ℕ), F.Countable ∧ ∀ B, MeetsTests B F →
      ∀ p : Condition A, p.stem = s → Avoids E p B → (Possible E s).Nonempty := by
  classical
  induction hs with
  | base p hp =>
    obtain ⟨k, hk⟩ := hdec p hp
    refine ⟨∅, Set.countable_empty, fun _ _ _ _ _ => ⟨k, ?_⟩⟩
    intro q hq
    exact ⟨merge q p hq, merge_le_left _ _ _, hmono p _ (merge_le_right _ _ _) k hk⟩
  | step s a ha t ht _ ih =>
    choose F hF hgood using ih
    let H : Set (Set ℕ) := (⋃ n, F n) ∪ range (tailValues E s t)
    refine ⟨H, (countable_iUnion hF).union (countable_range _), ?_⟩
    intro B hB p hp havoid
    obtain ⟨N, hN⟩ := p.admissible s (hp ▸ p.allowed) a ha
    have hallowed (n) (hn : N ≤ n) : s ∪ t n ∉ p.forbidden :=
      hN _ (fun k hk => ⟨(ht n k hk).1, hn.trans (ht n k hk).2⟩)
    have hrest (n) (hn : N ≤ n) : restem p (s ∪ t n) (hallowed n hn) ≤ p :=
      restem_le p _ _ (hp ▸ Finset.subset_union_left)
    have hne (n) (hn : N ≤ n) : (Possible E (s ∪ t n)).Nonempty := by
      apply hgood n B (meetsTests_mono hB (fun X hX => Or.inl (mem_iUnion.mpr ⟨n, hX⟩)))
        (restem p (s ∪ t n) (hallowed n hn)) rfl
      exact fun q hq => havoid q (hq.trans (hrest n hn))
    have hf : (tailValues E s t N).Finite := by
      by_contra hi
      obtain ⟨k, hk, hkB⟩ := (hB _ (Or.inr (mem_range_self N)) hi).nonempty
      obtain ⟨n, hn, hkn⟩ := hk
      obtain ⟨q, hq, hkq⟩ := hkn (restem p _ (hallowed n hn)) rfl
      exact havoid q (hq.trans (hrest n hn)) k hkB hkq
    exact possible_of_finite_tail ha t ht N hne hf

end InfinitaryCombinatorics.Formalizations.FIMAD.DowForcing
