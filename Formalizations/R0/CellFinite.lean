import Formalizations.R0.CountableCompletion

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal

/-- The diagonal obstruction to a countable infinite MAD family. -/
lemma mad_not_countable {X : Type} {M : Set (Set X)} (hM : MAD M) : ¬ M.Countable := by
  classical
  intro hc
  letI : Countable M := hc.to_subtype
  letI : Infinite M := hM.1.1.to_subtype
  let e : ℕ ≃ M := Classical.choice inferInstance
  let f : ℕ → Set X := fun n => (e n).val
  have hchoice (n : ℕ) : ∃ x ∈ f n, ∀ i < n, x ∉ f i := by
    have hf : (⋃ i ∈ Set.Iio n, f n ∩ f i).Finite := by
      apply (Set.finite_Iio n).biUnion
      intro i hi
      apply hM.1.2.2 _ (e n).property _ (e i).property
      intro h
      have := e.injective (Subtype.ext h)
      simp only [mem_Iio] at hi
      omega
    obtain ⟨x,hx,hnot⟩ := ((hM.1.2.1 _ (e n).property).diff hf).nonempty
    refine ⟨x,hx,?_⟩
    intro i hi hxi
    exact hnot (mem_iUnion₂.mpr ⟨i,hi,hx,hxi⟩)
  choose x hx havoid using hchoice
  have hxi : Function.Injective x := by
    intro n m h
    rcases lt_trichotomy n m with hnm | hnm | hnm
    · exact False.elim (havoid m n hnm (h ▸ hx n))
    · exact hnm
    · exact False.elim (havoid n m hnm (h.symm ▸ hx m))
  obtain ⟨a,ha,hi⟩ := hM.2 (range x) (Set.infinite_range_of_injective hxi)
  let n := e.symm ⟨a,ha⟩
  have hn : f n = a := congrArg Subtype.val (e.apply_symm_apply ⟨a,ha⟩)
  apply hi
  apply ((Set.finite_Iic n).image x).subset
  rintro y ⟨⟨k,rfl⟩,hya⟩
  refine ⟨k,?_,rfl⟩
  by_contra hkn
  exact havoid k n (by simpa using hkn) (hn.symm ▸ hya)

lemma aleph0_lt_almostDisjointnessNumber : ℵ₀ < almostDisjointnessNumber := by
  obtain ⟨M,hM,hc⟩ := exists_minimum_mad_nat
  rw [← hc]
  exact lt_of_not_ge (fun h => mad_not_countable hM (Cardinal.le_aleph0_iff_set_countable.mp h))

/-- Paper Lemma 8.1 on every countably infinite ground set and every infinite-cell partition. -/
theorem cell_finite_relative_completion {X : Type} [Countable X]
    (c : ℕ → Set X) (hi : ∀ n, (c n).Infinite)
    (hd : Pairwise (fun i j => Disjoint (c i) (c j)))
    (_hcover : ⋃ n, c n = Set.univ) :
    ∃ L : Set (Set X), ADFamily L ∧ #L = almostDisjointnessNumber ∧
      (∀ l ∈ L, ∀ n, (l ∩ c n).Finite) ∧
      ∀ Y : Set X, Y.Infinite → (∀ n, (Y ∩ c n).Finite) →
        ∃ l ∈ L, (Y ∩ l).Infinite := by
  classical
  have cinj : Function.Injective c := by
    intro n m h
    by_contra hnm
    obtain ⟨x,hx⟩ := (hi n).nonempty
    exact Set.disjoint_left.mp (hd hnm) hx (h ▸ hx)
  have hF : ADFamily (range c) := by
    refine ⟨?_,?_⟩
    · rintro _ ⟨n,rfl⟩; exact hi n
    · rintro _ ⟨n,rfl⟩ _ ⟨m,rfl⟩ h
      exact (Set.disjoint_iff_inter_eq_empty.mp (hd (fun (hnm : n = m) => h (congrArg c hnm)))) ▸ finite_empty
  letI : Infinite (c 0) := (hi 0).to_subtype
  letI : Infinite X := Infinite.of_injective (fun x : c 0 => x.val) Subtype.val_injective
  obtain ⟨K,hFK,hK,hKc⟩ := countable_infinite_mad_extension hF (Set.countable_range c)
    (Set.infinite_range_of_injective cinj)
  let L := K \ range c
  have hLa : ADFamily L := ⟨fun l hl => hK.1.2.1 l hl.1,
    fun l hl q hq hne => hK.1.2.2 l hl.1 q hq.1 hne⟩
  have hLc : #L = almostDisjointnessNumber := by
    apply le_antisymm ((Cardinal.mk_le_mk_of_subset diff_subset).trans_eq hKc)
    have hle : almostDisjointnessNumber ≤ max ℵ₀ #L := by
      calc
        almostDisjointnessNumber = #K := hKc.symm
        _ ≤ #(range c ∪ L : Set (Set X)) := Cardinal.mk_le_mk_of_subset (by
          intro p hp; by_cases h : p ∈ range c
          · exact Or.inl h
          · exact Or.inr ⟨hp,h⟩)
        _ ≤ #(range c) + #L := Cardinal.mk_union_le _ _
        _ ≤ ℵ₀ + #L := add_le_add (Cardinal.le_aleph0_iff_set_countable.mpr (Set.countable_range c)) le_rfl
        _ = max ℵ₀ #L := Cardinal.add_eq_max le_rfl
    exact (le_max_iff.mp hle).resolve_left (not_le_of_gt aleph0_lt_almostDisjointnessNumber)
  refine ⟨L,hLa,hLc,?_,?_⟩
  · intro l hl n
    exact hK.1.2.2 l hl.1 (c n) (hFK ⟨n,rfl⟩) (fun h => hl.2 ⟨n,h.symm⟩)
  · intro Y hY hf
    obtain ⟨l,hl,hyl⟩ := hK.2 Y hY
    refine ⟨l,⟨hl,?_⟩,hyl⟩
    rintro ⟨n,rfl⟩
    exact hyl (hf n)

end InfinitaryCombinatorics.Formalizations.R0
