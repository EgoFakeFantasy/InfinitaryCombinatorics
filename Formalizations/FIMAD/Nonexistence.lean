import Formalizations.FIMAD.Obstruction
import Formalizations.R0.CountableCompletion

namespace InfinitaryCombinatorics.Formalizations.FIMAD
open Set Cardinal
open InfinitaryCombinatorics.Formalizations.R0 (partitionPart partitionOwner partitionPart_almostEqual partitionPart_infinite almostDisjointnessNumber exists_minimum_mad_nat)

/-- The usual diagonal proof of b ≤ a, with no external cardinal comparison. -/
theorem infinite_ad_not_mad_of_bounding {A : Set (Set ℕ)}
    (hA : R0.AlmostDisjoint A) (hb : Bounding A) : ¬ MAD A := by
  classical
  let e : ℕ ↪ A := hA.1.natEmbedding A
  let f : ℕ → Set ℕ := fun n => (e n).val
  have hfi : Function.Injective f := fun _ _ h => e.injective (Subtype.ext h)
  have hp : ∀ n m, n ≠ m → (f n ∩ f m).Finite :=
    fun n m h => hA.2.2 _ (e n).property _ (e m).property (fun hh => h (hfi hh))
  let E := partitionPart f
  have hEinf (n) : (E n).Infinite := partitionPart_infinite f hp (fun n => hA.2.1 _ (e n).property) n
  have hfin (a : A) (n) (hne : a.val ≠ f n) : (a.val ∩ E n).Finite := by
    have hf := hA.2.2 _ a.property _ (e n).property hne
    have he := (partitionPart_almostEqual f hp n).1
    apply (hf.union he).subset
    intro x hx
    by_cases hh : x ∈ f n
    · exact Or.inl ⟨hx.1,hh⟩
    · exact Or.inr ⟨hx.2,hh⟩
  have hd : ∀ a : A, ∀ n, ∃ d, a.val ≠ f n → ∀ x ∈ a.val ∩ E n, x < d := by
    intro a n
    by_cases hh : a.val = f n
    · exact ⟨0,fun hn => (hn hh).elim⟩
    · obtain ⟨d,hd⟩ := (hfin a n hh).bddAbove
      exact ⟨d+1,fun _ x hx => Nat.lt_succ_of_le (hd hx)⟩
  choose d hd using hd
  obtain ⟨g,hg⟩ := hb d
  have hx : ∀ n, ∃ x ∈ E n, g n ≤ x := fun n => infinite_tail_point (hEinf n) (g n)
  choose x hx hgx using hx
  have hxi : Function.Injective x := by
    intro n m hh
    have hn : partitionOwner f (x n) = n := hx n
    have hm : partitionOwner f (x m) = m := hx m
    rw [hh] at hn
    exact hn.symm.trans hm
  have hX : (range x).Infinite := infinite_range_of_injective hxi
  have horth (a : A) : (range x ∩ a.val).Finite := by
    obtain ⟨N,hN⟩ := hg a
    have hex : {n | f n = a.val}.Finite := (finite_singleton a.val).preimage hfi.injOn
    apply (((finite_lt_nat N).image x).union (hex.image x)).subset
    rintro y ⟨⟨n,rfl⟩,hya⟩
    by_cases hn : n < N
    · exact Or.inl ⟨n,hn,rfl⟩
    · by_cases heq : f n = a.val
      · exact Or.inr ⟨n,heq,rfl⟩
      · have hneg := hd a n (Ne.symm heq) (x n) ⟨hya,hx n⟩
        have hbound := hN n (Nat.le_of_not_gt hn)
        have hlarge := hgx n
        omega
  intro hmad
  obtain ⟨a,ha,hi⟩ := hmad.2 (range x) hX
  exact hi (horth ⟨a,ha⟩)

lemma boundingNumber_le_mad_card {M : Set (Set ℕ)} (hM : MAD M) :
    boundingNumber ≤ #M := by
  by_contra h
  exact infinite_ad_not_mad_of_bounding hM.1 (bounding_of_card_lt (lt_of_not_ge h)) hM

lemma boundingNumber_le_almostDisjointnessNumber : boundingNumber ≤ almostDisjointnessNumber := by
  obtain ⟨M,hM,hc⟩ := exists_minimum_mad_nat
  exact hc ▸ boundingNumber_le_mad_card hM

def ExistsFIMAD : Prop := ∃ M : Set (Set ℕ), MAD M ∧ R0.FinIntersecting M

/-- Full nonexistence theorem with both ap and b inequalities exposed. -/
theorem no_fi_mad_of_s_lt_ap_and_b
    (hsep : R0.splittingNumber < almostDisjointSeparationNumber)
    (hbound : R0.splittingNumber < boundingNumber) : ¬ ExistsFIMAD := by
  rintro ⟨M,hM,hFI⟩
  exact not_finIntersecting_of_large hM.1.2
    (hbound.le.trans (boundingNumber_le_mad_card hM)) hsep hbound hFI

/-- The manuscript's stated hypothesis follows using the cited comparison ap ≤ b.
That comparison is an explicit external input, not an added axiom. -/
theorem no_fi_mad_of_s_lt_ap
    (ap_le_b : almostDisjointSeparationNumber ≤ boundingNumber)
    (hsep : R0.splittingNumber < almostDisjointSeparationNumber) : ¬ ExistsFIMAD :=
  no_fi_mad_of_s_lt_ap_and_b hsep (hsep.trans_le ap_le_b)

theorem fi_mad_implies_ap_le_s
    (ap_le_b : almostDisjointSeparationNumber ≤ boundingNumber)
    (h : ExistsFIMAD) : almostDisjointSeparationNumber ≤ R0.splittingNumber := by
  by_contra hn
  exact no_fi_mad_of_s_lt_ap ap_le_b (lt_of_not_ge hn) h

/-- Arbitrary trace labels, including the empty positive fiber. -/
theorem arbitrary_labels_below_ap {A : Set (Set ℕ)} (hA : R0.AlmostDisjoint A)
    (ap_le_b : almostDisjointSeparationNumber ≤ boundingNumber)
    (hcard : #A < almostDisjointSeparationNumber) (S : A → Set ℕ) :
    ∃ C : R0.FinSequence ℕ, ∀ a : A, EventuallyEqual (R0.trace C a) (S a) := by
  classical
  have hb := bounding_of_card_lt (hcard.trans_le ap_le_b)
  have hsep := weaklySeparable_of_card_lt hA.2 hcard
  have hnot := infinite_ad_not_mad_of_bounding hA hb
  have horth : ∃ X : Set ℕ, X.Infinite ∧ ∀ a ∈ A, (X ∩ a).Finite := by
    by_contra hn
    push Not at hn
    apply hnot
    refine ⟨hA,?_⟩
    intro X hX
    obtain ⟨a,ha,h⟩ := hn X hX
    exact ⟨a,ha,h⟩
  obtain ⟨Y,hY,hYA⟩ := horth
  have htest (n) : ∃ X : Set ℕ, X.Infinite ∧ ∀ a : A, (a.val ∩ X).Infinite ↔ n ∈ S a := by
    by_cases hn : ∃ a : A, n ∈ S a
    · let B : Set (Set ℕ) := {a | ∃ ha : a ∈ A, n ∈ S ⟨a,ha⟩}
      obtain ⟨X,hX⟩ := hsep B (fun _ h => h.choose)
      have hh (a : A) : (a.val ∩ X).Infinite ↔ n ∈ S a := by simpa [B] using hX a a.property
      obtain ⟨a,ha⟩ := hn
      exact ⟨X,((hh a).mpr ha).mono inter_subset_right,hh⟩
    · refine ⟨Y,hY,?_⟩
      intro a
      constructor
      · intro h
        exact False.elim (h (by simpa [inter_comm] using hYA a a.property))
      · intro ha
        exact False.elim (hn ⟨a,ha⟩)
  choose X hX ht using htest
  exact uniform_trace_coding A hb S X hX (fun a n => ht n a)

end InfinitaryCombinatorics.Formalizations.FIMAD
