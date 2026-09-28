import Formalizations.R0.CountableTransfer
import Formalizations.R0.BinarySplitting

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal

/-- The ambient product includes the triangular rows; unused points are caught by columns. -/
def predColumn (m : ℕ) : Set (ℕ × ℕ) := {p | p.1 = m}

def CellFinite (Y : Set (ℕ × ℕ)) : Prop := ∀ m, (Y ∩ predColumn m).Finite

def predGraph (A : Set ℕ) : Set (ℕ × ℕ) :=
  {p | p.1 ∈ A ∧ p.1 < p.2 ∧ ∀ m ∈ A, m < p.2 → m ≤ p.1}

lemma predColumn_infinite (m : ℕ) : (predColumn m).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (m,n))
  · intro n k h; exact congrArg Prod.snd h
  · intro n; rfl

lemma predColumns_ad : ADFamily (range predColumn) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨m,rfl⟩; exact predColumn_infinite m
  · rintro _ ⟨m,rfl⟩ _ ⟨n,rfl⟩ h
    apply finite_empty.subset
    rintro p ⟨hm,hn⟩
    exact False.elim (h (congrArg predColumn (hm.symm.trans hn)))

/-- A reusable relative completion bound, also valid when some cells are finite. -/
theorem cellFinite_completion (U : Set (ℕ × ℕ)) (hU : U.Infinite) :
    ∃ L : Set (Set (ℕ × ℕ)), ADFamily L ∧ #L ≤ almostDisjointnessNumber ∧
      (∀ l ∈ L, l ⊆ U ∧ CellFinite l) ∧
      ∀ Y ⊆ U, Y.Infinite → CellFinite Y → ∃ l ∈ L, (Y ∩ l).Infinite := by
  let F := restriction (range predColumn) U
  have hc : F.Countable := by
    apply (Set.countable_range (fun m => predColumn m ∩ U)).mono
    rintro p ⟨_,a,⟨m,rfl⟩,rfl⟩; exact ⟨m,rfl⟩
  have hb := countable_local_extensionCost_le (restriction_ad predColumns_ad U) hc
    (fun _ hp => restriction_subset hp) hU
  obtain ⟨L,hL,hcard⟩ := exists_minimum_remainder F U
  refine ⟨L,hL.1,hcard.le.trans hb,?_,?_⟩
  · intro l hl
    refine ⟨hL.2.1 l hl, ?_⟩
    have ho := (orthogonal_restriction (hL.2.1 l hl)).mp (hL.2.2.1 hl)
    exact fun m => ho _ ⟨m,rfl⟩
  · intro Y hYU hY hfin
    apply hL.2.2.2 Y hYU hY
    apply (orthogonal_restriction hYU).mpr
    rintro _ ⟨m,rfl⟩; exact hfin m

lemma predGraph_infinite {A : Set ℕ} (hA : A.Infinite) : (predGraph A).Infinite := by
  apply (hA.image (f := fun m => (m,m+1)) (by intro x _ y _ h; exact congrArg Prod.fst h)).mono
  rintro _ ⟨m,hm,rfl⟩
  exact ⟨hm,by dsimp; omega,fun k _ hk => by dsimp at *; omega⟩

lemma predGraph_cellFinite {A : Set ℕ} (hA : A.Infinite) : CellFinite (predGraph A) := by
  intro m
  obtain ⟨k,hk,hkm⟩ := hA.exists_gt m
  apply ((Set.finite_Iic k).image (fun n => (m,n))).subset
  rintro p ⟨hp,hm⟩
  refine ⟨p.2, ?_, ?_⟩
  · have : ¬ k < p.2 := by intro h; have := hp.2.2 k hk h; change p.1 = m at hm; omega
    exact Nat.le_of_not_gt this
  · change p.1 = m at hm
    exact Prod.ext hm.symm rfl

lemma cellFinite_inter_support {Y Z : Set (ℕ × ℕ)} {A B : Set ℕ}
    (hY : CellFinite Y) (hYA : ∀ p ∈ Y, p.1 ∈ A)
    (hZB : ∀ p ∈ Z, p.1 ∈ B) (hAB : (A ∩ B).Finite) : (Y ∩ Z).Finite := by
  apply (hAB.biUnion (fun m _ => hY m)).subset
  intro p hp
  exact mem_iUnion₂.mpr ⟨p.1,⟨hYA p hp.1,hZB p hp.2⟩,hp.1,rfl⟩

lemma predGraph_ad {H : Set (Set ℕ)} (hH : ADFamily H) : ADFamily (predGraph '' H) := by
  refine ⟨?_,?_⟩
  · rintro _ ⟨A,hA,rfl⟩; exact predGraph_infinite (hH.1 A hA)
  · rintro _ ⟨A,hA,rfl⟩ _ ⟨B,hB,rfl⟩ h
    exact cellFinite_inter_support (predGraph_cellFinite (hH.1 A hA))
      (fun _ hp => hp.1) (fun _ hp => hp.1)
      (hH.2 A hA B hB (fun e => h (e ▸ rfl)))

lemma cellFinite_projection {Y : Set (ℕ × ℕ)} (hY : Y.Infinite) (hf : CellFinite Y) :
    (Prod.fst '' Y).Infinite := by
  intro h
  apply hY
  apply (h.biUnion (fun m _ => hf m)).subset
  intro p hp; exact mem_iUnion₂.mpr ⟨p.1,⟨p,hp,rfl⟩,hp,rfl⟩

end InfinitaryCombinatorics.Formalizations.R0

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal

lemma cellFinite_completion_any (U : Set (ℕ × ℕ)) :
    ∃ L : Set (Set (ℕ × ℕ)), ADFamily L ∧ #L ≤ almostDisjointnessNumber ∧
      (∀ l ∈ L, l ⊆ U ∧ CellFinite l) ∧
      ∀ Y ⊆ U, Y.Infinite → CellFinite Y → ∃ l ∈ L, (Y ∩ l).Infinite := by
  by_cases hU : U.Infinite
  · exact cellFinite_completion U hU
  · refine ⟨∅,⟨by simp,by simp⟩,by simp,by simp,?_⟩
    intro Y hYU hY _
    exact False.elim (hU (hY.mono hYU))

lemma predGraph_local {A : Set ℕ} (hA : A.Infinite) :
    ∃ P : Set (Set (ℕ × ℕ)), ADFamily P ∧ #P ≤ almostDisjointnessNumber ∧
      predGraph A ∈ P ∧ (∀ p ∈ P, CellFinite p ∧ ∀ x ∈ p, x.1 ∈ A) ∧
      ∀ Y : Set (ℕ × ℕ), (∀ x ∈ Y, x.1 ∈ A) → Y.Infinite → CellFinite Y →
        ∃ p ∈ P, (Y ∩ p).Infinite := by
  classical
  let U : Set (ℕ × ℕ) := {p | p.1 ∈ A} \ predGraph A
  obtain ⟨L,hL,hLc,hLU,hLm⟩ := cellFinite_completion_any U
  have ho : predGraph A ∈ Orthogonal L := by
    intro l hl
    apply finite_empty.subset
    rintro p ⟨hp,hpl⟩
    exact False.elim ((hLU l hl).1 hpl |>.2 hp)
  refine ⟨insert (predGraph A) L, ad_insert_orthogonal hL (predGraph_infinite hA) ho, ?_,
    mem_insert _ _, ?_, ?_⟩
  · calc
      #(insert (predGraph A) L : Set (Set (ℕ × ℕ))) ≤ #L + 1 := Cardinal.mk_insert_le
      _ ≤ almostDisjointnessNumber + almostDisjointnessNumber := add_le_add hLc (Cardinal.one_le_aleph0.trans aleph0_le_almostDisjointnessNumber)
      _ = almostDisjointnessNumber := Cardinal.add_eq_self aleph0_le_almostDisjointnessNumber
  · intro p hp
    rcases hp with rfl | hp
    · exact ⟨predGraph_cellFinite hA,fun _ hx => hx.1⟩
    · exact ⟨(hLU p hp).2,fun x hx => ((hLU p hp).1 hx).1⟩
  · intro Y hYA hY hfin
    by_cases hg : (Y ∩ predGraph A).Infinite
    · exact ⟨predGraph A,mem_insert _ _,hg⟩
    · have hZ : (Y \ predGraph A).Infinite := by
        simpa [diff_inter] using hY.diff (not_infinite.mp hg)
      obtain ⟨p,hp,hi⟩ := hLm (Y \ predGraph A)
        (fun x hx => ⟨hYA x hx.1,hx.2⟩) hZ
        (fun m => (hfin m).subset (fun _ hx => ⟨hx.1.1,hx.2⟩))
      exact ⟨p,Or.inr hp,hi.mono (fun _ hx => ⟨hx.1.1,hx.2⟩)⟩

/-- Ordinary maximal completion of all predecessor graphs, with exact size control. -/
theorem predecessor_completion {H : Set (Set ℕ)} (hH : MAD H)
    (hHc : #H = almostDisjointnessNumber) :
    ∃ M : Set (Set (ℕ × ℕ)), MAD M ∧ #M = almostDisjointnessNumber ∧
      range predColumn ⊆ M ∧ predGraph '' H ⊆ M := by
  classical
  choose P hPad hPc hPg hPf hPm using fun A : H => predGraph_local (hH.1.2.1 A A.property)
  let F := ⋃ A : H, P A
  have hFad : ADFamily F := by
    refine ⟨?_,?_⟩
    · intro p hp; obtain ⟨A,hp⟩ := mem_iUnion.mp hp; exact (hPad A).1 p hp
    · intro p hp q hq hpq
      obtain ⟨A,hp⟩ := mem_iUnion.mp hp
      obtain ⟨B,hq⟩ := mem_iUnion.mp hq
      by_cases hAB : A = B
      · subst B; exact (hPad A).2 p hp q hq hpq
      · exact cellFinite_inter_support (hPf A p hp).1 (hPf A p hp).2 (hPf B q hq).2
          (hH.1.2.2 A A.property B B.property (fun h => hAB (Subtype.ext h)))
  have ho : F ⊆ Orthogonal (range predColumn) := by
    intro p hp; obtain ⟨A,hp⟩ := mem_iUnion.mp hp
    rintro _ ⟨m,rfl⟩; exact (hPf A p hp).1 m
  let M := range predColumn ∪ F
  have hCols : (range predColumn).Infinite := by
    apply Set.infinite_range_of_injective
    intro m n h
    have : (m,0) ∈ predColumn n := h ▸ (show (m,0) ∈ predColumn m from rfl)
    exact this
  have hM : MAD M := by
    refine ⟨⟨hCols.mono subset_union_left,ad_union_orthogonal predColumns_ad hFad ho⟩,?_⟩
    intro Y hY
    by_cases hf : CellFinite Y
    · obtain ⟨A,hA,hi⟩ := hH.2 (Prod.fst '' Y) (cellFinite_projection hY hf)
      let Z : Set (ℕ × ℕ) := {p ∈ Y | p.1 ∈ A}
      have hZi : Z.Infinite := by
        have hs : (Prod.fst '' Y) ∩ A ⊆ Prod.fst '' Z := by
          rintro m ⟨⟨p,hp,rfl⟩,hm⟩; exact ⟨p,⟨hp,hm⟩,rfl⟩
        exact Set.Infinite.of_image Prod.fst (hi.mono hs)
      obtain ⟨p,hp,hpi⟩ := hPm ⟨A,hA⟩ Z (fun _ hx => hx.2) hZi
        (fun m => (hf m).subset (fun _ hx => ⟨hx.1.1,hx.2⟩))
      exact ⟨p,Or.inr (mem_iUnion.mpr ⟨⟨A,hA⟩,hp⟩),hpi.mono (fun _ hx => ⟨hx.1.1,hx.2⟩)⟩
    · have : ∃ m, (Y ∩ predColumn m).Infinite := by
        simpa only [CellFinite, not_forall, Set.not_finite] using hf
      obtain ⟨m,hm⟩ := this
      exact ⟨predColumn m,Or.inl ⟨m,rfl⟩,hm⟩
  have hcF : #F ≤ almostDisjointnessNumber := by
    calc
      #F ≤ Cardinal.sum (fun A : H => #(P A)) := Cardinal.mk_iUnion_le_sum_mk
      _ ≤ Cardinal.sum (fun _ : H => almostDisjointnessNumber) := Cardinal.sum_le_sum _ _ hPc
      _ = #H * almostDisjointnessNumber := by simp only [Cardinal.sum_const, Cardinal.lift_id]
      _ = almostDisjointnessNumber := by rw [hHc, Cardinal.mul_eq_self aleph0_le_almostDisjointnessNumber]
  have hcM : #M ≤ almostDisjointnessNumber := by
    calc
      #M ≤ #(range predColumn) + #F := Cardinal.mk_union_le _ _
      _ ≤ almostDisjointnessNumber + almostDisjointnessNumber := add_le_add
        ((Cardinal.mk_range_le).trans (by simpa using aleph0_le_almostDisjointnessNumber)) hcF
      _ = almostDisjointnessNumber := Cardinal.add_eq_self aleph0_le_almostDisjointnessNumber
  refine ⟨M,hM,le_antisymm hcM (mad_card_lower hM),subset_union_left,?_⟩
  rintro _ ⟨A,hA,rfl⟩
  exact Or.inr (mem_iUnion.mpr ⟨⟨A,hA⟩,hPg ⟨A,hA⟩⟩)

end InfinitaryCombinatorics.Formalizations.R0

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal

lemma predGraph_injective : Function.Injective predGraph := by
  intro A B h
  have mem_diag (C : Set ℕ) (m : ℕ) : (m,m+1) ∈ predGraph C ↔ m ∈ C := by
    constructor
    · exact fun hp => hp.1
    · intro hm; exact ⟨hm,by omega,fun k _ hk => by dsimp at *; omega⟩
  ext m
  rw [← mem_diag A m,h,mem_diag B m]

def predecessorRows : _root_.R0.FinSequence (ℕ × ℕ) where
  block k := {p | p.2 = k+1 ∧ p.1 < p.2}
  finite k := by
    apply ((Set.finite_Iic k).image (fun m => (m,k+1))).subset
    rintro p ⟨hn,hm⟩
    refine ⟨p.1,?_,Prod.ext rfl hn.symm⟩
    simp only [mem_Iic]; omega
  nonempty k := ⟨(0,k+1),rfl,by omega⟩
  disjoint k l h := Set.disjoint_left.mpr (by
    rintro p ⟨hk,_⟩ ⟨hl,_⟩; exact h (by omega))

lemma predGraph_row_unique (A : Set ℕ) (k : ℕ) {p q : ℕ × ℕ}
    (hp : p ∈ predGraph A ∩ predecessorRows.block k)
    (hq : q ∈ predGraph A ∩ predecessorRows.block k) : p = q := by
  apply Prod.ext
  · have h1 := hp.1.2.2 q.1 hq.1.1 (by have := hp.2.1; have := hq.2.1; have := hq.1.2.1; omega)
    have h2 := hq.1.2.2 p.1 hp.1.1 (by have := hp.2.1; have := hq.2.1; have := hp.1.2.1; omega)
    exact le_antisymm h2 h1
  · exact hp.2.1.trans hq.2.1.symm

lemma predGraph_trace_tail {A : Set ℕ} {a : ℕ} (ha : a ∈ A) :
    ∀ k ≥ a, k ∈ _root_.R0.trace predecessorRows (predGraph A) := by
  classical
  intro k hk
  let t := (Finset.range (k+1)).filter (fun m => m ∈ A)
  have ht : t.Nonempty := ⟨a,by simp [t]; exact ⟨by omega,ha⟩⟩
  let m := t.max' ht
  have hm : m ∈ t := Finset.max'_mem t ht
  have hmA : m ∈ A := (Finset.mem_filter.mp hm).2
  have hmk : m < k+1 := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
  refine ⟨(m,k+1),⟨hmA,hmk,?_⟩,rfl,hmk⟩
  intro b hb hbk
  exact Finset.le_max' t b (by simp only [t,Finset.mem_filter,Finset.mem_range]; exact ⟨hbk,hb⟩)

/-- Paper Theorem 8.3: no hypothesis on the continuum or additional cardinal invariants. -/
theorem exists_nonFinIntersecting_mad_size_a
    (hsa : _root_.R0.splittingNumber ≤ almostDisjointnessNumber) :
    ∃ K : Set (Set ℕ), MAD K ∧ #K = almostDisjointnessNumber ∧
      ¬ _root_.R0.FinIntersecting K := by
  classical
  obtain ⟨H,hH,hHc⟩ := exists_minimum_mad_nat
  obtain ⟨M,hM,hMc,_,hGM⟩ := predecessor_completion hH hHc
  obtain ⟨S,hS,hSc⟩ := _root_.R0.exists_minimal_splitting
  have hSH : #S ≤ #H := by simpa only [hSc,hHc] using hsa
  obtain ⟨e⟩ := (Cardinal.le_def S H).mp hSH
  obtain ⟨s0,hs0,_⟩ := hS univ infinite_univ
  letI : Nonempty S := ⟨⟨s0,hs0⟩⟩
  let f : S → Set (ℕ × ℕ) := fun s => predGraph (e s).val
  have hfi : Function.Injective f := by
    intro s t h
    exact e.injective (Subtype.ext (predGraph_injective h))
  let label : Set (ℕ × ℕ) → Set ℕ := fun p => (Function.invFun f p).val
  have hsub : range f ⊆ M := by
    rintro p ⟨s,rfl⟩; exact hGM ⟨(e s).val,(e s).property,rfl⟩
  have hTS : TraceSplitCondition (range f) predecessorRows label := by
    intro I hI
    obtain ⟨s,hs,hsplit⟩ := hS I hI
    let j : S := ⟨s,hs⟩
    have hl : label (f j) = s := congrArg Subtype.val (Function.leftInverse_invFun hfi j)
    obtain ⟨a,ha⟩ := (hH.1.2.1 (e j).val (e j).property).nonempty
    have ht := predGraph_trace_tail ha
    refine ⟨f j,⟨j,rfl⟩,?_,?_⟩
    · apply (hsplit.1.diff (Set.finite_Iio a)).mono
      rintro n ⟨⟨hnI,hns⟩,hna⟩
      refine ⟨hnI,ht n (by simpa using hna),?_⟩
      simpa only [hl] using hns
    · apply (hsplit.2.diff (Set.finite_Iio a)).mono
      rintro n ⟨⟨hnI,hns⟩,hna⟩
      refine ⟨hnI,ht n (by simpa using hna),?_⟩
      simpa only [hl] using hns
  obtain ⟨K,hK,hKc,hnot⟩ := trace_splitting_replacement hM hsub predecessorRows label hTS
  let eqv : (ℕ × ℕ) ≃ ℕ := Classical.choice inferInstance
  refine ⟨Set.image eqv '' K, mad_image eqv hK, ?_, ?_⟩
  · exact (Cardinal.mk_image_eq eqv.injective.image_injective).trans (hKc.trans hMc)
  · exact (finIntersecting_equiv eqv K).not.mpr hnot

/-- Paper Corollary 8.4, including the necessary direction. -/
theorem nonFinIntersecting_mad_size_a_iff :
    (∃ K : Set (Set ℕ), MAD K ∧ #K = almostDisjointnessNumber ∧
      ¬ _root_.R0.FinIntersecting K) ↔
        _root_.R0.splittingNumber ≤ almostDisjointnessNumber := by
  constructor
  · rintro ⟨K,_,hc,hn⟩
    simpa only [hc] using _root_.R0.splittingNumber_le_of_not_finIntersecting hn
  · exact exists_nonFinIntersecting_mad_size_a

end InfinitaryCombinatorics.Formalizations.R0

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal

/-- The exact triangular ground set used in Section 8. -/
def predTriangle : Set (ℕ × ℕ) := {p | p.1 < p.2}

lemma predGraph_subset_triangle (A : Set ℕ) : predGraph A ⊆ predTriangle :=
  fun _ hp => hp.2.1

lemma predecessor_row_singleton {A : Set ℕ} {a k : ℕ} (ha : a ∈ A) (hk : a ≤ k) :
    ∃! p, p ∈ predGraph A ∩ predecessorRows.block k := by
  obtain ⟨p,hp⟩ := predGraph_trace_tail ha k hk
  exact ⟨p,hp,fun q hq => predGraph_row_unique A k hq hp⟩

/-- Paper Lemma 8.2 on its exact triangular ground set, retaining the actual graphs. -/
theorem predecessor_completion_triangle {H : Set (Set ℕ)} (hH : MAD H)
    (hHc : #H = almostDisjointnessNumber) :
    ∃ M : Set (Set (ℕ × ℕ)), M.Infinite ∧ MaximalOn M predTriangle ∧
      #M = almostDisjointnessNumber ∧ predGraph '' H ⊆ M ∧
      ∀ m, predColumn m ∩ predTriangle ∈ M := by
  obtain ⟨K,hK,hKc,hcols,hgraphs⟩ := predecessor_completion hH hHc
  let M := restriction K predTriangle
  have hGM : predGraph '' H ⊆ M := by
    rintro _ ⟨A,hA,rfl⟩
    exact ⟨predGraph_infinite (hH.1.2.1 A hA),predGraph A,hgraphs ⟨A,hA,rfl⟩,
      (Set.inter_eq_left.mpr (predGraph_subset_triangle A)).symm⟩
  have hi : M.Infinite := (hH.1.1.image predGraph_injective.injOn).mono hGM
  refine ⟨M,hi,⟨restriction_ad hK.1.2 predTriangle,fun _ hp => restriction_subset hp,?_⟩,
    ?_,hGM,?_⟩
  · intro Y hYW hY
    obtain ⟨a,ha,hYa⟩ := hK.2 Y hY
    have hai : (a ∩ predTriangle).Infinite := hYa.mono (fun _ hx => ⟨hx.2,hYW hx.1⟩)
    exact ⟨a ∩ predTriangle,⟨hai,a,ha,rfl⟩,hYa.mono (fun _ hx => ⟨hx.1,hx.2,hYW hx.1⟩)⟩
  · apply le_antisymm ((restriction_card_le K predTriangle).trans_eq hKc)
    calc
      almostDisjointnessNumber = #H := hHc.symm
      _ = #(predGraph '' H) := (Cardinal.mk_image_eq predGraph_injective).symm
      _ ≤ #M := Cardinal.mk_le_mk_of_subset hGM
  · intro m
    have hcell : (predColumn m ∩ predTriangle).Infinite := by
      apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (m,m+n+1))
      · intro n k h; have := congrArg Prod.snd h; dsimp at this; omega
      · intro n; exact ⟨rfl,by dsimp [predTriangle]; omega⟩
    exact ⟨hcell,predColumn m,hcols ⟨m,rfl⟩,rfl⟩

end InfinitaryCombinatorics.Formalizations.R0
