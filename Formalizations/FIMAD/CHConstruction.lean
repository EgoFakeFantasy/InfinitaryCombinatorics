import Formalizations.FIMAD.IdealCover
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Continuum

namespace InfinitaryCombinatorics.Formalizations.FIMAD
open Set
open InfinitaryCombinatorics.Formalizations.R0 (blocksOver)

def tracePattern (C : R0.FinSequence ℕ) (I : Set ℕ) (F : Set (Set ℕ)) : Set ℕ :=
  I ∩ ⋂ a ∈ F, R0.trace C a

structure FIStage where
  member : Set ℕ
  witness : Set ℕ

namespace CHConstruction
variable {ι : Type} [LinearOrder ι]

def oldFamily (B : Set (Set ℕ)) (x : ι) (p : Set.Iio x → FIStage) : Set (Set ℕ) :=
  B ∪ range (fun y => (p y).member)

noncomputable def registeredWitness (x : ι) (p : Set.Iio x → FIStage)
    (I : Set ℕ) (γ : ι) : Set ℕ :=
  if h : γ < x then (p ⟨γ, h⟩).witness else I

def requirements (C : ι → R0.FinSequence ℕ) (X : ι → Set ℕ)
    (B : Set (Set ℕ)) (x : ι) (p : Set.Iio x → FIStage) (I : Set ℕ) : Set (Set ℕ) :=
  insert (X x) (⋃ γ ∈ Set.Iic x, ⋃ F ∈ {F : Set (Set ℕ) | F.Finite ∧ F ⊆ oldFamily B x p},
    {blocksOver (C γ) (tracePattern (C γ) (registeredWitness x p I γ) F)})

def StageOK (C : ι → R0.FinSequence ℕ) (X : ι → Set ℕ)
    (B : Set (Set ℕ)) (x : ι) (p : Set.Iio x → FIStage) (s : FIStage) : Prop :=
  s.member.Infinite ∧
  (∀ a ∈ oldFamily B x p, (s.member ∩ a).Finite) ∧
  s.witness.Infinite ∧
  (∀ a ∈ oldFamily B x p, (s.witness ∩ R0.trace (C x) a).Infinite →
    AlmostSubset s.witness (R0.trace (C x) a)) ∧
  ∀ Y ∈ requirements C X B x p s.witness,
    ¬ InIdeal (oldFamily B x p) Y → (s.member ∩ Y).Infinite

lemma oldFamily_countable {B : Set (Set ℕ)} (hB : B.Countable)
    (x : ι) (hx : (Set.Iio x).Countable) (p : Set.Iio x → FIStage) :
    (oldFamily B x p).Countable := by
  letI := hx.to_subtype
  exact hB.union (countable_range _)

lemma stage_exists (C : ι → R0.FinSequence ℕ) (X : ι → Set ℕ)
    {B : Set (Set ℕ)} (hcB : B.Countable) (x : ι) (hx : (Set.Iio x).Countable)
    (p : Set.Iio x → FIStage) (hA : R0.AlmostDisjoint (oldFamily B x p)) :
    ∃ s, StageOK C X B x p s := by
  classical
  have hcA := oldFamily_countable hcB x hx p
  obtain ⟨I, hI, hIA⟩ := exists_unsplit_of_countable (R0.trace (C x) '' oldFamily B x p)
    (hcA.image _)
  have hcR : (requirements C X B x p I).Countable := by
    apply Set.Countable.insert
    have hic : (Set.Iic x).Countable := (hx.insert x).mono (by
      intro y hy
      rcases lt_or_eq_of_le hy with h | h
      · exact Or.inr h
      · exact Or.inl h)
    exact hic.biUnion fun γ _ => (Set.countable_setOf_finite_subset hcA).biUnion fun F _ => countable_singleton _
  obtain ⟨a, ha, haA, haR⟩ := countable_positive_extension hA hcA
    (hcR.mono (inter_subset_left : requirements C X B x p I ∩ {Y | ¬ InIdeal (oldFamily B x p) Y} ⊆ _))
    (fun _ h => h.2)
  refine ⟨⟨a, I⟩, ha, haA, hI, ?_, ?_⟩
  · intro b hb hi
    exact not_infinite.mp (fun hd => hIA _ ⟨b, hb, rfl⟩ ⟨hi, hd⟩)
  · intro Y hY hpos
    exact haR Y ⟨hY, hpos⟩

variable [WellFoundedLT ι]

noncomputable def build (C : ι → R0.FinSequence ℕ) (X : ι → Set ℕ)
    (B : Set (Set ℕ)) : ι → FIStage := by
  classical
  exact WellFounded.fix wellFounded_lt fun x prev =>
    if h : ∃ s, StageOK C X B x (fun y => prev y.val y.property) s
    then h.choose else ⟨∅, ∅⟩

lemma build_stage (C : ι → R0.FinSequence ℕ) (X : ι → Set ℕ)
    {B : Set (Set ℕ)} (hB : R0.AlmostDisjoint B) (hcB : B.Countable)
    (hc : ∀ x : ι, (Set.Iio x).Countable) (x : ι) :
    StageOK C X B x (fun y => build C X B y.val) (build C X B x) := by
  classical
  induction x using (wellFounded_lt (α := ι)).induction with
  | h x ih =>
    have hA : R0.AlmostDisjoint (oldFamily B x (fun y => build C X B y.val)) := by
      refine ⟨hB.1.mono subset_union_left, ?_, ?_⟩
      · rintro a (ha | ⟨y, rfl⟩)
        · exact hB.2.1 a ha
        · exact (ih y y.property).1
      · rintro a (ha | ⟨y, rfl⟩) b (hb | ⟨z, rfl⟩) hab
        · exact hB.2.2 a ha b hb hab
        · simpa [inter_comm] using (ih z z.property).2.1 a (Or.inl ha)
        · exact (ih y y.property).2.1 b (Or.inl hb)
        · rcases lt_trichotomy y.val z.val with h | h | h
          · simpa [inter_comm] using (ih z z.property).2.1 _ (Or.inr ⟨⟨y, h⟩, rfl⟩)
          · exact False.elim (hab (congrArg (fun t => (build C X B t).member) h))
          · exact (ih y y.property).2.1 _ (Or.inr ⟨⟨z, h⟩, rfl⟩)
    have hex := stage_exists C X hcB x (hc x) (fun y => build C X B y.val) hA
    conv_rhs => rw [build, WellFounded.fix_eq]
    exact dif_pos hex ▸ hex.choose_spec

def finalFamily (B : Set (Set ℕ)) (f : ι → FIStage) : Set (Set ℕ) :=
  B ∪ range (fun x => (f x).member)

omit [WellFoundedLT ι] in
lemma oldFamily_subset_final (B : Set (Set ℕ)) (f : ι → FIStage) (x : ι) :
    oldFamily B x (fun y => f y.val) ⊆ finalFamily B f := by
  rintro a (ha | ⟨y, rfl⟩)
  · exact Or.inl ha
  · exact Or.inr (mem_range_self y.val)

omit [WellFoundedLT ι] in
lemma oldFamily_mono (B : Set (Set ℕ)) (f : ι → FIStage) {x y : ι} (hxy : x ≤ y) :
    oldFamily B x (fun z => f z.val) ⊆ oldFamily B y (fun z => f z.val) := by
  rintro a (ha | ⟨z, rfl⟩)
  · exact Or.inl ha
  · exact Or.inr ⟨⟨z, z.property.trans_le hxy⟩, rfl⟩

omit [WellFoundedLT ι] in
lemma finalFamily_ad (C : ι → R0.FinSequence ℕ) (X : ι → Set ℕ)
    {B : Set (Set ℕ)} (hB : R0.AlmostDisjoint B) (f : ι → FIStage)
    (hf : ∀ x, StageOK C X B x (fun y => f y.val) (f x)) :
    R0.AlmostDisjoint (finalFamily B f) := by
  refine ⟨hB.1.mono subset_union_left, ?_, ?_⟩
  · rintro a (ha | ⟨x, rfl⟩)
    · exact hB.2.1 a ha
    · exact (hf x).1
  · rintro a (ha | ⟨x, rfl⟩) b (hb | ⟨y, rfl⟩) hab
    · exact hB.2.2 a ha b hb hab
    · simpa [inter_comm] using (hf y).2.1 a (Or.inl ha)
    · exact (hf x).2.1 b (Or.inl hb)
    · rcases lt_trichotomy x y with h | h | h
      · simpa [inter_comm] using (hf y).2.1 _ (Or.inr ⟨⟨x, h⟩, rfl⟩)
      · exact False.elim (hab (congrArg (fun t => (f t).member) h))
      · exact (hf x).2.1 _ (Or.inr ⟨⟨y, h⟩, rfl⟩)

omit [WellFoundedLT ι] in
lemma finalFamily_mad (C : ι → R0.FinSequence ℕ) (X : ι → Set ℕ)
    {B : Set (Set ℕ)} (hB : R0.AlmostDisjoint B) (f : ι → FIStage)
    (hf : ∀ x, StageOK C X B x (fun y => f y.val) (f x))
    (hX : Function.Surjective X) : MAD (finalFamily B f) := by
  refine ⟨finalFamily_ad C X hB f hf, ?_⟩
  intro Y hY
  obtain ⟨x, rfl⟩ := hX Y
  by_cases hpos : InIdeal (oldFamily B x (fun y => f y.val)) (X x)
  · obtain ⟨a, ha, hi⟩ := infinite_inIdeal_meets_member hY hpos
    exact ⟨a, oldFamily_subset_final B f x ha, hi⟩
  · refine ⟨(f x).member, Or.inr (mem_range_self x), ?_⟩
    simpa [inter_comm] using (hf x).2.2.2.2 (X x) (mem_insert _ _) hpos

lemma inIdeal_mono_family {A B : Set (Set ℕ)} (hAB : A ⊆ B) {Y : Set ℕ}
    (h : InIdeal A Y) : InIdeal B Y := by
  obtain ⟨F, hF, hFA, hY⟩ := h
  exact ⟨F, hF, hFA.trans hAB, hY⟩

lemma finite_cofinite_pattern {C : R0.FinSequence ℕ} {I : Set ℕ} (hI : I.Infinite)
    {F : Set (Set ℕ)} (hF : F.Finite) (h : ∀ a ∈ F, AlmostSubset I (R0.trace C a)) :
    (tracePattern C I F).Infinite := by
  have he : (⋃ a ∈ F, I \ R0.trace C a).Finite := hF.biUnion h
  apply (hI.diff he).mono
  rintro n ⟨hn, hnot⟩
  refine ⟨hn, mem_iInter₂.mpr ?_⟩
  intro a ha
  by_contra hh
  exact hnot (mem_iUnion₂.mpr ⟨a, ha, hn, hh⟩)

lemma pattern_insert (C : R0.FinSequence ℕ) (I : Set ℕ) (F : Set (Set ℕ)) (a : Set ℕ) :
    tracePattern C I (insert a F) = tracePattern C I F ∩ R0.trace C a := by
  ext n
  simp only [tracePattern, mem_inter_iff, mem_iInter, mem_insert_iff]
  aesop

omit [WellFoundedLT ι] in
/-- Once no infinite block union lies in the final ideal, every finite
collection of later members preserves the registered infinite intersection. -/
lemma later_pattern_infinite (C : ι → R0.FinSequence ℕ) (X : ι → Set ℕ)
    (B : Set (Set ℕ)) (f : ι → FIStage)
    (hf : ∀ x, StageOK C X B x (fun y => f y.val) (f x)) (γ : ι)
    (hpos : ∀ S : Set ℕ, S.Infinite → ¬ InIdeal (finalFamily B f) (blocksOver (C γ) S))
    {G : Set (Set ℕ)} (hG : G.Finite) (hGold : G ⊆ oldFamily B γ (fun y => f y.val))
    (hGI : ∀ a ∈ G, ((f γ).witness ∩ R0.trace (C γ) a).Infinite)
    (K : Finset ι) (hK : ∀ δ ∈ K, γ ≤ δ) :
    (tracePattern (C γ) (f γ).witness (G ∪ (fun δ => (f δ).member) '' (K : Set ι))).Infinite := by
  classical
  induction K using Finset.induction_on_max with
  | empty =>
    simp only [Finset.coe_empty, image_empty, union_empty]
    exact finite_cofinite_pattern (hf γ).2.2.1 hG
      (fun a ha => (hf γ).2.2.2.1 a (hGold ha) (hGI a ha))
  | insert δ K hlt ih =>
    have hγδ := hK δ (Finset.mem_insert_self _ _)
    have hKi : ∀ ε ∈ K, γ ≤ ε := fun ε hε => hK ε (Finset.mem_insert_of_mem hε)
    have hS := ih hKi
    let F := G ∪ (fun ε => (f ε).member) '' (K : Set ι)
    have hF : F.Finite := hG.union (K.finite_toSet.image _)
    have hFold : F ⊆ oldFamily B δ (fun y => f y.val) := by
      rintro a (ha | ⟨ε, hε, rfl⟩)
      · exact oldFamily_mono B f hγδ (hGold ha)
      · exact Or.inr ⟨⟨ε, hlt ε hε⟩, rfl⟩
    have hreg : registeredWitness δ (fun y => f y.val) (f δ).witness γ = (f γ).witness := by
      by_cases hh : γ < δ
      · simp [registeredWitness, hh]
      · have heq : γ = δ := le_antisymm hγδ (le_of_not_gt hh)
        subst γ
        simp [registeredWitness]
    have hreq : blocksOver (C γ) (tracePattern (C γ) (f γ).witness F) ∈
        requirements C X B δ (fun y => f y.val) (f δ).witness := by
      apply mem_insert_of_mem
      apply mem_iUnion₂.mpr
      refine ⟨γ, hγδ, mem_iUnion₂.mpr ⟨F, ⟨hF, hFold⟩, ?_⟩⟩
      simp only [hreg, mem_singleton_iff]
    have hp : ¬ InIdeal (oldFamily B δ (fun y => f y.val))
        (blocksOver (C γ) (tracePattern (C γ) (f γ).witness F)) :=
      fun h => hpos _ hS (inIdeal_mono_family (oldFamily_subset_final B f δ) h)
    have hh := trace_infinite_of_infinite_inter_blocks (C γ) ((hf δ).2.2.2.2 _ hreq hp)
    have heq : G ∪ (fun ε => (f ε).member) '' (↑(insert δ K) : Set ι) = insert (f δ).member F := by
      simp only [F, Finset.coe_insert, Set.image_insert_eq, union_insert]
    rw [heq, pattern_insert]
    exact hh

omit [WellFoundedLT ι] in
lemma finalFamily_fi (C : ι → R0.FinSequence ℕ) (X : ι → Set ℕ)
    {B : Set (Set ℕ)} (hB : R0.AlmostDisjoint B) (f : ι → FIStage)
    (hf : ∀ x, StageOK C X B x (fun y => f y.val) (f x))
    (hC : Function.Surjective C) : R0.FinIntersecting (finalFamily B f) := by
  classical
  intro D
  obtain ⟨γ, rfl⟩ := hC D
  by_cases hcover : ∃ I : Set ℕ, I.Infinite ∧ InIdeal (finalFamily B f) (blocksOver (C γ) I)
  · obtain ⟨I, hI, hc⟩ := hcover
    obtain ⟨J, _, hJ, hcenter⟩ := ideal_block_cover_witness (finalFamily_ad C X hB f hf).2 (C γ) hI hc
    exact ⟨J, hJ, hcenter⟩
  · have hpos : ∀ I : Set ℕ, I.Infinite → ¬ InIdeal (finalFamily B f) (blocksOver (C γ) I) :=
      fun I hI h => hcover ⟨I, hI, h⟩
    refine ⟨(f γ).witness, (hf γ).2.2.1, ?_⟩
    intro T hT hTf hTne
    letI := hTf.to_subtype
    have hw (t : T) : ∃ a ∈ finalFamily B f, t.val = (f γ).witness ∩ R0.trace (C γ) a :=
      (hT t.property).2
    choose a ha hta using hw
    let F : Set (Set ℕ) := range a
    have hF : F.Finite := finite_range a
    let O := oldFamily B γ (fun y => f y.val)
    have hi (b) (hb : b ∈ F) : ((f γ).witness ∩ R0.trace (C γ) b).Infinite := by
      obtain ⟨t, rfl⟩ := hb
      exact hta t ▸ (hT t.property).1
    have hm (b) (hb : b ∈ F) : b ∈ finalFamily B f := by
      obtain ⟨t, rfl⟩ := hb
      exact ha t
    have hl (b : ↥(F \ O)) : ∃ δ : ι, γ ≤ δ ∧ (f δ).member = b.val := by
      rcases hm b b.property.1 with hb | ⟨δ, hδ⟩
      · exact False.elim (b.property.2 (Or.inl hb))
      · refine ⟨δ, ?_, hδ⟩
        by_contra hδγ
        exact b.property.2 (Or.inr ⟨⟨δ, lt_of_not_ge hδγ⟩, hδ⟩)
    choose δ hδγ hδb using hl
    letI := (hF.diff (t := O)).to_subtype
    let K := (finite_range δ).toFinset
    have hK : ∀ ε ∈ K, γ ≤ ε := by
      intro ε hε
      obtain ⟨b, rfl⟩ := (finite_range δ).mem_toFinset.mp hε
      exact hδγ b
    have hh := later_pattern_infinite C X B f hf γ hpos (hF.inter_of_left O)
      (inter_subset_right : F ∩ O ⊆ O) (fun b hb => hi b hb.1) K hK
    apply hh.mono
    intro n hn
    apply mem_iInter₂.mpr
    intro t ht
    have htEq : t = (f γ).witness ∩ R0.trace (C γ) (a ⟨t, ht⟩) := hta ⟨t, ht⟩
    rw [htEq]
    refine ⟨hn.1, mem_iInter₂.mp hn.2 (a ⟨t, ht⟩) ?_⟩
    have hbF : a ⟨t, ht⟩ ∈ F := mem_range_self _
    by_cases hbO : a ⟨t, ht⟩ ∈ O
    · exact Or.inl ⟨hbF, hbO⟩
    · let b : ↥(F \ O) := ⟨a ⟨t, ht⟩, hbF, hbO⟩
      exact Or.inr ⟨δ b, (finite_range δ).mem_toFinset.mpr (mem_range_self b), hδb b⟩

theorem exists_fi_mad_of_enumerations (C : ι → R0.FinSequence ℕ) (X : ι → Set ℕ)
    {B : Set (Set ℕ)} (hB : R0.AlmostDisjoint B) (hcB : B.Countable)
    (hc : ∀ x : ι, (Set.Iio x).Countable)
    (hC : Function.Surjective C) (hX : Function.Surjective X) : ExistsFIMAD := by
  let f := build C X B
  have hf := build_stage C X hB hcB hc
  exact ⟨finalFamily B f, finalFamily_mad C X hB f hf hX, finalFamily_fi C X hB f hf hC⟩

end CHConstruction

lemma finSequence_card_le_continuum :
    Cardinal.mk (R0.FinSequence ℕ) ≤ (2 : Cardinal) ^ Cardinal.aleph0 := by
  let code : R0.FinSequence ℕ → Set (ℕ × ℕ) := fun C => {p | p.2 ∈ C.block p.1}
  have hi : Function.Injective code := by
    intro C D h
    have hb : C.block = D.block := by
      funext n
      ext k
      exact Set.ext_iff.mp h (n, k)
    cases C
    cases D
    cases hb
    rfl
  simpa using Cardinal.mk_le_of_injective hi

/-- The full CH construction on the genuine first uncountable ordinal.
The output is an infinite maximal AD family on Nat, with all fin-sequences tested. -/
theorem exists_fi_mad_of_CH
    (hCH : (2 : Cardinal.{0}) ^ Cardinal.aleph0 = Cardinal.aleph 1) : ExistsFIMAD := by
  classical
  let ι := (Cardinal.aleph 1).ord.ToType
  have hc (x : ι) : (Set.Iio x).Countable := by
    apply Cardinal.le_aleph0_iff_set_countable.mp
    apply Cardinal.lt_aleph_one_iff.mp
    have h := Cardinal.mk_Iio_lt x (by simp [ι])
    simpa [ι] using h
  let D : R0.FinSequence ℕ := {
    block := fun n => {n}
    finite := fun n => finite_singleton n
    nonempty := fun n => singleton_nonempty n
    disjoint := by intro n m h; exact disjoint_singleton.mpr h }
  letI : Nonempty (Set ℕ × R0.FinSequence ℕ) := ⟨(univ, D)⟩
  have hcard : Cardinal.mk (Set ℕ × R0.FinSequence ℕ) ≤ Cardinal.mk ι := by
    calc
      Cardinal.mk (Set ℕ × R0.FinSequence ℕ) =
          (2 : Cardinal) ^ Cardinal.aleph0 * Cardinal.mk (R0.FinSequence ℕ) := by simp
      _ ≤ (2 : Cardinal) ^ Cardinal.aleph0 * (2 : Cardinal) ^ Cardinal.aleph0 :=
        mul_le_mul_right finSequence_card_le_continuum _
      _ = (2 : Cardinal) ^ Cardinal.aleph0 := Cardinal.mul_eq_self Cardinal.aleph0_le_continuum
      _ = Cardinal.mk ι := by simpa only [ι, Cardinal.mk_toType, Cardinal.card_ord] using hCH
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hcard
  let tasks : ι → Set ℕ × R0.FinSequence ℕ := Function.invFun e
  have ht : Function.Surjective tasks := by
    intro p
    exact ⟨e p, Function.leftInverse_invFun e.injective p⟩
  have hX : Function.Surjective (fun x => (tasks x).1) := by
    intro X
    obtain ⟨x, hx⟩ := ht (X, D)
    exact ⟨x, congrArg Prod.fst hx⟩
  have hC : Function.Surjective (fun x => (tasks x).2) := by
    intro C
    obtain ⟨x, hx⟩ := ht (univ, C)
    exact ⟨x, congrArg Prod.snd hx⟩
  obtain ⟨M, hM, _, _⟩ := InfinitaryCombinatorics.Formalizations.R0.uniform_nonFinIntersecting_mad
  obtain ⟨B, hBM, hcB, hiB⟩ := hM.1.1.exists_subset_countable_infinite
  exact CHConstruction.exists_fi_mad_of_enumerations _ _
    ⟨hiB, ADFamily.mono hM.1.2 hBM⟩ hcB hc hC hX

theorem exists_fi_mad_size_aleph_one_of_CH
    (hCH : (2 : Cardinal.{0}) ^ Cardinal.aleph0 = Cardinal.aleph 1) :
    ∃ M : Set (Set ℕ), MAD M ∧ R0.FinIntersecting M ∧ Cardinal.mk M = Cardinal.aleph 1 := by
  obtain ⟨M, hM, hFI⟩ := exists_fi_mad_of_CH hCH
  refine ⟨M, hM, hFI, le_antisymm ?_ ?_⟩
  · calc
      Cardinal.mk M ≤ Cardinal.mk (Set ℕ) := Cardinal.mk_set_le M
      _ = Cardinal.aleph 1 := by simpa using hCH
  · exact Cardinal.aleph_one_le_iff.mpr (aleph0_lt_boundingNumber.trans_le (boundingNumber_le_mad_card hM))

end InfinitaryCombinatorics.Formalizations.FIMAD
