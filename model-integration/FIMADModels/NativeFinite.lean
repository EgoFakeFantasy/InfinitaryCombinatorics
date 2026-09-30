import Formalizations.FIMAD.UnboundedSyntax
import YesMetaZFC.SetTheory.FunctionConstruction
import YesMetaZFC.SetTheory.Ord.Natural

/-! Reuse the native ZF model API with the manuscript's Kuratowski pairs and
injection-based finiteness. All natural numbers here belong to the model. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.Internal
open YesMetaZFC YesMetaZFC.SetTheory
universe u
variable {M : SetTheory.Structure.{u}}

private theorem pair_intersection {p a b x : M.Domain} (h : Pair M.mem p a b) :
    (∀ z, M.mem z p → M.mem x z) ↔ x = a := by
  obtain ⟨s, t, hs, ht, hp⟩ := h
  constructor
  · intro h
    exact (hs x).mp (h s ((hp s).mpr (Or.inl rfl)))
  · intro hx z hz
    rcases (hp z).mp hz with rfl | rfl
    · exact (hs x).mpr hx
    · exact (ht x).mpr (Or.inl hx)

private theorem pair_union {p a b x : M.Domain} (h : Pair M.mem p a b) :
    (∃ z, M.mem z p ∧ M.mem x z) ↔ x = a ∨ x = b := by
  obtain ⟨s, t, hs, ht, hp⟩ := h
  constructor
  · rintro ⟨z, hz, hx⟩
    rcases (hp z).mp hz with rfl | rfl
    · exact Or.inl ((hs x).mp hx)
    · exact (ht x).mp hx
  · intro hx
    exact ⟨t, (hp t).mpr (Or.inr rfl), (ht x).mpr hx⟩

/-- The actual Kuratowski encoding determines both coordinates. -/
theorem pair_injective {p a b c d : M.Domain}
    (h : Pair M.mem p a b) (h' : Pair M.mem p c d) : a = c ∧ b = d := by
  have hac : a = c := (pair_intersection h').mp ((pair_intersection h).mpr rfl)
  subst c
  have hbd : b = a ∨ b = d := (pair_union h').mp ((pair_union h).mpr (Or.inr rfl))
  have hdb : d = a ∨ d = b := (pair_union h).mp ((pair_union h').mpr (Or.inr rfl))
  refine ⟨rfl, ?_⟩
  rcases hbd with hba | hbd
  · rcases hdb with hda | hdb
    · exact hba.trans hda.symm
    · exact hdb.symm
  · exact hbd

theorem pair_unique (hExt : Extensional M) {p q a b : M.Domain}
    (h : Pair M.mem p a b) (h' : Pair M.mem q a b) : p = q := by
  obtain ⟨s, t, hs, ht, hp⟩ := h
  obtain ⟨s', t', hs', ht', hq⟩ := h'
  have hss : s = s' := hExt.eq_of_same_members _ _ (fun x => (hs x).trans (hs' x).symm)
  have htt : t = t' := hExt.eq_of_same_members _ _ (fun x => (ht x).trans (ht' x).symm)
  subst s'
  subst t'
  exact hExt.eq_of_same_members _ _ (fun x => (hp x).trans (hq x).symm)

def pairConvention : Definitional.Project.OrderedPairConvention where
  code := Syntax.PairFormula
  freeClosed_code := Syntax.closed_PairFormula

/-- The upstream function API can use precisely the manuscript's pair coding. -/
def pairInterpretation (hZF : M.Models SetTheory.ZF) : pairConvention.Interpretation M where
  Codes := Pair M.mem
  realizes := Syntax.satisfies_PairFormula hZF.1
  total := by
    intro a b
    obtain ⟨s, hs⟩ := KP.exists_singleton (ZF.modelsKP hZF) a
    obtain ⟨t, ht⟩ := KP.exists_pair (ZF.modelsKP hZF) a b
    obtain ⟨p, hp⟩ := KP.exists_pair (ZF.modelsKP hZF) s t
    exact ⟨p, s, t, hs, ht, hp⟩
  unique := pair_unique hZF.1
  injective := pair_injective

theorem value_pairMember (hZF : M.Models SetTheory.ZF) (f x y : M.Domain) :
    Value M.mem f x y ↔ M.PairMember (pairInterpretation hZF) x y f := by
  exact exists_congr (fun _ => and_comm)

/-- Exact equivalence, including the requirement that every graph member is a pair. -/
theorem injection_native_iff (hZF : M.Models SetTheory.ZF) (f a b : M.Domain) :
    Injection M.mem f a b ↔ M.IsSetInjectionFromTo (pairInterpretation hZF) f a b := by
  have hv := value_pairMember hZF f
  constructor
  · rintro ⟨hf, hr, hi⟩
    have hd : ∀ x y, Value M.mem f x y → M.mem x a := by
      rintro x y ⟨p, hp, hpcode⟩
      obtain ⟨z, w, hz, hw⟩ := hf.1 p hp
      exact (pair_injective hpcode hw).1 ▸ hz
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · intro p hp
      obtain ⟨x, y, _, hc⟩ := hf.1 p hp
      exact ⟨x, y, hc⟩
    · intro x y z hy hz
      obtain ⟨w, _, hw⟩ := hf.2 x (hd x y ((hv x y).mpr hy))
      exact (hw y ((hv x y).mpr hy)).trans (hw z ((hv x z).mpr hz)).symm
    · intro x
      constructor
      · intro hx
        obtain ⟨y, hy, _⟩ := hf.2 x hx
        exact ⟨y, (hv x y).mp hy⟩
      · rintro ⟨y, hy⟩
        exact hd x y ((hv x y).mpr hy)
    · intro x hx
      obtain ⟨y, hy, _⟩ := hf.2 x hx
      exact ⟨y, hr x y hy, (hv x y).mp hy⟩
    · intro x z y hx hz
      exact hi x z y ((hv x y).mpr hx) ((hv z y).mpr hz)
  · rintro ⟨⟨hf, hd, ht⟩, hi⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro p hp
      obtain ⟨x, y, hc⟩ := hf.1 p hp
      exact ⟨x, y, (hd x).mpr ⟨y, p, hc, hp⟩, hc⟩
    · intro x hx
      obtain ⟨y, _, hy⟩ := ht x hx
      exact ⟨y, (hv x y).mpr hy, fun z hz => hf.2 x z y ((hv x z).mp hz) hy⟩
    · intro x y hy
      have hpair := (hv x y).mp hy
      obtain ⟨z, hz, hp⟩ := ht x ((hd x).mpr ⟨y, hpair⟩)
      exact (hf.2 x z y hp hpair) ▸ hz
    · intro x z y hx hz
      exact hi x z y ((hv x y).mp hx) ((hv z y).mp hz)

/-- A subset of an internal natural number is finite in the original sense. -/
theorem finite_of_subset_natural (hZF : M.Models SetTheory.ZF)
    {w a n : M.Domain} (hn : M.mem n w) (ha : Subset M.mem a n) : Finite M.mem w a := by
  obtain ⟨f, hf⟩ := ZF.exists_inclusionInjection hZF (pairInterpretation hZF) ha
  exact ⟨n, hn, f, (injection_native_iff hZF f a n).mpr hf⟩

theorem successor_native_iff (hExt : Extensional M) (s n : M.Domain) :
    Succ M.mem s n ↔ M.SuccessorOf s n := by
  apply forall_congr'
  intro x
  apply iff_congr Iff.rfl
  exact or_congr Iff.rfl ⟨fun h => h ▸ (fun _ => Iff.rfl),
    hExt.eq_of_same_members x n⟩

theorem inductive_native_iff (hExt : Extensional M) (a : M.Domain) :
    Inductive M.mem a ↔ M.IsInductive a := by
  unfold Inductive Structure.IsInductive
  apply and_congr Iff.rfl
  apply forall_congr'
  intro x
  apply imp_congr Iff.rfl
  apply exists_congr
  intro y
  exact and_congr (successor_native_iff hExt y x) Iff.rfl

theorem omega_native_iff (hExt : Extensional M) (w : M.Domain) :
    Omega M.mem w ↔ M.IsOmega w := by
  unfold Omega Structure.IsOmega
  apply and_congr (inductive_native_iff hExt w)
  apply forall_congr'
  intro a
  exact imp_congr (inductive_native_iff hExt a) Iff.rfl

/-- Failure of unboundedness yields an actual internal finite witness. -/
theorem finite_of_not_unbounded (hZF : M.Models SetTheory.ZF)
    {w a : M.Domain} (hw : Omega M.mem w) (ha : Subset M.mem a w)
    (h : ¬ Unbounded M.mem w a) : Finite M.mem w a := by
  classical
  have hn := (omega_native_iff hZF.1 w).mp hw
  have ho := hn.membershipWellOrder hZF
  have hex : ∃ n, M.mem n w ∧ ¬ ∃ y, M.mem y w ∧ (M.mem n y ∨ n = y) ∧ M.mem y a := by
    apply Classical.byContradiction
    intro hex
    apply h
    intro n hn
    exact Classical.byContradiction (fun hy => hex ⟨n, hn, hy⟩)
  obtain ⟨n, hnw, htail⟩ := hex
  apply finite_of_subset_natural hZF hnw
  intro y hy
  rcases ho.linear.compare n hnw y (ha y hy) with heq | hny | hyn
  · exact False.elim (htail ⟨y, ha y hy, Or.inr (hZF.1.eq_of_same_members n y heq), hy⟩)
  · exact False.elim (htail ⟨y, ha y hy, Or.inl hny, hy⟩)
  · exact hyn

/-- This direction now uses upstream ZF constructions with the original definition. -/
theorem unbounded_of_infinite (hZF : M.Models SetTheory.ZF)
    {w a : M.Domain} (hw : Omega M.mem w) (ha : Subset M.mem a w)
    (hi : Infinite M.mem w a) : Unbounded M.mem w a := by
  classical
  exact Classical.byContradiction (fun h => hi (finite_of_not_unbounded hZF hw ha h))
end InfinitaryCombinatorics.Formalizations.FIMAD.Internal
