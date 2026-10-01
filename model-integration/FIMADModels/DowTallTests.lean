import FIMADModels.DowValueTails

/-! One internal countable family tests every finite stem and natural bound.
The indexing product, selected families, and possible-value sets are all sets
of the arbitrary ZFC model. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def ValueSet (w A E N s V : M.Domain) : Prop :=
  ∀ k, M.mem k V ↔ M.mem k w ∧ AtLeast (M := M) N k ∧ PossibleValue w A E s k

def TotalTailTests (w A E H : M.Domain) : Prop :=
  InternalCountable w H ∧ (∀ X, M.mem X H → Internal.Subset M.mem X w) ∧
  ∀ N s, M.mem N w → FiniteSubset w s →
    (∃ F, TailTests w A E N s F ∧ Internal.Subset M.mem F H) ∧
    (∃ V, ValueSet w A E N s V ∧ M.mem V H)

namespace Syntax
def indexedTailTestsFormula {n} (w A E i F : Project.Term n) : Project.Formula 1 n :=
  .existsE (.existsE (.conj (kpair_m i.weaken.weaken (.bound 1) .newest)
    (tailTestsFormula w.weaken.weaken A.weaken.weaken E.weaken.weaken
      (.bound 1) .newest F.weaken.weaken)))

def valueSetFormula {n} (w A E N s V : Project.Term n) : Project.Formula 1 n :=
  .forallE (.iff (.mem .newest V.weaken)
    (.conj (.mem .newest w.weaken) (.conj (atLeastFormula N.weaken .newest)
      (possibleValueFormula w.weaken A.weaken E.weaken s.weaken .newest))))

def indexedValueSetFormula {n} (w A E i V : Project.Term n) : Project.Formula 1 n :=
  .existsE (.existsE (.conj (kpair_m i.weaken.weaken (.bound 1) .newest)
    (valueSetFormula w.weaken.weaken A.weaken.weaken E.weaken.weaken
      (.bound 1) .newest V.weaken.weaken)))

derive_free_closed indexedTailTestsFormula
derive_free_closed valueSetFormula
derive_free_closed indexedValueSetFormula

theorem indexedTailTestsFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E i F : Project.Term n) : Project.Formula.satisfies ρ (indexedTailTestsFormula w A E i F) ↔
      ∃ N s, KPair_d M (i.eval ρ) N s ∧ TailTests (w.eval ρ) (A.eval ρ) (E.eval ρ) N s (F.eval ρ) := by
  simp only [indexedTailTestsFormula, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, kpair_sat_l M hE, tailTestsFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem valueSetFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E N s V : Project.Term n) : Project.Formula.satisfies ρ (valueSetFormula w A E N s V) ↔
      ValueSet (w.eval ρ) (A.eval ρ) (E.eval ρ) (N.eval ρ) (s.eval ρ) (V.eval ρ) := by
  simp only [valueSetFormula, ValueSet, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_conj_iff, atLeastFormula_semantics hE,
    possibleValueFormula_semantics hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem indexedValueSetFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E i V : Project.Term n) : Project.Formula.satisfies ρ (indexedValueSetFormula w A E i V) ↔
      ∃ N s, KPair_d M (i.eval ρ) N s ∧ ValueSet (w.eval ρ) (A.eval ρ) (E.eval ρ) N s (V.eval ρ) := by
  simp only [indexedValueSetFormula, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, kpair_sat_l M hE, valueSetFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl
end Syntax

theorem value_set_exists (hZF : M.Models SetTheory.ZF) (w A E N s : M.Domain) :
    ∃ V, ValueSet w A E N s V := by
  let ρ : Env M 5 := ((((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push E).push N).push s
  let φ : UnarySchema 5 := {
    body := .conj (Syntax.atLeastFormula (.bound 2) .newest)
      (Syntax.possibleValueFormula (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest) }
  obtain ⟨V, hV⟩ := ZF.separation_exists_d hZF φ ρ w
  refine ⟨V, fun k => (hV k).trans ?_⟩
  simp only [φ, Project.Formula.satisfies_conj_iff, Syntax.atLeastFormula_semantics hZF.1,
    Syntax.possibleValueFormula_semantics hZF.1]
  rfl

theorem total_tail_tests_exists (hZFC : M.Models SetTheory.ZFC) {w A E : M.Domain}
    (hw : M.IsOmega w) (hUnbounded : UnboundedDecisions w A E)
    (hMono : MonotoneDecisions w A E) : ∃ H, TotalTailTests w A E H := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨P, hP, hPc⟩ := FiniteStems.finite_stem_space hZFC hw
  obtain ⟨id, hid⟩ := ZF.exists_identityBijection hZF I w
  obtain ⟨J, hJ⟩ := ZF.exists_cartesianProduct hZF I w P
  have hJc : InternalCountable w J := (countable_native_iff hZF w J).mpr
    (ZF.countable_product_l I hZF hw ⟨id, hid.1⟩ hPc hJ)
  have index {i} (hi : M.mem i J) : ∃ N s, M.mem N w ∧ FiniteSubset w s ∧ KPair_d M i N s := by
    obtain ⟨N, hN, s, hs, hi⟩ := (hJ i).mp hi
    exact ⟨N, s, hN, (hP s).mp hs, hi⟩
  obtain ⟨W, hW⟩ := ZF.exists_powerSet hZF w
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF W
  let ρ : Env M 3 := ((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push E
  let φ : BinarySchema 3 := {
    body := Syntax.indexedTailTestsFormula (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ i F : φ.denote ρ i F ↔ ∃ N s, KPair_d M i N s ∧ TailTests w A E N s F :=
    Syntax.indexedTailTestsFormula_semantics hZF.1 _ _ _ _ _ _
  obtain ⟨G, hG, he⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := J) (Y := Q) (by
    intro i hi
    obtain ⟨N, s, hN, hs, hiNs⟩ := index hi
    obtain ⟨F, hF⟩ := tail_tests_exists hZFC hw hs hN hUnbounded hMono
    exact ⟨F, (hQ F).mpr (fun X hX => (hW X).mpr (hF.2.1 X hX)),
      (hφ i F).mpr ⟨N, s, hiNs, hF⟩⟩)
  let η : Env M 1 := ⟨fun _ => G, fun _ => G⟩
  let χ : BinarySchema 1 := { body := entry_m (.bound 1) .newest (.bound 2) }
  have hχ i F : χ.denote η i F ↔ Entry_d M i F G := entry_sat_l M hZF.1 _ _ _ _
  obtain ⟨C, hC, hCc⟩ := countable_test_image hZFC χ η hJc
    (fun i hi => (hG.2.2 i hi).elim fun F hF => ⟨F, (hχ i F).mpr hF.2⟩)
    (fun i _ F F' hF hF' => hG.1.2 i F F' ((hχ i F).mp hF) ((hχ i F').mp hF'))
  have family {F} (hF : M.mem F C) : ∃ N s, TailTests w A E N s F := by
    obtain ⟨i, _, hiF⟩ := (hC F).mp hF
    obtain ⟨N, s, _, hF⟩ := (hφ i F).mp (he i F ((hχ i F).mp hiF))
    exact ⟨N, s, hF⟩
  obtain ⟨L, hL⟩ := KP.exists_union (ZF.modelsKP hZF) C
  have hLc : InternalCountable w L := (countable_native_iff hZF w L).mpr
    (ZFC.countable_union_l I hZFC hw ((countable_native_iff hZF w C).mp hCc) hL
      (fun F hF => (family hF).elim fun _ h => h.elim fun _ ht =>
        (countable_native_iff hZF w F).mp ht.1))
  have hLw X (hX : M.mem X L) : Internal.Subset M.mem X w := by
    obtain ⟨F, hFC, hXF⟩ := (hL X).mp hX
    obtain ⟨_, _, ht⟩ := family hFC
    exact ht.2.1 X hXF
  let ψ : BinarySchema 3 := {
    body := Syntax.indexedValueSetFormula (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hψ i V : ψ.denote ρ i V ↔ ∃ N s, KPair_d M i N s ∧ ValueSet w A E N s V :=
    Syntax.indexedValueSetFormula_semantics hZF.1 _ _ _ _ _ _
  obtain ⟨K, hK, hKc⟩ := countable_test_image hZFC ψ ρ hJc (by
    intro i hi
    obtain ⟨N, s, _, _, hiNs⟩ := index hi
    obtain ⟨V, hV⟩ := value_set_exists hZF w A E N s
    exact ⟨V, (hψ i V).mpr ⟨N, s, hiNs, hV⟩⟩) (by
      intro i _ V V' hV hV'
      obtain ⟨N, s, hiNs, hV⟩ := (hψ i V).mp hV
      obtain ⟨N', s', hiNs', hV'⟩ := (hψ i V').mp hV'
      obtain ⟨rfl, rfl⟩ := I.injective hiNs hiNs'
      exact hZF.1.eq_of_same_members V V' (fun k => (hV k).trans (hV' k).symm))
  obtain ⟨H, hH⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) L K
  have hHc : InternalCountable w H := (countable_native_iff hZF w H).mpr
    (ZF.countable_union_two_l I hZF hw ((countable_native_iff hZF w L).mp hLc)
      ((countable_native_iff hZF w K).mp hKc) hH)
  refine ⟨H, hHc, ?_, ?_⟩
  · intro X hX
    rcases (hH X).mp hX with hXL | hXK
    · exact hLw X hXL
    · obtain ⟨i, _, hiX⟩ := (hK X).mp hXK
      obtain ⟨_, _, _, hX⟩ := (hψ i X).mp hiX
      exact fun k hk => ((hX k).mp hk).1
  · intro N s hN hs
    obtain ⟨i, hi⟩ := I.total N s
    have hiJ : M.mem i J := (hJ i).mpr ⟨N, hN, s, (hP s).mpr hs, hi⟩
    constructor
    · obtain ⟨F, _, hiF⟩ := hG.2.2 i hiJ
      obtain ⟨N', s', hi', ht⟩ := (hφ i F).mp (he i F hiF)
      obtain ⟨rfl, rfl⟩ := I.injective hi hi'
      have hFC := (hC F).mpr ⟨i, hiJ, (hχ i F).mpr hiF⟩
      exact ⟨F, ht, fun X hXF => (hH X).mpr (Or.inl ((hL X).mpr ⟨F, hFC, hXF⟩))⟩
    · obtain ⟨V, hV⟩ := value_set_exists hZF w A E N s
      exact ⟨V, hV, (hH V).mpr (Or.inr ((hK V).mpr ⟨i, hiJ, (hψ i V).mpr ⟨N, s, hi, hV⟩⟩))⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
