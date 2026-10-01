import FIMADModels.DowTests

/-! Internal assembly of the countable tests at a dense-stem closure step.
Every image, union and tail-value test is an actual model set. The selected
tail/test witnesses are an internal function graph, not an external sequence. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def SelectedTests (w A E a s G : M.Domain) : Prop :=
  ∀ n, M.mem n w → ∃ q r F t,
    Entry_d M n q G ∧ KPair_d M q r F ∧ Tail w a n t ∧
      M.IsUnionOfTwo r s t ∧ TestsWitness w A E r F

def TailValue (w A E G N k : M.Domain) : Prop :=
  ∃ n q r F, M.mem n w ∧ AtLeast (M := M) N n ∧
    Entry_d M n q G ∧ KPair_d M q r F ∧ PossibleValue w A E r k

namespace Syntax
def selectedFamilyFormula {n} (G i F : Project.Term n) : Project.Formula 1 n :=
  .existsE (.existsE (.conj (entry_m i.weaken.weaken (.bound 1) G.weaken.weaken)
    (kpair_m (.bound 1) .newest F.weaken.weaken)))

def tailValueFormula {n} (w A E G N k : Project.Term n) : Project.Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound 3) w.weaken.weaken.weaken.weaken)
    (.conj (atLeastFormula N.weaken.weaken.weaken.weaken (.bound 3))
      (.conj (entry_m (.bound 3) (.bound 2) G.weaken.weaken.weaken.weaken)
        (.conj (kpair_m (.bound 2) (.bound 1) .newest)
          (possibleValueFormula w.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken
            E.weaken.weaken.weaken.weaken (.bound 1) k.weaken.weaken.weaken.weaken))))))))

derive_free_closed selectedFamilyFormula
derive_free_closed tailValueFormula

theorem selectedFamilyFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (G i F : Project.Term n) : Project.Formula.satisfies ρ (selectedFamilyFormula G i F) ↔
      ∃ q r, Entry_d M (i.eval ρ) q (G.eval ρ) ∧ KPair_d M q r (F.eval ρ) := by
  simp only [selectedFamilyFormula, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, entry_sat_l M hE, kpair_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem tailValueFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E G N k : Project.Term n) : Project.Formula.satisfies ρ (tailValueFormula w A E G N k) ↔
      TailValue (w.eval ρ) (A.eval ρ) (E.eval ρ) (G.eval ρ) (N.eval ρ) (k.eval ρ) := by
  simp only [tailValueFormula, TailValue, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff,
    atLeastFormula, AtLeast, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq hE, entry_sat_l M hE, kpair_sat_l M hE,
    possibleValueFormula_semantics hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl
end Syntax

theorem countable_native_iff (hZF : M.Models SetTheory.ZF) (w X : M.Domain) :
    InternalCountable w X ↔ M.CardinalLessOrEqual
      (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) X w := by
  constructor
  · rintro ⟨J, hJ⟩
    exact ⟨J, (ForcingFinite.injection_correct hZF J X w).mp hJ⟩
  · rintro ⟨J, hJ⟩
    exact ⟨J, (ForcingFinite.injection_correct hZF J X w).mpr hJ⟩

theorem assemble_selected_tests (hZFC : M.Models SetTheory.ZFC) {w A E a s G : M.Domain}
    (hw : M.IsOmega w) (ha : M.mem a A) (hs : FiniteSubset w s)
    (hSelected : SelectedTests w A E a s G)
    (hFun : ∀ n q q', Entry_d M n q G → Entry_d M n q' G → q = q') :
    ∃ H, TestsWitness w A E s H := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  have hw' := (Internal.omega_native_iff hZF.1 w).mpr hw
  obtain ⟨id, hid⟩ := ZF.exists_identityBijection hZF I w
  have hww : InternalCountable w w :=
    (countable_native_iff hZF w w).mpr ⟨id, hid.1⟩
  have select_unique {n q r F q' r' F'} (h : Entry_d M n q G) (h' : Entry_d M n q' G)
      (hp : KPair_d M q r F) (hp' : KPair_d M q' r' F') : r = r' ∧ F = F' :=
    I.injective hp ((hFun n q' q h' h) ▸ hp')
  let ρ : Env M 1 := ⟨fun _ => G, fun _ => G⟩
  let φ : BinarySchema 1 := { body := Syntax.selectedFamilyFormula (.bound 2) (.bound 1) .newest }
  have hφ n F : φ.denote ρ n F ↔ ∃ q r, Entry_d M n q G ∧ KPair_d M q r F :=
    Syntax.selectedFamilyFormula_semantics hZF.1 _ _ _ _
  obtain ⟨C, hC, hCc⟩ := countable_test_image hZFC φ ρ hww (fun n hn => by
    obtain ⟨q, r, F, _, hq, hp, _⟩ := hSelected n hn
    exact ⟨F, (hφ n F).mpr ⟨q, r, hq, hp⟩⟩) (by
      intro n _ F F' hF hF'
      obtain ⟨q, r, hq, hp⟩ := (hφ n F).mp hF
      obtain ⟨q', r', hq', hp'⟩ := (hφ n F').mp hF'
      exact (select_unique hq hq' hp hp').2)
  have hCspec {F} (hF : M.mem F C) :
      ∃ n r t, M.mem n w ∧ Tail w a n t ∧ M.IsUnionOfTwo r s t ∧ TestsWitness w A E r F := by
    obtain ⟨n, hn, hFn⟩ := (hC F).mp hF
    obtain ⟨q', r', hq', hp'⟩ := (hφ n F).mp hFn
    obtain ⟨q, r, F', t, hq, hp, ht, hr, hTest⟩ := hSelected n hn
    obtain ⟨_, eqF⟩ := select_unique hq hq' hp hp'
    subst F'
    exact ⟨n, r, t, hn, ht, hr, hTest⟩
  obtain ⟨L, hL⟩ := KP.exists_union (ZF.modelsKP hZF) C
  have hLc : InternalCountable w L := (countable_native_iff hZF w L).mpr
    (ZFC.countable_union_l I hZFC hw ((countable_native_iff hZF w C).mp hCc) hL
      (fun F hF => by
        obtain ⟨_, _, _, _, _, _, hTest⟩ := hCspec hF
        exact (countable_native_iff hZF w F).mp hTest.1))
  have hLX X (hX : M.mem X L) : Internal.Subset M.mem X w := by
    obtain ⟨F, hF, hXF⟩ := (hL X).mp hX
    obtain ⟨_, _, _, _, _, _, hTest⟩ := hCspec hF
    exact hTest.2.1 X hXF
  let δ : Env M 4 := (((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push E).push G
  let ψ : BinarySchema 4 := {
    body := .forallE (.iff (.mem .newest (.bound 1))
      (.conj (.mem .newest (.bound 6))
        (Syntax.tailValueFormula (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest))) }
  have hψ N V : ψ.denote δ N V ↔ ∀ k, M.mem k V ↔ M.mem k w ∧ TailValue w A E G N k := by
    simp only [BinarySchema.denote, ψ, Project.Formula.satisfies_forall_iff,
      Project.Formula.satisfies_iff_iff, Project.Formula.satisfies_mem_iff,
      Project.Formula.satisfies_conj_iff, Syntax.tailValueFormula_semantics hZF.1]
    rfl
  have tail_set N : ∃ V, ∀ k, M.mem k V ↔ M.mem k w ∧ TailValue w A E G N k := by
    let η := δ.push N
    let χ : UnarySchema 5 := {
      body := Syntax.tailValueFormula (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
    obtain ⟨V, hV⟩ := ZF.separation_exists_d hZF χ η w
    exact ⟨V, fun k => (hV k).trans (and_congr_right fun _ =>
      Syntax.tailValueFormula_semantics hZF.1 _ _ _ _ _ _ _)⟩
  obtain ⟨K, hK, hKc⟩ := countable_test_image hZFC ψ δ hww
    (fun N _ => (tail_set N).elim fun V hV => ⟨V, (hψ N V).mpr hV⟩)
    (fun N _ V V' hV hV' => hZF.1.eq_of_same_members V V'
      (fun k => ((hψ N V).mp hV k).trans ((hψ N V').mp hV' k).symm))
  obtain ⟨H, hH⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) L K
  have hHc := (countable_native_iff hZF w H).mpr
    (ZF.countable_union_two_l I hZF hw ((countable_native_iff hZF w L).mp hLc)
      ((countable_native_iff hZF w K).mp hKc) hH)
  refine ⟨H, hHc, ?_, ?_⟩
  · intro X hX
    rcases (hH X).mp hX with hXL | hXK
    · exact hLX X hXL
    · obtain ⟨N, _, hNV⟩ := (hK X).mp hXK
      exact fun k hk => (((hψ N X).mp hNV k).mp hk).1
  · intro B hB p hp hAvoid
    obtain ⟨S, hps, hCond⟩ := hp
    obtain ⟨N, hN, hAllow⟩ := hCond.2.2.2 s hs hCond.2.2.1 a ha
    have restem {n q r F} (hn : M.mem n w) (hNn : AtLeast (M := M) N n)
        (hqn : Entry_d M n q G) (hpair : KPair_d M q r F) :
        ∃ t, Tail w a n t ∧ M.IsUnionOfTwo r s t ∧
          TestsWitness w A E r F ∧ ∃ v, SameStem w A r v ∧ CodedExtends (M := M) v p := by
      obtain ⟨q', r', F', t', hq', hp', ht', hr', hTest⟩ := hSelected n hn
      obtain ⟨eqr, eqF⟩ := select_unique hq' hqn hp' hpair
      subst r'
      subst F'
      have hrS := hAllow t' (tail_mono hZF hw' hNn ht') r hr'
      have hRestem : Condition w A r S :=
        ⟨finiteSubset_union hZF hw hs ht'.1 hr', hCond.2.1, hrS, hCond.2.2.2⟩
      obtain ⟨v, hv⟩ := I.total r S
      exact ⟨t', ht', hr', hTest, v, ⟨S, hv, hRestem⟩,
        r, S, s, S, hv, hps, (fun k hk => (hr' k).mpr (Or.inl hk)), (fun _ h => h), hrS⟩
    have inherited {v} (hvp : CodedExtends (M := M) v p) : AvoidsValues w A E v B :=
      fun k hk r hr hrv => hAvoid k hk r hr (coded_extends_trans hZF hrv hvp)
    have hBF {n q r F} (hn : M.mem n w) (hqn : Entry_d M n q G) (hpair : KPair_d M q r F) :
        MeetsTests w B F := by
      have hFC := (hC F).mpr ⟨n, hn, (hφ n F).mpr ⟨q, r, hqn, hpair⟩⟩
      exact fun X hXF hi => hB X ((hH X).mpr (Or.inl ((hL X).mpr ⟨F, hFC, hXF⟩))) hi
    obtain ⟨V, hV⟩ := tail_set N
    have hVK : M.mem V K := (hK V).mpr ⟨N, hN, (hψ N V).mpr hV⟩
    have hVw : Internal.Subset M.mem V w := fun k hk => ((hV k).mp hk).1
    have hFinite : Internal.Finite M.mem w V := by
      classical
      apply Classical.byContradiction
      intro hInf
      obtain ⟨d, hd, hdi⟩ := hB V ((hH V).mpr (Or.inr hVK)) hInf
      have hdw : Internal.Subset M.mem d w := fun k hk => hVw k ((hd k).mp hk).1
      obtain ⟨zero, _, hz⟩ := hw.1.1
      obtain ⟨k, _, _, hkd⟩ := (Internal.infinite_iff_unbounded hZF hw' hdw).mp hdi zero hz
      obtain ⟨hkV, hkB⟩ := (hd k).mp hkd
      obtain ⟨_, n, q, r, F, hn, hNn, hqn, hpair, hPossible⟩ := (hV k).mp hkV
      obtain ⟨_, _, _, _, v, hv, hvp⟩ := restem hn hNn hqn hpair
      obtain ⟨z, hzc, hzv, hzk⟩ := hPossible v hv
      exact hAvoid k hkB z hzc (coded_extends_trans hZF hzv hvp) hzk
    have hTail : FiniteTailWitnesses w A E a s N V := by
      intro n hn hNn
      obtain ⟨q, r, F, _, hqn, hpair, _⟩ := hSelected n hn
      obtain ⟨t, ht, hr, hTest, v, hv, hvp⟩ := restem hn hNn hqn hpair
      obtain ⟨k, hkw, hPossible⟩ := hTest.2.2 B (hBF hn hqn hpair) v hv (inherited hvp)
      exact ⟨t, r, k, ht, hr, hPossible,
        (hV k).mpr ⟨hkw, n, q, r, F, hn, hNn, hqn, hpair, hPossible⟩⟩
    obtain ⟨k, hkV, hPossible⟩ := possible_of_finite_tail hZFC hw ha hs hN hFinite hTail
    exact ⟨k, hVw k hkV, hPossible⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
