import FIMADModels.DowInternal
import FIMADModels.ForcingFinite
import YesMetaZFC.SetTheory.Card.FiniteSequenceCountable
import YesMetaZFC.SetTheory.DependentChoice

/-! The model's own finite subsets of omega form a countable internal set.
Enumeration uses first-order finite insertion induction, including nonstandard
finite sets. All sequence graphs, ranges and injections are internal sets. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.FiniteStems
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem finite_enumeration (hZF : M.Models SetTheory.ZF) {w X : M.Domain}
    (hw : M.IsOmega w) (hX : DowInternal.FiniteSubset w X) :
    ∃ n F, M.mem n w ∧ M.IsSetFunctionFromTo
      (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) F n w ∧
      M.IsRangeOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) X F := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 1 := ⟨fun _ => w, fun _ => w⟩
  let φ : UnarySchema 1 := {
    body := .imp (Project.Formula.subset .newest (.bound 1))
      (.existsE (.existsE (.conj (.mem (.bound 1) (.bound 3))
        (.conj (Project.Formula.isFunctionFromTo kpair_convention_l .newest (.bound 1) (.bound 3))
          (Project.Formula.isRange kpair_convention_l (.bound 2) .newest))))) }
  have hφ Y : φ.denote ρ Y ↔ M.MemberSubset Y w → ∃ n F,
      M.mem n w ∧ M.IsSetFunctionFromTo I F n w ∧ M.IsRangeOf I Y F := by
    simp only [UnarySchema.denote, φ, Project.Formula.satisfies_imp_iff,
      Project.Formula.satisfies_subset_iff, Project.Formula.satisfies_exists_iff,
      Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff,
      Project.Formula.satisfies_isFunctionFromTo_iff I hZF.1,
      Project.Formula.satisfies_isRange_iff I]
    rfl
  apply (hφ X).mp (ZF.finite_ind_l I hZF hw φ ρ ?_ ?_ X
    ((ForcingFinite.finite_correct hZF w X).mp hX.2)) hX.1
  · intro E hE
    apply (hφ E).mpr
    intro _
    obtain ⟨e, he, hew⟩ := hw.1.1
    have seq := Structure.IsSequenceOfLength.empty I hE
    have eq : E = e := hZF.1.eq_of_same_members E e
      (fun x => iff_of_false (hE x) (he x))
    subst e
    refine ⟨E, E, hew, ⟨seq.2.1, seq.2.2, fun x hx => (hE x hx).elim⟩, ?_⟩
    intro y
    exact ⟨fun hy => (hE y hy).elim, fun ⟨x, hxy⟩ =>
      (hE x ((seq.2.2 x).mpr ⟨y, hxy⟩)).elim⟩
  · intro Y a Z _ ih hZ
    apply (hφ Z).mpr
    intro hZw
    have hYw : M.MemberSubset Y w := fun x hx => hZw x ((hZ x).mpr (Or.inl hx))
    have haw := hZw a ((hZ a).mpr (Or.inr rfl))
    obtain ⟨n, F, hn, hf, hr⟩ := (hφ Y).mp ih hYw
    obtain ⟨s, hs, hsw⟩ := hw.1.2 n hn
    obtain ⟨G, hg, hGF⟩ := Structure.IsSequenceOfLength.exists_append (value := a)
      (ZF.modelsKP hZF) I ⟨hw.members_areOrdinals hZF n hn, hf.1, hf.2.1⟩
      (hw.members_areOrdinals hZF s hsw) hs
    refine ⟨s, G, hsw, ⟨hg.2.1, hg.2.2, fun i hi => ?_⟩, ?_⟩
    · obtain ⟨x, hx⟩ := (hg.2.2 i).mp hi
      refine ⟨x, ?_, hx⟩
      exact ((hGF i x).mp hx).elim hf.output_mem_of_pairMember
        (fun h => h.2 ▸ haw)
    · intro x
      rw [hZ x]
      constructor
      · intro hx
        rcases hx with hx | rfl
        · obtain ⟨i, hi⟩ := (hr x).mp hx
          exact ⟨i, (hGF i x).mpr (Or.inl hi)⟩
        · exact ⟨n, (hGF n x).mpr (Or.inr ⟨rfl, rfl⟩)⟩
      · rintro ⟨i, hi⟩
        exact ((hGF i x).mp hi).elim (fun h => Or.inl ((hr x).mpr ⟨i, h⟩))
          (fun h => Or.inr h.2)

theorem finite_stem_space (hZFC : M.Models SetTheory.ZFC) {w : M.Domain}
    (hw : M.IsOmega w) : ∃ P,
      (∀ X, M.mem X P ↔ DowInternal.FiniteSubset w X) ∧
      M.CardinalLessOrEqual
        (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) P w := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨W, hW⟩ := ZF.exists_powerSet hZF w
  let ρ : Env M 1 := ⟨fun _ => w, fun _ => w⟩
  let φ : UnarySchema 1 := {
    body := DowInternal.Syntax.finiteSubsetFormula (.bound 1) .newest
    freeClosed := DowInternal.Syntax.finiteSubsetFormula_closed _ _ rfl rfl }
  obtain ⟨P, hP⟩ := ZF.separation_exists_d hZF φ ρ W
  have hP X : M.mem X P ↔ DowInternal.FiniteSubset w X := by
    rw [hP X]
    have hSat := DowInternal.Syntax.finiteSubsetFormula_semantics hZF.1 (ρ.push X) (.bound 1) .newest
    change M.mem X W ∧ Project.Formula.satisfies (ρ.push X) φ.body ↔ _
    rw [show Project.Formula.satisfies (ρ.push X) φ.body ↔ DowInternal.FiniteSubset w X from hSat]
    exact ⟨And.right, fun h => ⟨(hW X).mpr h.1, h⟩⟩
  obtain ⟨Id, hId⟩ := ZF.exists_identityBijection hZF I w
  obtain ⟨S, hS, hsCount⟩ := ZF.fseq_countable_space_l I hZF hw ⟨Id, hId.1⟩
  let ψ : BinarySchema 0 := { body := Project.Formula.isRange kpair_convention_l .newest (.bound 1) }
  let η : Env M 0 := ⟨Fin.elim0, fun _ => w⟩
  have hψ F X : ψ.denote η F X ↔ M.IsRangeOf I X F :=
    Project.Formula.satisfies_isRange_iff I _ _ _
  obtain ⟨G, hg, hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ η
    (source := S) (target := P) (by
      intro F hF
      obtain ⟨n, _, hf⟩ := (hS F).mp hF
      obtain ⟨X, hX⟩ := ZF.exists_range_of_setFunction hZF I hf.1 hf.2.1
      exact ⟨X, (hψ F X).mpr hX⟩) (by
      intro F _ X Y hx hy
      exact hZF.1.eq_of_same_members X Y
        (fun z => ((hψ F X).mp hx z).trans ((hψ F Y).mp hy z).symm)) (by
      intro F X hF hX
      obtain ⟨n, hn, hf⟩ := (hS F).mp hF
      have hr := (hψ F X).mp hX
      have hXw : M.MemberSubset X w := fun x hx =>
        ((hr x).mp hx).elim fun i hi => hf.output_mem_of_pairMember hi
      have hfX : M.IsSetFunctionFromTo I F n X :=
        ⟨hf.1, hf.2.1, fun i hi => (hf.2.2 i hi).elim fun x hx =>
          ⟨x, (hr x).mpr ⟨i, hx.2⟩, hx.2⟩⟩
      have hSurj : M.IsSetSurjectiveOnto I F n X := fun x hx =>
        ((hr x).mp hx).elim fun i hi => ⟨i, hf.input_mem_of_pairMember hi, hi⟩
      exact (hP X).mpr ⟨hXw, (ForcingFinite.finite_correct hZF w X).mpr
        ⟨n, hn, ZFC.surjection_bound_l I hZFC hfX hSurj⟩⟩)
  have hSurj : M.IsSetSurjectiveOnto I G S P := by
    intro X hX
    obtain ⟨n, F, hn, hf, hr⟩ := finite_enumeration hZF hw ((hP X).mp hX)
    have hFS := (hS F).mpr ⟨n, hn, hf⟩
    exact ⟨F, hFS, (hGraph F X).mpr ⟨hFS, (hψ F X).mpr hr⟩⟩
  obtain ⟨J, hJ⟩ := ZFC.surjection_bound_l I hZFC hg hSurj
  obtain ⟨K, hK⟩ := hsCount
  exact ⟨P, hP, ZF.exists_compositionInjection hZF I hJ hK⟩

def countableBody : Project.Formula 1 1 :=
  .imp (Project.Formula.isOmega .newest)
    (.existsE (.conj
      (.forallE (.iff (.mem .newest (.bound 1))
        (DowInternal.Syntax.finiteSubsetFormula (.bound 2) .newest)))
      (Project.Formula.cardinalLessOrEqual kpair_convention_l .newest (.bound 1))))

theorem countableBody_closed : countableBody.FreeClosed := by
  simp -implicitDefEqProofs [countableBody, Definitional.Formula.FreeClosed]

def countableSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose countableBody)
  (ObjectTheory.universalClose_closed _ countableBody_closed)

theorem countableBody_valid (hZFC : M.Models SetTheory.ZFC) (ρ : Env M 1) :
    Project.Formula.satisfies ρ countableBody := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  simp only [countableBody, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff, Project.Formula.satisfies_mem_iff,
    DowInternal.Syntax.finiteSubsetFormula_semantics hZF.1,
    Project.Formula.satisfies_cardinalLessOrEqual_iff I hZF.1]
  exact fun hw => finite_stem_space hZFC hw

theorem derives_countable_finite_stems : Project.Derives SetTheory.ZFC countableSentence := by
  apply ObjectTheory.derives_of_native_zfc_models
  intro M hZFC
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid countableBody (countableBody_valid hZFC)

end InfinitaryCombinatorics.Formalizations.FIMAD.FiniteStems
