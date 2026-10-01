import FIMADModels.DowDense

/-! Actual internal blockers and the dense finite-intersection requirements.
The blocker is separated from the model's power set of omega. Its admissibility
uses internal finite/bounded equivalence, not an external finite-set argument. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def Blocker (w s b t : M.Domain) : Prop :=
  FiniteSubset w t ∧ ∃ k, M.mem k t ∧ M.mem k b ∧ ¬ M.mem k s

def Orthogonal (w A b : M.Domain) : Prop :=
  Internal.Subset M.mem b w ∧ ∀ a, M.mem a A →
    ∃ d, Internal.Inter M.mem d a b ∧ Internal.Finite M.mem w d

def StemAvoid (w b s S : M.Domain) : Prop :=
  ∀ t, Blocker w s b t → M.mem t S

def Avoid (w b p : M.Domain) : Prop :=
  ∃ s S, KPair_d M p s S ∧ StemAvoid w b s S

namespace Syntax
open Internal.Syntax

def blockerFormula {n} (w s b t : Project.Term n) : Project.Formula 1 n :=
  .conj (finiteSubsetFormula w t)
    (.existsE (.conj (.mem .newest t.weaken)
      (.conj (.mem .newest b.weaken) (.neg (.mem .newest s.weaken)))))

def orthogonalFormula {n} (w A b : Project.Term n) : Project.Formula 1 n :=
  .conj (SubsetFormula b w)
    (.forallE (.imp (.mem .newest A.weaken)
      (.existsE (.conj (InterFormula .newest (.bound 1) b.weaken.weaken)
        (FiniteFormula w.weaken.weaken .newest)))))

def stemAvoidFormula {n} (w b s S : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (blockerFormula w.weaken s.weaken b.weaken .newest) (.mem .newest S.weaken))

derive_free_closed blockerFormula
derive_free_closed orthogonalFormula
derive_free_closed stemAvoidFormula

theorem blockerFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w s b t : Project.Term n) : Project.Formula.satisfies ρ (blockerFormula w s b t) ↔
      Blocker (w.eval ρ) (s.eval ρ) (b.eval ρ) (t.eval ρ) := by
  simp only [blockerFormula, Blocker, Project.Formula.satisfies_conj_iff,
    finiteSubsetFormula_semantics hE, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_neg_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem orthogonalFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A b : Project.Term n) : Project.Formula.satisfies ρ (orthogonalFormula w A b) ↔
      Orthogonal (w.eval ρ) (A.eval ρ) (b.eval ρ) := by
  simp only [orthogonalFormula, Orthogonal, Project.Formula.satisfies_conj_iff,
    satisfies_SubsetFormula hE, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_exists_iff, satisfies_InterFormula hE, satisfies_FiniteFormula hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem stemAvoidFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w b s S : Project.Term n) : Project.Formula.satisfies ρ (stemAvoidFormula w b s S) ↔
      StemAvoid (w.eval ρ) (b.eval ρ) (s.eval ρ) (S.eval ρ) := by
  simp only [stemAvoidFormula, StemAvoid, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, blockerFormula_semantics hE,
    Project.Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
end Syntax

theorem blocker_exists (hZF : M.Models SetTheory.ZF) (w s b : M.Domain) :
    ∃ Q, ∀ t, M.mem t Q ↔ Blocker w s b t := by
  obtain ⟨W, hW⟩ := ZF.exists_powerSet hZF w
  let ρ : Env M 3 := ((⟨fun _ => w, fun _ => w⟩ : Env M 1).push s).push b
  let φ : UnarySchema 3 := {
    body := Syntax.blockerFormula (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨Q, hQ⟩ := ZF.separation_exists_d hZF φ ρ W
  have hφ t : φ.denote ρ t ↔ Blocker w s b t :=
    Syntax.blockerFormula_semantics hZF.1 _ _ _ _ _
  refine ⟨Q, fun t => (hQ t).trans ?_⟩
  change M.mem t W ∧ φ.denote ρ t ↔ _
  rw [hφ t]
  exact ⟨And.right, fun h => ⟨(hW t).mpr h.1.1, h⟩⟩

theorem blocker_admissible (hZF : M.Models SetTheory.ZF) {w A s b Q : M.Domain}
    (hw : M.IsOmega w) (hOrth : Orthogonal w A b)
    (hQ : ∀ t, M.mem t Q ↔ Blocker w s b t) : Admissible w A Q := by
  intro t ht htQ a ha
  obtain ⟨d, hd, hdf⟩ := hOrth.2 a ha
  have hdw : Internal.Subset M.mem d w := fun k hk => hOrth.1 k ((hd k).mp hk).2
  obtain ⟨n, hn, hdn⟩ := (Internal.finite_iff_bounded hZF
    ((Internal.omega_native_iff hZF.1 w).mpr hw) hdw).mp hdf
  refine ⟨n, hn, fun v hv r hr hbad => ?_⟩
  obtain ⟨_, k, hkr, hkb, hks⟩ := (hQ r).mp hbad
  rcases (hr k).mp hkr with hkt | hkv
  · exact htQ ((hQ t).mpr ⟨ht, k, hkt, hkb, hks⟩)
  · have hka := (hv.2 k hkv).1
    have hkn := hdn k ((hd k).mpr ⟨hka, hkb⟩)
    rcases (hv.2 k hkv).2 with rfl | hnk
    · exact KP.mem_irrefl_d (ZF.modelsKP hZF) k hkn
    · exact KP.mem_irrefl_d (ZF.modelsKP hZF) n
        ((hw.members_areOrdinals hZF n hn).transitive k hkn n hnk)

theorem avoid_extension (hZF : M.Models SetTheory.ZF) {w A b s S : M.Domain}
    (hw : M.IsOmega w) (hOrth : Orthogonal w A b) (hp : Condition w A s S) :
    ∃ T, Condition w A s T ∧ Extends s T s S ∧ StemAvoid w b s T := by
  obtain ⟨Q, hQ⟩ := blocker_exists hZF w s b
  have hsQ : ¬ M.mem s Q := by
    intro h
    obtain ⟨_, k, hks, _, hkns⟩ := (hQ s).mp h
    exact hkns hks
  obtain ⟨T, hT⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) S Q
  refine ⟨T, ⟨hp.1, ?_, ?_, admissible_union hZF
    ((Internal.omega_native_iff hZF.1 w).mpr hw) hp.2.2.2
    (blocker_admissible hZF hw hOrth hQ) hT⟩,
    ⟨fun _ h => h, (fun x hx => (hT x).mpr (Or.inl hx)), hp.2.2.1⟩, ?_⟩
  · intro t ht
    exact ((hT t).mp ht).elim (hp.2.1 t) (fun h => ((hQ t).mp h).1)
  · intro h
    exact ((hT s).mp h).elim hp.2.2.1 hsQ
  · intro t ht
    exact (hT t).mpr (Or.inr ((hQ t).mpr ht))

theorem avoid_dense (hZF : M.Models SetTheory.ZF) {w A B R b : M.Domain} (hw : M.IsOmega w)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q)
    (hOrth : Orthogonal w A b) :
    ∀ p, M.mem p B → ∃ q, M.mem q B ∧ Entry_d M q p R ∧ Avoid w b q := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  intro p hp
  obtain ⟨s, S, hps, hCond⟩ := (hB p).mp hp
  obtain ⟨T, hT, hTS, hAvoid⟩ := avoid_extension hZF hw hOrth hCond
  obtain ⟨q, hq⟩ := I.total s T
  have hqB := (hB q).mpr ⟨s, T, hq, hT⟩
  exact ⟨q, hqB, (hR q p).mpr ⟨hqB, hp, s, T, s, S, hq, hps, hTS⟩,
    s, T, hq, hAvoid⟩

namespace Syntax
def avoidBody : Project.Formula 1 5 :=
  .imp (Project.Formula.isOmega (.bound 4))
    (.imp (orthogonalFormula (.bound 4) (.bound 3) (.bound 2))
      (.imp (conditionFormula (.bound 4) (.bound 3) (.bound 1) .newest)
        (.existsE (.conj (conditionFormula (.bound 5) (.bound 4) (.bound 2) .newest)
          (.conj (extendsFormula (.bound 2) .newest (.bound 2) (.bound 1))
            (stemAvoidFormula (.bound 5) (.bound 3) (.bound 2) .newest))))))

theorem avoidBody_closed : avoidBody.FreeClosed := by
  simp -implicitDefEqProofs [avoidBody, Definitional.Formula.FreeClosed]

def avoidSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose avoidBody) (ObjectTheory.universalClose_closed _ avoidBody_closed)

theorem avoidBody_valid (hZF : M.Models SetTheory.ZF) (ρ : Env M 5) :
    Project.Formula.satisfies ρ avoidBody := by
  simp only [avoidBody, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_isOmega_iff,
    orthogonalFormula_semantics hZF.1, conditionFormula_semantics hZF.1,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    extendsFormula_semantics hZF.1, stemAvoidFormula_semantics hZF.1]
  exact fun hw hOrth hp => avoid_extension hZF hw hOrth hp
end Syntax

theorem derives_avoid_extension : Project.Derives SetTheory.ZF Syntax.avoidSentence := by
  apply ObjectTheory.derives_of_native_zf_models
  intro M hZF
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.avoidBody (Syntax.avoidBody_valid hZF)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
