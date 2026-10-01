import FIMADModels.DowSeparator

/-! Internally finite same-stem families have an actual common extension.
The induction is an instance of the original ZF finite-set induction schema;
external finiteness of the family is neither assumed nor used. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def SameStem (w A s p : M.Domain) : Prop :=
  ∃ S, KPair_d M p s S ∧ Condition w A s S

def SameStemFamily (w A s P : M.Domain) : Prop :=
  ∀ p, M.mem p P → SameStem w A s p

def Amalgam (w A s P q : M.Domain) : Prop :=
  SameStem w A s q ∧ ∀ p, M.mem p P → CodedExtends (M := M) q p

namespace Syntax
def sameStemFormula {n} (w A s p : Project.Term n) : Project.Formula 1 n :=
  .existsE (.conj (kpair_m p.weaken s.weaken .newest)
    (conditionFormula w.weaken A.weaken s.weaken .newest))

def sameStemFamilyFormula {n} (w A s P : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.mem .newest P.weaken)
    (sameStemFormula w.weaken A.weaken s.weaken .newest))

def amalgamFormula {n} (w A s P q : Project.Term n) : Project.Formula 1 n :=
  .conj (sameStemFormula w A s q)
    (.forallE (.imp (.mem .newest P.weaken) (codedExtendsFormula q.weaken .newest)))

derive_free_closed sameStemFormula
derive_free_closed sameStemFamilyFormula
derive_free_closed amalgamFormula

theorem sameStemFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A s p : Project.Term n) : Project.Formula.satisfies ρ (sameStemFormula w A s p) ↔
      SameStem (w.eval ρ) (A.eval ρ) (s.eval ρ) (p.eval ρ) := by
  simp only [sameStemFormula, SameStem, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, kpair_sat_l M hE,
    conditionFormula_semantics hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem sameStemFamilyFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A s P : Project.Term n) : Project.Formula.satisfies ρ (sameStemFamilyFormula w A s P) ↔
      SameStemFamily (w.eval ρ) (A.eval ρ) (s.eval ρ) (P.eval ρ) := by
  simp only [sameStemFamilyFormula, SameStemFamily, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    sameStemFormula_semantics hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem amalgamFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A s P q : Project.Term n) : Project.Formula.satisfies ρ (amalgamFormula w A s P q) ↔
      Amalgam (w.eval ρ) (A.eval ρ) (s.eval ρ) (P.eval ρ) (q.eval ρ) := by
  simp only [amalgamFormula, Amalgam, Project.Formula.satisfies_conj_iff,
    sameStemFormula_semantics hE, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    codedExtendsFormula_semantics hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
end Syntax

theorem finite_same_stem_amalgam (hZF : M.Models SetTheory.ZF) {w A s P : M.Domain}
    (hw : M.IsOmega w) (hs : FiniteSubset w s) (hP : Internal.Finite M.mem w P)
    (hFamily : SameStemFamily w A s P) : ∃ q, Amalgam w A s P q := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 3 := ((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push s
  let φ : UnarySchema 3 := {
    body := .imp (Syntax.sameStemFamilyFormula (.bound 3) (.bound 2) (.bound 1) .newest)
      (.existsE (Syntax.amalgamFormula (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)) }
  have hφ X : φ.denote ρ X ↔ SameStemFamily w A s X → ∃ q, Amalgam w A s X q := by
    simp only [UnarySchema.denote, φ, Project.Formula.satisfies_imp_iff,
      Syntax.sameStemFamilyFormula_semantics hZF.1, Project.Formula.satisfies_exists_iff,
      Syntax.amalgamFormula_semantics hZF.1]
    rfl
  apply (hφ P).mp (ZF.finite_ind_l I hZF hw φ ρ ?_ ?_ P
    ((ForcingFinite.finite_correct hZF w P).mp hP)) hFamily
  · intro E hE
    apply (hφ E).mpr
    intro _
    obtain ⟨empty, hEmpty⟩ := KP.exists_empty (ZF.modelsKP hZF)
    have hCond : Condition w A s empty := ⟨hs,
      (fun t ht => False.elim (hEmpty t ht)), hEmpty s,
      fun t _ _ a _ => hw.1.1.elim fun n hn =>
        ⟨n, hn.2, fun v _ r _ => hEmpty r⟩⟩
    obtain ⟨q, hq⟩ := I.total s empty
    exact ⟨q, ⟨empty, hq, hCond⟩, fun p hp => False.elim (hE p hp)⟩
  · intro X p Y _ ih hY
    apply (hφ Y).mpr
    intro hF
    have hFX : SameStemFamily w A s X := fun q hq => hF q ((hY q).mpr (Or.inl hq))
    obtain ⟨q, ⟨S, hq, hS⟩, hqX⟩ := (hφ X).mp ih hFX
    obtain ⟨T, hp, hT⟩ := hF p ((hY p).mpr (Or.inr rfl))
    obtain ⟨U, _, hCond, hUS, hUT⟩ := same_stem_merge hZF
      ((Internal.omega_native_iff hZF.1 w).mpr hw) hS hT
    obtain ⟨r, hr⟩ := I.total s U
    have hrq : CodedExtends (M := M) r q := ⟨s, U, s, S, hr, hq, hUS⟩
    have hrp : CodedExtends (M := M) r p := ⟨s, U, s, T, hr, hp, hUT⟩
    exact ⟨r, ⟨U, hr, hCond⟩, fun t ht => ((hY t).mp ht).elim
      (fun ht => coded_extends_trans hZF hrq (hqX t ht)) (fun eq => eq ▸ hrp)⟩

namespace Syntax
open Internal.Syntax
def amalgamBody : Project.Formula 1 4 :=
  .imp (Project.Formula.isOmega (.bound 3))
    (.imp (finiteSubsetFormula (.bound 3) (.bound 1))
      (.imp (FiniteFormula (.bound 3) .newest)
        (.imp (sameStemFamilyFormula (.bound 3) (.bound 2) (.bound 1) .newest)
          (.existsE (amalgamFormula (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)))))

theorem amalgamBody_closed : amalgamBody.FreeClosed := by
  simp -implicitDefEqProofs [amalgamBody, Definitional.Formula.FreeClosed]

def amalgamSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose amalgamBody) (ObjectTheory.universalClose_closed _ amalgamBody_closed)

theorem amalgamBody_valid (hZF : M.Models SetTheory.ZF) (ρ : Env M 4) :
    Project.Formula.satisfies ρ amalgamBody := by
  simp only [amalgamBody, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff, finiteSubsetFormula_semantics hZF.1,
    satisfies_FiniteFormula hZF.1, sameStemFamilyFormula_semantics hZF.1,
    Project.Formula.satisfies_exists_iff, amalgamFormula_semantics hZF.1]
  exact fun hw hs hP hF => finite_same_stem_amalgam hZF hw hs hP hF
end Syntax

theorem derives_finite_amalgam : Project.Derives SetTheory.ZF Syntax.amalgamSentence := by
  apply ObjectTheory.derives_of_native_zf_models
  intro M hZF
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.amalgamBody (Syntax.amalgamBody_valid hZF)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
