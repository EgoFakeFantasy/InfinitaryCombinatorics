import FIMADModels.ObjectTheory
import YesMetaZFC.SetTheory.SetConstruction

/-! Dow's forbidden-stem forcing, interpreted inside arbitrary ZF models.
The forbidden coordinate is an arbitrary internal set of finite subsets of
omega. It is not a finite family of almost disjoint sets. The same-stem merge
has an endpoint in the original membership-language derivation kernel. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def FiniteSubset (w s : M.Domain) : Prop :=
  Internal.Subset M.mem s w ∧ Internal.Finite M.mem w s

def Tail (w a n t : M.Domain) : Prop :=
  FiniteSubset w t ∧ ∀ k, M.mem k t → M.mem k a ∧ (k = n ∨ M.mem n k)

def Admissible (w A S : M.Domain) : Prop :=
  ∀ s, FiniteSubset w s → ¬ M.mem s S → ∀ a, M.mem a A →
    ∃ n, M.mem n w ∧ ∀ t, Tail w a n t →
      ∀ r, M.IsUnionOfTwo r s t → ¬ M.mem r S

def Condition (w A s S : M.Domain) : Prop :=
  FiniteSubset w s ∧ (∀ t, M.mem t S → FiniteSubset w t) ∧
    ¬ M.mem s S ∧ Admissible w A S

/-- The first pair of coordinates gives the stronger condition. -/
def Extends (s S q T : M.Domain) : Prop :=
  Internal.Subset M.mem q s ∧ Internal.Subset M.mem T S ∧ ¬ M.mem s T

theorem tail_mono (hZF : M.Models SetTheory.ZF) {w a n m t : M.Domain}
    (hw : Internal.Omega M.mem w) (hnm : n = m ∨ M.mem n m)
    (ht : Tail w a m t) : Tail w a n t := by
  refine ⟨ht.1, fun k hk => ⟨(ht.2 k hk).1, ?_⟩⟩
  rcases hnm with rfl | hnm
  · exact (ht.2 k hk).2
  · rcases (ht.2 k hk).2 with rfl | hmk
    · exact Or.inr hnm
    · have hkω := ht.1.1 k hk
      have hkOrd := ((Internal.omega_native_iff hZF.1 w).mp hw).members_areOrdinals hZF k hkω
      exact Or.inr (hkOrd.transitive m hmk n hnm)

/-- The bound is an internal natural maximum, even in nonstandard models. -/
theorem natural_common_bound (hZF : M.Models SetTheory.ZF) {w n m : M.Domain}
    (hw : Internal.Omega M.mem w) (hn : M.mem n w) (hm : M.mem m w) :
    ∃ b, M.mem b w ∧ (n = b ∨ M.mem n b) ∧ (m = b ∨ M.mem m b) := by
  have ho := ((Internal.omega_native_iff hZF.1 w).mp hw).membershipWellOrder hZF
  rcases ho.linear.compare n hn m hm with heq | hnm | hmn
  · exact ⟨m, hm, Or.inl (hZF.1.eq_of_same_members n m heq), Or.inl rfl⟩
  · exact ⟨m, hm, Or.inr hnm, Or.inl rfl⟩
  · exact ⟨n, hn, Or.inl rfl, Or.inr hmn⟩

theorem admissible_union (hZF : M.Models SetTheory.ZF) {w A S T U : M.Domain}
    (hw : Internal.Omega M.mem w) (hS : Admissible w A S) (hT : Admissible w A T)
    (hU : M.IsUnionOfTwo U S T) : Admissible w A U := by
  intro s hs hsU a ha
  obtain ⟨n, hn, hnTail⟩ := hS s hs (fun h => hsU ((hU s).mpr (Or.inl h))) a ha
  obtain ⟨m, hm, hmTail⟩ := hT s hs (fun h => hsU ((hU s).mpr (Or.inr h))) a ha
  obtain ⟨b, hb, hnb, hmb⟩ := natural_common_bound hZF hw hn hm
  refine ⟨b, hb, fun t ht r hr hbad => ?_⟩
  rcases (hU r).mp hbad with hbad | hbad
  · exact hnTail t (tail_mono hZF hw hnb ht) r hr hbad
  · exact hmTail t (tail_mono hZF hw hmb ht) r hr hbad

theorem same_stem_merge (hZF : M.Models SetTheory.ZF) {w A s S T : M.Domain}
    (hw : Internal.Omega M.mem w) (hS : Condition w A s S) (hT : Condition w A s T) :
    ∃ U, M.IsUnionOfTwo U S T ∧ Condition w A s U ∧
      Extends s U s S ∧ Extends s U s T := by
  obtain ⟨U, hU⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) S T
  have hSubS : Internal.Subset M.mem S U := fun t ht => (hU t).mpr (Or.inl ht)
  have hSubT : Internal.Subset M.mem T U := fun t ht => (hU t).mpr (Or.inr ht)
  refine ⟨U, hU, ⟨hS.1, ?_, ?_, admissible_union hZF hw hS.2.2.2 hT.2.2.2 hU⟩,
    ⟨fun _ h => h, hSubS, hS.2.2.1⟩, ⟨fun _ h => h, hSubT, hT.2.2.1⟩⟩
  · intro t ht
    exact ((hU t).mp ht).elim (hS.2.1 t) (hT.2.1 t)
  · intro hs
    exact ((hU s).mp hs).elim hS.2.2.1 hT.2.2.1

namespace Syntax
open Internal.Syntax

def finiteSubsetFormula {n} (w s : Project.Term n) : Project.Formula 1 n :=
  .conj (SubsetFormula s w) (FiniteFormula w s)

def tailFormula {n} (w a b t : Project.Term n) : Project.Formula 1 n :=
  .conj (finiteSubsetFormula w t)
    (.forallE (.imp (.mem .newest t.weaken)
      (.conj (.mem .newest a.weaken)
        (.disj (Project.Formula.extensionalEq .newest b.weaken) (.mem b.weaken .newest)))))

def admissibleFormula {n} (w A S : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (finiteSubsetFormula w.weaken .newest)
    (.imp (.neg (.mem .newest S.weaken))
      (.forallE (.imp (.mem .newest A.weaken.weaken)
        (.existsE (.conj (.mem .newest w.weaken.weaken.weaken)
          (.forallE (.imp
            (tailFormula w.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
            (.forallE (.imp (Project.Formula.isUnionOfTwo .newest (.bound 4) (.bound 1))
              (.neg (.mem .newest S.weaken.weaken.weaken.weaken.weaken))))))))))))

def conditionFormula {n} (w A s S : Project.Term n) : Project.Formula 1 n :=
  .conj (finiteSubsetFormula w s)
    (.conj (.forallE (.imp (.mem .newest S.weaken) (finiteSubsetFormula w.weaken .newest)))
      (.conj (.neg (.mem s S)) (admissibleFormula w A S)))

def extendsFormula {n} (s S q T : Project.Term n) : Project.Formula 1 n :=
  .conj (SubsetFormula q s) (.conj (SubsetFormula T S) (.neg (.mem s T)))

@[simp] theorem finiteSubsetFormula_closed {n} (w s : Project.Term n)
    (hw : w.freeSupport = []) (hs : s.freeSupport = []) :
    (finiteSubsetFormula w s).FreeClosed := by
  simp only [finiteSubsetFormula, Definitional.Formula.FreeClosed]
  exact ⟨closed_SubsetFormula _ _ hs hw, closed_FiniteFormula _ _ hw hs⟩

@[simp] theorem unionFormula_closed {n} (U S T : Project.Term n)
    (hU : U.freeSupport = []) (hS : S.freeSupport = []) (hT : T.freeSupport = []) :
    (Project.Formula.isUnionOfTwo U S T).FreeClosed := by
  simp [Project.Formula.isUnionOfTwo, Definitional.Formula.FreeClosed, *]

derive_free_closed tailFormula
derive_free_closed admissibleFormula
derive_free_closed conditionFormula
derive_free_closed extendsFormula

theorem finiteSubsetFormula_semantics (hExt : Extensional M) {n} (ρ : Env M n)
    (w s : Project.Term n) : Project.Formula.satisfies ρ (finiteSubsetFormula w s) ↔
      FiniteSubset (w.eval ρ) (s.eval ρ) := by
  simp only [finiteSubsetFormula, FiniteSubset, Project.Formula.satisfies_conj_iff,
    satisfies_SubsetFormula hExt, satisfies_FiniteFormula hExt]

theorem tailFormula_semantics (hExt : Extensional M) {n} (ρ : Env M n)
    (w a b t : Project.Term n) : Project.Formula.satisfies ρ (tailFormula w a b t) ↔
      Tail (w.eval ρ) (a.eval ρ) (b.eval ρ) (t.eval ρ) := by
  simp only [tailFormula, Tail, Project.Formula.satisfies_conj_iff,
    finiteSubsetFormula_semantics hExt, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_extensionalEq_iff_eq hExt,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem admissibleFormula_semantics (hExt : Extensional M) {n} (ρ : Env M n)
    (w A S : Project.Term n) : Project.Formula.satisfies ρ (admissibleFormula w A S) ↔
      Admissible (w.eval ρ) (A.eval ρ) (S.eval ρ) := by
  simp only [admissibleFormula, Admissible, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_isUnionOfTwo_iff,
    finiteSubsetFormula_semantics hExt, tailFormula_semantics hExt,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem conditionFormula_semantics (hExt : Extensional M) {n} (ρ : Env M n)
    (w A s S : Project.Term n) : Project.Formula.satisfies ρ (conditionFormula w A s S) ↔
      Condition (w.eval ρ) (A.eval ρ) (s.eval ρ) (S.eval ρ) := by
  simp only [conditionFormula, Condition, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_neg_iff, Project.Formula.satisfies_mem_iff,
    finiteSubsetFormula_semantics hExt, admissibleFormula_semantics hExt,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem extendsFormula_semantics (hExt : Extensional M) {n} (ρ : Env M n)
    (s S q T : Project.Term n) : Project.Formula.satisfies ρ (extendsFormula s S q T) ↔
      Extends (s.eval ρ) (S.eval ρ) (q.eval ρ) (T.eval ρ) := by
  simp only [extendsFormula, Extends, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff, Project.Formula.satisfies_mem_iff,
    satisfies_SubsetFormula hExt]

/-- Parameters in order w, A, s, S, T; the existential witness is S union T. -/
def mergeBody : Project.Formula 1 5 :=
  .imp (OmegaFormula (.bound 4))
    (.imp (conditionFormula (.bound 4) (.bound 3) (.bound 2) (.bound 1))
      (.imp (conditionFormula (.bound 4) (.bound 3) (.bound 2) (.bound 0))
        (.existsE (.conj (Project.Formula.isUnionOfTwo .newest (.bound 2) (.bound 1))
          (.conj (conditionFormula (.bound 5) (.bound 4) (.bound 3) .newest)
            (.conj (extendsFormula (.bound 3) .newest (.bound 3) (.bound 2))
              (extendsFormula (.bound 3) .newest (.bound 3) (.bound 1))))))))

theorem mergeBody_closed : mergeBody.FreeClosed := by
  simp -implicitDefEqProofs [mergeBody, Definitional.Formula.FreeClosed,
    OmegaFormula, Project.Formula.isUnionOfTwo, *]

def mergeSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose mergeBody)
  (ObjectTheory.universalClose_closed _ mergeBody_closed)

theorem mergeBody_valid (hZF : M.Models SetTheory.ZF) (ρ : Env M 5) :
    Project.Formula.satisfies ρ mergeBody := by
  simp only [mergeBody, Project.Formula.satisfies_imp_iff,
    satisfies_OmegaFormula hZF.1, conditionFormula_semantics hZF.1,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isUnionOfTwo_iff, extendsFormula_semantics hZF.1]
  exact fun hw hS hT => same_stem_merge hZF hw hS hT

end Syntax

/-- An original ZF derivation, with no assumption that model omega is standard. -/
theorem derives_same_stem_merge : Project.Derives SetTheory.ZF Syntax.mergeSentence := by
  apply ObjectTheory.derives_of_native_zf_models
  intro M hZF
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.mergeBody (Syntax.mergeBody_valid hZF)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
