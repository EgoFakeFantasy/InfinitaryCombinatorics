import FIMADModels.ObjectTheory
import YesMetaZFC.Model.Forcing.Iteration.FiniteSupport.RecursionCCC

/-! Pure-membership object proof of finite-support CCC preservation. The
successor premise records actual names, forcing assertions and two-step rows.
This is the common iteration step needed by the BMZ construction; it does not
assert that a BMZ bookkeeping rule has already been constructed. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.Iteration
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal

/-- Insert actual condition and name terms into the internal forcing translation. -/
def forcingFormula {k n} (φ : Project.Formula 1 k) (es : Fin k → Project.Term n)
    (B R z p : Project.Term n) : Project.Formula 1 n :=
  (force_code_m φ).bind (Fin.cases p (Fin.cases z (Fin.cases R (Fin.cases B es))))

@[simp] theorem forcingFormula_closed {k n} (φ : Project.Formula 1 k)
    (es : Fin k → Project.Term n) (B R z p : Project.Term n) (hφ : φ.FreeClosed)
    (hes : ∀ i, (es i).freeSupport = []) (hB : B.freeSupport = [])
    (hR : R.freeSupport = []) (hz : z.freeSupport = []) (hp : p.freeSupport = []) :
    (forcingFormula φ es B R z p).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hp (Fin.cases hz (Fin.cases hR (Fin.cases hB hes)))) _).mpr
    (force_code_closed_l φ hφ)

universe u
variable {M : SetTheory.Structure.{u}}

theorem forcingFormula_semantics {k n} (φ : Project.Formula 1 k)
    (es : Fin k → Project.Term n) (B R z p : Project.Term n) (ρ : Env M n) :
    Project.Formula.satisfies ρ (forcingFormula φ es B R z p) ↔
      Forces_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) φ
        ⟨fun i => (es i).eval ρ, ρ.free⟩ (p.eval ρ) := by
  rw [forcingFormula, Project.Formula.satisfies_bind]
  have h : Definitional.Env.substitute ρ
      (Fin.cases p (Fin.cases z (Fin.cases R (Fin.cases B es)))) =
      fenv_l (⟨fun i => (es i).eval ρ, ρ.free⟩ : Env M k)
        (B.eval ρ) (R.eval ρ) (z.eval ρ) (p.eval ρ) := by
    rw [Env.mk.injEq]
    exact ⟨funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))), rfl⟩
  rw [h]
  rfl

def nextFormula {n} (α B R e D V : Project.Term n) : Project.Formula 1 n :=
  .existsE (.existsE (.existsE
    (.conj (name_m B.weaken.weaken.weaken (.bound 1))
      (.conj (forcingFormula (preord_m (.bound 0) (.bound 1))
        (Fin.cases (.bound 2) (Fin.cases (.bound 1) Fin.elim0))
        B.weaken.weaken.weaken R.weaken.weaken.weaken B.weaken.weaken.weaken e.weaken.weaken.weaken)
        (.conj (forcingFormula (ccc_exists_m (.bound 0) (.bound 1))
          (Fin.cases (.bound 2) (Fin.cases (.bound 1) Fin.elim0))
          B.weaken.weaken.weaken R.weaken.weaken.weaken B.weaken.weaken.weaken e.weaken.weaken.weaken)
          (row_next_m α.weaken.weaken.weaken B.weaken.weaken.weaken R.weaken.weaken.weaken
            e.weaken.weaken.weaken (.bound 2) (.bound 1) .newest D.weaken.weaken.weaken V.weaken.weaken.weaken))))))

theorem nextFormula_closed {n} (α B R e D V : Project.Term n)
    (hα : α.freeSupport = []) (hB : B.freeSupport = []) (hR : R.freeSupport = [])
    (he : e.freeSupport = []) (hD : D.freeSupport = []) (hV : V.freeSupport = []) :
    (nextFormula α B R e D V).FreeClosed := by
  simp only [nextFormula, Definitional.Formula.FreeClosed]
  refine ⟨name_m_freeClosed _ _ (by simpa using hB) rfl, ?_, ?_,
    row_next_m_freeClosed _ _ _ _ _ _ _ _ _ (by simpa using hα) (by simpa using hB)
      (by simpa using hR) (by simpa using he) rfl rfl rfl (by simpa using hD) (by simpa using hV)⟩
  · exact forcingFormula_closed _ _ _ _ _ _ (preord_m_freeClosed _ _ rfl rfl)
      (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) (by simpa using hB) (by simpa using hR)
      (by simpa using hB) (by simpa using he)
  · exact forcingFormula_closed _ _ _ _ _ _ (ccc_exists_m_freeClosed _ _ rfl rfl)
      (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) (by simpa using hB) (by simpa using hR)
      (by simpa using hB) (by simpa using he)

theorem nextFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (α B R e D V : Project.Term n) :
    Project.Formula.satisfies ρ (nextFormula α B R e D V) ↔
      Row_ccc_next_d (α.eval ρ) (B.eval ρ) (R.eval ρ) (e.eval ρ) (D.eval ρ) (V.eval ρ) := by
  simp only [nextFormula, Row_ccc_next_d, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, name_sat_l M hE, forcingFormula_semantics,
    row_next_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  apply exists_congr; intro A
  apply exists_congr; intro T
  apply exists_congr; intro t
  refine and_congr Iff.rfl (and_congr ?_ (and_congr ?_ Iff.rfl))
  · exact forces_env_l hE _ (preord_m_freeClosed _ _ rfl rfl) _ _
      (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) _
  · exact forces_env_l hE _ (ccc_exists_m_freeClosed _ _ rfl rfl) _ _
      (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) _

def nextStagesFormula {n} (F H e : Project.Term n) : Project.Formula 1 n :=
  .forallE (.forallE (.forallE (.forallE
    (.imp (Project.Formula.isSuccessor (.bound 2) (.bound 3))
      (.imp (entry_m (.bound 2) (.bound 1) F.weaken.weaken.weaken.weaken)
        (.imp (entry_m (.bound 2) .newest H.weaken.weaken.weaken.weaken)
          (.existsE (.existsE
            (.conj (entry_m (.bound 5) (.bound 1) F.weaken.weaken.weaken.weaken.weaken.weaken)
              (.conj (entry_m (.bound 5) .newest H.weaken.weaken.weaken.weaken.weaken.weaken)
                (nextFormula (.bound 5) (.bound 1) .newest e.weaken.weaken.weaken.weaken.weaken.weaken
                  (.bound 3) (.bound 2))))))))))))

theorem nextStagesFormula_closed {n} (F H e : Project.Term n)
    (hF : F.freeSupport = []) (hH : H.freeSupport = []) (he : e.freeSupport = []) :
    (nextStagesFormula F H e).FreeClosed := by
  simp only [nextStagesFormula, Definitional.Formula.FreeClosed]
  exact ⟨Project.Formula.isSuccessor_freeClosed _ _ rfl rfl,
    entry_m_freeClosed _ _ _ rfl rfl (by simpa using hF),
    entry_m_freeClosed _ _ _ rfl rfl (by simpa using hH),
    entry_m_freeClosed _ _ _ rfl rfl (by simpa using hF),
    entry_m_freeClosed _ _ _ rfl rfl (by simpa using hH),
    nextFormula_closed _ _ _ _ _ _ rfl rfl rfl (by simpa using he) rfl rfl⟩

theorem nextStagesFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (F H e : Project.Term n) :
    Project.Formula.satisfies ρ (nextStagesFormula F H e) ↔
      ∀ α β D V, M.SuccessorOf β α → Entry_d M β D (F.eval ρ) → Entry_d M β V (H.eval ρ) →
        ∃ B R, Entry_d M α B (F.eval ρ) ∧ Entry_d M α R (H.eval ρ) ∧
          Row_ccc_next_d α B R (e.eval ρ) D V := by
  simp only [nextStagesFormula, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_isSuccessor_iff,
    entry_sat_l M hE, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, nextFormula_semantics hE, Definitional.Term.eval_weaken]
  rfl

def stagesCCCFormula {n} (ω F H : Project.Term n) : Project.Formula 1 n :=
  .forallE (.forallE (.forallE
    (.imp (entry_m (.bound 2) (.bound 1) F.weaken.weaken.weaken)
      (.imp (entry_m (.bound 2) .newest H.weaken.weaken.weaken)
        (ccc_m kpair_convention_l ω.weaken.weaken.weaken (.bound 1) .newest (.bound 1))))))

theorem stagesCCCFormula_closed {n} (ω F H : Project.Term n)
    (hω : ω.freeSupport = []) (hF : F.freeSupport = []) (hH : H.freeSupport = []) :
    (stagesCCCFormula ω F H).FreeClosed := by
  simp only [stagesCCCFormula, Definitional.Formula.FreeClosed]
  exact ⟨entry_m_freeClosed _ _ _ rfl rfl (by simpa using hF),
    entry_m_freeClosed _ _ _ rfl rfl (by simpa using hH),
    ccc_m_freeClosed _ _ _ _ _ (by simpa using hω) rfl rfl rfl⟩

theorem stagesCCCFormula_semantics (I : kpair_convention_l.Interpretation M)
    (hE : Extensional M) {n} (ρ : Env M n) (ω F H : Project.Term n) :
    Project.Formula.satisfies ρ (stagesCCCFormula ω F H) ↔
      ∀ δ D V, Entry_d M δ D (F.eval ρ) → Entry_d M δ V (H.eval ρ) →
        Ccc_d M I (ω.eval ρ) D V D := by
  simp only [stagesCCCFormula, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, entry_sat_l M hE, ccc_sat_l I hE,
    Definitional.Term.eval_weaken]
  rfl

def systemCCCBody : Project.Formula 1 5 :=
  .imp (row_system_m (.bound 4) (.bound 3) (.bound 2) (.bound 1))
    (.imp (Project.Formula.isOmega (.bound 0))
      (.imp (row_system_supp_m false (.bound 0) (.bound 3))
        (.imp (nextStagesFormula (.bound 3) (.bound 2) (.bound 1))
          (stagesCCCFormula (.bound 0) (.bound 3) (.bound 2)))))

theorem systemCCCBody_closed : systemCCCBody.FreeClosed := by
  simp only [systemCCCBody, Definitional.Formula.FreeClosed]
  exact ⟨row_system_m_freeClosed _ _ _ _ rfl rfl rfl rfl,
    Project.Formula.isOmega_freeClosed _ rfl,
    row_system_supp_m_freeClosed _ _ _ rfl rfl,
    nextStagesFormula_closed _ _ _ rfl rfl rfl,
    stagesCCCFormula_closed _ _ _ rfl rfl rfl⟩

def systemCCCSentence : Project.Sentence :=
  Project.Sentence.ofFormula
    (.forallE (.forallE (.forallE (.forallE (.forallE systemCCCBody)))))
    (by simpa only [Definitional.Formula.FreeClosed] using systemCCCBody_closed)

/-- Finite-support preservation in the original proof kernel, with genuine
name-level successor hypotheses rather than an assumed CCC conclusion. -/
theorem derives_system_ccc : Project.Derives SetTheory.ZFC systemCCCSentence := by
  apply ObjectTheory.derives_of_native_zfc_models
  intro M hZFC
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  rw [SetTheory.Structure.satisfiesSentence_iff]
  simp only [systemCCCSentence, Project.Sentence.ofFormula, systemCCCBody,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    row_system_sat_l I hZF.1, Project.Formula.satisfies_isOmega_iff,
    row_system_supp_sat_l I hZF.1, nextStagesFormula_semantics hZF.1,
    stagesCCCFormula_semantics I hZF.1]
  intro free γ F H e ω hs hω hSupp hNext
  exact row_system_ccc_l hZFC hs hω hSupp hNext

end InfinitaryCombinatorics.Formalizations.FIMAD.Iteration
