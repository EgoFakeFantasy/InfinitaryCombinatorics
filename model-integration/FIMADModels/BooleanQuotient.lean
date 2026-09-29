import FIMADModels.CheckedBooleanZFC
import FIMADModels.UltrafilterTruth
import YesMetaZFC.Model.FirstOrder.Morphism

/-! An actual two-valued quotient of standard Boolean names. The maximum
principle supplies quantifier witnesses, so the ultrafilter need not be generic.
-/
namespace InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.Model YesMetaZFC.Model.Boolean
open BV_graph
universe u
variable {B : Type u} (𝔹 : CB_alg B) (U : Filter_l 𝔹.toBA_alg)

namespace BooleanQuotient

def nameSetoid : Setoid (BV_name B) where
  r G H := U.mem (bv_eq 𝔹 G H)
  iseqv := {
    refl := fun G => by rw [eq_refl]; exact U.top_mem
    symm := fun {G H} h => by rw [eq_symm]; exact h
    trans := fun {G H K} h k => U.upward (U.meet_mem h k) (eq_trans 𝔹 G H K)
  }

abbrev Carrier := Quotient (nameSetoid 𝔹 U)
def classOf (G : BV_name B) : Carrier 𝔹 U := Quotient.mk _ G

theorem membership_congr {G G' H H' : BV_name B}
    (hG : U.mem (bv_eq 𝔹 G G')) (hH : U.mem (bv_eq 𝔹 H H')) :
    U.mem (bv_mem 𝔹 G H) ↔ U.mem (bv_mem 𝔹 G' H') := by
  constructor
  · intro h; exact U.upward (U.meet_mem (U.meet_mem hG hH) h) (mem_congr 𝔹 G G' H H')
  · intro h
    have hG' : U.mem (bv_eq 𝔹 G' G) := by rw [eq_symm]; exact hG
    have hH' : U.mem (bv_eq 𝔹 H' H) := by rw [eq_symm]; exact hH
    exact U.upward (U.meet_mem (U.meet_mem hG' hH') h) (mem_congr 𝔹 G' G H' H)

def membership (a b : Carrier 𝔹 U) : Prop :=
  Quotient.liftOn₂ a b (fun G H => U.mem (bv_mem 𝔹 G H))
    (fun _ _ _ _ hG hH => propext (membership_congr 𝔹 U hG hH))

@[implicit_reducible] def quotientStructure : YesMetaZFC.Logic.FirstOrder.Structure ℒ where
  Carrier _ := Carrier 𝔹 U
  nonempty _ := ⟨classOf 𝔹 U (BV_graph.empty 𝔹.toPO_bot)⟩
  funcInterp r := nomatch r
  relInterp | .membership, .cons a (.cons b .nil) => membership 𝔹 U a b

abbrev rawStructure := BV_str.top_structure 𝔹.toBA_alg (name_structure 𝔹)

def quotientMap : Fn_map (rawStructure 𝔹) (quotientStructure 𝔹 U) where
  map _ := classOf 𝔹 U
  function_eq r := nomatch r

attribute [local implicit_reducible] name_structure quotientMap SetTheory.signature

/-- Every existential Boolean value, with arbitrary finite parameters, is attained. -/
theorem value_maximum {b f s} (φ : Formula ℒ (s :: b) f)
    (ρ : Env (rawStructure 𝔹) b f) :
    ∃ G, BV_str.value 𝔹 (name_structure 𝔹) φ (ρ.pushBound G) =
      𝔹.iSup (fun H => BV_str.value 𝔹 (name_structure 𝔹) φ (ρ.pushBound H)) := by
  apply BV_graph.maximum 𝔹
  intro G H
  apply (BV_str.value_congr 𝔹 _ (name_laws 𝔹) φ (ρ.pushBound G) (ρ.pushBound H) ?_).1
  constructor
  · intro t i
    cases i with
    | here => exact 𝔹.le_refl _
    | there i => change 𝔹.le _ (bv_eq 𝔹 (ρ.boundVal i) (ρ.boundVal i)); rw [eq_refl]; exact 𝔹.le_top _
  · intro t i
    change 𝔹.le _ (bv_eq 𝔹 (ρ.freeVal i) (ρ.freeVal i))
    rw [eq_refl]; exact 𝔹.le_top _

/-- Full truth lemma, including both quantifiers, for the concrete quotient. -/
theorem truth (hU : U.Maximal_l) {b f} (φ : Formula ℒ b f)
    (ρ : Env (rawStructure 𝔹) b f) :
    φ.satisfies (ρ.map (quotientMap 𝔹 U).map) ↔
      U.mem (BV_str.value 𝔹 (name_structure 𝔹) φ ρ) := by
  induction φ with
  | falsum => exact ⟨False.elim, hU.1⟩
  | truth => exact ⟨fun _ => U.top_mem, fun _ => trivial⟩
  | equal t t' =>
    rw [BV_str.value_equal]
    change (t.eval _ = t'.eval _) ↔ _
    rw [← (quotientMap 𝔹 U).term_eval_eq ρ t, ← (quotientMap 𝔹 U).term_eval_eq ρ t']
    change (Quotient.mk (nameSetoid 𝔹 U) (t.eval ρ) =
      Quotient.mk (nameSetoid 𝔹 U) (t'.eval ρ)) ↔
      (nameSetoid 𝔹 U).r (t.eval ρ) (t'.eval ρ)
    exact ⟨Quotient.exact, @Quotient.sound _ (nameSetoid 𝔹 U) _ _⟩
  | rel r ts =>
    rw [BV_str.value_rel]
    change (quotientStructure 𝔹 U).relInterp r (ts.eval _) ↔ _
    rw [← (quotientMap 𝔹 U).arguments_eval_eq ρ ts]
    cases r
    cases ts.eval ρ with
    | cons a xs => cases xs with
      | cons b xs => cases xs; rfl
  | neg φ ih => exact (not_congr (ih ρ)).trans (UltrafilterTruth.neg_iff 𝔹 U hU _).symm
  | conj φ ψ ih ik =>
    exact (and_congr (ih ρ) (ik ρ)).trans (UltrafilterTruth.meet_iff 𝔹 U _ _).symm
  | disj φ ψ ih ik =>
    exact (or_congr (ih ρ) (ik ρ)).trans (UltrafilterTruth.join_iff 𝔹 U hU _ _).symm
  | imp φ ψ ih ik =>
    exact (imp_congr (ih ρ) (ik ρ)).trans (UltrafilterTruth.imp_iff 𝔹 U hU _ _).symm
  | iff φ ψ ih ik =>
    exact (iff_congr (ih ρ) (ik ρ)).trans (UltrafilterTruth.iff_iff 𝔹 U hU _ _).symm
  | existsE s φ ih =>
    rw [BV_str.value_ex, UltrafilterTruth.attained_sup_iff 𝔹 U _ (value_maximum 𝔹 φ ρ)]
    constructor
    · rintro ⟨q, hq⟩
      induction q using Quotient.inductionOn with
      | h G => exact ⟨G, (ih (ρ.pushBound G)).mp (by simpa only [Env.map_pushBound, quotientMap, classOf] using hq)⟩
    · rintro ⟨G, hG⟩
      exact ⟨classOf 𝔹 U G, by simpa only [Env.map_pushBound, quotientMap, classOf] using (ih (ρ.pushBound G)).mpr hG⟩
  | forallE s φ ih =>
    rw [BV_str.value_all, UltrafilterTruth.attained_inf_iff 𝔹 U _ (value_maximum 𝔹 (.neg φ) ρ)]
    constructor
    · intro h G
      exact (ih (ρ.pushBound G)).mp (by simpa only [Env.map_pushBound, quotientMap, classOf] using h (classOf 𝔹 U G))
    · intro h q
      induction q using Quotient.inductionOn with
      | h G => simpa only [Env.map_pushBound, quotientMap, classOf] using (ih (ρ.pushBound G)).mpr (h G)

/-- All ZFC axioms, including the full schemes, hold in the quotient structure. -/
theorem models_zfc (hU : U.Maximal_l) : Theory.Models (quotientStructure 𝔹 U) zfcTheory := by
  intro φ hφ
  have h := (truth 𝔹 U hU φ Env.empty).mpr
    (U.upward U.top_mem (CheckedBooleanZFC.models_zfc 𝔹 φ hφ Env.empty))
  simpa only [Env.map_empty, Formula.TrueIn] using h

/-- The quotient is extensional for its actual membership relation. -/
theorem extensional (hU : U.Maximal_l) :
    Extensional (Definitional.Project.FirstOrderSemantics.reduct (quotientStructure 𝔹 U)) := by
  have h := models_zfc 𝔹 U hU _
    ⟨CheckedZFC.extensionality, CheckedZFC.Axiom.extensionality, rfl⟩
  simp only [Formula.TrueIn, Definitional.Project.fo_sentence, CheckedZFC.extensionality,
    Definitional.Project.Sentence.ofFormula, Definitional.Project.fo_formula,
    Definitional.Project.fo_mem, Definitional.Project.fo_term,
    Definitional.Project.fo_bound_variable, Formula.satisfies, Arguments.eval, Term.eval,
    Definitional.Project.Term.newest, Definitional.Project.Term.weaken,
    Definitional.Term.newest, Definitional.Term.weaken, Definitional.Term.rename,
    Definitional.Term.bind, Definitional.Project.Formula.extensionalEq,
    Definitional.Project.Formula.pairArguments] at h
  change (∀ a b : Carrier 𝔹 U,
    (∀ x, membership 𝔹 U x a ↔ membership 𝔹 U x b) → a = b) at h
  exact ⟨h⟩

/-- A nonzero Boolean value produces an actual ordinary ZFC model of the sentence.
The ultrafilter is constructed here, not supplied as an additional assumption. -/
theorem model_of_nonzero (φ : YesMetaZFC.Logic.FirstOrder.Sentence ℒ)
    (hφ : BV_str.value 𝔹 (name_structure 𝔹) φ Env.empty ≠ 𝔹.bot) :
    ∃ M : YesMetaZFC.Logic.FirstOrder.Structure.{0,0,0,u+1} ℒ,
      Theory.Models M zfcTheory ∧
      Extensional (Definitional.Project.FirstOrderSemantics.reduct M) ∧ φ.TrueIn M := by
  let v := BV_str.value 𝔹 (name_structure 𝔹) φ Env.empty
  let F := Filter_l.principal_l (𝔹 := 𝔹.toBA_alg) v
  obtain ⟨V, hV, hFV⟩ := Filter_l.tarski_extension_l F
    ((Filter_l.principal_proper_l v).mpr hφ)
  refine ⟨quotientStructure 𝔹 V, models_zfc 𝔹 V hV, extensional 𝔹 V hV, ?_⟩
  have hv : V.mem v := hFV v (𝔹.le_refl v)
  have h := (truth 𝔹 V hV φ Env.empty).mpr hv
  simpa only [Env.map_empty, Formula.TrueIn] using h

end BooleanQuotient
end InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels
