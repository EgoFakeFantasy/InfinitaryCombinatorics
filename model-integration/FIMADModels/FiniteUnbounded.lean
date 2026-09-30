import FIMADModels.NativeFinite

/-! Internal finiteness and boundedness for subsets of omega. The induction is
on the model's own omega, with an explicitly separated first-order property. -/
set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.Internal
open YesMetaZFC YesMetaZFC.SetTheory Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

/-- Strict boundedness inside the model. -/
def Bounded (w a : M.Domain) : Prop := ∃ n, M.mem n w ∧ Subset M.mem a n

private def boundedFormula {depth : Nat} (w a : Term depth) : Formula 1 depth :=
  .existsE (.conj (.mem (.bound 0) w.weaken) (Syntax.SubsetFormula a.weaken (.bound 0)))

private theorem boundedFormula_closed {depth : Nat} (w a : Term depth)
    (hw : w.freeSupport = []) (ha : a.freeSupport = []) :
    (boundedFormula w a).FreeClosed := by
  simp only [boundedFormula, Definitional.Formula.FreeClosed,
    Syntax.SubsetFormula, Definitional.Term.freeSupport_bound,
    Definitional.Term.freeSupport_weaken, hw, ha, and_self]
  all_goals trivial

private theorem boundedFormula_semantics (hExt : Extensional M) {depth : Nat}
    (env : SetTheory.Env M depth) (w a : Term depth) :
    Formula.satisfies env (boundedFormula w a) ↔
      Bounded (M := M) (w.eval env) (a.eval env) := by
  simp only [boundedFormula, Bounded, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Syntax.satisfies_SubsetFormula hExt, Definitional.Term.eval_weaken]
  rfl

private def boundInjectionSchema : UnarySchema 1 where
  body := .forallE (.forallE (.imp
    (.conj (Syntax.SubsetFormula (.bound 1) (.bound 3))
      (Syntax.InjectionFormula (.bound 0) (.bound 1) (.bound 2)))
    (boundedFormula (.bound 3) (.bound 1))))
  freeClosed := by
    simp only [Definitional.Formula.FreeClosed]
    exact ⟨⟨Syntax.closed_SubsetFormula _ _ rfl rfl,
      Syntax.closed_InjectionFormula _ _ _ rfl rfl rfl⟩,
      boundedFormula_closed _ _ rfl rfl⟩

private theorem boundInjectionSchema_semantics (hExt : Extensional M)
    (env : SetTheory.Env M 1) (n : M.Domain) :
    Formula.satisfies (env.push n) boundInjectionSchema.body ↔
      ∀ a f, Subset M.mem a (env.bound 0) → Injection M.mem f a n →
        Bounded (M := M) (env.bound 0) a := by
  simp only [boundInjectionSchema, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_conj_iff,
    Syntax.satisfies_SubsetFormula hExt, Syntax.satisfies_InjectionFormula hExt,
    boundedFormula_semantics hExt, Definitional.Term.eval, SetTheory.Env.push]
  exact forall_congr' (fun _ => forall_congr' (fun _ => and_imp))

private def removeFiberSchema : UnarySchema 2 where
  body := .neg (Syntax.ValueFormula (.bound 1) (.bound 0) (.bound 2))
  freeClosed := by
    simpa only [Definitional.Formula.FreeClosed] using
      (Syntax.closed_ValueFormula (.bound 1) (.bound 0) (.bound 2) rfl rfl rfl :
        (Syntax.ValueFormula (.bound 1) (.bound 0) (.bound 2) : Formula 1 3).FreeClosed)

private theorem removeFiber_exists (hZF : M.Models SetTheory.ZF) (a f n : M.Domain) :
    ∃ d, ∀ x, M.mem x d ↔ M.mem x a ∧ ¬ Value M.mem f x n := by
  let env : SetTheory.Env M 2 := ⟨Fin.cases f (fun _ => n), fun _ => a⟩
  obtain ⟨d, hd⟩ := ZF.separation_exists_d hZF removeFiberSchema env a
  refine ⟨d, fun x => (hd x).trans ?_⟩
  apply and_congr Iff.rfl
  simpa [removeFiberSchema, Formula.satisfies_neg_iff,
    Definitional.Term.eval, SetTheory.Env.push, env, Fin.cases, Fin.induction] using!
    not_congr (Syntax.satisfies_ValueFormula hZF.1 (env.push x) (.bound 1) (.bound 0) (.bound 2))

private theorem restrict_injection (hZF : M.Models SetTheory.ZF)
    {f a d b : M.Domain} (hf : Injection M.mem f a b) (hd : Subset M.mem d a) :
    ∃ g, Injection M.mem g d b ∧ ∀ x y, Value M.mem g x y ↔ M.mem x d ∧ Value M.mem f x y := by
  let I := pairInterpretation hZF
  have hn := (injection_native_iff hZF f a b).mp hf
  obtain ⟨g, hg⟩ := ZF.exists_restriction hZF I f d
  have hi : M.IsSetInjectionFromTo I g d b :=
    ⟨hg.isSetFunctionFromTo hn.1 hd,
      fun x z y hx hz => hn.2 x z y ((hg.2 x y).mp hx).2 ((hg.2 z y).mp hz).2⟩
  refine ⟨g, (injection_native_iff hZF g d b).mpr hi, ?_⟩
  intro x y
  rw [value_pairMember hZF g, value_pairMember hZF f]
  exact hg.2 x y

private theorem bounded_insert (hZF : M.Models SetTheory.ZF) {w a d x : M.Domain}
    (hw : Omega M.mem w) (hx : M.mem x w) (hd : Bounded (M := M) w d)
    (ha : ∀ y, M.mem y a → M.mem y d ∨ y = x) : Bounded (M := M) w a := by
  obtain ⟨b, hb, hdb⟩ := hd
  have hn := (omega_native_iff hZF.1 w).mp hw
  have ho := hn.membershipWellOrder hZF
  have hmax : ∃ m, M.mem m w ∧ (b = m ∨ M.mem b m) ∧ (x = m ∨ M.mem x m) := by
    rcases ho.linear.compare b hb x hx with heq | hbx | hxb
    · exact ⟨x, hx, Or.inl (hZF.1.eq_of_same_members b x heq), Or.inl rfl⟩
    · exact ⟨x, hx, Or.inr hbx, Or.inl rfl⟩
    · exact ⟨b, hb, Or.inl rfl, Or.inr hxb⟩
  obtain ⟨m, hm, hbm, hxm⟩ := hmax
  obtain ⟨s, hs, hsw⟩ := hw.1.2 m hm
  refine ⟨s, hsw, fun y hy => (hs y).mpr ?_⟩
  rcases ha y hy with hyd | rfl
  · apply Or.inl
    rcases hbm with rfl | hbm
    · exact hdb y hyd
    · exact (hn.members_areOrdinals hZF m hm).transitive b hbm y (hdb y hyd)
  · exact hxm.symm

/-- Every injection into an internal natural number has bounded domain in omega.
The separated induction property quantifies over all internal sets and graphs. -/
theorem bounded_of_injection (hZF : M.Models SetTheory.ZF)
    {w : M.Domain} (hw : Omega M.mem w) :
    ∀ n, M.mem n w → ∀ a f, Subset M.mem a w → Injection M.mem f a n →
      Bounded (M := M) w a := by
  classical
  have hn := (omega_native_iff hZF.1 w).mp hw
  let env : SetTheory.Env M 1 := ⟨fun _ => w, fun _ => w⟩
  apply hn.induction (fun n => ∀ a f, Subset M.mem a w → Injection M.mem f a n → Bounded (M := M) w a)
  · obtain ⟨s, hs⟩ := ZF.separation_exists_d hZF boundInjectionSchema env w
    exact ⟨s, fun n => (hs n).trans (and_congr Iff.rfl (boundInjectionSchema_semantics hZF.1 env n))⟩
  · intro z hz a f _ hf
    obtain ⟨zero, _, hzero⟩ := hw.1.1
    refine ⟨zero, hzero, ?_⟩
    intro x hx
    obtain ⟨y, hy, _⟩ := hf.1.2 x hx
    exact False.elim (hz y (hf.2.1 x y hy))
  · intro n hnw ih s hs a f haw hf
    have hsucc := (successor_native_iff hZF.1 s n).mpr hs
    obtain ⟨d, hd⟩ := removeFiber_exists hZF a f n
    obtain ⟨g, hg, hp⟩ := restrict_injection hZF hf (fun x hx => ((hd x).mp hx).1)
    have hgn : Injection M.mem g d n := by
      refine ⟨hg.1, ?_, hg.2.2⟩
      intro x y hxy
      have hx := (hp x y).mp hxy
      rcases (hsucc y).mp (hg.2.1 x y hxy) with hy | rfl
      · exact hy
      · exact False.elim (((hd x).mp hx.1).2 hx.2)
    have hbd := ih d g (fun x hx => haw x ((hd x).mp hx).1) hgn
    by_cases he : ∃ x, M.mem x a ∧ Value M.mem f x n
    · obtain ⟨x, hx, hfx⟩ := he
      apply bounded_insert hZF hw (haw x hx) hbd
      intro y hy
      by_cases hfy : Value M.mem f y n
      · exact Or.inr (hf.2.2 y x n hfy hfx)
      · exact Or.inl ((hd y).mpr ⟨hy, hfy⟩)
    · obtain ⟨b, hb, hdb⟩ := hbd
      exact ⟨b, hb, fun y hy => hdb y ((hd y).mpr ⟨hy, fun hfy => he ⟨y, hy, hfy⟩⟩)⟩

/-- The original finite-set definition is equivalent to internal boundedness. -/
theorem finite_iff_bounded (hZF : M.Models SetTheory.ZF)
    {w a : M.Domain} (hw : Omega M.mem w) (ha : Subset M.mem a w) :
    Finite M.mem w a ↔ Bounded (M := M) w a := by
  constructor
  · rintro ⟨n, hn, f, hf⟩
    exact bounded_of_injection hZF hw n hn a f ha hf
  · rintro ⟨n, hn, ha⟩
    exact finite_of_subset_natural hZF hn ha

/-- Exact infinitude/unboundedness equivalence in any native ZF model. -/
theorem infinite_iff_unbounded (hZF : M.Models SetTheory.ZF)
    {w a : M.Domain} (hw : Omega M.mem w) (ha : Subset M.mem a w) :
    Infinite M.mem w a ↔ Unbounded M.mem w a := by
  constructor
  · exact unbounded_of_infinite hZF hw ha
  · intro hu hf
    obtain ⟨n, hn, hab⟩ := (finite_iff_bounded hZF hw ha).mp hf
    obtain ⟨y, hy, hny, hya⟩ := hu n hn
    have hyn := hab y hya
    have ho := ((omega_native_iff hZF.1 w).mp hw).membershipWellOrder hZF
    rcases hny with hny | rfl
    · exact ho.linear.irrefl n hn (ho.linear.trans n hn y hy n hn hny hyn)
    · exact ho.linear.irrefl n hn hyn

end InfinitaryCombinatorics.Formalizations.FIMAD.Internal
