import FIMADModels.DowGeneric

/-! The actual Dow generic extension weakly separates the given orthogonal
families. All finite and infinite assertions refer to the extension's own
sets, omega and injection graphs. This is one forcing step, not the BMZ
iteration or the final independence theorem. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem generic_stems_avoid (hZF : M.Models SetTheory.ZF) {w A B R b p s S : M.Domain}
    {U : M.Domain → Prop} (hU : Generic_d M B R B U)
    (hB : ∀ q, M.mem q B ↔ CodedCondition w A q)
    (hR : ∀ q r, Entry_d M q r R ↔
      M.mem q B ∧ M.mem r B ∧ CodedExtends (M := M) q r)
    (hp : U p) (hps : KPair_d M p s S) (hAvoid : StemAvoid w b s S) :
    ∀ k q, M.mem k b → U q → InStem q k → M.mem k s := by
  intro k q hkb hq hStem
  obtain ⟨t, T, hqt, hkt⟩ := hStem
  obtain ⟨r, hr, hrp, hrq⟩ := hU.directed p q hp hq
  obtain ⟨v, V, hrv, hCond⟩ := (hB r).mp (hU.proper r hr).1
  have hvp := extends_of_codes hZF hrv hps ((hR r p).mp hrp).2.2
  have hvq := extends_of_codes hZF hrv hqt ((hR r q).mp hrq).2.2
  classical
  by_cases hks : M.mem k s
  · exact hks
  · exact False.elim (hvp.2.2 (hAvoid v ⟨hCond.1, k, hvq.1 k hkt, hkb, hks⟩))

theorem separator_in_extension (hZF : M.Models SetTheory.ZF) {w A C B R c : M.Domain}
    {U : M.Domain → Prop} (O : Cond_order_d M B R B)
    (hU : Generic_d M B R B U) (hc : U c) (hw : M.IsOmega w)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔
      M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q)
    (hA : ∀ a, M.mem a A → Internal.Subset M.mem a w ∧ Internal.Infinite M.mem w a)
    (hC : ∀ b, M.mem b C → Orthogonal w A b)
    (e : M.Domain → (extension_l M hZF B R B U).Domain)
    (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ k, M.mem k a ∧ e k = y)
    (hv : ∀ a t, Check_d M c a t → Qval_d M B R B U t (e a)) :
    ∃ X, WeakSeparator (M := extension_l M hZF B R B U) (e w) (e A) (e C) X := by
  let E := extension_l M hZF B R B U
  have hE : E.Models SetTheory.ZF := preserves_zf_l O hZF hU
  have mem_image {a k} (hk : M.mem k a) : E.mem (e k) (e a) :=
    (he a (e k)).mpr ⟨k, hk, rfl⟩
  have reflect_mem {a k} (hk : E.mem (e k) (e a)) : M.mem k a := by
    obtain ⟨j, hj, hjk⟩ := (he a (e k)).mp hk
    exact hi hjk ▸ hj
  have hwE : E.IsOmega (e w) := image_omega_l (hEN := hE.1) e hi he hZF
    (internal_foundation_l O hZF hU) hw
    (fun T => KP.difference_exists_d (ZF.modelsKP hE) T (e w))
  have hwE' := (Internal.omega_native_iff hE.1 (e w)).mpr hwE
  obtain ⟨X, hX⟩ := generic_stem_real hZF O hU hc hB e hv
  have hXw : Internal.Subset E.mem X (e w) := by
    intro y hy
    obtain ⟨k, _, hkw, _, _, rfl⟩ := (hX y).mp hy
    exact mem_image hkw
  refine ⟨X, hXw, ?_, ?_⟩
  · intro a' ha'
    obtain ⟨a, ha, rfl⟩ := (he A a').mp ha'
    obtain ⟨d, hd⟩ := KP.intersection_exists_d (ZF.modelsKP hE) (e a) X
    have hdw : Internal.Subset E.mem d (e w) := fun y hy => hXw y ((hd y).mp hy).2
    refine ⟨d, hd, (Internal.infinite_iff_unbounded hE hwE' hdw).mpr ?_⟩
    intro n' hn'
    obtain ⟨n, hn, rfl⟩ := (he w n').mp hn'
    obtain ⟨p, hp, s, S, hps, k, hks, hka, hnk⟩ :=
      generic_meets_hit hZF hU hw hB hR ha (hA a ha).1 (hA a ha).2 hn
    have hkw := (hA a ha).1 k hka
    have hkX : E.mem (e k) X := (hX (e k)).mpr ⟨k, p, hkw, hp, ⟨s, S, hps, hks⟩, rfl⟩
    refine ⟨e k, mem_image hkw, ?_, (hd (e k)).mpr ⟨mem_image hka, hkX⟩⟩
    rcases hnk with rfl | hnk
    · exact Or.inr rfl
    · exact Or.inl (mem_image hnk)
  · intro b' hb'
    obtain ⟨b, hb, rfl⟩ := (he C b').mp hb'
    obtain ⟨p, hp, s, S, hps, hAvoid⟩ := generic_meets_avoid hZF hU hw hB hR (hC b hb)
    have hCond := condition_of_codes hZF hps ((hB p).mp (hU.proper p hp).1)
    obtain ⟨n, hn, hsn⟩ := (Internal.finite_iff_bounded hZF
      ((Internal.omega_native_iff hZF.1 w).mpr hw) hCond.1.1).mp hCond.1.2
    obtain ⟨d, hd⟩ := KP.intersection_exists_d (ZF.modelsKP hE) (e b) X
    have hdw : Internal.Subset E.mem d (e w) := fun y hy => hXw y ((hd y).mp hy).2
    refine ⟨d, hd, (Internal.finite_iff_bounded hE hwE' hdw).mpr
      ⟨e n, mem_image hn, ?_⟩⟩
    intro y hy
    obtain ⟨hyb, hyX⟩ := (hd y).mp hy
    obtain ⟨k, q, _, hq, hStem, rfl⟩ := (hX y).mp hyX
    have hkb := reflect_mem hyb
    exact mem_image (hsn k (generic_stems_avoid hZF hU hB hR hp hps hAvoid k q hkb hq hStem))

/-- Construct a genuine ZFC Dow extension and separator for enumerated ground models.
The enumeration is used only to construct the external generic predicate. -/
theorem dow_extension_exists (hZFC : M.Models SetTheory.ZFC) {w A C : M.Domain}
    (hw : M.IsOmega w)
    (hA : ∀ a, M.mem a A → Internal.Subset M.mem a w ∧ Internal.Infinite M.mem w a)
    (hC : ∀ b, M.mem b C → Orthogonal w A b)
    (enum : Nat → M.Domain) (hEnum : Function.Surjective enum) :
    ∃ E : SetTheory.Structure.{u}, E.Models SetTheory.ZFC ∧
      ∃ e : M.Domain → E.Domain, Function.Injective e ∧
        (∀ a y, E.mem y (e a) ↔ ∃ k, M.mem k a ∧ e k = y) ∧
        E.IsOmega (e w) ∧ ∃ X, WeakSeparator (M := E) (e w) (e A) (e C) X := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨B, R, hB, hR, O⟩ := order_exists hZF w A
  obtain ⟨c, hc, _⟩ := top_exists hZF hw hB hR
  have hcz : c ≠ B := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (eq ▸ hc)
  obtain ⟨U, hU, hcU⟩ := internal_generic_l O enum hEnum hc hcz
  let E := extension_l M hZF B R B U
  have hE : E.Models SetTheory.ZFC := preserves_zfc_l O hZFC hU
  obtain ⟨e, hv, he, hi⟩ := check_map_l O hZF hU hcU
  have hwE : E.IsOmega (e w) := image_omega_l
    (hEN := (ZFC.models_zf_l hE).1) e hi he hZF
    (internal_foundation_l O hZF hU) hw
    (fun T => KP.difference_exists_d (ZF.modelsKP (ZFC.models_zf_l hE)) T (e w))
  exact ⟨E, hE, e, hi, he, hwE,
    separator_in_extension hZF O hU hcU hw hB hR hA hC e hi he hv⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
