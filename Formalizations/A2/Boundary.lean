import Formalizations.A2.Triangle
import Formalizations.A2.Sharpness

/-! The extra-colour boundary and the three-point calculation for arXiv v2. -/
namespace InfinitaryCombinatorics.Formalizations.A2
universe u

attribute [local instance] Classical.propDecidable

noncomputable def boundaryColor : PairColoring BinarySeq (Option ℕ) where
  color x y := if h : x = y then none else
    if delta x y h = 0 then none else some (delta x y h - 1)
  symm x y := by
    classical
    by_cases h : x = y
    · subst y; rfl
    · simp only [h, Ne.symm h, ↓reduceDIte]
      rw [delta_symm x y h]

theorem boundaryColor_value {x y : BinarySeq} (h : x ≠ y) :
    boundaryColor.color x y = if delta x y h = 0 then none else some (delta x y h - 1) := by
  simp [boundaryColor, h]

theorem boundaryColor_no_triangle : ¬ boundaryColor.HasClique 3 := by
  apply no_triangle_of_delta_injective
  intro x y v w hxy hvw he
  rw [boundaryColor_value hxy, boundaryColor_value hvw] at he
  split_ifs at he <;> simp_all
  omega

def optionOrdinal (k : Option ℕ) : Set.Iio (Ordinal.omega0.{u} + 1) :=
  match k with
  | none => ⟨Ordinal.omega0, by simp⟩
  | some n => ⟨n, (Ordinal.natCast_lt_omega0 n).trans (by simp)⟩

theorem optionOrdinal_injective : Function.Injective optionOrdinal.{u} := by
  intro a b h
  have hv := congrArg Subtype.val h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some n => exact (ne_of_gt (Ordinal.natCast_lt_omega0 n) hv).elim
  | some n =>
    cases b with
    | none => exact (ne_of_lt (Ordinal.natCast_lt_omega0 n) hv).elim
    | some m => congr 1; exact Nat.cast_inj.mp hv

noncomputable def extraColoring :
    PairColoring (Branch Ordinal.omega0.{u}) (Set.Iio (Ordinal.omega0.{u} + 1)) :=
  (boundaryColor.pullback omegaEquiv.symm).recolor optionOrdinal

theorem extraColoring_no_triangle : ¬ extraColoring.{u}.HasClique 3 := by
  rintro ⟨e, k, hk⟩
  have hcij (i j : Fin 3) (hij : i ≠ j) :
      boundaryColor.color (omegaEquiv.symm (e i)) (omegaEquiv.symm (e j)) =
      boundaryColor.color (omegaEquiv.symm (e 0)) (omegaEquiv.symm (e 1)) :=
    optionOrdinal_injective ((hk i j hij).trans (hk 0 1 (by decide)).symm)
  exact boundaryColor_no_triangle
    ⟨e.trans omegaEquiv.symm.toEmbedding, _, hcij⟩

theorem extraColoring_regressive (x y : Branch Ordinal.omega0.{u}) (hxy : x ≠ y)
    (hp : 0 < (delta x y hxy).val) :
    (extraColoring.color x y).val < (delta x y hxy).val := by
  have hr : omegaEquiv.symm x ≠ omegaEquiv.symm y := omegaEquiv.symm.injective.ne hxy
  have hd := firstDifference_of_nat (le_refl Ordinal.omega0.{u})
    (delta_spec (omegaEquiv.symm x) (omegaEquiv.symm y) hr)
  have he := (delta_spec x y hxy).unique hd
  have hpn : 0 < delta (omegaEquiv.symm x) (omegaEquiv.symm y) hr := by
    rw [he] at hp
    change (0 : Ordinal.{u}) < (delta (omegaEquiv.symm x) (omegaEquiv.symm y) hr : ℕ) at hp
    exact_mod_cast hp
  change (optionOrdinal (boundaryColor.color (omegaEquiv.symm x) (omegaEquiv.symm y))).val < _
  rw [boundaryColor_value hr, if_neg (Nat.ne_of_gt hpn), he]
  change ((delta (omegaEquiv.symm x) (omegaEquiv.symm y) hr - 1 : ℕ) : Ordinal.{u}) <
    (delta (omegaEquiv.symm x) (omegaEquiv.symm y) hr : ℕ)
  exact_mod_cast Nat.sub_one_lt_of_lt hpn

theorem proposition_5_3 : Proposition53.{u} :=
  ⟨extraColoring, extraColoring_regressive, extraColoring_no_triangle⟩

/-- The displayed colouring in Observation 2.1 of arXiv:2002.02480v2. -/
noncomputable def observationColor : PairColoring BinarySeq ℕ where
  color x y := if h : x = y then 0 else
    if delta x y h = 0 then (x 1).toNat + (y 1).toNat |>.mod 2
    else delta x y h - 1
  symm x y := by
    classical
    by_cases h : x = y
    · subst y; rfl
    · simp only [h, Ne.symm h, ↓reduceDIte]
      rw [delta_symm x y h, Nat.add_comm]

def counterF : BinarySeq := fun _ => false
def counterG : BinarySeq := fun n => decide (n = 2)
def counterH : BinarySeq := fun n => decide (n < 2)

theorem observation_counterexample :
    counterF ≠ counterG ∧ counterG ≠ counterH ∧ counterF ≠ counterH ∧
    observationColor.color counterF counterG = 1 ∧
    observationColor.color counterG counterH = 1 ∧
    observationColor.color counterF counterH = 1 := by
  have fg : FirstDifference counterF counterG 2 := by
    refine ⟨by decide, ?_⟩
    intro k hk
    simp [counterF, counterG, ne_of_lt hk]
  have gh : FirstDifference counterG counterH 0 := by
    refine ⟨by decide, ?_⟩
    intro k hk; omega
  have fh : FirstDifference counterF counterH 0 := by
    refine ⟨by decide, ?_⟩
    intro k hk; omega
  have efg := (delta_spec _ _ fg.ne).unique fg
  have egh := (delta_spec _ _ gh.ne).unique gh
  have efh := (delta_spec _ _ fh.ne).unique fh
  refine ⟨fg.ne, gh.ne, fh.ne, ?_, ?_, ?_⟩ <;>
    simp [observationColor, fg.ne, gh.ne, fh.ne, efg, egh, efh,
      counterF, counterG, counterH]

end InfinitaryCombinatorics.Formalizations.A2
