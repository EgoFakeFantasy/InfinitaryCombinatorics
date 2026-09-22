import Formalizations.A2.Theorem23
import Formalizations.A2.Coordinates

/-! First-difference preserving embeddings and the canonical-copy sharpness result. -/
namespace InfinitaryCombinatorics.Formalizations.A2
open Set
universe u

attribute [local instance] Classical.propDecidable

def restrictBranch {α κ : Ordinal.{u}} (h : α ≤ κ) (x : Branch κ) : Branch α :=
  fun ξ => x ⟨ξ.val, ξ.property.trans_le h⟩

noncomputable def zeroExtend {α κ : Ordinal.{u}} (_h : α ≤ κ) (x : Branch α) : Branch κ :=
  fun ξ => if hξ : ξ.val < α then x ⟨ξ.val, hξ⟩ else false

@[simp] theorem restrict_zeroExtend {α κ : Ordinal.{u}} (h : α ≤ κ) (x : Branch α) :
    restrictBranch h (zeroExtend h x) = x := by
  funext ξ
  change (if hξ : ξ.val < α then x ⟨ξ.val, hξ⟩ else false) = x ξ
  rw [dif_pos (show ξ.val < α from ξ.property)]

theorem zeroExtend_injective {α κ : Ordinal.{u}} (h : α ≤ κ) :
    Function.Injective (zeroExtend h) :=
  Function.LeftInverse.injective (restrict_zeroExtend h)

theorem firstDifference_restrict {α κ : Ordinal.{u}} (h : α ≤ κ)
    {x y : Branch κ} {δ : Set.Iio α}
    (hd : FirstDifference (restrictBranch h x) (restrictBranch h y) δ) :
    FirstDifference x y ⟨δ.val, δ.property.trans_le h⟩ := by
  refine ⟨hd.1, ?_⟩
  intro γ hγ
  exact hd.2 ⟨γ.val, (show γ.val < δ.val from hγ).trans δ.property⟩ hγ

theorem firstDifference_zeroExtend {α κ : Ordinal.{u}} (h : α ≤ κ)
    {x y : Branch α} {δ : Set.Iio α} (hd : FirstDifference x y δ) :
    FirstDifference (zeroExtend h x) (zeroExtend h y) ⟨δ.val, δ.property.trans_le h⟩ := by
  apply firstDifference_restrict h
  simpa using hd

theorem canonical_range {κ : Ordinal.{u}} (hκ : Ordinal.omega0 + 1 ≤ κ) :
    Set.range (zeroExtend hκ) =
      {x : Branch κ | ∀ ξ, Ordinal.omega0 < ξ.val → x ξ = false} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ ξ hξ
    have hn : ¬ ξ.val < Ordinal.omega0 + 1 := by
      simpa [Order.succ_eq_add_one] using (not_lt_of_ge ((Order.succ_le_iff).mpr hξ))
    simp [zeroExtend, hn]
  · intro hx
    refine ⟨restrictBranch hκ x, ?_⟩
    funext ξ
    by_cases hξ : ξ.val < Ordinal.omega0 + 1
    · simp [zeroExtend, hξ, restrictBranch]
    · have hw : Ordinal.omega0 < ξ.val := by
        apply (Order.succ_le_iff).mp
        simpa [Order.succ_eq_add_one] using le_of_not_gt hξ
      simp [zeroExtend, hξ, hx ξ hw]

noncomputable def canonicalColoring {κ : Ordinal.{u}} (hκ : Ordinal.omega0 + 1 ≤ κ) :
    PairColoring (Branch κ) (Set.Iio κ) where
  color x y := if h : restrictBranch hκ x = restrictBranch hκ y then
      ⟨0, zero_lt_omega_add_one.trans_le hκ⟩
    else ⟨(sharpColoringC.color (restrictBranch hκ x) (restrictBranch hκ y)).val,
      (sharpColoringC.color (restrictBranch hκ x) (restrictBranch hκ y)).property.trans_le hκ⟩
  symm x y := by
    classical
    by_cases h : restrictBranch hκ x = restrictBranch hκ y
    · rw [dif_pos h, dif_pos h.symm]
    · rw [dif_neg h, dif_neg (Ne.symm h)]
      apply Subtype.ext
      exact congrArg (fun k : Set.Iio (Ordinal.omega0.{u} + 1) => k.val) (sharpColoringC.symm (restrictBranch hκ x) (restrictBranch hκ y))

theorem canonicalColoring_regressive {κ : Ordinal.{u}} (hκ : Ordinal.omega0 + 1 ≤ κ) :
    DeltaRegressive κ (canonicalColoring hκ) := by
  intro x y hxy hp
  by_cases h : restrictBranch hκ x = restrictBranch hκ y
  · simpa [canonicalColoring, h] using hp
  · have hd := firstDifference_restrict hκ (delta_spec _ _ h)
    have he := (delta_spec x y hxy).unique hd
    have hpr : 0 < (delta (restrictBranch hκ x) (restrictBranch hκ y) h).val := by
      simpa [he] using hp
    have hr := sharpColoring_regressive (restrictBranch hκ x) (restrictBranch hκ y) h hpr
    simpa [canonicalColoring, h, he, sharpColoringC] using hr

theorem canonicalColoring_on_copy {κ : Ordinal.{u}} (hκ : Ordinal.omega0 + 1 ≤ κ)
    {x y : Branch (Ordinal.omega0 + 1)} (hxy : x ≠ y) :
    ((canonicalColoring hκ).color (zeroExtend hκ x) (zeroExtend hκ y)).val =
      (sharpColoringC.color x y).val := by
  simp [canonicalColoring, hxy]

/-- Proposition 4.2. The pullback is exactly the restriction to the canonical copy;
`canonical_range` identifies that copy with the zero-above-omega functions. -/
theorem canonicalColoring_no_five_on_copy {κ : Ordinal.{u}}
    (hκ : Ordinal.omega0 + 1 ≤ κ) :
    ¬ ((canonicalColoring hκ).pullback (zeroExtend hκ)).HasClique 5 := by
  rintro ⟨e, k, hk⟩
  have he (i j : Fin 5) (hij : i ≠ j) :
      (sharpColoringC.color (e i) (e j)).val = k.val := by
    exact (canonicalColoring_on_copy hκ (e.injective.ne hij)).symm.trans
      (congrArg Subtype.val (hk i j hij))
  apply sharpColoring_noClique5
  refine ⟨e, sharpColoringC.color (e 0) (e 1), ?_⟩
  intro i j hij
  exact Subtype.ext ((he i j hij).trans (he 0 1 (by decide)).symm)

end InfinitaryCombinatorics.Formalizations.A2
