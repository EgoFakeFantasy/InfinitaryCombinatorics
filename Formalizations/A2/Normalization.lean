import Formalizations.A2.Transfer

/-! The normalized reduction in Remark 3.3, including the unconstrained zero split. -/
namespace InfinitaryCombinatorics.Formalizations.A2
universe u
attribute [local instance] Classical.propDecidable

noncomputable def truncateColour {κ : Ordinal.{u}} (k : Set.Iio κ) :
    Set.Iio (Ordinal.omega0.{u} + 1) :=
  if h : k.val < Ordinal.omega0 + 1 then ⟨k.val, h⟩ else ⟨0, zero_lt_omega_add_one⟩

noncomputable def normalizedPullback {κ : Ordinal.{u}} (hκ : Ordinal.omega0 + 1 ≤ κ)
    (c : PairColoring (Branch κ) (Set.Iio κ)) :
    PairColoring (Branch (Ordinal.omega0.{u} + 1)) (Set.Iio (Ordinal.omega0.{u} + 1)) where
  color x y := if x ⟨0, zero_lt_omega_add_one⟩ = y ⟨0, zero_lt_omega_add_one⟩ then
    truncateColour (c.color (zeroExtend hκ x) (zeroExtend hκ y)) else ⟨0, zero_lt_omega_add_one⟩
  symm x y := by
    rw [c.symm]
    by_cases h : x ⟨0, zero_lt_omega_add_one⟩ = y ⟨0, zero_lt_omega_add_one⟩
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]

theorem normalizedPullback_positive {κ : Ordinal.{u}} (hκ : Ordinal.omega0 + 1 ≤ κ)
    (c : PairColoring (Branch κ) (Set.Iio κ)) (hc : DeltaRegressive κ c)
    {x y : Branch (Ordinal.omega0.{u} + 1)} (hxy : x ≠ y)
    (hp : 0 < (delta x y hxy).val) :
    ((normalizedPullback hκ c).color x y).val =
      (c.color (zeroExtend hκ x) (zeroExtend hκ y)).val := by
  have hxy' := (zeroExtend_injective hκ).ne hxy
  have hd := firstDifference_zeroExtend hκ (delta_spec x y hxy)
  have he := (delta_spec _ _ hxy').unique hd
  have hp' : 0 < (delta (zeroExtend hκ x) (zeroExtend hκ y) hxy').val := by
    simpa [he] using hp
  have hb := hc _ _ hxy' hp'
  have hb' : (c.color (zeroExtend hκ x) (zeroExtend hκ y)).val < Ordinal.omega0 + 1 := by
    rw [he] at hb
    exact hb.trans (delta x y hxy).property
  have h0 := (delta_spec x y hxy).2 ⟨0, zero_lt_omega_add_one⟩ hp
  simp only [normalizedPullback, if_pos h0]
  unfold truncateColour
  rw [dif_pos hb']

theorem normalizedPullback_regressive {κ : Ordinal.{u}} (hκ : Ordinal.omega0 + 1 ≤ κ)
    (c : PairColoring (Branch κ) (Set.Iio κ)) (hc : DeltaRegressive κ c) :
    DeltaRegressive (Ordinal.omega0 + 1) (normalizedPullback hκ c) := by
  intro x y hxy hp
  rw [normalizedPullback_positive hκ c hc hxy hp]
  have hxy' := (zeroExtend_injective hκ).ne hxy
  have hd := firstDifference_zeroExtend hκ (delta_spec x y hxy)
  have he := (delta_spec _ _ hxy').unique hd
  have hp' : 0 < (delta (zeroExtend hκ x) (zeroExtend hκ y) hxy').val := by
    simpa [he] using hp
  simpa [he] using hc _ _ hxy' hp'

theorem normalizedPullback_at_zero {κ : Ordinal.{u}} (hκ : Ordinal.omega0 + 1 ≤ κ)
    (c : PairColoring (Branch κ) (Set.Iio κ))
    {x y : Branch (Ordinal.omega0.{u} + 1)} (hxy : x ≠ y)
    (hz : (delta x y hxy).val = 0) : ((normalizedPullback hκ c).color x y).val = 0 := by
  have he : delta x y hxy = ⟨0, zero_lt_omega_add_one⟩ := Subtype.ext hz
  have hd := (delta_spec x y hxy).1
  rw [he] at hd
  simp [normalizedPullback, hd]

/-- Distinct points in the zero cone retain their original colour. -/
theorem normalizedPullback_on_zero_cone {κ : Ordinal.{u}} (hκ : Ordinal.omega0 + 1 ≤ κ)
    (c : PairColoring (Branch κ) (Set.Iio κ)) (hc : DeltaRegressive κ c)
    {x y : Branch (Ordinal.omega0.{u} + 1)}
    (hx : x ∈ zeroCone _ zero_lt_omega_add_one) (hy : y ∈ zeroCone _ zero_lt_omega_add_one)
    (hxy : x ≠ y) : ((normalizedPullback hκ c).color x y).val =
      (c.color (zeroExtend hκ x) (zeroExtend hκ y)).val := by
  apply normalizedPullback_positive hκ c hc hxy
  apply lt_of_le_of_ne bot_le
  intro hz
  have he : delta x y hxy = ⟨0, zero_lt_omega_add_one⟩ := Subtype.ext hz.symm
  have hd := (delta_spec x y hxy).1
  rw [he] at hd
  exact hd (hx.trans hy.symm)

end InfinitaryCombinatorics.Formalizations.A2
