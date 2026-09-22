import Formalizations.A2.Basic
import Formalizations.A2.Fusion
import Mathlib.SetTheory.Ordinal.Arithmetic

/-! Exact bridges between natural coordinates and arbitrary ordinal lengths. -/
namespace InfinitaryCombinatorics.Formalizations.A2
open Set
universe u

def natCoord {κ : Ordinal.{u}} (hκ : Ordinal.omega0 ≤ κ) (n : ℕ) : Set.Iio κ :=
  ⟨n, (Ordinal.natCast_lt_omega0 n).trans_le hκ⟩

noncomputable def finiteIndex (ξ : Set.Iio Ordinal.omega0.{u}) : ℕ :=
  (Ordinal.lt_omega0.mp ξ.property).choose

theorem finiteIndex_spec (ξ : Set.Iio Ordinal.omega0.{u}) :
    ξ.val = (finiteIndex ξ : Ordinal.{u}) :=
  (Ordinal.lt_omega0.mp ξ.property).choose_spec

@[simp] theorem finiteIndex_natCoord (n : ℕ) :
    finiteIndex (natCoord (le_refl Ordinal.omega0.{u}) n) = n := by
  have h := finiteIndex_spec (natCoord (le_refl Ordinal.omega0.{u}) n)
  exact Nat.cast_inj.mp (show (finiteIndex (natCoord (le_refl Ordinal.omega0.{u}) n) : Ordinal.{u}) = (n : Ordinal.{u}) from h.symm)

def natRestrict {κ : Ordinal.{u}} (hκ : Ordinal.omega0 ≤ κ) (x : Branch κ) : BinarySeq :=
  fun n => x (natCoord hκ n)

noncomputable def omegaBranch (s : BinarySeq) : Branch Ordinal.omega0.{u} :=
  fun ξ => s (finiteIndex ξ)

@[simp] theorem omegaBranch_nat (s : BinarySeq) (n : ℕ) :
    omegaBranch.{u} s (natCoord le_rfl n) = s n := by simp [omegaBranch]

theorem omegaBranch_injective : Function.Injective omegaBranch.{u} := by
  intro s t h
  funext n
  simpa using congrFun h (natCoord le_rfl n)

theorem firstDifference_of_nat {κ : Ordinal.{u}} (hκ : Ordinal.omega0 ≤ κ)
    {x y : Branch κ} {n : ℕ}
    (h : FirstDifference (natRestrict hκ x) (natRestrict hκ y) n) :
    FirstDifference x y (natCoord hκ n) := by
  refine ⟨h.1, ?_⟩
  intro ξ hξ
  have hξn : ξ.val < (n : Ordinal.{u}) := hξ
  obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp (hξn.trans (Ordinal.natCast_lt_omega0 n))
  have hkn : k < n := by exact_mod_cast (hk ▸ hξn)
  have he : ξ = natCoord hκ k := Subtype.ext hk
  subst ξ
  exact h.2 k hkn

theorem omegaBranch_firstDifference {s t : BinarySeq} {n : ℕ}
    (h : FirstDifference s t n) :
    FirstDifference (omegaBranch.{u} s) (omegaBranch t) (natCoord le_rfl n) := by
  apply firstDifference_of_nat le_rfl
  simpa only [FirstDifference, natRestrict, omegaBranch_nat] using h

/-- The ordinary Cantor space and ordinal-indexed omega branches are equivalent. -/
noncomputable def omegaEquiv : BinarySeq ≃ Branch Ordinal.omega0.{u} where
  toFun := omegaBranch
  invFun := natRestrict le_rfl
  left_inv s := by funext n; exact omegaBranch_nat s n
  right_inv x := by
    funext ξ
    change x (natCoord le_rfl (finiteIndex ξ)) = x ξ
    congr 1
    exact Subtype.ext (finiteIndex_spec ξ).symm

noncomputable def extendOmega {κ : Ordinal.{u}} (_hκ : Ordinal.omega0 < κ)
    (s : BinarySeq) (b : Bool) : Branch κ := fun ξ =>
  if h : ξ.val < Ordinal.omega0 then s (finiteIndex ⟨ξ.val, h⟩)
  else if ξ.val = Ordinal.omega0 then b else false

@[simp] theorem extendOmega_nat {κ : Ordinal.{u}} (hκ : Ordinal.omega0 < κ)
    (s : BinarySeq) (b : Bool) (n : ℕ) :
    extendOmega hκ s b (natCoord hκ.le n) = s n := by
  simp only [extendOmega, natCoord, Ordinal.natCast_lt_omega0, dif_pos]
  change s (finiteIndex (natCoord (le_refl Ordinal.omega0.{u}) n)) = s n
  rw [finiteIndex_natCoord]

@[simp] theorem extendOmega_omega {κ : Ordinal.{u}} (hκ : Ordinal.omega0 < κ)
    (s : BinarySeq) (b : Bool) : extendOmega hκ s b ⟨Ordinal.omega0, hκ⟩ = b := by
  simp [extendOmega]

theorem extendOmega_firstDifference {κ : Ordinal.{u}} (hκ : Ordinal.omega0 < κ)
    (s : BinarySeq) :
    FirstDifference (extendOmega hκ s false) (extendOmega hκ s true) ⟨Ordinal.omega0, hκ⟩ := by
  refine ⟨by simp, ?_⟩
  intro ξ hξ
  have h : ξ.val < Ordinal.omega0 := hξ
  simp [extendOmega, h]

end InfinitaryCombinatorics.Formalizations.A2
