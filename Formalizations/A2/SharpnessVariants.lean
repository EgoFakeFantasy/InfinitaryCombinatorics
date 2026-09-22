import Formalizations.A2.Theorem23
import Formalizations.A2.Coordinates

/-! The no-five bound permits arbitrary finite colours on the terminal fibres. -/
namespace InfinitaryCombinatorics.Formalizations.A2
universe u

theorem sharpness_finite_terminal_variation
    (c : PairColoring (Branch (Ordinal.omega0.{u} + 1)) (Set.Iio (Ordinal.omega0.{u} + 1)))
    (hzero : ∀ x y (hxy : x ≠ y), (delta x y hxy).val = 0 →
      (c.color x y).val = Ordinal.omega0)
    (hfinite : ∀ x y (hxy : x ≠ y), 0 < (delta x y hxy).val →
      (delta x y hxy).val < Ordinal.omega0 →
      (c.color x y).val = (delta x y hxy).val - 1)
    (hterminal : ∀ x y (hxy : x ≠ y), (delta x y hxy).val = Ordinal.omega0 →
      (c.color x y).val < Ordinal.omega0) : ¬ c.HasClique 5 := by
  classical
  rintro ⟨e, k, hk⟩
  have colour (i j : Fin 5) (hij : i ≠ j) : (c.color (e i) (e j)).val = k.val :=
    congrArg Subtype.val (hk i j hij)
  have inv (i j : Fin 5) (hij : i ≠ j) :
      (delta (e i) (e j) (e.injective.ne hij)).val = Ordinal.omega0 ∨
      (k.val = Ordinal.omega0 ∧ (delta (e i) (e j) (e.injective.ne hij)).val = 0) ∨
      (delta (e i) (e j) (e.injective.ne hij)).val = k.val + 1 := by
    let d := (delta (e i) (e j) (e.injective.ne hij)).val
    by_cases hdw : d = Ordinal.omega0
    · exact Or.inl hdw
    · have hdlt : d < Ordinal.omega0 :=
        lt_of_le_of_ne (le_omega_of_lt_omega_add_one
          (delta (e i) (e j) (e.injective.ne hij)).property) hdw
      by_cases hd0 : d = 0
      · exact Or.inr (Or.inl ⟨(colour i j hij).symm.trans (hzero _ _ _ hd0), hd0⟩)
      · have hp : 0 < d := lt_of_le_of_ne bot_le (Ne.symm hd0)
        exact Or.inr (Or.inr (sub_one_eq_iff hp hdlt
          ((hfinite _ _ _ hp hdlt).symm.trans (colour i j hij))))
  by_cases hkw : k.val = Ordinal.omega0
  · have hd0 (i j : Fin 5) (hij : i ≠ j) :
        (delta (e i) (e j) (e.injective.ne hij)).val = 0 := by
      rcases inv i j hij with hw | ⟨_, h0⟩ | hn
      · have h := hterminal _ _ (e.injective.ne hij) hw
        rw [colour i j hij, hkw] at h
        exact (lt_irrefl _ h).elim
      · exact h0
      · have h : (delta (e i) (e j) (e.injective.ne hij)).val < Ordinal.omega0 + 1 :=
          (delta (e i) (e j) (e.injective.ne hij)).property
        rw [hn, hkw] at h
        exact (lt_irrefl _ h).elim
    exact no_three_same_delta (e 0) (e 1) (e 2)
      (e.injective.ne (by decide)) (e.injective.ne (by decide)) (e.injective.ne (by decide))
      (Subtype.ext ((hd0 0 1 (by decide)).trans (hd0 0 2 (by decide)).symm))
      (Subtype.ext ((hd0 1 2 (by decide)).trans (hd0 0 2 (by decide)).symm))
  · have hklt : k.val < Ordinal.omega0 :=
      lt_of_le_of_ne (le_omega_of_lt_omega_add_one k.property) hkw
    obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hklt
    let p : Set.Iio (Ordinal.omega0.{u} + 1) := natCoord (by simp) (m + 1)
    let f : Fin 5 → Bool × Bool := fun i => (e i p, e i omegaCoord)
    have hi : Function.Injective f := by
      intro i j heq
      by_contra hij
      have hd := (delta_spec (e i) (e j) (e.injective.ne hij)).1
      rcases inv i j hij with hw | ⟨hw, _⟩ | hn
      · have he : delta (e i) (e j) (e.injective.ne hij) = omegaCoord := Subtype.ext hw
        rw [he] at hd
        exact hd (congrArg Prod.snd heq)
      · exact hkw hw
      · have he : delta (e i) (e j) (e.injective.ne hij) = p := by
          apply Subtype.ext
          simpa [hm, p, natCoord, Nat.cast_add] using hn
        rw [he] at hd
        exact hd (congrArg Prod.fst heq)
    have hcard := Fintype.card_le_of_injective f hi
    simp at hcard

end InfinitaryCombinatorics.Formalizations.A2
