import Lean

/-! Regular lower sets of an arbitrary forcing preorder. This file is shared
unchanged by the two pinned Lean packages; it needs neither mathlib nor a
particular version of the Boolean-name library. Smaller conditions are stronger.
The Boolean operations and their laws are constructed, not assumed. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular
universe u v

structure Order (P : Type u) where
  le : P → P → Prop
  refl : ∀ p, le p p
  trans : ∀ {p q r}, le p q → le q r → le p r

variable {P : Type u} (R : Order P)

def Closure (S : P → Prop) (p : P) : Prop :=
  ∀ q, R.le q p → ∃ r, R.le r q ∧ S r

structure Regular where
  mem : P → Prop
  lower : ∀ {p q}, R.le p q → mem q → mem p
  closed : ∀ p, Closure R mem p → mem p

namespace Regular
variable {R} (U V W : Regular R)

theorem ext (h : ∀ p, U.mem p ↔ V.mem p) : U = V := by
  cases U
  cases V
  congr
  exact funext (fun p => propext (h p))

def Le : Prop := ∀ p, U.mem p → V.mem p

def closure (S : P → Prop) : Regular R where
  mem := Closure R S
  lower h k q hq := k q (R.trans hq h)
  closed _ h q hq := by
    obtain ⟨r, hr, hSr⟩ := h q hq
    obtain ⟨s, hs, hSs⟩ := hSr r (R.refl r)
    exact ⟨s, R.trans hs hr, hSs⟩

def bot : Regular R where
  mem _ := False
  lower _ h := h
  closed p h := by obtain ⟨_, _, h⟩ := h p (R.refl p); exact h

def top : Regular R where
  mem _ := True
  lower _ _ := True.intro
  closed _ _ := True.intro

def meet : Regular R where
  mem p := U.mem p ∧ V.mem p
  lower h k := ⟨U.lower h k.1, V.lower h k.2⟩
  closed p h := by
    constructor
    · apply U.closed p
      intro q hq
      obtain ⟨r, hr, hU, _⟩ := h q hq
      exact ⟨r, hr, hU⟩
    · apply V.closed p
      intro q hq
      obtain ⟨r, hr, _, hV⟩ := h q hq
      exact ⟨r, hr, hV⟩

def imp : Regular R where
  mem p := ∀ q, R.le q p → U.mem q → V.mem q
  lower h k q hq := k q (R.trans hq h)
  closed p h q hq hU := by
    apply V.closed q
    intro r hr
    obtain ⟨s, hs, hk⟩ := h r (R.trans hr hq)
    exact ⟨s, hs, hk s (R.refl s) (U.lower (R.trans hs hr) hU)⟩

def sup (S : Regular R → Prop) : Regular R :=
  closure (fun p => ∃ U, S U ∧ U.mem p)

def iSup {I : Sort v} (f : I → Regular R) : Regular R :=
  closure (fun p => ∃ i, (f i).mem p)

theorem le_refl : U.Le U := fun _ h => h

theorem le_trans (h : U.Le V) (k : V.Le W) : U.Le W := fun p hp => k p (h p hp)

theorem le_antisymm (h : U.Le V) (k : V.Le U) : U = V :=
  ext U V (fun p => ⟨h p, k p⟩)

theorem le_meet_iff : U.Le (meet V W) ↔ U.Le V ∧ U.Le W :=
  ⟨fun h => ⟨fun p hp => (h p hp).1, fun p hp => (h p hp).2⟩,
    fun h p hp => ⟨h.1 p hp, h.2 p hp⟩⟩

theorem le_imp_iff : U.Le (imp V W) ↔ (meet U V).Le W := by
  constructor
  · intro h p hp
    exact h p hp.1 p (R.refl p) hp.2
  · intro h p hp q hq hV
    exact h q ⟨U.lower hq hp, hV⟩

theorem double_neg : imp (imp U bot) bot = U := by
  classical
  apply ext
  intro p
  constructor
  · intro h
    apply U.closed p
    intro q hq
    apply Classical.byContradiction
    intro hn
    apply h q hq
    intro r hr hU
    exact hn ⟨r, hr, hU⟩
  · intro h q hq hn
    exact hn q (R.refl q) (U.lower hq h)

theorem sup_le_iff (S : Regular R → Prop) :
    (sup S).Le U ↔ ∀ V, S V → V.Le U := by
  constructor
  · intro h V hV p hp
    apply h p
    exact fun q hq => ⟨q, R.refl q, V, hV, V.lower hq hp⟩
  · intro h p hp
    apply U.closed p
    intro q hq
    obtain ⟨r, hr, V, hV, hpV⟩ := hp q hq
    exact ⟨r, hr, h V hV r hpV⟩

theorem iSup_le_iff {I : Sort v} (f : I → Regular R) :
    (iSup f).Le U ↔ ∀ i, (f i).Le U := by
  constructor
  · intro h i p hp
    exact h p (fun q hq => ⟨q, R.refl q, i, (f i).lower hq hp⟩)
  · intro h p hp
    apply U.closed p
    intro q hq
    obtain ⟨r, hr, i, hi⟩ := hp q hq
    exact ⟨r, hr, h i r hi⟩

/-- The canonical map factors through the separative quotient; injectivity of
the original preorder is deliberately not asserted. -/
def condition (p : P) : Regular R := closure (fun q => R.le q p)

theorem condition_mem (p : P) : (condition (R := R) p).mem p :=
  fun q hq => ⟨q, R.refl q, hq⟩

theorem condition_le_iff (p : P) : (condition p).Le U ↔ U.mem p := by
  constructor
  · intro h; exact h p (condition_mem p)
  · intro h q hq
    apply U.closed q
    intro r hr
    obtain ⟨s, hs, hsp⟩ := hq r hr
    exact ⟨s, hs, U.lower hsp h⟩

theorem condition_mono {p q : P} (h : R.le p q) :
    (condition (R := R) p).Le (condition q) :=
  (condition_le_iff _ p).mpr (fun r hr => ⟨r, R.refl r, R.trans hr h⟩)

theorem condition_ne_bot (p : P) : condition (R := R) p ≠ bot := by
  intro h
  have hp := condition_mem (R := R) p
  rw [h] at hp
  exact hp

theorem nonzero_iff : U ≠ bot ↔ ∃ p, U.mem p := by
  classical
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    exact h (ext U bot (fun p => ⟨fun hp => hn ⟨p, hp⟩, False.elim⟩))
  · rintro ⟨p, hp⟩ h
    rw [h] at hp
    exact hp

theorem condition_dense (h : U ≠ bot) : ∃ p, (condition p).Le U := by
  obtain ⟨p, hp⟩ := (nonzero_iff U).mp h
  exact ⟨p, (condition_le_iff U p).mpr hp⟩

theorem iSup_eq_top_iff {I : Sort v} (f : I → Regular R) :
    iSup f = top ↔ ∀ p, ∃ q, R.le q p ∧ ∃ i, (f i).mem q := by
  constructor
  · intro h p
    have hp : (iSup f).mem p := by rw [h]; trivial
    exact hp p (R.refl p)
  · intro h
    apply ext
    intro p
    exact ⟨fun _ => True.intro, fun _ q _ => h q⟩

end Regular
end InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular
