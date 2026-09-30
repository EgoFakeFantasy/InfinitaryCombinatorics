import Formalizations.FIMAD.InternalSemantics
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.EquivFin

/-! Interpretation of the membership-language primitives in mathlib's standard
universe of well-founded sets. These identifications concern this particular
universe; they do not assert that an arbitrary model has standard natural numbers. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.Standard
universe u

abbrev mem : ZFSet.{u} → ZFSet.{u} → Prop := fun x y => x ∈ y

/-- The finite von Neumann ordinals in the standard set universe. -/
def nat : ℕ → ZFSet.{u}
  | 0 => ∅
  | n + 1 => insert (nat n) (nat n)

theorem nat_eq_mk (n : ℕ) : nat.{u} n = ZFSet.mk (PSet.ofNat n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change insert (nat n) (nat n) = _
    rw [ih]
    rfl

theorem mem_omega {x : ZFSet.{u}} : x ∈ ZFSet.omega ↔ ∃ n, x = nat n := by
  induction x using Quotient.inductionOn with
  | h x =>
    constructor
    · rintro ⟨⟨n⟩, h⟩
      exact ⟨n, (ZFSet.sound h).trans (nat_eq_mk n).symm⟩
    · rintro ⟨n, h⟩
      exact ⟨⟨n⟩, ZFSet.exact (h.trans (nat_eq_mk n))⟩

theorem nat_mem_omega (n : ℕ) : nat.{u} n ∈ ZFSet.omega := mem_omega.mpr ⟨n, rfl⟩

theorem mem_nat {x : ZFSet.{u}} (n : ℕ) : x ∈ nat n ↔ ∃ k < n, x = nat k := by
  induction n with
  | zero => simp [nat]
  | succ n ih =>
    simp only [nat, ZFSet.mem_insert_iff, ih]
    constructor
    · rintro (h | ⟨k, hk, rfl⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨k, Nat.lt_succ_of_lt hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with h | rfl
      · exact Or.inr ⟨k, h, rfl⟩
      · exact Or.inl rfl

theorem nat_injective : Function.Injective nat.{u} := by
  intro n m h
  rcases lt_trichotomy n m with hlt | heq | hgt
  · have hm := (mem_nat m).mpr ⟨n, hlt, h.symm⟩
    exact False.elim (ZFSet.mem_irrefl _ hm)
  · exact heq
  · have hn := (mem_nat n).mpr ⟨m, hgt, h⟩
    exact False.elim (ZFSet.mem_irrefl _ hn)

theorem finite_nat (n : ℕ) : (nat.{u} n : Set ZFSet).Finite := by
  induction n with
  | zero => simp [nat]
  | succ n ih => simpa [nat] using ih.insert (nat n)

theorem empty_iff (a : ZFSet.{u}) : Internal.Empty mem a ↔ a = ∅ := by
  simp only [Internal.Empty, mem, ZFSet.ext_iff, ZFSet.notMem_empty, iff_false]

theorem succ_iff (b a : ZFSet.{u}) : Internal.Succ mem b a ↔ b = insert a a := by
  simp only [Internal.Succ, mem, ZFSet.ext_iff, ZFSet.mem_insert_iff, or_comm]

theorem omega : Internal.Omega mem ZFSet.omega.{u} := by
  constructor
  · exact ⟨⟨∅, (empty_iff ∅).mpr rfl, ZFSet.omega_zero⟩,
      fun x hx => ⟨insert x x, (succ_iff _ _).mpr rfl, ZFSet.omega_succ hx⟩⟩
  · intro a ha x hx
    obtain ⟨n, rfl⟩ := mem_omega.mp hx
    induction n with
    | zero =>
      obtain ⟨z, hz, hza⟩ := ha.1
      simpa [nat, (empty_iff z).mp hz] using hza
    | succ n ih =>
      obtain ⟨y, hy, hya⟩ := ha.2 (nat n) (ih (nat_mem_omega n))
      simpa [nat, (succ_iff _ _).mp hy] using hya

theorem singleton_iff (s a : ZFSet.{u}) : Internal.Singleton mem s a ↔ s = {a} := by
  simp only [Internal.Singleton, mem, ZFSet.ext_iff, ZFSet.mem_singleton]

theorem unorderedPair_iff (s a b : ZFSet.{u}) :
    Internal.UnorderedPair mem s a b ↔ s = {a, b} := by
  simp only [Internal.UnorderedPair, mem, ZFSet.ext_iff, ZFSet.mem_pair]

theorem pair_iff (p a b : ZFSet.{u}) : Internal.Pair mem p a b ↔ p = ZFSet.pair a b := by
  simp only [Internal.Pair, singleton_iff, unorderedPair_iff]
  simp [ZFSet.pair]

theorem value_iff (f a b : ZFSet.{u}) : Internal.Value mem f a b ↔ ZFSet.pair a b ∈ f := by
  simp [Internal.Value, pair_iff, mem]

theorem value_map (g : ZFSet.{u} → ZFSet.{u}) [ZFSet.Definable₁ g] (a x y : ZFSet.{u}) :
    Internal.Value mem (ZFSet.map g a) x y ↔ x ∈ a ∧ g x = y := by
  simp [value_iff, ZFSet.pair_inj]

theorem functionOn_map (g : ZFSet.{u} → ZFSet.{u}) [ZFSet.Definable₁ g] (a : ZFSet.{u}) :
    Internal.FunctionOn mem (ZFSet.map g a) a := by
  constructor
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := ZFSet.mem_map.mp hp
    exact ⟨x, g x, hx, (pair_iff _ _ _).mpr rfl⟩
  · intro x hx
    exact ⟨g x, (value_map _ _ _ _).mpr ⟨hx, rfl⟩,
      fun z hz => ((value_map _ _ _ _).mp hz).2.symm⟩

theorem injection_map (g : ZFSet.{u} → ZFSet.{u}) [ZFSet.Definable₁ g]
    (a b : ZFSet.{u}) (hmem : ∀ x ∈ a, g x ∈ b)
    (hinj : Set.InjOn g (a : Set ZFSet)) : Internal.Injection mem (ZFSet.map g a) a b := by
  refine ⟨functionOn_map g a, ?_, ?_⟩
  · intro x y h
    obtain ⟨hx, rfl⟩ := (value_map _ _ _ _).mp h
    exact hmem x hx
  · intro x z y h₁ h₂
    obtain ⟨hx, hy⟩ := (value_map _ _ _ _).mp h₁
    obtain ⟨hz, hy'⟩ := (value_map _ _ _ _).mp h₂
    exact hinj hx hz (hy.trans hy'.symm)

/-- The target of an internal injection bounds the external cardinality of its domain. -/
theorem finite_of_injection {f a b : ZFSet.{u}} (h : Internal.Injection mem f a b)
    (hb : (b : Set ZFSet).Finite) : (a : Set ZFSet).Finite := by
  classical
  let g : ↥(a : Set ZFSet) → ↥(b : Set ZFSet) := fun x =>
    ⟨(h.1.2 x x.property).choose, h.2.1 _ _ (h.1.2 x x.property).choose_spec.1⟩
  have hg : Function.Injective g := by
    intro x z heq
    have hv : (h.1.2 x x.property).choose = (h.1.2 z z.property).choose :=
      congrArg Subtype.val heq
    apply Subtype.ext (h.2.2 _ _ _ (h.1.2 x x.property).choose_spec.1 ?_)
    rw [hv]
    exact (h.1.2 z z.property).choose_spec.1
  letI := hb.to_subtype
  letI := Finite.of_injective g hg
  exact Set.toFinite _

/-- Internal finiteness and ordinary finiteness coincide in the standard universe. -/
theorem finite_iff (a : ZFSet.{u}) :
    Internal.Finite mem ZFSet.omega a ↔ (a : Set ZFSet).Finite := by
  classical
  constructor
  · rintro ⟨n, hn, f, hf⟩
    obtain ⟨k, rfl⟩ := mem_omega.mp hn
    exact finite_of_injection hf (finite_nat k)
  · intro ha
    letI := ha.fintype
    let e := Fintype.equivFin (a : Set ZFSet)
    let g : ZFSet → ZFSet := fun x => if hx : x ∈ a then nat (e ⟨x, hx⟩).val else ∅
    letI : ZFSet.Definable₁ g := Classical.allZFSetDefinable _
    refine ⟨nat (Fintype.card (a : Set ZFSet)), nat_mem_omega _, ZFSet.map g a,
      injection_map g a _ ?_ ?_⟩
    · intro x hx
      exact (mem_nat _).mpr ⟨(e ⟨x, hx⟩).val, (e ⟨x, hx⟩).isLt, by simp [g, hx]⟩
    · intro x hx y hy hxy
      change x ∈ a at hx
      change y ∈ a at hy
      have hval := nat_injective (by simpa [g, hx, hy] using hxy)
      exact congrArg Subtype.val (e.injective (Fin.ext hval))

theorem infinite_iff (a : ZFSet.{u}) :
    Internal.Infinite mem ZFSet.omega a ↔ (a : Set ZFSet).Infinite :=
  not_congr (finite_iff a)

end InfinitaryCombinatorics.Formalizations.FIMAD.Standard
