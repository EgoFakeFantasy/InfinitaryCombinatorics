import FIMADModels.PosetCompletion

/-! Exact natural-number and real names over the constructed completion.
Different ground naturals have bottom equality value; every sequence of Boolean
membership coefficients is realized by an actual graph name for a subset of omega. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular
open YesMetaZFC.Model.Boolean
open BV_graph
universe u
variable {P : Type u} (R : Order P)

theorem natural_mem_of_lt {n m : Nat} (h : n < m) :
    bv_mem (algebra R) (natural R n) (natural R m) = (algebra R).top := by
  apply ((algebra R).top_le_iff _).mp
  change (algebra R).le _
    (bv_mem (algebra R) (natural R n) (omega_piece (algebra R) (List.replicate m PUnit.unit)))
  rw [omega_piece_mem]
  have hn : (List.replicate n (PUnit.unit : PUnit.{u+1})).length <
      (List.replicate m (PUnit.unit : PUnit.{u+1})).length := by simpa using h
  have hk := (algebra R).le_iSup
    (fun b : {b : List PUnit.{u+1} // b.length < (List.replicate m PUnit.unit).length} =>
      bv_eq (algebra R) (natural R n) (omega_piece (algebra R) b.1))
    ⟨List.replicate n PUnit.unit, hn⟩
  simpa only [natural, eq_refl] using hk

theorem natural_self_mem (n : Nat) :
    bv_mem (algebra R) (natural R n) (natural R n) = (algebra R).bot := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    apply (algebra R).le_antisymm _ ((algebra R).bot_le _)
    change (algebra R).le
      (bv_mem (algebra R) (natural R n) (omega_piece (algebra R) (List.replicate n PUnit.unit))) _
    rw [omega_piece_mem, (algebra R).iSup_le_iff]
    intro b
    have hb : b.1.length < n := by simpa using b.2
    have he : b.1 = List.replicate b.1.length PUnit.unit :=
      List.ext_getElem (by simp) (fun _ _ _ => Subsingleton.elim _ _)
    have hk := mem_right (algebra R) (natural R b.1.length) (natural R n)
      (natural R b.1.length)
    rw [natural_mem_of_lt R hb, (algebra R).meet_top, ih b.1.length hb] at hk
    rw [he]
    exact hk

theorem natural_eq_of_ne {n m : Nat} (h : n ≠ m) :
    bv_eq (algebra R) (natural R n) (natural R m) = (algebra R).bot := by
  apply (algebra R).le_antisymm _ ((algebra R).bot_le _)
  rcases Nat.lt_or_gt_of_ne h with hlt | hgt
  · have hk := mem_right (algebra R) (natural R n) (natural R m) (natural R n)
    rw [natural_mem_of_lt R hlt, (algebra R).meet_top, natural_self_mem,
      eq_symm (algebra R) (natural R m)] at hk
    exact hk
  · have hk := mem_right (algebra R) (natural R m) (natural R n) (natural R m)
    rw [natural_mem_of_lt R hgt, (algebra R).meet_top, natural_self_mem] at hk
    exact hk

theorem natural_mem_of_ge {n m : Nat} (h : m ≤ n) :
    bv_mem (algebra R) (natural R n) (natural R m) = (algebra R).bot := by
  apply (algebra R).le_antisymm _ ((algebra R).bot_le _)
  change (algebra R).le
    (bv_mem (algebra R) (natural R n) (omega_piece (algebra R) (List.replicate m PUnit.unit))) _
  rw [omega_piece_mem, (algebra R).iSup_le_iff]
  intro b
  have hb : b.1.length < m := by simpa using b.2
  have he : b.1 = List.replicate b.1.length PUnit.unit :=
    List.ext_getElem (by simp) (fun _ _ _ => Subsingleton.elim _ _)
  rw [he]
  change (algebra R).le (bv_eq (algebra R) (natural R n) (natural R b.1.length)) _
  rw [natural_eq_of_ne R (Nat.ne_of_gt (Nat.lt_of_lt_of_le hb h))]
  exact (algebra R).le_refl _

/-- The usual internal assertion i <= G for natural-number names. -/
def atLeast (i : Nat) (G : BV_name (Regular R)) : Regular R :=
  (algebra R).join (bv_mem (algebra R) (natural R i) G)
    (bv_eq (algebra R) (natural R i) G)

/-- The semantic lower-bound premise on an enumeration implies that all its
smaller-value decisions have bottom truth value. -/
theorem small_value_eq_bot (G : BV_name (Regular R)) (i : Nat)
    (hG : atLeast R i G = (algebra R).top) {k : Nat} (hk : k < i) :
    bv_eq (algebra R) G (natural R k) = (algebra R).bot := by
  have hs : Stable (algebra R) (atLeast R i) :=
    stable_join (algebra R) (stable_set (algebra R) (natural R i))
      (stable_eq (algebra R) (natural R i))
  have h := hs G (natural R k)
  rw [hG, (algebra R).meet_top] at h
  change (algebra R).le _ ((algebra R).join
    (bv_mem (algebra R) (natural R i) (natural R k))
    (bv_eq (algebra R) (natural R i) (natural R k))) at h
  rw [natural_mem_of_ge R (Nat.le_of_lt hk), natural_eq_of_ne R (Nat.ne_of_gt hk)] at h
  have hz : (algebra R).le ((algebra R).join (algebra R).bot (algebra R).bot)
      (algebra R).bot := ((algebra R).join_le_iff _ _ _).mpr
        ⟨(algebra R).le_refl _, (algebra R).le_refl _⟩
  exact (algebra R).le_antisymm ((algebra R).le_trans h hz) ((algebra R).bot_le _)

/-- Different values of a single natural-number name cannot both be true. -/
theorem decisions_disjoint (G : BV_name (Regular R)) {n m : Nat} (h : n ≠ m) :
    (algebra R).meet (bv_eq (algebra R) G (natural R n))
      (bv_eq (algebra R) G (natural R m)) = (algebra R).bot := by
  apply (algebra R).le_antisymm _ ((algebra R).bot_le _)
  have ht := eq_trans (algebra R) (natural R n) G (natural R m)
  rw [eq_symm (algebra R) (natural R n), natural_eq_of_ne R h] at ht
  exact ht

/-- A genuine name for the real with the prescribed membership coefficients. -/
def real (b : Nat → Regular R) : BV_name (Regular R) :=
  root_sum (algebra R).toSup_order
    (fun n : ULift.{u} Nat => natural R n.down) (fun n => b n.down)

theorem real_mem (b : Nat → Regular R) (n : Nat) :
    bv_mem (algebra R) (natural R n) (real R b) = b n := by
  rw [real, sum_mem]
  apply (algebra R).le_antisymm
  · apply ((algebra R).iSup_le_iff _ _).mpr
    intro m
    by_cases h : n = m.down
    · rw [← h, eq_refl, (algebra R).meet_top]
      exact (algebra R).le_refl _
    · rw [natural_eq_of_ne R h, (algebra R).meet_bot]
      exact (algebra R).bot_le _
  · have hk := (algebra R).le_iSup
      (fun m : ULift.{u} Nat => (algebra R).meet (b m.down)
        (bv_eq (algebra R) (natural R n) (natural R m.down))) ⟨n⟩
    simpa only [eq_refl, BA_alg.meet_top] using hk

theorem real_subset_omega (b : Nat → Regular R) :
    subset (algebra R) (real R b) (omega (algebra R)) = (algebra R).top := by
  apply ((algebra R).top_le_iff _).mp
  apply ((algebra R).le_iInf_iff _ _).mpr
  intro G
  apply ((algebra R).valid_imp_iff _ _).mpr
  rw [real, sum_mem, (algebra R).iSup_le_iff]
  intro n
  apply (algebra R).le_trans ((algebra R).meet_le_right _ _)
  rw [omega_mem_eq]
  exact (algebra R).le_iSup (fun k : Nat => bv_eq (algebra R) G (natural R k)) n.down

end InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular
