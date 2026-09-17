import InfinitaryCombinatorics.FinIntersection

/-! Bijection invariance; callers need not depend on a particular coding of their base set. -/
namespace InfinitaryCombinatorics
open Set
universe u v
variable {X : Type u} {Y : Type v}

theorem family_image_inverse (e : X ≃ Y) (A : Set (Set X)) :
    Set.image (Set.image e.symm) (Set.image (Set.image e) A) = A := by
  have h : ∀ a : Set X, e.symm '' (e '' a) = a := by
    intro a
    simp [Set.image_image]
  ext a
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, hba⟩
    rw [h] at hba
    exact hba ▸ hb
  · intro ha
    exact ⟨e '' a, ⟨a, ha, rfl⟩, h a⟩

theorem finIntersecting_equiv (e : X ≃ Y) (A : Set (Set X)) :
    R0.FinIntersecting (Set.image e '' A) ↔ R0.FinIntersecting A := by
  constructor
  · exact R0.finIntersecting_of_map e.toEmbedding
  · intro hA
    apply R0.finIntersecting_of_map e.symm.toEmbedding
    simpa only [Equiv.coe_toEmbedding, family_image_inverse] using hA

theorem almostDisjoint_equiv (e : X ≃ Y) (A : Set (Set X)) :
    R0.AlmostDisjoint (Set.image e '' A) ↔ R0.AlmostDisjoint A := by
  constructor
  · intro h
    have h' := R0.almostDisjoint_map e.symm.toEmbedding h
    simpa only [Equiv.coe_toEmbedding, family_image_inverse] using h'
  · exact R0.almostDisjoint_map e.toEmbedding

end InfinitaryCombinatorics
