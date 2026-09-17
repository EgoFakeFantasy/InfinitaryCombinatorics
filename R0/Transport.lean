import R0.Basic

namespace R0
open Set

universe u v

def mapBlocks {X : Type u} {Y : Type v} (e : X ↪ Y) (C : FinSequence X) :
    FinSequence Y where
  block n := e '' C.block n
  finite n := (C.finite n).image e
  nonempty n := (C.nonempty n).image e
  disjoint n m hnm := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, heq⟩
    have hzx : z = x := e.injective heq
    subst z
    exact Set.disjoint_left.mp (C.disjoint n m hnm) hx hz

lemma trace_map {X : Type u} {Y : Type v} (e : X ↪ Y) (C : FinSequence X)
    (a : Set X) : trace (mapBlocks e C) (e '' a) = trace C a := by
  ext n
  constructor
  · rintro ⟨y, ⟨x, hx, he⟩, z, hz, he'⟩
    have hxz : x = z := e.injective (he.trans he'.symm)
    subst z
    exact ⟨x, hx, hz⟩
  · rintro ⟨x, hx, hC⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, ⟨x, hC, rfl⟩⟩

lemma retainedTraces_map {X : Type u} {Y : Type v} (e : X ↪ Y)
    (C : FinSequence X) (A : Set (Set X)) (i : Set ℕ) :
    retainedTraces (mapBlocks e C) (Set.image e '' A) i = retainedTraces C A i := by
  ext t
  constructor
  · rintro ⟨ht, _, ⟨a, ha, rfl⟩, heq⟩
    exact ⟨ht, a, ha, by simpa only [trace_map] using heq⟩
  · rintro ⟨ht, a, ha, heq⟩
    exact ⟨ht, e '' a, ⟨a, ha, rfl⟩, by simpa only [trace_map] using heq⟩

lemma finIntersecting_of_map {X : Type u} {Y : Type v} (e : X ↪ Y)
    {A : Set (Set X)} (h : FinIntersecting (Set.image e '' A)) : FinIntersecting A := by
  intro C
  obtain ⟨i, hi, hC⟩ := h (mapBlocks e C)
  exact ⟨i, hi, by simpa only [retainedTraces_map] using hC⟩

lemma not_finIntersecting_map {X : Type u} {Y : Type v} (e : X ↪ Y)
    {A : Set (Set X)} (h : ¬ FinIntersecting A) :
    ¬ FinIntersecting (Set.image e '' A) := fun h' => h (finIntersecting_of_map e h')

lemma almostDisjoint_map {X : Type u} {Y : Type v} (e : X ↪ Y)
    {A : Set (Set X)} (h : AlmostDisjoint A) : AlmostDisjoint (Set.image e '' A) := by
  refine ⟨Set.Infinite.image e.injective.image_injective.injOn h.1, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact Set.Infinite.image e.injective.injOn (h.2.1 a ha)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    have hne : a ≠ b := fun heq => hab (congrArg (Set.image e) heq)
    rw [← Set.image_inter e.injective]
    exact (h.2.2 a ha b hb hne).image e

end R0
