module

import Mathlib

open Metric Set Relation Complex Bornology

/-- Subspace definition of Hawaiian Earring -/
noncomputable def p (n : ℕ) : ℂ := ⟨1 / n, 0⟩
noncomputable def r (n : ℕ) : ℝ := 1 / n
noncomputable def H1 : Set ℂ := ⋃ n, sphere (p n) (r n)


/-- Relation with collapsing a set into one point. Could be added to mathlib -/
def RelOnSet {X : Type} (D : Set X) : X → X → Prop := ReflGen (fun x y ↦ (x ∈ D ∧ y ∈ D))

lemma equivalence_relOnSet {X : Type} (D : Set X) : Equivalence (RelOnSet D) := by
  unfold RelOnSet
  constructor <;> grind

/-- Suspension definition of Hawaiian Earring -/
noncomputable def X : Set ℝ := { 1 / n | n : ℕ }
@[reducible]
def Y := X × (Icc (0 : ℝ) 1)

def D : Set Y := { y : Y | y.1 = (0 : ℝ) ∨ y.2 = 0 ∨ y.2 = 1 }

def RelY := RelOnSet D

instance setoidY : Setoid Y where
  r := RelY
  iseqv := equivalence_relOnSet D

@[reducible]
def H2 := Quotient setoidY


-- H1 is Hausdorff 
lemma H1isHausdorff : T2Space H1 := inferInstance



-- H1 is closed, bounded and compact

noncomputable def Ear (m : ℕ) : Set ℂ :=
  (⋃ n : Fin (m + 1), sphere (p n) (r n)) ∪ closedBall (p (m + 2)) (r (m + 2))

lemma isClosed_Ear (m : ℕ) : IsClosed (Ear m) := by
  refine IsClosed.union ?_ ?_
  · apply isClosed_iUnion_of_finite 
    intro k
    exact isClosed_sphere
  · exact isClosed_closedBall

lemma isBounded_Ear (m : ℕ) : IsBounded (Ear m) := by
  refine IsBounded.union ?_ ?_
  · rw [isBounded_iUnion]
    intro k
    exact isBounded_sphere
  · exact isBounded_closedBall

lemma isCompact_Ear (m : ℕ) : CompactSpace (Ear m) := by
  rw [← isCompact_iff_compactSpace]
  exact isCompact_of_isClosed_isBounded (isClosed_Ear m) (isBounded_Ear m)


lemma Ear_union_H1_closedBall (m : ℕ) : Ear (m : ℕ) = H1 ∪ closedBall (p (m + 2)) (r (m + 2)) := by
  sorry

lemma H1_inter_Ear : H1 = ⋂ n, Ear n := by
    simp only [Ear_union_H1_closedBall]
    rw [← union_iInter]
    have h1 : ⋂ i, closedBall (p (i + 2)) (r (i + 2)) = {⟨0,0⟩} := by
      sorry
    rw [h1]
    symm
    apply union_eq_self_of_subset_right
    apply subset_iUnion_of_subset 0
    simp [p, r]

lemma H1isClosed : IsClosed H1 := by
  rw [H1_inter_Ear]
  apply isClosed_iInter
  intro m
  exact isClosed_Ear m

lemma H1isBounded : IsBounded H1 := by
  rw [H1_inter_Ear]
  exact Bornology.IsBounded.subset (isBounded_Ear 0) (iInter_subset Ear 0)

lemma H1isCompact : CompactSpace H1 := by
  rw [← isCompact_iff_compactSpace]
  exact isCompact_of_isClosed_isBounded H1isClosed H1isBounded


-- H1 is PathConnected
lemma H1isPathConnected : PathConnectedSpace H1 := sorry

  

