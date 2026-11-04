module

import Mathlib

open Metric Set Relation

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

-- H1 is Compact
lemma H1isCompact : CompactSpace H1 := sorry

-- H1 is PathConnected
lemma H1isPathConnected : PathConnectedSpace H1 := sorry

  





