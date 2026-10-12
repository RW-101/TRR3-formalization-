import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finsupp.Basic

set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
open scoped BigOperators Classical

noncomputable section

variable {X : Type*} [PseudoMetricSpace X]

def IsVRSimplex (ε : ℝ) (s : Finset X) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ ε

def VRComplex (ε : ℝ) : Set (Finset X) :=
  { s : Finset X | IsVRSimplex ε s }

theorem trr_resolution_monotonicity {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    VRComplex (X := X) ε₁ ⊆ VRComplex (X := X) ε₂ := by
  intro s hs
  dsimp [VRComplex, IsVRSimplex] at hs ⊢
  intro x hx y hy
  have hdist := hs x hx y hy
  exact le_trans hdist h

theorem trr_simplex_downward_closed {ε : ℝ} {s t : Finset X}
    (ht : t ∈ VRComplex (X := X) ε) (hst : s ⊆ t) :
    s ∈ VRComplex (X := X) ε := by
  dsimp [VRComplex, IsVRSimplex] at ht ⊢
  intro x hx y hy
  exact ht x (hst hx) y (hst hy)

abbrev Chain (X : Type*) := Finset X →₀ ZMod 2

def boundarySimplex (s : Finset X) : Chain X :=
  s.sum (fun v => Finsupp.single (s.erase v) (1 : ZMod 2))

def boundaryChain (c : Chain X) : Chain X :=
  c.sum (fun s _ => boundarySimplex s)

/-- Симметрия двукратного удаления вершин симплекса -/
lemma simplex_face2_comm (s : Finset X) (u v : X) :
    (s.erase u).erase v = (s.erase v).erase u :=
  Finset.erase_right_comm

/-- Nilpotency of boundary operator on simplices: ∂² = 0 over 𝔽₂ -/
theorem boundary_boundary_simplex (s : Finset X) :
    boundaryChain (boundarySimplex s) = 0 := by
  sorry

/-- Nilpotency of boundary operator on arbitrary chains: ∂² = 0 over 𝔽₂ -/
theorem boundary_sq_zero (c : Chain X) :
    boundaryChain (boundaryChain c) = 0 := by
  sorry

#print axioms trr_resolution_monotonicity
#print axioms trr_simplex_downward_closed
