import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

variable {X : Type*} [PseudoMetricSpace X]

/-- Предикат симплекса Вьеториса–Рипса на масштабе разрешения ε -/
def IsVRSimplex (ε : ℝ) (s : Finset X) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ ε

/-- Комплекс Вьеториса–Рипса на уровне разрешения ε -/
def VRComplex (ε : ℝ) : Set (Finset X) :=
  { s : Finset X | IsVRSimplex ε s }

/-- Теорема 1: Монотонность фильтрации TRR 3.0 по масштабу разрешения -/
theorem trr_resolution_monotonicity {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    VRComplex (X := X) ε₁ ⊆ VRComplex (X := X) ε₂ := by
  intro s hs
  dsimp [VRComplex, IsVRSimplex] at hs ⊢
  intro x hx y hy
  have hdist := hs x hx y hy
  exact le_trans hdist h

/-- Теорема 2: Нисходящая замкнутость (подмножество симплекса является симплексом) -/
theorem trr_simplex_downward_closed {ε : ℝ} {s t : Finset X}
    (ht : t ∈ VRComplex (X := X) ε) (hst : s ⊆ t) :
    s ∈ VRComplex (X := X) ε := by
  dsimp [VRComplex, IsVRSimplex] at ht ⊢
  intro x hx y hy
  exact ht x (hst hx) y (hst hy)

#print axioms trr_resolution_monotonicity
#print axioms trr_simplex_downward_closed
