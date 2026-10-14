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

/-- Тождество сложения над полем характеристики 2 -/
lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

/-- В пространстве цепей над 𝔽₂ удвоение любого элемента даёт нулевую цепь -/
lemma chain_add_self (c : Chain X) : c + c = 0 := by
  ext s
  simp [zmod2_add_self]

set_option linter.deprecated false

lemma zmod2_eq_one_of_ne_zero (x : ZMod 2) (h : x ≠ 0) : x = 1 := by
  revert x h
  decide

lemma chain_sum_eq_sum_mul (c : Chain X) (f : Finset X → ZMod 2) :
    c.sum (fun a _ => f a) = c.sum (fun a b => b * f a) := by
  unfold Finsupp.sum
  refine Finset.sum_congr rfl (fun a ha => ?_)
  change f a = c a * f a
  rw [zmod2_eq_one_of_ne_zero (c a) (Finsupp.mem_support_iff.mp ha), one_mul]

lemma boundarySimplex_sum_mul (s : Finset X) (f : Finset X → ZMod 2) :
    (boundarySimplex s).sum (fun a b => b * f a) = s.sum (fun u => f (s.erase u)) := by
  unfold boundarySimplex
  rw [← Finsupp.sum_finsetSum_index (by intro a; exact zero_mul _)
    (by intro a b1 b2; exact add_mul _ _ _)]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have h_single : (Finsupp.single (s.erase u) (1 : ZMod 2)).sum (fun a b => b * f a) =
      (1 : ZMod 2) * f (s.erase u) :=
    Finsupp.sum_single_index (zero_mul (f (s.erase u)))
  rw [h_single, one_mul]

lemma boundarySimplex_apply (s : Finset X) (t : Finset X) :
    boundarySimplex s t = s.sum (fun v => if s.erase v = t then (1 : ZMod 2) else 0) := by
  dsimp [boundarySimplex]
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]

lemma sum_erase_eq_ite (s : Finset X) (x : X) (hx : x ∈ s) (f : X → ZMod 2) :
    (s.erase x).sum f = s.sum (fun v => if v = x then 0 else f v) := by
  have hx_not : x ∉ s.erase x := fun h => (Finset.mem_erase.mp h).1 rfl
  have h_ins : (insert x (s.erase x)).sum (fun v => if v = x then 0 else f v) =
      s.sum (fun v => if v = x then 0 else f v) := by
    rw [Finset.insert_erase hx]
  rw [← h_ins, Finset.sum_insert hx_not, if_pos rfl, zero_add]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  rw [if_neg (Finset.mem_erase.mp hv).1]

lemma sum_symm_zero (s : Finset X) (F : X → X → ZMod 2)
    (h_diag : ∀ x, F x x = 0) (h_symm : ∀ x y, F x y = F y x) :
    s.sum (fun x => s.sum (fun y => F x y)) = 0 := by
  refine Finset.induction_on s (by simp) (fun a s ha ih => ?_)
  rw [Finset.sum_insert ha, Finset.sum_insert ha, h_diag a, zero_add]
  have h_inner : s.sum (fun x => (insert a s).sum (fun y => F x y)) =
      s.sum (fun x => F a x) + s.sum (fun x => s.sum (fun y => F x y)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_insert ha, h_symm x a]
  rw [h_inner, ih, add_zero, zmod2_add_self]

theorem boundary_boundary_simplex (s : Finset X) :
    boundaryChain (boundarySimplex s) = 0 := by
  ext t
  simp only [Finsupp.zero_apply]
  dsimp [boundaryChain]
  rw [Finsupp.sum_apply]
  rw [chain_sum_eq_sum_mul]
  rw [boundarySimplex_sum_mul]
  simp_rw [boundarySimplex_apply]
  have h_step1 : s.sum (fun x => (s.erase x).sum (fun v => if (s.erase x).erase v = t then (1 : ZMod 2) else 0)) =
      s.sum (fun x => s.sum (fun v => if v = x then 0 else if (s.erase x).erase v = t then (1 : ZMod 2) else 0)) := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    exact sum_erase_eq_ite s x hx _
  rw [h_step1]
  refine sum_symm_zero s (fun x v => if v = x then 0 else if (s.erase x).erase v = t then (1 : ZMod 2) else 0) ?_ ?_
  · intro x
    simp
  · intro x y
    by_cases hxy : y = x
    · subst hxy
      rfl
    · have hyx : x ≠ y := fun h => hxy h.symm
      rw [if_neg hxy, if_neg hyx, simplex_face2_comm]

lemma boundaryChain_eq_support_sum (c : Chain X) :
    boundaryChain c = c.support.sum (fun s => boundarySimplex s) := rfl

lemma boundaryChain_apply_mul (d : Chain X) (t : Finset X) :
    boundaryChain d t = d.sum (fun a b => b * boundarySimplex a t) := by
  dsimp [boundaryChain]
  rw [Finsupp.sum_apply, chain_sum_eq_sum_mul]

theorem boundary_sq_zero (c : Chain X) :
    boundaryChain (boundaryChain c) = 0 := by
  ext t
  simp only [Finsupp.zero_apply]
  rw [boundaryChain_apply_mul (boundaryChain c) t, boundaryChain_eq_support_sum c]
  rw [<- Finsupp.sum_finsetSum_index (by intro a; exact zero_mul _)
    (by intro a b1 b2; exact add_mul _ _ _)]
  refine Finset.sum_eq_zero (fun s _ => ?_)
  rw [<- boundaryChain_apply_mul (boundarySimplex s) t]
  rw [boundary_boundary_simplex s, Finsupp.zero_apply]

#print axioms trr_resolution_monotonicity
#print axioms trr_simplex_downward_closed
#print axioms zmod2_add_self
#print axioms chain_add_self
#print axioms boundary_boundary_simplex
#print axioms boundary_sq_zero
