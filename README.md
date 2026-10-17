# TRR3 Formalization in Lean 4

Machine-checked formalization of simplicial chain complexes over F_2 and metric filtration invariants for Relational Resolution Theory (TRR 3.0) in Lean 4 (Mathlib4).

## Verified Theorems (Zero sorry)

- `trr_resolution_monotonicity`: Metric filtration monotonicity
- `trr_simplex_downward_closed`: Simplicial downward closure
- `zmod2_add_self`: Characteristic 2 scalar involution (x + x = 0)
- `chain_add_self`: Chain addition involution (c + c = 0)
- `boundary_boundary_simplex`: Simplex boundary nilpotency (d(d(s)) = 0)
- `boundary_sq_zero`: Chain boundary nilpotency (d^2(c) = 0)
- `boundary_is_cycle`: Cycle inclusion (im d <= ker d)
- `boundaryChain_add`: Linearity of boundary operator (d(c1 + c2) = d(c1) + d(c2))
- `boundarySimplex_card`: Grading shift on boundary faces (|t| + 1 = |s|)
- `boundarySimplex_closed`: Subcomplex invariance under boundary operator

## Axiom Footprint

All 10 declarations depend solely on `[propext, Classical.choice, Quot.sound]`.
