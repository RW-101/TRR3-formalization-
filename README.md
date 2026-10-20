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
---

## 2. Verified Benchmark Results ($N=20$, 1,160 Epochs, Strict LOSO-CV)

| Architecture & Strictly Causal Calibration Budget $k$ | Calib Time | Cohen's $d$ | Full Pool AUC | Balanced Holdout AUC | Mean Subject AUC ($\pm\text{SE}$) | Subject Wilcoxon $p$ (Pos) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| **1. Stage 6 Global $H_0$ (Baseline 4s ImCoh, 20 ch)** | $0\text{ s } (k=0)$ | $-0.60$ | $0.650$ | $0.626$ | $0.652 \pm 0.051$ | $7.30 \times 10^{-3}$ ($16/20$) |
| **2. Pure Topo: Posterior $\mathrm{rLagImCoh}$ $H_0$ (8 ch)** | $0\text{ s } (k=0)$ | $-0.85$ | $0.780$ | $0.764$ | $0.905 \pm 0.029$ | $3.81 \times 10^{-6}$ ($19/20$) |
| **3. Pure Topo: Spatial Gradient ($\mathcal{K}_{\mathrm{post}} - \mathcal{K}_{\mathrm{ant}}$) $H_0$** | $0\text{ s } (k=0)$ | $-0.82$ | **0.837** | **0.819** | **0.927 $\pm$ 0.022** | **$1.91 \times 10^{-6}$** (**20/20**) |
| **Pure Topological TRR ($\mathbb{F}_2$ only, $k=0$)** | $0\text{ s}$ | $+0.82$ | $0.830$ | $0.812$ | $0.927 \pm 0.022$ | $1.91 \times 10^{-6}$ ($20/20$) |
| **Pure Topological TRR ($\mathbb{F}_2$ only, $k=1$)** | $4\text{ s}$ | $+0.85$ | $0.831$ | $0.811$ | $0.929 \pm 0.021$ | $1.91 \times 10^{-6}$ ($20/20$) |
| **Pure Topological TRR ($\mathbb{F}_2$ only, $k=2$)** | $6\text{ s}$ | $+0.86$ | $0.836$ | $0.815$ | $0.929 \pm 0.021$ | $1.91 \times 10^{-6}$ ($20/20$) |
| **Pure Topological TRR ($\mathbb{F}_2$ only, $k=3$)** | **$8\text{ s}$** | **$+0.87$** | **0.840** | **0.818** | **0.929 $\pm$ 0.021** | **$1.91 \times 10^{-6}$** (**20/20**) |
| **Pure Topological TRR ($\mathbb{F}_2$ only, $k=5$)** | $12\text{ s}$ | $+0.89$ | $0.850$ | $0.827$ | $0.929 \pm 0.020$ | $1.91 \times 10^{-6}$ ($20/20$) |
| **Pure Topological TRR ($\mathbb{F}_2$ only, $k=10$)** | **$22\text{ s}$** | **$+0.88$** | **0.874** | **0.852** | **0.928 $\pm$ 0.021** | **$1.91 \times 10^{-6}$** (**20/20**) |
| **Pure Topological TRR ($\mathbb{F}_2$ only, $k=29$)** | $60\text{ s}$ | $+1.01$ | **0.895** | N/A (Full) | $0.915 \pm 0.024$ | $1.91 \times 10^{-6}$ ($20/20$) |
| **Hybrid SpecTopo TRR (Topo + Power, $k=0$)** | **$0\text{ s}$** | **$+1.68$** | **0.869** | **0.856** | **0.955 $\pm$ 0.013** | **$1.91 \times 10^{-6}$** (**20/20**) |
| **Hybrid SpecTopo TRR (Topo + Power, $k=1$)** | $4\text{ s}$ | $+1.72$ | $0.874$ | $0.861$ | $0.955 \pm 0.013$ | $1.91 \times 10^{-6}$ ($20/20$) |
| **Hybrid SpecTopo TRR (Topo + Power, $k=2$)** | $6\text{ s}$ | $+1.83$ | $0.887$ | $0.874$ | $0.955 \pm 0.013$ | $1.91 \times 10^{-6}$ ($20/20$) |
| **Hybrid SpecTopo TRR (Topo + Power, $k=3$)** | **$8\text{ s}$** | **$+1.91$** | **0.897** | **0.883** | **0.955 $\pm$ 0.013** | **$1.91 \times 10^{-6}$** (**20/20**) |
| **Hybrid SpecTopo TRR (Topo + Power, $k=5$)** | $12\text{ s}$ | $+2.01$ | $0.908$ | $0.893$ | $0.956 \pm 0.012$ | $1.91 \times 10^{-6}$ ($20/20$) |
| **Hybrid SpecTopo TRR (Topo + Power, $k=10$)** | **$22\text{ s}$** | **$+2.20$** | **0.928** | **0.914** | **0.957 $\pm$ 0.012** | **$1.91 \times 10^{-6}$** (**20/20**) |
| **Hybrid SpecTopo TRR (Topo + Power, $k=29$)** | **$60\text{ s}$** | **$+2.34$** | **0.954** | N/A (Full) | **0.957 $\pm$ 0.013** | **$1.91 \times 10^{-6}$** (**20/20**) |

---

## 3. Reproducing the Benchmark

```bash
pip install -r requirements.txt
python benchmarks/trr_stage7_flawless_N20.py
