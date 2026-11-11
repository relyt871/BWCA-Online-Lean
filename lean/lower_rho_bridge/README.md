# Lean entry point for `lem:lower-rho-bridge`

This directory is the stable entry point for the lower-rho bridge lemma.

## What Lean proves

The paper-facing theorem is

```lean
theorem lower_rho_bridge_D_gt_one {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 31 / 100) :
    1 < D rho 1
```

This is the complete statement of the paper lemma. It combines the checked
identity between `D rho 1` and its factorial series with the theorem

```lean
theorem lower_rho_bridge_series_entry_point {rho : ℝ}
    (he : (19 / 7 : ℝ) < Real.exp 1)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 31 / 100) :
    1 < lowerRhoBridgeDSeries rho
```

which checks the alternating-series proof for the series expression
corresponding to equation `(25')` in the paper. The assumption `he` is the
elementary numerical bound `e > 19/7`; the unconditional theorem derives this
bound from Mathlib.

## How to check it

From the `lean` directory:

```bash
lake exe cache get
lake build
lake env lean lower_rho_bridge/LowerRhoBridge.lean
```
