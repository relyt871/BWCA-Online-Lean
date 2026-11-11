# Lean entry point for `lem:buy-by-breakeven-threshold-bound`

This directory contains the stable Lean entry point for the checked statements
used in the paper lemma with label `lem:buy-by-breakeven-threshold-bound`.

From the parent `lean/` directory, run:

```bash
lake env lean buy_by_breakeven_threshold/BuyByBreakevenRho.lean
```

The entry file exposes the power-series definition and functional identity for
`U`, multiplier recurrence and nonnegativity, and the two exact rational
truncation checks around `rho_star`. It also proves the full endpoint comparison

```lean
D rho xi <= D rho 1
```

for `rho` in `[0.31,1]` and `xi` in `[0,1]`. This proof identifies the integral
definition of `D` with its power series, differentiates that series, checks its
alternating tail and finite first four terms, and applies the derivative test
for monotonicity.

`BuyByBreakevenRho.lean` completes the remaining parts of the threshold
argument. It proves continuity in `xi` on the closed interval, differentiates
the endpoint series with respect to `rho`, proves that `rho ↦ D rho 1` is
strictly decreasing on `(0,1)`, and connects the alternating truncations to
the actual infinite series. It then proves the exact endpoint signs, existence
and uniqueness of `rho_star`, its sign pattern, and the rigorous rounding
`rho_star ≈ 0.311`.
