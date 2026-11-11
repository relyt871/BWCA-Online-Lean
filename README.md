# Lean certificates for ski rental

This is a small Lean companion project for the ski-rental section of the
paper.  It checks exact rational arithmetic used in the numerical parts of the
tight analysis and provides Mathlib-backed definitions for the `U`, `D`, and
`K` functions.

Recommended first-time check:

```bash
cd lean
lake exe cache get
lake build
```

The default `lake build` target checks every paper-facing theorem in one
build.  Its top-level roots are the buy-by-breakeven threshold, the lower-rho
bridge, and the general-`K` analysis.  Their imports cover the one-third,
concavity, and shared analysis files.  Each entry file can also be checked
separately with the commands listed in its subdirectory README.

The first command downloads precompiled Mathlib artifacts.  If it is skipped,
`lake build` will still work, but it may compile Mathlib dependencies from
source and take much longer.

Current scope:

* `SkiRental.Certificates`: pure exact rational checks for outward-rounded
  interval arithmetic and truncation brackets.
* `SkiRental.LemmaCertificates`: generated exact rational Bernstein
  coefficient checks for the finite algebraic certificates in
  `lem:buy-by-breakeven-threshold-bound` and the concavity estimate used in
  `lem:general-tail-reduction`.
* `SkiRental.Polynomial`: reusable positivity helpers for power and Bernstein
  polynomial certificates.
* `SkiRental.Analysis`: the paper-facing import for the Mathlib definitions
  and finite or closed-form reductions.

For `lem:one-third-kernel`, the project checks the complete statement.  This
includes nonnegativity of `U(1/3, xi, t)` on the full closed parameter box,
`D(1/3, xi) < 1` for every `xi in [0,1]`, and positivity of the late-tail
integral at `xi = 1`.  The proof includes the alternating finite bounds,
interval integrations, sum-integral exchanges, and exact rational estimates.

For `lem:buy-by-breakeven-threshold-bound` and `lem:lower-rho-bridge`, the project
checks:

* the endpoint-safe power-series definition of `U`;
* the functional identity `U rho xi t + xi * U rho xi (rho * t) = exp (-t)`;
* the dual multiplier recurrence `gamma * u_k + u_{k+1} = b_k`;
* nonnegativity of the dual multipliers on the certificate box;
* the endpoint-safe power-series definition of `U` is nonnegative on
  `rho in [0.31,1]`, `xi,t in [0,1]`;
* the full cleared cubic lower-bound numerator has positive Bernstein
  coefficients on that same box;
* the cleared finite expression used for `partial D / partial xi` has
  nonnegative Bernstein coefficients;
* continuity of `D(rho,xi)` in `xi` on the full closed interval;
* strict decrease of `D(rho,1)` in `rho` on `(0,1)`;
* the alternating-series bounds connecting the published rational brackets
  to the actual infinite series;
* existence and uniqueness of `rho_star`, the sign of `D(rho,1)-1` on either
  side, and the rigorous rounding `rho_star ≈ 0.311`;
* the exact rational endpoint arithmetic used in the lower-`rho` bridge;
* the alternating-series lower-`rho` bridge for the series expression,
  together with the elementary numerical bound `e > 19/7` from Mathlib.

The paper first defines `U` through the geometric or probabilistic expression
for `xi < 1`, derives the power series, and extends it to `xi = 1`.  Lean uses
that endpoint-safe power series, called `Upower`, as its formal definition.
The analytic identification of the two expressions is supplied in the paper.

For the concavity estimate in `lem:general-tail-reduction`, the project
checks:

* the cleared endpoint `P5` numerator has 126 positive tensor-product
  Bernstein coefficients;
* the endpoint certificate's smallest coefficient matches the paper's
  `3435842560 / 1162261467`;
* the paper's `P5` expression equals the cleared numerator divided by a
  positive denominator;
* after `rho = 1/3 + 2 alpha / 3`, the cleared numerator is exactly the
  tensor-product Bernstein polynomial built from the 126 listed coefficients;
* consequently `P5(rho, xi) > 0` for `rho in [1/3,1]` and `xi in [0,1]`;
* a stronger all-`t` six-term lower polynomial has positive tensor-product
  Bernstein coefficients of degrees `(20,5,5)` on
  `(alpha,beta,tau) in [0,1]^3`;
* the corresponding infinite series is at least that six-term polynomial,
  by an alternating-tail proof from index `6` onward;
* the power-series representation `Upower` is differentiable term-by-term on
  the needed `t in [0,1]` interval;
* the resulting derivative series is reindexed and algebraically assembled;
* consequently `Upower + rho * Upower'` is nonnegative for
  `rho in [1/3,1]` and `xi,t in [0,1]`.

For `lem:general-K`, the project now checks:

* the two finite denominator-cleared polynomial inequalities used to show that
  the four-term expression `F(rho, xi)` decreases in `xi`;
* positivity of the exact numerator for `F(rho,1)` after the shift
  `rho = 1/3 + s`;
* the finite polynomial checks used in the lower bound for `K'(rho)`;
* the alternating-tail lower bound for the `xi`-derivative series after its
  first four terms;
* the alternating-tail lower and upper bounds for the endpoint series after
  the partial sums used at `rho = 1/3` and `rho = 1/2`;
* the rational tail-bound and derivative-margin arithmetic in the proof that
  `K` is strictly increasing;
* the exact endpoint arithmetic used to bracket the unique zero between
  `1/3` and `1/2`.
* the endpoint sign `K(1/3,1) < 0`, including the required elementary
  exponential bound from Mathlib;
* the endpoint sign `0 < K(1/2,1)`, including the elementary exponential
  bound from Mathlib.
* continuity of `K(rho, xi)` in `xi` on `[0,1]`;
* termwise differentiation of the series defining `K(rho, xi)` and the exact
  derivative formula used in the paper;
* the complete comparison `K(rho,1) <= K(rho,xi)` for
  `rho in [1/3,1]` and `xi in [0,1]`;
* the exact identity between the weighted endpoint integral and
  `(1-rho)/rho^2 * K(rho,xi)`, including the sum-integral exchange;
* the exact series identity for the one-third late-tail integral and its
  strict positivity;
* termwise differentiation of `K(rho,1)` in `rho` and positivity of its
  derivative on `(0,1)`;
* strict monotonicity of `K(rho,1)` and the intermediate-value argument giving
  its unique zero in `(1/3,1/2)`.
