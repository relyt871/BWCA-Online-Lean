# Lean entry point for `lem:one-third-kernel`

This directory contains the main Lean entry point for the second assertion in
the paper lemma labeled `lem:one-third-kernel`.  The analytic assembly for the
third assertion is in `general_K/GeneralKAnalytic.lean`.

## Certified statement

The exported theorem

```lean
theorem one_third_kernel_D_lt_one {xi : Real}
    (hxi0 : 0 <= xi) (hxi1 : xi <= 1) :
    D (1 / 3) xi < 1
```

uses the same series-defined function `U` and interval-integral definition of
`D` from the shared analysis layer.

The proof checks:

* the alternating tail after the first five terms is nonpositive;
* the five-term polynomial is a pointwise upper bound for `U` on `[1/3,1]`;
* its interval integral equals the antiderivative used in the paper;
* after multiplying by `3 xi`, that integral is the paper's rational function
  `s(xi)`;
* `s(xi) <= 11671 / 34440` on `[0,1]`, by clearing positive denominators;
* `exp(1) * (11671 / 34440) < 1`.

The shared theorem `buy_by_breakeven_U_nonneg` proves the first assertion at
`rho = 1/3`.  The file `general_K/GeneralKAnalytic.lean` proves the exact
identity

```lean
theorem one_third_late_integral_eq_series :
    oneThirdLateIntegral =
      6 * (oneThirdLateSeries - 1 / (3 * Real.exp 1))
```

and combines it with the alternating-series endpoint bound to prove
`one_third_late_integral_positive`.

## How to check it

From the `lean` directory:

```bash
lake exe cache get
lake build
lake env lean general_K/GeneralKAnalytic.lean
```
