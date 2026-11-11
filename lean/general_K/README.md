# Lean entry point for `lem:general-K`

This directory is the stable entry point for the Lean proof around Lemmas
`lem:general-K-xi` and `lem:general-K-rho` in the paper.

## What Lean checks here

The file `general_K/GeneralK.lean` contains the finite inequalities,
alternating-tail bounds, and endpoint arithmetic.  It exposes:

* `general_K_first_pair_nonneg`: the denominator-cleared polynomial identity
  used for the first pair in the proof that the four-term expression
  `F(rho, xi)` decreases in `xi`.
* `general_K_second_pair_nonneg`: the denominator-cleared polynomial
  nonnegativity check used for the second pair in that same argument.
* `general_K_F_at_one_pos`: the positivity of the numerator obtained after
  putting `F(rho,1)` over the paper's positive denominator, for
  `rho >= 1/3`.
* `general_K_f2_special_clear_pos` and
  `general_K_f4_special_clear_nonneg`: the finite polynomial checks used in
  the lower bound for `K'(rho)`.
* `general_K_factorial_tail_bound_arithmetic` and
  `general_K_derivative_margin_arithmetic`: the rational arithmetic in the
  lower bound for `K'(rho)`.
* `general_K_Dxi_fourTerm_le_series`: the alternating-tail lower bound saying
  the full `xi`-derivative series is at least its first four terms.
* `general_K_partial5_le_series`: the alternating-tail lower bound used at
  `rho = 1/3`.
* `general_K_series_le_partial2`: the alternating-tail upper bound used at
  `rho = 1/2`.
* `general_K_left_endpoint_arithmetic`,
  `general_K_left_e_bound_arithmetic`,
  `general_K_right_endpoint_margin`, and
  `general_K_right_e_bound_arithmetic`: the exact endpoint arithmetic used to
  bracket the zero between `1/3` and `1/2`, together with the paper's
  alternating-truncation and elementary exponential bounds.
* `general_K_left_endpoint_negative_unconditional`: the endpoint sign
  `K(1/3,1) < 0`, including the required elementary exponential bound from
  Mathlib.
* `general_K_right_endpoint_positive`: the endpoint sign `0 < K(1/2,1)`,
  assuming the elementary exponential bound displayed in its statement.

The file `general_K/GeneralKAnalytic.lean` imports those results and completes
the analytic assembly.  Its paper-facing theorems are:

```lean
theorem general_K_continuousOn_xi {rho : Real}
    (hrho0 : 0 <= rho) (hrho1 : rho <= 1) :
    ContinuousOn (fun xi => K rho xi) (Set.Icc (0 : Real) 1)

theorem general_K_minimized_at_one {rho xi : Real}
    (hrho : (1 / 3 : Real) <= rho) (hrho1 : rho <= 1)
    (hxi0 : 0 <= xi) (hxi1 : xi <= 1) :
    K rho 1 <= K rho xi

theorem general_K_scaled_endpoint_identity {rho xi : Real}
    (hrho0 : 0 < rho) (hrho1 : rho <= 1) (hxi0 : 0 <= xi) :
    (1 - rho) / (Real.exp 1 * rho)
        - xi / rho ^ 2 *
          (∫ x in rho..1, (1 + rho - x) * U rho xi x)
      = (1 - rho) / rho ^ 2 * K rho xi

theorem one_third_late_integral_eq_series :
    oneThirdLateIntegral =
      6 * (oneThirdLateSeries - 1 / (3 * Real.exp 1))

theorem one_third_late_integral_positive :
    0 < oneThirdLateIntegral
```

The first two theorems include the uniform derivative bound, termwise
differentiation of the actual `K` series, and the decreasing-in-`xi`
argument.  The endpoint identity includes the weighted power integral and
the justified exchange of the infinite sum with the integral.  The final two
theorems formalize the complete one-third late-tail calculation.

The file `general_K/GeneralKRho.lean` completes the dependence-on-`rho`
argument.  Its paper-facing theorems are:

```lean
theorem general_K_strictMonoOn_rho :
    StrictMonoOn (fun rho : Real => K rho 1) (Set.Ioo 0 1)

theorem general_K_existsUnique_zero :
    ∃! rho : Real, rho ∈ Set.Ioo (1 / 3 : Real) (1 / 2 : Real) ∧ K rho 1 = 0
```

The file proves the coefficient derivative bounds, justifies termwise
differentiation, proves positivity of the derivative with an exact tail
estimate, and combines the endpoint signs with the intermediate value theorem.

## How to check it

From the `lean` directory:

```bash
lake exe cache get
lake build
lake env lean general_K/GeneralKRho.lean
```
