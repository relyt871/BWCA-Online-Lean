import Lake
open Lake DSL

package "ski-rental-certificates" where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

@[default_target]
lean_lib SkiRental where
  roots := #[
    `SkiRental.Certificates,
    `SkiRental.LemmaCertificates,
    `SkiRental.Polynomial,
    `SkiRental.Scalar,
    `SkiRental.Analysis,
    `buy_by_breakeven_threshold.BuyByBreakevenThreshold,
    `buy_by_breakeven_threshold.BuyByBreakevenRho,
    `general_K.GeneralK,
    `one_third_kernel.OneThirdKernel,
    `general_K.GeneralKAnalytic,
    `general_K.GeneralKRho,
    `lower_rho_bridge.LowerRhoBridge,
  ]
