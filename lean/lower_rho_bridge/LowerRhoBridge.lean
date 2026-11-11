import buy_by_breakeven_threshold.BuyByBreakevenRho

/-!
# Entry point for `lem:lower-rho-bridge`

This file gives the stable Lean entry point for the lower-rho bridge lemma.
-/

namespace SkiRental.Scalar

open scoped BigOperators

noncomputable section

theorem lower_rho_bridge_S6_margin_certificate :
    SkiRental.Certificates.lowerRhoBridgeS6Margin
      =
      SkiRental.Certificates.q
        1538190334986700888894969
        20237843235225380172556254400 :=
  SkiRental.Certificates.lower_rho_bridge_S6_margin_value

theorem lower_rho_bridge_S6_margin_positive :
    0 < SkiRental.Certificates.lowerRhoBridgeS6Margin :=
  SkiRental.Certificates.lower_rho_bridge_S6_margin_positive

theorem lower_rho_bridge_e_partial_gt :
    SkiRental.Certificates.q 19 7 < SkiRental.Certificates.q 163 60 :=
  SkiRental.Certificates.lower_rho_bridge_e_partial_gt

theorem lower_rho_bridge_series_entry_point {rho : ℝ}
    (he : (19 / 7 : ℝ) < Real.exp 1)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 31 / 100) :
    1 < lowerRhoBridgeDSeries rho :=
  lowerRhoBridgeDSeries_gt_one he hrho0 hrho1

theorem lower_rho_bridge_unconditional {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 31 / 100) :
    1 < lowerRhoBridgeDSeries rho := by
  apply lower_rho_bridge_series_entry_point ?_ hrho0 hrho1
  exact (by norm_num : (19 / 7 : ℝ) < 2.7182818283).trans
    Real.exp_one_gt_d9

theorem lower_rho_bridge_D_gt_one {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 31 / 100) :
    1 < D rho 1 := by
  have hrho_unit : rho ≤ 1 := hrho1.trans (by norm_num)
  rw [SkiRental.Analysis.buy_by_breakeven_D_eq_lowerRhoBridgeDSeries
    hrho0 hrho_unit]
  exact lower_rho_bridge_unconditional hrho0 hrho1

end

end SkiRental.Scalar
