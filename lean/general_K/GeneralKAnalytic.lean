import general_K.GeneralK
import buy_by_breakeven_threshold.BuyByBreakevenThreshold
import one_third_kernel.OneThirdKernel

/-!
# Analytic assembly for the general endpoint quantity

This file completes three paper-facing arguments using the exact series and
finite inequalities in `GeneralK.lean`:

* `K rho xi` is minimized at `xi = 1` on the paper's parameter range;
* the weighted endpoint integral is exactly the positive factor times `K`;
* the one-third late-tail integral equals the series expression used in the
  endpoint sign check and is strictly positive.
-/

namespace SkiRental.Scalar

open scoped BigOperators

noncomputable section

theorem general_endpoint_concavity_factor_nonneg {rho xi t : ℝ}
    (hrho0 : (1 / 3 : ℝ) ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ U rho xi t + rho * deriv (fun z => U rho xi z) t := by
  exact generalVPositive_nonneg_on_box
    hrho0 hrho1 hxi0 hxi1 ht0 ht1

def generalKFirstPair (rho xi : ℝ) : ℝ :=
  dCoeff rho 0 / (1 + xi) ^ 2
    - dCoeff rho 1 / (1 + xi * rho) ^ 2

def generalKSecondPair (rho xi : ℝ) : ℝ :=
  dCoeff rho 2 / (2 * (1 + xi * rho ^ 2) ^ 2)
    - dCoeff rho 3 / (6 * (1 + xi * rho ^ 3) ^ 2)

theorem general_K_Dxi_fourTerm_eq_pairs (rho xi : ℝ) :
    generalKDxiFourTerm rho xi =
      generalKFirstPair rho xi + generalKSecondPair rho xi := by
  norm_num [generalKDxiFourTerm, generalKDxiTerm, generalKDxiMag,
    generalKFirstPair, generalKSecondPair, Finset.sum_range_succ]
  ring

theorem general_K_first_pair_base {rho : ℝ} (hrho : 0 ≤ rho) :
    8 * rho * dCoeff rho 1 ≤ dCoeff rho 0 * (1 + rho) ^ 3 := by
  have hclear := general_K_first_pair_nonneg hrho
  norm_num [generalKFirstPairClear, dCoeff, Finset.sum_Icc_succ_top] at hclear ⊢
  nlinarith

theorem general_K_second_pair_base {rho : ℝ} (hrho : 0 ≤ rho) :
    rho * dCoeff rho 3 * (1 + rho ^ 2) ^ 3
      ≤ 3 * dCoeff rho 2 * (1 + rho ^ 3) ^ 3 := by
  have hclear := general_K_second_pair_nonneg hrho
  norm_num [generalKSecondPairClear, dCoeff, Finset.sum_Icc_succ_top] at hclear ⊢
  nlinarith

theorem general_K_first_pair_deriv_nonpos {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    -2 * dCoeff rho 0 / (1 + xi) ^ 3
      + 2 * rho * dCoeff rho 1 / (1 + xi * rho) ^ 3 ≤ 0 := by
  have hbase := general_K_first_pair_base hrho0
  have hratio : (1 + rho) * (1 + xi) ≤ 2 * (1 + xi * rho) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrho1) (sub_nonneg.mpr hxi1)]
  have hleft0 : 0 ≤ (1 + rho) * (1 + xi) := by positivity
  have hcube := pow_le_pow_left₀ hleft0 hratio 3
  have hcube' : (1 + rho) ^ 3 * (1 + xi) ^ 3
      ≤ 8 * (1 + xi * rho) ^ 3 := by
    norm_num [mul_pow] at hcube ⊢
    exact hcube
  have hd0 : 0 ≤ dCoeff rho 0 := general_K_dCoeff_nonneg hrho0 0
  have hA3 : 0 ≤ (1 + xi) ^ 3 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hbase hA3
  have h2 := mul_le_mul_of_nonneg_left hcube' hd0
  have hcross : rho * dCoeff rho 1 * (1 + xi) ^ 3
      ≤ dCoeff rho 0 * (1 + xi * rho) ^ 3 := by
    nlinarith
  have hApos : 0 < (1 + xi) ^ 3 := by positivity
  have hBpos : 0 < (1 + xi * rho) ^ 3 := by positivity
  have hfrac : rho * dCoeff rho 1 / (1 + xi * rho) ^ 3
      ≤ dCoeff rho 0 / (1 + xi) ^ 3 := by
    rw [div_le_div_iff₀ hBpos hApos]
    exact hcross
  calc
    -2 * dCoeff rho 0 / (1 + xi) ^ 3
        + 2 * rho * dCoeff rho 1 / (1 + xi * rho) ^ 3
        = 2 * (rho * dCoeff rho 1 / (1 + xi * rho) ^ 3
            - dCoeff rho 0 / (1 + xi) ^ 3) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sub_nonpos.mpr hfrac)

theorem general_K_second_pair_deriv_nonpos {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    -dCoeff rho 2 * rho ^ 2 / (1 + xi * rho ^ 2) ^ 3
      + dCoeff rho 3 * rho ^ 3 / (3 * (1 + xi * rho ^ 3) ^ 3) ≤ 0 := by
  have hbase := general_K_second_pair_base hrho0
  have hpow : rho ^ 3 ≤ rho ^ 2 :=
    pow_le_pow_of_le_one hrho0 hrho1 (by norm_num)
  have hratio : (1 + rho ^ 3) * (1 + xi * rho ^ 2)
      ≤ (1 + rho ^ 2) * (1 + xi * rho ^ 3) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpow) (sub_nonneg.mpr hxi1)]
  have hleft0 : 0 ≤ (1 + rho ^ 3) * (1 + xi * rho ^ 2) := by positivity
  have hcube := pow_le_pow_left₀ hleft0 hratio 3
  have hcube' : (1 + rho ^ 3) ^ 3 * (1 + xi * rho ^ 2) ^ 3
      ≤ (1 + rho ^ 2) ^ 3 * (1 + xi * rho ^ 3) ^ 3 := by
    simpa [mul_pow] using hcube
  have hd2 : 0 ≤ dCoeff rho 2 := general_K_dCoeff_nonneg hrho0 2
  have hA3 : 0 ≤ (1 + xi * rho ^ 2) ^ 3 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hbase hA3
  have hDpos : 0 < (1 + rho ^ 2) ^ 3 := by positivity
  have hcross : rho * dCoeff rho 3 * (1 + xi * rho ^ 2) ^ 3
      ≤ 3 * dCoeff rho 2 * (1 + xi * rho ^ 3) ^ 3 := by
    have hwithD :
        (1 + rho ^ 2) ^ 3 *
            (rho * dCoeff rho 3 * (1 + xi * rho ^ 2) ^ 3)
          ≤
        (1 + rho ^ 2) ^ 3 *
            (3 * dCoeff rho 2 * (1 + xi * rho ^ 3) ^ 3) := by
      calc
        (1 + rho ^ 2) ^ 3 *
              (rho * dCoeff rho 3 * (1 + xi * rho ^ 2) ^ 3)
            = (rho * dCoeff rho 3 * (1 + rho ^ 2) ^ 3)
                * (1 + xi * rho ^ 2) ^ 3 := by ring
        _ ≤ (3 * dCoeff rho 2 * (1 + rho ^ 3) ^ 3)
                * (1 + xi * rho ^ 2) ^ 3 := h1
        _ = (3 * dCoeff rho 2) *
                ((1 + rho ^ 3) ^ 3 * (1 + xi * rho ^ 2) ^ 3) := by ring
        _ ≤ (3 * dCoeff rho 2) *
                ((1 + rho ^ 2) ^ 3 * (1 + xi * rho ^ 3) ^ 3) :=
              mul_le_mul_of_nonneg_left hcube' (by positivity)
        _ = (1 + rho ^ 2) ^ 3 *
              (3 * dCoeff rho 2 * (1 + xi * rho ^ 3) ^ 3) := by ring
    nlinarith [hwithD]
  have hApos : 0 < (1 + xi * rho ^ 2) ^ 3 := by positivity
  have hBpos : 0 < (1 + xi * rho ^ 3) ^ 3 := by positivity
  have hfrac : dCoeff rho 3 * rho ^ 3 / (3 * (1 + xi * rho ^ 3) ^ 3)
      ≤ dCoeff rho 2 * rho ^ 2 / (1 + xi * rho ^ 2) ^ 3 := by
    have hrho_cross : dCoeff rho 3 * rho ^ 3 * (1 + xi * rho ^ 2) ^ 3
        ≤ 3 * dCoeff rho 2 * rho ^ 2 * (1 + xi * rho ^ 3) ^ 3 := by
      have h := mul_le_mul_of_nonneg_left hcross (sq_nonneg rho)
      nlinarith
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hBpos) hApos]
    nlinarith
  calc
    -dCoeff rho 2 * rho ^ 2 / (1 + xi * rho ^ 2) ^ 3
        + dCoeff rho 3 * rho ^ 3 / (3 * (1 + xi * rho ^ 3) ^ 3)
        = dCoeff rho 3 * rho ^ 3 / (3 * (1 + xi * rho ^ 3) ^ 3)
            - dCoeff rho 2 * rho ^ 2 / (1 + xi * rho ^ 2) ^ 3 := by ring
    _ ≤ 0 := sub_nonpos.mpr hfrac

theorem hasDerivAt_generalKFirstPair {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hxi0 : 0 ≤ xi) :
    HasDerivAt (fun z => generalKFirstPair rho z)
      (-2 * dCoeff rho 0 / (1 + xi) ^ 3
        + 2 * rho * dCoeff rho 1 / (1 + xi * rho) ^ 3) xi := by
  have hA : 1 + xi ≠ 0 := by positivity
  have hB : 1 + xi * rho ≠ 0 := by positivity
  have hA2 : (1 + xi) ^ 2 ≠ 0 := pow_ne_zero 2 hA
  have hB2 : (1 + xi * rho) ^ 2 ≠ 0 := pow_ne_zero 2 hB
  have hfirst := (hasDerivAt_const xi (dCoeff rho 0)).div
    (((hasDerivAt_const xi 1).add (hasDerivAt_id xi)).pow 2) hA2
  have hsecond := (hasDerivAt_const xi (dCoeff rho 1)).div
    (((hasDerivAt_const xi 1).add ((hasDerivAt_id xi).mul_const rho)).pow 2) hB2
  have hraw := hfirst.sub hsecond
  change HasDerivAt (fun z => generalKFirstPair rho z) _ xi at hraw
  apply hraw.congr_deriv
  simp only [id_eq, Pi.add_apply, Pi.pow_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_mul, zero_add, one_mul]
  field_simp [hA, hB]
  ring

theorem hasDerivAt_generalKSecondPair {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hxi0 : 0 ≤ xi) :
    HasDerivAt (fun z => generalKSecondPair rho z)
      (-dCoeff rho 2 * rho ^ 2 / (1 + xi * rho ^ 2) ^ 3
        + dCoeff rho 3 * rho ^ 3 / (3 * (1 + xi * rho ^ 3) ^ 3)) xi := by
  have hA : 1 + xi * rho ^ 2 ≠ 0 := by positivity
  have hB : 1 + xi * rho ^ 3 ≠ 0 := by positivity
  have hA2 : 2 * (1 + xi * rho ^ 2) ^ 2 ≠ 0 := by positivity
  have hB2 : 6 * (1 + xi * rho ^ 3) ^ 2 ≠ 0 := by positivity
  have hfirst := (hasDerivAt_const xi (dCoeff rho 2)).div
    ((hasDerivAt_const xi 2).mul
      (((hasDerivAt_const xi 1).add
        ((hasDerivAt_id xi).mul_const (rho ^ 2))).pow 2)) hA2
  have hsecond := (hasDerivAt_const xi (dCoeff rho 3)).div
    ((hasDerivAt_const xi 6).mul
      (((hasDerivAt_const xi 1).add
        ((hasDerivAt_id xi).mul_const (rho ^ 3))).pow 2)) hB2
  have hraw := hfirst.sub hsecond
  change HasDerivAt (fun z => generalKSecondPair rho z) _ xi at hraw
  apply hraw.congr_deriv
  simp only [id_eq, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_mul, zero_add, one_mul]
  field_simp [hA, hB]
  ring

theorem general_K_Dxi_fourTerm_at_one (rho : ℝ) :
    generalKDxiFourTerm rho 1 = generalKFAtOne rho := by
  rw [general_K_Dxi_fourTerm_eq_pairs]
  norm_num [generalKFirstPair, generalKSecondPair, generalKFAtOne,
    dCoeff, Finset.sum_Icc_succ_top]
  ring

theorem hasDerivAt_generalKDxiFourTerm {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hxi0 : 0 ≤ xi) :
    HasDerivAt (fun z => generalKDxiFourTerm rho z)
      ((-2 * dCoeff rho 0 / (1 + xi) ^ 3
          + 2 * rho * dCoeff rho 1 / (1 + xi * rho) ^ 3)
        + (-dCoeff rho 2 * rho ^ 2 / (1 + xi * rho ^ 2) ^ 3
          + dCoeff rho 3 * rho ^ 3 / (3 * (1 + xi * rho ^ 3) ^ 3))) xi := by
  have hfun : (fun z => generalKDxiFourTerm rho z) =
      (fun z => generalKFirstPair rho z + generalKSecondPair rho z) := by
    funext z
    exact general_K_Dxi_fourTerm_eq_pairs rho z
  rw [hfun]
  exact (hasDerivAt_generalKFirstPair hrho0 hxi0).add
    (hasDerivAt_generalKSecondPair hrho0 hxi0)

theorem general_K_Dxi_fourTerm_pos {rho xi : ℝ}
    (hrho : (1 / 3 : ℝ) ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    0 < generalKDxiFourTerm rho xi := by
  have hrho0 : 0 ≤ rho := by nlinarith
  have hderiv (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :=
    hasDerivAt_generalKDxiFourTerm (rho := rho) hrho0 hz0
  have hcont : ContinuousOn (fun z => generalKDxiFourTerm rho z) (Set.Icc xi 1) := by
    intro z hz
    exact (hderiv z (le_trans hxi0 hz.1) hz.2).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun z => generalKDxiFourTerm rho z)
      (interior (Set.Icc xi 1)) := by
    intro z hz
    have hz' : z ∈ Set.Ioo xi 1 := by simpa [interior_Icc] using hz
    exact (hderiv z (le_trans hxi0 (le_of_lt hz'.1)) (le_of_lt hz'.2))
      |>.differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn (fun z => generalKDxiFourTerm rho z) (Set.Icc xi 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc xi 1) hcont hdiff
    intro z hz
    have hz' : z ∈ Set.Ioo xi 1 := by simpa [interior_Icc] using hz
    have hd := hderiv z (le_trans hxi0 (le_of_lt hz'.1)) (le_of_lt hz'.2)
    rw [hd.deriv]
    exact add_nonpos
      (general_K_first_pair_deriv_nonpos hrho0 hrho1
        (le_trans hxi0 (le_of_lt hz'.1)) (le_of_lt hz'.2))
      (general_K_second_pair_deriv_nonpos hrho0 hrho1
        (le_trans hxi0 (le_of_lt hz'.1)) (le_of_lt hz'.2))
  have hone : 0 < generalKDxiFourTerm rho 1 := by
    rw [general_K_Dxi_fourTerm_at_one]
    exact general_K_F_at_one_pos hrho
  exact lt_of_lt_of_le hone
    (hanti (by exact ⟨le_rfl, hxi1⟩) (by exact ⟨hxi1, le_rfl⟩) hxi1)

theorem general_K_Dxi_series_pos {rho xi : ℝ}
    (hrho : (1 / 3 : ℝ) ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    0 < generalKDxiSeries rho xi := by
  exact lt_of_lt_of_le
    (general_K_Dxi_fourTerm_pos hrho hrho1 hxi0 hxi1)
    (general_K_Dxi_fourTerm_le_series (by nlinarith) hrho1 hxi0 hxi1)

def generalKXiSeriesTerm (rho xi : ℝ) (n : Nat) : ℝ :=
  ((-1 : ℝ) ^ n * dCoeff rho n / (Nat.factorial n : ℝ))
    * (xi / (1 + xi * rho ^ n))

noncomputable def generalKXiSeries (rho xi : ℝ) : ℝ :=
  ∑' n : Nat, generalKXiSeriesTerm rho xi n

theorem general_K_xi_den_lower {rho z : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hz : -(1 / 2 : ℝ) < z) (n : Nat) :
    1 / 2 < 1 + z * rho ^ n := by
  have hp0 : 0 ≤ rho ^ n := pow_nonneg hrho0 n
  have hp1 : rho ^ n ≤ 1 := pow_le_one₀ hrho0 hrho1
  rcases le_total 0 z with hz0 | hz0
  · nlinarith [mul_nonneg hz0 hp0]
  · have hmul : z ≤ z * rho ^ n := by
      have h := mul_nonneg (neg_nonneg.mpr hz0) (sub_nonneg.mpr hp1)
      nlinarith
    nlinarith

theorem hasDerivAt_generalKXiSeriesTerm {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi : -(1 / 2 : ℝ) < xi) (n : Nat) :
    HasDerivAt (fun z => generalKXiSeriesTerm rho z n)
      (generalKDxiTerm rho xi n) xi := by
  have hdenpos := general_K_xi_den_lower hrho0 hrho1 hxi n
  have hden : 1 + xi * rho ^ n ≠ 0 := ne_of_gt (lt_trans (by norm_num) hdenpos)
  have hquot : HasDerivAt (fun z : ℝ => z / (1 + z * rho ^ n))
      (1 / (1 + xi * rho ^ n) ^ 2) xi := by
    have hraw := (hasDerivAt_id xi).div
      ((hasDerivAt_const xi 1).add ((hasDerivAt_id xi).mul_const (rho ^ n))) hden
    convert hraw using 1 <;>
      first
      | rfl
      | (simp only [id_eq, Pi.add_apply, one_mul, zero_add]
         field_simp [hden]
         ring)
  let c : ℝ := (-1 : ℝ) ^ n * dCoeff rho n / (Nat.factorial n : ℝ)
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have heq : c * (1 / (1 + xi * rho ^ n) ^ 2) =
      generalKDxiTerm rho xi n := by
    dsimp [c]
    unfold generalKDxiTerm generalKDxiMag
    field_simp [hfac, hden]
  rw [← heq]
  simpa only [generalKXiSeriesTerm, c] using hquot.const_mul c

theorem general_K_DxiTerm_norm_le_four_factorial {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi : -(1 / 2 : ℝ) < xi) (n : Nat) :
    ‖generalKDxiTerm rho xi n‖ ≤ 4 / (Nat.factorial n : ℝ) := by
  have hdenhalf := general_K_xi_den_lower hrho0 hrho1 hxi n
  have hdenpos : 0 < 1 + xi * rho ^ n := lt_trans (by norm_num) hdenhalf
  have hdenquarter : 1 / 4 < (1 + xi * rho ^ n) ^ 2 := by nlinarith
  have hd0 := general_K_dCoeff_nonneg hrho0 n
  have hd1 := general_K_dCoeff_le_one hrho0 hrho1 n
  have hfac : 0 < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  rw [generalKDxiTerm, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul]
  have hmag0 : 0 ≤ generalKDxiMag rho xi n := by
    unfold generalKDxiMag
    positivity
  rw [abs_of_nonneg hmag0]
  unfold generalKDxiMag
  rw [div_le_div_iff₀ (mul_pos hfac (sq_pos_of_pos hdenpos)) hfac]
  nlinarith

set_option maxHeartbeats 800000 in
theorem hasDerivAt_generalKXiSeries {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi : -(1 / 2 : ℝ) < xi) :
    HasDerivAt (fun z => generalKXiSeries rho z)
      (generalKDxiSeries rho xi) xi := by
  have hfac : Summable (fun n : Nat => (4 : ℝ) / (Nat.factorial n : ℝ)) := by
    have h : Summable (fun n : Nat => (1 : ℝ) / (Nat.factorial n : ℝ)) := by
      simpa [one_pow] using Real.summable_pow_div_factorial (1 : ℝ)
    have h4 : Summable
        (fun n : Nat => (4 : ℝ) * ((1 : ℝ) / (Nat.factorial n : ℝ))) :=
      h.mul_left 4
    exact h4.congr (fun n => by ring)
  have hbase : Summable (fun n => generalKXiSeriesTerm rho 0 n) := by
    simp [generalKXiSeriesTerm]
  unfold generalKXiSeries generalKDxiSeries
  exact hasDerivAt_tsum_of_isPreconnected
      (α := Nat) (𝕜 := ℝ) (F := ℝ)
      (u := fun n : Nat => (4 : ℝ) / (Nat.factorial n : ℝ))
      (g := fun n z => generalKXiSeriesTerm rho z n)
      (g' := fun n z => generalKDxiTerm rho z n)
      (t := Set.Ioi (-(1 / 2 : ℝ))) (y₀ := 0)
      hfac isOpen_Ioi isPreconnected_Ioi
      (fun n z hz => hasDerivAt_generalKXiSeriesTerm hrho0 hrho1 hz n)
      (fun n z hz => general_K_DxiTerm_norm_le_four_factorial hrho0 hrho1 hz n)
      (by norm_num) hbase hxi

theorem general_K_eq_xi_series {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi : -(1 / 2 : ℝ) < xi) :
    K rho xi = rho / Real.exp 1 - generalKXiSeries rho xi := by
  have hden (n : Nat) : 1 + xi * rho ^ n ≠ 0 := by
    have hpos : 0 < 1 + xi * rho ^ n := by
      exact lt_trans (by norm_num) (general_K_xi_den_lower hrho0 hrho1 hxi n)
    exact ne_of_gt hpos
  unfold K generalKXiSeries
  rw [← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  unfold generalKXiSeriesTerm
  field_simp [hden n]

theorem hasDerivAt_general_K_xi {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi : -(1 / 2 : ℝ) < xi) :
    HasDerivAt (fun z => K rho z) (-generalKDxiSeries rho xi) xi := by
  have hseries := hasDerivAt_generalKXiSeries hrho0 hrho1 hxi
  have hraw := (hasDerivAt_const xi (rho / Real.exp 1)).sub hseries
  have hraw' := hraw.congr_deriv (by ring : 0 - generalKDxiSeries rho xi =
    -generalKDxiSeries rho xi)
  apply hraw'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hxi] with z hz
  exact general_K_eq_xi_series hrho0 hrho1 hz

theorem general_K_continuousOn_xi {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    ContinuousOn (fun xi => K rho xi) (Set.Icc (0 : ℝ) 1) := by
  intro xi hxi
  exact (hasDerivAt_general_K_xi hrho0 hrho1 (by nlinarith [hxi.1]))
    |>.continuousAt.continuousWithinAt

theorem general_K_minimized_at_one {rho xi : ℝ}
    (hrho : (1 / 3 : ℝ) ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    K rho 1 ≤ K rho xi := by
  have hrho0 : 0 ≤ rho := by nlinarith
  have hderiv (z : ℝ) (hz0 : 0 ≤ z) :=
    hasDerivAt_general_K_xi (rho := rho) hrho0 hrho1 (by nlinarith : -(1 / 2 : ℝ) < z)
  have hcont : ContinuousOn (fun z => K rho z) (Set.Icc xi 1) := by
    intro z hz
    exact (hderiv z (le_trans hxi0 hz.1)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun z => K rho z) (interior (Set.Icc xi 1)) := by
    intro z hz
    have hz' : z ∈ Set.Ioo xi 1 := by simpa [interior_Icc] using hz
    exact (hderiv z (le_trans hxi0 (le_of_lt hz'.1)))
      |>.differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn (fun z => K rho z) (Set.Icc xi 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc xi 1) hcont hdiff
    intro z hz
    have hz' : z ∈ Set.Ioo xi 1 := by simpa [interior_Icc] using hz
    have hd := hderiv z (le_trans hxi0 (le_of_lt hz'.1))
    rw [hd.deriv]
    exact neg_nonpos.mpr (le_of_lt
      (general_K_Dxi_series_pos hrho hrho1
        (le_trans hxi0 (le_of_lt hz'.1)) (le_of_lt hz'.2)))
  exact hanti (by exact ⟨le_rfl, hxi1⟩) (by exact ⟨hxi1, le_rfl⟩) hxi1

theorem general_K_sum_Icc_one_eq_mul_geom (rho : ℝ) (n : Nat) :
    (Finset.Icc 1 n).sum (fun k => rho ^ k)
      = rho * (Finset.range n).sum (fun k => rho ^ k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top]
      · rw [ih, Finset.sum_range_succ]
        ring
      · omega

theorem general_K_dCoeff_alternative (rho : ℝ) (n : Nat) :
    (1 - rho) * dCoeff rho n =
      (1 + rho) * (1 - rho ^ (n + 1)) / (n + 1 : ℝ)
        - (1 - rho ^ (n + 2)) / (n + 2 : ℝ) := by
  have hgeom := geom_sum_mul_neg rho n
  have hsum :
      (Finset.Icc 1 n).sum (fun k => rho ^ k) * (1 - rho)
        = rho - rho ^ (n + 1) := by
    rw [general_K_sum_Icc_one_eq_mul_geom]
    calc
      (rho * ∑ k ∈ Finset.range n, rho ^ k) * (1 - rho)
          = rho * ((∑ k ∈ Finset.range n, rho ^ k) * (1 - rho)) := by ring
      _ = rho * (1 - rho ^ n) := by rw [hgeom]
      _ = rho - rho ^ (n + 1) := by rw [pow_succ]; ring
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
  unfold dCoeff
  field_simp [hn1, hn2]
  ring_nf at hsum ⊢
  nlinarith

theorem general_K_weighted_power_integral (rho : ℝ) (n : Nat) :
    (∫ x in rho..1, (1 + rho - x) * x ^ n)
      = (1 - rho) * dCoeff rho n := by
  have hn : IntervalIntegrable (fun x : ℝ => x ^ n) MeasureTheory.volume rho 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ n)).intervalIntegrable _ _
  have hns : IntervalIntegrable (fun x : ℝ => x ^ (n + 1)) MeasureTheory.volume rho 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ (n + 1))).intervalIntegrable _ _
  calc
    (∫ x in rho..1, (1 + rho - x) * x ^ n)
        = ∫ x in rho..1, (1 + rho) * x ^ n - x ^ (n + 1) := by
            apply intervalIntegral.integral_congr
            intro x _
            dsimp
            rw [pow_succ]
            ring
    _ = (1 + rho) * (∫ x in rho..1, x ^ n)
          - ∫ x in rho..1, x ^ (n + 1) := by
            rw [intervalIntegral.integral_sub (hn.const_mul (1 + rho)) hns,
              intervalIntegral.integral_const_mul]
    _ = (1 + rho) * (1 - rho ^ (n + 1)) / (n + 1 : ℝ)
          - (1 - rho ^ (n + 2)) / (n + 2 : ℝ) := by
            rw [integral_pow, integral_pow]
            norm_num
            ring
    _ = (1 - rho) * dCoeff rho n := (general_K_dCoeff_alternative rho n).symm

noncomputable def generalKWeightedContinuousTerm
    (rho xi : ℝ) (n : Nat) : C(ℝ, ℝ) :=
  ⟨fun x => (1 + rho - x) * UpowerTerm rho xi n x, by
    unfold UpowerTerm
    fun_prop⟩

theorem general_K_weighted_continuous_norm_le {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hxi0 : 0 ≤ xi) (n : Nat) :
    ‖(generalKWeightedContinuousTerm rho xi n).restrict
      (⟨Set.uIcc rho 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖
      ≤ 1 / (Nat.factorial n : ℝ) := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change ‖(1 + rho - (x : ℝ)) * UpowerTerm rho xi n (x : ℝ)‖
    ≤ 1 / (Nat.factorial n : ℝ)
  have hx : (x : ℝ) ∈ Set.Icc rho 1 := by
    simpa [Set.uIcc_of_le hrho1] using x.property
  have hw0 : 0 ≤ 1 + rho - (x : ℝ) := by nlinarith [hx.2, hrho0]
  have hw1 : 1 + rho - (x : ℝ) ≤ 1 := by nlinarith [hx.1]
  let base := (SkiRental.Analysis.buyByBreakevenUContinuousTerm rho xi n).restrict
    (⟨Set.uIcc rho 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)
  have hpoint : ‖UpowerTerm rho xi n (x : ℝ)‖ ≤ ‖base‖ := by
    exact ContinuousMap.norm_coe_le_norm base x
  have hbase : ‖base‖ ≤ 1 / (Nat.factorial n : ℝ) := by
    dsimp [base]
    exact SkiRental.Analysis.buy_by_breakeven_UContinuousTerm_norm_le
      hrho0 hrho1 hxi0 n
  rw [norm_mul, Real.norm_of_nonneg hw0]
  calc
    (1 + rho - (x : ℝ)) * ‖UpowerTerm rho xi n (x : ℝ)‖
        ≤ 1 * ‖UpowerTerm rho xi n (x : ℝ)‖ :=
          mul_le_mul_of_nonneg_right hw1 (norm_nonneg _)
    _ ≤ ‖base‖ := by simpa using hpoint
    _ ≤ 1 / (Nat.factorial n : ℝ) := hbase

theorem general_K_weighted_U_integral_eq_tsum {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hxi0 : 0 ≤ xi) :
    (∫ x in rho..1, (1 + rho - x) * U rho xi x)
      = ∑' n : Nat,
          ∫ x in rho..1, (1 + rho - x) * UpowerTerm rho xi n x := by
  have hfac : Summable (fun n : Nat => (1 : ℝ) / (Nat.factorial n : ℝ)) := by
    simpa [one_pow] using Real.summable_pow_div_factorial (1 : ℝ)
  have hnorm : Summable (fun n =>
      ‖(generalKWeightedContinuousTerm rho xi n).restrict
        (⟨Set.uIcc rho 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖) := by
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => general_K_weighted_continuous_norm_le hrho0 hrho1 hxi0 n) hfac
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hnorm
  have hfun : (fun x => (1 + rho - x) * U rho xi x) =
      (fun x => ∑' n : Nat, (1 + rho - x) * UpowerTerm rho xi n x) := by
    funext x
    unfold U Upower
    rw [tsum_mul_left]
  rw [hfun]
  simpa [generalKWeightedContinuousTerm] using hswap.symm

theorem general_K_weighted_UpowerTerm_integral {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hxi0 : 0 ≤ xi) (n : Nat) :
    (∫ x in rho..1, (1 + rho - x) * UpowerTerm rho xi n x)
      = (-1 : ℝ) ^ n * (1 - rho) * dCoeff rho n /
          ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n)) := by
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hden : 1 + xi * rho ^ n ≠ 0 := by positivity
  calc
    (∫ x in rho..1, (1 + rho - x) * UpowerTerm rho xi n x)
        = ((-1 : ℝ) ^ n /
            ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n))) *
            (∫ x in rho..1, (1 + rho - x) * x ^ n) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro x _
          unfold UpowerTerm
          dsimp
          rw [show -x = (-1 : ℝ) * x by ring, mul_pow]
          ring
    _ = (-1 : ℝ) ^ n * (1 - rho) * dCoeff rho n /
          ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n)) := by
          rw [general_K_weighted_power_integral]
          ring

theorem general_K_weighted_U_integral_eq_K_series {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hxi0 : 0 ≤ xi) :
    (∫ x in rho..1, (1 + rho - x) * U rho xi x)
      = (1 - rho) * ∑' n : Nat,
          (-1 : ℝ) ^ n * dCoeff rho n /
            ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n)) := by
  rw [general_K_weighted_U_integral_eq_tsum hrho0 hrho1 hxi0]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [general_K_weighted_UpowerTerm_integral hrho0 hxi0]
  ring

theorem general_K_scaled_endpoint_identity {rho xi : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) (hxi0 : 0 ≤ xi) :
    (1 - rho) / (Real.exp 1 * rho)
        - xi / rho ^ 2 * (∫ x in rho..1, (1 + rho - x) * U rho xi x)
      = (1 - rho) / rho ^ 2 * K rho xi := by
  have hrho_nonneg : 0 ≤ rho := le_of_lt hrho0
  rw [general_K_weighted_U_integral_eq_K_series
    hrho_nonneg hrho1 hxi0]
  unfold K
  have hrho : rho ≠ 0 := ne_of_gt hrho0
  have he : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
  field_simp [hrho, he]

theorem one_third_weighted_integral_eq_series :
    (∫ x in (1 / 3 : ℝ)..1,
        (4 / 3 - x) * U (1 / 3) 1 x)
      = (2 / 3 : ℝ) * oneThirdLateSeries := by
  have h := general_K_weighted_U_integral_eq_K_series
    (rho := (1 / 3 : ℝ)) (xi := 1) (by norm_num) (by norm_num) (by norm_num)
  calc
    (∫ x in (1 / 3 : ℝ)..1, (4 / 3 - x) * U (1 / 3) 1 x)
        = ∫ x in (1 / 3 : ℝ)..1,
            (1 + (1 / 3 : ℝ) - x) * U (1 / 3) 1 x := by
              apply intervalIntegral.integral_congr
              intro x _
              ring
    _ = (1 - (1 / 3 : ℝ)) * ∑' n : Nat,
          (-1 : ℝ) ^ n * dCoeff (1 / 3) n /
            ((Nat.factorial n : ℝ) * (1 + (1 : ℝ) * (1 / 3) ^ n)) := h
    _ = (2 / 3 : ℝ) * oneThirdLateSeries := by
          unfold oneThirdLateSeries generalKSeries generalKSeriesTerm generalKSeriesMag
          congr 1
          · norm_num
          · apply tsum_congr
            intro n
            ring

noncomputable def oneThirdExpPrimitive (x : ℝ) : ℝ :=
  Real.exp (-3 * x) * ((x - 1) / 3)

theorem one_third_exp_primitive_deriv (x : ℝ) :
    HasDerivAt oneThirdExpPrimitive
      ((4 / 3 - x) * Real.exp (-3 * x)) x := by
  have harg : HasDerivAt (fun y : ℝ => -3 * y) (-3) x := by
    simpa only [id_eq, mul_comm, one_mul] using (hasDerivAt_id x).const_mul (-3)
  have hexp := (Real.hasDerivAt_exp (-3 * x)).comp x harg
  have hlin := ((hasDerivAt_id x).sub_const 1).div_const 3
  have hraw := hexp.mul hlin
  change HasDerivAt oneThirdExpPrimitive _ x at hraw
  apply hraw.congr_deriv
  simp only [Function.comp_apply, id_eq]
  ring

theorem one_third_exp_integral :
    (∫ x in (1 / 3 : ℝ)..1, (4 / 3 - x) * Real.exp (-3 * x))
      = 2 / (9 * Real.exp 1) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => one_third_exp_primitive_deriv x)
    ((by fun_prop : Continuous
      (fun x : ℝ => (4 / 3 - x) * Real.exp (-3 * x))).intervalIntegrable _ _)]
  unfold oneThirdExpPrimitive
  rw [show -3 * (1 / 3 : ℝ) = -1 by norm_num, Real.exp_neg]
  norm_num
  have he : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
  field_simp [he]

noncomputable def oneThirdLateIntegral : ℝ :=
  ∫ t in (1 : ℝ)..3, (t - 4) * U (1 / 3) 1 t

theorem one_third_late_integral_eq_series :
    oneThirdLateIntegral =
      6 * (oneThirdLateSeries - 1 / (3 * Real.exp 1)) := by
  let f := fun t : ℝ => (t - 4) * U (1 / 3) 1 t
  have hsub :
      3 * (∫ x in (1 / 3 : ℝ)..1, f (3 * x))
        = ∫ t in (1 : ℝ)..3, f t := by
    simpa [smul_eq_mul, f] using
      (intervalIntegral.smul_integral_comp_mul_left
        (f := f) (a := (1 / 3 : ℝ)) (b := 1) (3 : ℝ))
  have hU (x : ℝ) :
      U (1 / 3) 1 (3 * x) = Real.exp (-3 * x) - U (1 / 3) 1 x := by
    have h := scalarCertificateTightU_functional_identity
      (ρ := (1 / 3 : ℝ)) (ξ := 1) (t := 3 * x) (by norm_num) (by norm_num)
    rw [show (1 / 3 : ℝ) * (3 * x) = x by ring] at h
    rw [show -(3 * x) = -3 * x by ring] at h
    linarith
  have hUcont :
      ContinuousOn (fun x => U (1 / 3) 1 x) (Set.uIcc (1 / 3 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (1 / 3 : ℝ) ≤ 1)]
    intro x hx
    simpa [U] using
      (hasDerivAt_Upower (ρ := (1 / 3 : ℝ)) (ξ := 1)
        (by norm_num) (by norm_num) (by linarith [hx.1]) (by linarith [hx.2]))
        |>.continuousAt.continuousWithinAt
  have hexpInt : IntervalIntegrable
      (fun x : ℝ => -9 * ((4 / 3 - x) * Real.exp (-3 * x)))
      MeasureTheory.volume (1 / 3) 1 :=
    (by fun_prop : Continuous
      (fun x : ℝ => -9 * ((4 / 3 - x) * Real.exp (-3 * x))))
      |>.intervalIntegrable _ _
  have hUInt : IntervalIntegrable
      (fun x : ℝ => 9 * ((4 / 3 - x) * U (1 / 3) 1 x))
      MeasureTheory.volume (1 / 3) 1 := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  unfold oneThirdLateIntegral
  rw [← hsub]
  rw [← intervalIntegral.integral_const_mul]
  calc
    (∫ x in (1 / 3 : ℝ)..1, 3 * f (3 * x))
        = ∫ x in (1 / 3 : ℝ)..1,
            -9 * ((4 / 3 - x) * Real.exp (-3 * x))
              + 9 * ((4 / 3 - x) * U (1 / 3) 1 x) := by
            apply intervalIntegral.integral_congr
            intro x _
            dsimp [f]
            rw [hU]
            ring
    _ = -9 * (∫ x in (1 / 3 : ℝ)..1,
            (4 / 3 - x) * Real.exp (-3 * x))
          + 9 * (∫ x in (1 / 3 : ℝ)..1,
            (4 / 3 - x) * U (1 / 3) 1 x) := by
            rw [intervalIntegral.integral_add hexpInt hUInt,
              intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const_mul]
    _ = 6 * (oneThirdLateSeries - 1 / (3 * Real.exp 1)) := by
          rw [one_third_exp_integral,
            one_third_weighted_integral_eq_series]
          have he : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
          field_simp [he]
          ring

theorem one_third_late_integral_positive :
    0 < oneThirdLateIntegral := by
  rw [one_third_late_integral_eq_series]
  have h := one_third_kernel_late_series_positive
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have heq : (1 / 3 : ℝ) / Real.exp 1 = 1 / (3 * Real.exp 1) := by
    field_simp [ne_of_gt he]
  rw [heq] at h
  positivity

end

end SkiRental.Scalar
