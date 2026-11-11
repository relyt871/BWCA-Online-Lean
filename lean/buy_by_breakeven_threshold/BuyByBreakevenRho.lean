import buy_by_breakeven_threshold.BuyByBreakevenThreshold

/-!
# Dependence of the buy-by-breakeven endpoint quantity on `rho`

This file completes the analytic part of the paper's threshold lemma.  It
proves continuity in `xi`, strict decrease of `rho ↦ D rho 1`, and the
existence and uniqueness of the threshold between `0.31087` and `0.31088`.
-/

namespace SkiRental.Analysis

open scoped BigOperators
open SkiRental.Scalar

noncomputable section

theorem buy_by_breakeven_DSeriesTerm_norm_le_factorial {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) (n : Nat) :
    ‖buyByBreakevenDSeriesTerm rho xi n‖ ≤
      1 / (Nat.factorial n : ℝ) := by
  have hc0 := buy_by_breakeven_DxiCoeff_nonneg hrho0 hrho1 n
  have hc1 := buy_by_breakeven_DxiCoeff_le_one hrho0 hrho1 n
  have hfac : 0 < (Nat.factorial n : ℝ) := by positivity
  have hpow : 0 ≤ rho ^ n := pow_nonneg hrho0 n
  have hden : 1 ≤ 1 + xi * rho ^ n := by
    nlinarith [mul_nonneg hxi0 hpow]
  have hquot : 0 ≤ xi / (1 + xi * rho ^ n) := by positivity
  have hquot_le : xi / (1 + xi * rho ^ n) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  unfold buyByBreakevenDSeriesTerm
  rw [norm_mul, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul, abs_of_nonneg hc0,
    abs_of_pos hfac, Real.norm_of_nonneg hquot]
  have hcdiv : buyByBreakevenDxiCoeff rho n / (Nat.factorial n : ℝ) ≤
      1 / (Nat.factorial n : ℝ) :=
    div_le_div_of_nonneg_right hc1 (le_of_lt hfac)
  calc
    buyByBreakevenDxiCoeff rho n / (Nat.factorial n : ℝ) *
          (xi / (1 + xi * rho ^ n))
        ≤ buyByBreakevenDxiCoeff rho n / (Nat.factorial n : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hquot_le (div_nonneg hc0 (le_of_lt hfac))
    _ ≤ 1 / (Nat.factorial n : ℝ) := by simpa using hcdiv

theorem buy_by_breakeven_D_continuousOn_xi {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) :
    ContinuousOn (fun xi => D rho xi) (Set.Icc (0 : ℝ) 1) := by
  have hrho0' : 0 ≤ rho := le_of_lt hrho0
  have hfac : Summable (fun n : Nat => (1 : ℝ) / (Nat.factorial n : ℝ)) := by
    simpa [one_pow] using Real.summable_pow_div_factorial (1 : ℝ)
  have hterms : ∀ n : Nat,
      ContinuousOn (fun xi => buyByBreakevenDSeriesTerm rho xi n)
        (Set.Icc (0 : ℝ) 1) := by
    intro n xi hxi
    exact (hasDerivAt_buyByBreakevenDSeriesTerm hrho0' hxi.1 n).continuousAt.continuousWithinAt
  have hsum : ContinuousOn
      (fun xi => ∑' n : Nat, buyByBreakevenDSeriesTerm rho xi n)
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_tsum hterms hfac
      (fun n xi hxi => buy_by_breakeven_DSeriesTerm_norm_le_factorial
        hrho0' hrho1 hxi.1 hxi.2 n)
  have hseries : ContinuousOn (fun xi => buyByBreakevenDSeries rho xi)
      (Set.Icc (0 : ℝ) 1) := by
    unfold buyByBreakevenDSeries
    exact hsum.const_mul (Real.exp 1 / rho)
  exact hseries.congr fun xi hxi =>
    buy_by_breakeven_D_eq_series hrho0' hrho1 hxi.1

def buyByBreakevenDRhoH (rho : ℝ) (n : Nat) : ℝ :=
  (1 + (n + 1 : ℝ) * rho ^ n + (n : ℝ) * rho ^ (n + 1)) /
    (1 + rho ^ n) ^ 2

def buyByBreakevenDRhoTerm (rho : ℝ) (n : Nat) : ℝ :=
  Real.exp 1 / rho *
    (((-1 : ℝ) ^ n /
      ((n + 1 : ℝ) * (Nat.factorial n : ℝ))) *
      ((1 - rho ^ (n + 1)) / (1 + rho ^ n)))

noncomputable def buyByBreakevenDRhoSeries (rho : ℝ) : ℝ :=
  ∑' n : Nat, buyByBreakevenDRhoTerm rho n

def buyByBreakevenDRhoCoreTerm (rho : ℝ) (n : Nat) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * buyByBreakevenDRhoH rho n /
    (Nat.factorial (n + 1) : ℝ)

def buyByBreakevenDRhoDerivTerm (rho : ℝ) (n : Nat) : ℝ :=
  Real.exp 1 / rho ^ 2 * buyByBreakevenDRhoCoreTerm rho n

theorem buy_by_breakeven_D_eq_rhoSeries {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) :
    D rho 1 = buyByBreakevenDRhoSeries rho := by
  rw [buy_by_breakeven_D_eq_series (le_of_lt hrho0) hrho1 (by norm_num)]
  unfold buyByBreakevenDSeries buyByBreakevenDRhoSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  unfold buyByBreakevenDRhoTerm buyByBreakevenDSeriesTerm
  unfold buyByBreakevenDxiCoeff
  simp only [one_mul]
  field_simp [hfac, hn]

theorem hasDerivAt_buyByBreakevenDRhoTerm {rho : ℝ}
    (hrho0 : 0 < rho) (n : Nat) :
    HasDerivAt (fun z => buyByBreakevenDRhoTerm z n)
      (buyByBreakevenDRhoDerivTerm rho n) rho := by
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hden : 1 + rho ^ n ≠ 0 := by positivity
  have hrho : rho ≠ 0 := ne_of_gt hrho0
  have hpow := (hasDerivAt_id rho).pow (n + 1)
  have hnum := (hasDerivAt_const rho 1).sub hpow
  have hdenDeriv := (hasDerivAt_const rho 1).add ((hasDerivAt_id rho).pow n)
  have hquot := hnum.div hdenDeriv hden
  have hrhoInv := (hasDerivAt_const rho (Real.exp 1)).div (hasDerivAt_id rho) hrho
  have hraw := hrhoInv.mul
    (hquot.const_mul ((-1 : ℝ) ^ n /
      ((n + 1 : ℝ) * (Nat.factorial n : ℝ))))
  change HasDerivAt
    (fun z => Real.exp 1 / z *
      (((-1 : ℝ) ^ n /
        ((n + 1 : ℝ) * (Nat.factorial n : ℝ))) *
        ((1 - z ^ (n + 1)) / (1 + z ^ n))))
      (buyByBreakevenDRhoDerivTerm rho n) rho
  apply hraw.congr_deriv
  unfold buyByBreakevenDRhoDerivTerm buyByBreakevenDRhoCoreTerm
  unfold buyByBreakevenDRhoH
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq, Pi.add_apply,
    zero_add, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
  rw [Nat.factorial_succ]
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp [hrho, hden, hfac]
  cases n with
  | zero => norm_num; ring
  | succ n =>
      rw [show n + 1 - 1 = n by omega]
      simp only [pow_succ]
      ring

theorem buy_by_breakeven_DRhoH_nonneg {rho : ℝ}
    (hrho0 : 0 ≤ rho) (n : Nat) :
    0 ≤ buyByBreakevenDRhoH rho n := by
  unfold buyByBreakevenDRhoH
  positivity

theorem buy_by_breakeven_DRhoH_le {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (n : Nat) :
    buyByBreakevenDRhoH rho n ≤ 2 * (n + 1 : ℝ) := by
  have hpowN : rho ^ n ≤ 1 := pow_le_one₀ hrho0 hrho1
  have hpowS : rho ^ (n + 1) ≤ 1 := pow_le_one₀ hrho0 hrho1
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hn1 : 0 ≤ (n + 1 : ℝ) := by positivity
  have hnum :
      1 + (n + 1 : ℝ) * rho ^ n + (n : ℝ) * rho ^ (n + 1)
        ≤ 2 * (n + 1 : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hpowN hn1,
      mul_le_mul_of_nonneg_left hpowS hn0]
  have hden0 : 0 < (1 + rho ^ n) ^ 2 := by positivity
  have hden1 : 1 ≤ (1 + rho ^ n) ^ 2 := by
    nlinarith [pow_nonneg hrho0 n]
  unfold buyByBreakevenDRhoH
  rw [div_le_iff₀ hden0]
  have hscale :
      2 * (n + 1 : ℝ) ≤ 2 * (n + 1 : ℝ) * (1 + rho ^ n) ^ 2 :=
    by
      have h := mul_le_mul_of_nonneg_left hden1
        (show 0 ≤ 2 * (n + 1 : ℝ) by positivity)
      simpa only [mul_one] using h
  exact hnum.trans hscale

theorem buy_by_breakeven_DRhoH_zero (rho : ℝ) :
    buyByBreakevenDRhoH rho 0 = 1 / 2 := by
  unfold buyByBreakevenDRhoH
  norm_num

theorem buy_by_breakeven_DRhoH_one {rho : ℝ} (hrho0 : 0 ≤ rho) :
    buyByBreakevenDRhoH rho 1 = 1 := by
  unfold buyByBreakevenDRhoH
  field_simp [show 1 + rho ≠ 0 by positivity]
  ring

theorem buy_by_breakeven_DRhoH_gt_one {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho < 1) {n : Nat} (hn : 2 ≤ n) :
    1 < buyByBreakevenDRhoH rho n := by
  have hpow0 : 0 < rho ^ n := pow_pos hrho0 n
  have hpow1 : rho ^ n < 1 := pow_lt_one₀ (le_of_lt hrho0) hrho1 (by omega)
  have hbracket : 0 < (n - 1 : ℝ) + (n : ℝ) * rho - rho ^ n := by
    have hncast : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [mul_pos (by positivity : (0 : ℝ) < n) hrho0]
  have hden : 0 < (1 + rho ^ n) ^ 2 := by positivity
  unfold buyByBreakevenDRhoH
  rw [lt_div_iff₀ hden]
  have hidentity :
      1 + (n + 1 : ℝ) * rho ^ n + (n : ℝ) * rho ^ (n + 1)
        - (1 + rho ^ n) ^ 2 =
      rho ^ n * ((n - 1 : ℝ) + (n : ℝ) * rho - rho ^ n) := by
    rw [pow_succ]
    ring
  nlinarith [mul_pos hpow0 hbracket]

theorem buy_by_breakeven_DRhoH_lt_index {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho < 1) {n : Nat} (hn : 1 ≤ n) :
    buyByBreakevenDRhoH rho n < (n + 1 : ℝ) := by
  have hpow0 : 0 ≤ rho ^ n := pow_nonneg (le_of_lt hrho0) n
  have hgap : 0 < (n + 1 : ℝ) - (n : ℝ) * rho := by
    have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [mul_lt_mul_of_pos_left hrho1 (by positivity : (0 : ℝ) < n)]
  have hden : 0 < (1 + rho ^ n) ^ 2 := by positivity
  unfold buyByBreakevenDRhoH
  rw [div_lt_iff₀ hden]
  have hidentity :
      (n + 1 : ℝ) * (1 + rho ^ n) ^ 2 -
        (1 + (n + 1 : ℝ) * rho ^ n + (n : ℝ) * rho ^ (n + 1)) =
      (n : ℝ) + rho ^ n *
        ((n + 1 : ℝ) - (n : ℝ) * rho +
          (n + 1 : ℝ) * rho ^ n) := by
    rw [pow_succ]
    ring
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hinner : 0 <
      (n + 1 : ℝ) - (n : ℝ) * rho +
        (n + 1 : ℝ) * rho ^ n := by
    exact add_pos_of_pos_of_nonneg hgap
      (mul_nonneg (by positivity) hpow0)
  have hright : 0 < (n : ℝ) + rho ^ n *
      ((n + 1 : ℝ) - (n : ℝ) * rho +
        (n + 1 : ℝ) * rho ^ n) :=
    add_pos_of_pos_of_nonneg hnpos (mul_nonneg hpow0 (le_of_lt hinner))
  nlinarith

theorem buy_by_breakeven_DRhoCore_pair_zero {rho : ℝ} (hrho0 : 0 ≤ rho) :
    buyByBreakevenDRhoCoreTerm rho 0 +
      buyByBreakevenDRhoCoreTerm rho 1 = 0 := by
  simp [buyByBreakevenDRhoCoreTerm, buy_by_breakeven_DRhoH_zero,
    buy_by_breakeven_DRhoH_one hrho0]

theorem buy_by_breakeven_DRhoCore_pair_neg {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho < 1) {k : Nat} (hk : 1 ≤ k) :
    buyByBreakevenDRhoCoreTerm rho (2 * k) +
      buyByBreakevenDRhoCoreTerm rho (2 * k + 1) < 0 := by
  have heven := buy_by_breakeven_DRhoH_gt_one hrho0 hrho1 (n := 2 * k) (by omega)
  have hodd := buy_by_breakeven_DRhoH_lt_index hrho0 hrho1
    (n := 2 * k + 1) (by omega)
  have hfac : 0 < (Nat.factorial (2 * k + 1) : ℝ) := by positivity
  have hindex : 0 < (2 * k + 2 : ℝ) := by positivity
  have hsignEven : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  have hsignOdd : (-1 : ℝ) ^ (2 * k + 1 + 1) = 1 := by
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, pow_mul]
    norm_num
  unfold buyByBreakevenDRhoCoreTerm
  rw [show Nat.factorial (2 * k + 1 + 1) =
      (2 * k + 2) * Nat.factorial (2 * k + 1) by
        rw [show 2 * k + 1 + 1 = (2 * k + 1) + 1 by omega,
          Nat.factorial_succ]]
  rw [hsignEven, hsignOdd]
  simp only [neg_mul, one_mul]
  push_cast
  have hodd' :
      buyByBreakevenDRhoH rho (2 * k + 1) < (2 * k + 2 : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_mul] at hodd ⊢
    linarith
  have hnum :
      -(2 * k + 2 : ℝ) * buyByBreakevenDRhoH rho (2 * k) +
        buyByBreakevenDRhoH rho (2 * k + 1) < 0 := by
    nlinarith [mul_lt_mul_of_pos_left heven hindex, hodd']
  calc
    -buyByBreakevenDRhoH rho (2 * k) /
          (Nat.factorial (2 * k + 1) : ℝ) +
        buyByBreakevenDRhoH rho (2 * k + 1) /
          ((2 * k + 2 : ℝ) * (Nat.factorial (2 * k + 1) : ℝ)) =
      (-(2 * k + 2 : ℝ) * buyByBreakevenDRhoH rho (2 * k) +
        buyByBreakevenDRhoH rho (2 * k + 1)) /
          ((2 * k + 2 : ℝ) * (Nat.factorial (2 * k + 1) : ℝ)) := by
            field_simp
    _ < 0 := by
      rw [div_lt_iff₀ (mul_pos hindex hfac)]
      simpa using hnum

theorem buy_by_breakeven_DRhoCoreTerm_norm_le {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (n : Nat) :
    ‖buyByBreakevenDRhoCoreTerm rho n‖ ≤
      2 / (Nat.factorial n : ℝ) := by
  have hH0 := buy_by_breakeven_DRhoH_nonneg hrho0 n
  have hHle := buy_by_breakeven_DRhoH_le hrho0 hrho1 n
  have hn1 : 0 < (n + 1 : ℝ) := by positivity
  have hfac : 0 < (Nat.factorial n : ℝ) := by positivity
  have hden : 0 < (n + 1 : ℝ) * (Nat.factorial n : ℝ) :=
    mul_pos hn1 hfac
  unfold buyByBreakevenDRhoCoreTerm
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    Real.norm_of_nonneg hH0, Nat.factorial_succ]
  norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [abs_of_pos hn1]
  rw [div_le_iff₀ hden]
  calc
    buyByBreakevenDRhoH rho n ≤ 2 * (n + 1 : ℝ) := hHle
    _ = (2 / (Nat.factorial n : ℝ)) *
          ((n + 1 : ℝ) * (Nat.factorial n : ℝ)) := by
            field_simp

theorem buy_by_breakeven_DRhoTerm_eq_DSeriesTerm {rho : ℝ}
    (hrho0 : 0 < rho) (n : Nat) :
    buyByBreakevenDRhoTerm rho n =
      Real.exp 1 / rho * buyByBreakevenDSeriesTerm rho 1 n := by
  have hrho : rho ≠ 0 := ne_of_gt hrho0
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hden : 1 + rho ^ n ≠ 0 := by positivity
  unfold buyByBreakevenDRhoTerm buyByBreakevenDSeriesTerm
  unfold buyByBreakevenDxiCoeff
  simp only [one_mul]
  field_simp [hrho, hn, hfac, hden]

theorem buy_by_breakeven_DRhoTerm_summable {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) :
    Summable (fun n : Nat => buyByBreakevenDRhoTerm rho n) := by
  have hfac : Summable (fun n : Nat => (1 : ℝ) / (Nat.factorial n : ℝ)) := by
    simpa [one_pow] using Real.summable_pow_div_factorial (1 : ℝ)
  have hterms : Summable
      (fun n : Nat => buyByBreakevenDSeriesTerm rho 1 n) := by
    refine Summable.of_norm_bounded hfac ?_
    intro n
    exact buy_by_breakeven_DSeriesTerm_norm_le_factorial
      (le_of_lt hrho0) hrho1 (by norm_num) (by norm_num) n
  have hscaled := hterms.mul_left (Real.exp 1 / rho)
  simpa only [← buy_by_breakeven_DRhoTerm_eq_DSeriesTerm hrho0] using hscaled

theorem buy_by_breakeven_DRhoDerivTerm_norm_le {rho y : ℝ}
    (hrho0 : 0 < rho)
    (hy : y ∈ Set.Ioo (rho / 2) 1) (n : Nat) :
    ‖buyByBreakevenDRhoDerivTerm y n‖ ≤
      (8 * Real.exp 1 / rho ^ 2) /
        (Nat.factorial n : ℝ) := by
  have hy0 : 0 < y := by nlinarith [hy.1]
  have hy1 : y ≤ 1 := le_of_lt hy.2
  have hcore := buy_by_breakeven_DRhoCoreTerm_norm_le
    (le_of_lt hy0) hy1 n
  have hrle : rho ≤ 2 * y := by nlinarith [hy.1]
  have hsquare : rho ^ 2 ≤ 4 * y ^ 2 := by
    nlinarith [mul_self_le_mul_self (le_of_lt hrho0) hrle]
  have hinv : 1 / y ^ 2 ≤ 4 / rho ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hy0) (sq_pos_of_pos hrho0)]
    simpa [pow_two] using hsquare
  have hexpInv : Real.exp 1 / y ^ 2 ≤
      4 * Real.exp 1 / rho ^ 2 := by
    have := mul_le_mul_of_nonneg_left hinv (Real.exp_pos 1).le
    calc
      Real.exp 1 / y ^ 2 = Real.exp 1 * (1 / y ^ 2) := by ring
      _ ≤ Real.exp 1 * (4 / rho ^ 2) := this
      _ = 4 * Real.exp 1 / rho ^ 2 := by ring
  unfold buyByBreakevenDRhoDerivTerm
  rw [norm_mul, Real.norm_of_nonneg (by positivity :
    0 ≤ Real.exp 1 / y ^ 2)]
  calc
    Real.exp 1 / y ^ 2 * ‖buyByBreakevenDRhoCoreTerm y n‖
        ≤ (4 * Real.exp 1 / rho ^ 2) *
            (2 / (Nat.factorial n : ℝ)) :=
          mul_le_mul hexpInv hcore (norm_nonneg _) (by positivity)
    _ = (8 * Real.exp 1 / rho ^ 2) /
          (Nat.factorial n : ℝ) := by ring

theorem hasDerivAt_buyByBreakevenDRhoSeries {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    HasDerivAt buyByBreakevenDRhoSeries
      (∑' n : Nat, buyByBreakevenDRhoDerivTerm rho n) rho := by
  let c : ℝ := 8 * Real.exp 1 / rho ^ 2
  have hfac : Summable (fun n : Nat => (1 : ℝ) / (Nat.factorial n : ℝ)) := by
    simpa [one_pow] using Real.summable_pow_div_factorial (1 : ℝ)
  have hbound : Summable (fun n : Nat => c / (Nat.factorial n : ℝ)) := by
    simpa [div_eq_mul_inv, mul_assoc] using hfac.mul_left c
  have hrhoMem : rho ∈ Set.Ioo (rho / 2) 1 := by
    constructor <;> nlinarith
  unfold buyByBreakevenDRhoSeries
  exact hasDerivAt_tsum_of_isPreconnected
    hbound isOpen_Ioo isPreconnected_Ioo
    (fun n y hy => hasDerivAt_buyByBreakevenDRhoTerm (by nlinarith [hy.1]) n)
    (fun n y hy => by
      change ‖buyByBreakevenDRhoDerivTerm y n‖ ≤
        (8 * Real.exp 1 / rho ^ 2) / (Nat.factorial n : ℝ)
      exact buy_by_breakeven_DRhoDerivTerm_norm_le hrho0 hy n)
    hrhoMem (buy_by_breakeven_DRhoTerm_summable hrho0 (le_of_lt hrho1)) hrhoMem

def buyByBreakevenDRhoCorePair (rho : ℝ) (k : Nat) : ℝ :=
  buyByBreakevenDRhoCoreTerm rho (2 * k) +
    buyByBreakevenDRhoCoreTerm rho (2 * k + 1)

theorem buy_by_breakeven_DRhoCoreTerm_summable {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    Summable (fun n : Nat => buyByBreakevenDRhoCoreTerm rho n) := by
  have hfac : Summable (fun n : Nat => (1 : ℝ) / (Nat.factorial n : ℝ)) := by
    simpa [one_pow] using Real.summable_pow_div_factorial (1 : ℝ)
  have hbound : Summable (fun n : Nat => 2 / (Nat.factorial n : ℝ)) := by
    simpa [div_eq_mul_inv, mul_assoc] using hfac.mul_left 2
  exact Summable.of_norm_bounded hbound
    (buy_by_breakeven_DRhoCoreTerm_norm_le hrho0 hrho1)

theorem buy_by_breakeven_DRhoCorePair_summable {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    Summable (fun k : Nat => buyByBreakevenDRhoCorePair rho k) := by
  have hcore := buy_by_breakeven_DRhoCoreTerm_summable hrho0 hrho1
  have hevenInj : Function.Injective (fun k : Nat => 2 * k) := by
    intro a b hab
    exact Nat.mul_left_cancel (by norm_num) hab
  have hoddInj : Function.Injective (fun k : Nat => 2 * k + 1) := by
    intro a b hab
    exact Nat.mul_left_cancel (by norm_num) (Nat.add_right_cancel hab)
  have heven : Summable
      (fun k : Nat => buyByBreakevenDRhoCoreTerm rho (2 * k)) := by
    simpa only [Function.comp_def] using
      hcore.comp_injective hevenInj
  have hodd : Summable
      (fun k : Nat => buyByBreakevenDRhoCoreTerm rho (2 * k + 1)) := by
    simpa only [Function.comp_def] using
      hcore.comp_injective hoddInj
  exact heven.add hodd

theorem buy_by_breakeven_DRhoCorePair_nonpos {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho < 1) (k : Nat) :
    buyByBreakevenDRhoCorePair rho k ≤ 0 := by
  by_cases hk : k = 0
  · subst k
    exact le_of_eq (buy_by_breakeven_DRhoCore_pair_zero (le_of_lt hrho0))
  · exact le_of_lt (buy_by_breakeven_DRhoCore_pair_neg hrho0 hrho1
      (Nat.one_le_iff_ne_zero.mpr hk))

theorem buy_by_breakeven_DRhoCorePair_one_neg {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    buyByBreakevenDRhoCorePair rho 1 < 0 := by
  exact buy_by_breakeven_DRhoCore_pair_neg hrho0 hrho1 (by norm_num)

theorem buy_by_breakeven_DRhoCorePair_tsum_neg {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    (∑' k : Nat, buyByBreakevenDRhoCorePair rho k) < 0 := by
  have hpairs := buy_by_breakeven_DRhoCorePair_summable
    (le_of_lt hrho0) (le_of_lt hrho1)
  have hzero : Summable (fun _ : Nat => (0 : ℝ)) := summable_zero
  have hlt :
      (∑' k : Nat, buyByBreakevenDRhoCorePair rho k) <
        ∑' _k : Nat, (0 : ℝ) :=
    Summable.tsum_lt_tsum
      (buy_by_breakeven_DRhoCorePair_nonpos hrho0 hrho1)
      (buy_by_breakeven_DRhoCorePair_one_neg hrho0 hrho1)
      hpairs hzero
  simpa using hlt

theorem buy_by_breakeven_DRhoCore_tsum_eq_pairs {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    (∑' n : Nat, buyByBreakevenDRhoCoreTerm rho n) =
      ∑' k : Nat, buyByBreakevenDRhoCorePair rho k := by
  have hcore := buy_by_breakeven_DRhoCoreTerm_summable hrho0 hrho1
  have hevenInj : Function.Injective (fun k : Nat => 2 * k) := by
    intro a b hab
    exact Nat.mul_left_cancel (by norm_num) hab
  have hoddInj : Function.Injective (fun k : Nat => 2 * k + 1) := by
    intro a b hab
    exact Nat.mul_left_cancel (by norm_num) (Nat.add_right_cancel hab)
  have heven : Summable
      (fun k : Nat => buyByBreakevenDRhoCoreTerm rho (2 * k)) := by
    simpa only [Function.comp_def] using
      hcore.comp_injective hevenInj
  have hodd : Summable
      (fun k : Nat => buyByBreakevenDRhoCoreTerm rho (2 * k + 1)) := by
    simpa only [Function.comp_def] using
      hcore.comp_injective hoddInj
  calc
    (∑' n : Nat, buyByBreakevenDRhoCoreTerm rho n) =
        (∑' k : Nat, buyByBreakevenDRhoCoreTerm rho (2 * k)) +
          ∑' k : Nat, buyByBreakevenDRhoCoreTerm rho (2 * k + 1) :=
      (tsum_even_add_odd heven hodd).symm
    _ = ∑' k : Nat, buyByBreakevenDRhoCorePair rho k := by
      rw [← Summable.tsum_add heven hodd]
      rfl

theorem buy_by_breakeven_DRhoCore_tsum_neg {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    (∑' n : Nat, buyByBreakevenDRhoCoreTerm rho n) < 0 := by
  rw [buy_by_breakeven_DRhoCore_tsum_eq_pairs
    (le_of_lt hrho0) (le_of_lt hrho1)]
  exact buy_by_breakeven_DRhoCorePair_tsum_neg hrho0 hrho1

theorem buy_by_breakeven_DRhoDeriv_tsum_neg {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    (∑' n : Nat, buyByBreakevenDRhoDerivTerm rho n) < 0 := by
  rw [show (∑' n : Nat, buyByBreakevenDRhoDerivTerm rho n) =
      Real.exp 1 / rho ^ 2 *
        ∑' n : Nat, buyByBreakevenDRhoCoreTerm rho n by
    unfold buyByBreakevenDRhoDerivTerm
    exact tsum_mul_left]
  exact mul_neg_of_pos_of_neg (by positivity)
    (buy_by_breakeven_DRhoCore_tsum_neg hrho0 hrho1)

theorem hasDerivAt_buy_by_breakeven_D_rho {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    HasDerivAt (fun z => D z 1)
      (∑' n : Nat, buyByBreakevenDRhoDerivTerm rho n) rho := by
  have hseries := hasDerivAt_buyByBreakevenDRhoSeries hrho0 hrho1
  apply hseries.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hrho0 hrho1] with z hz
  exact buy_by_breakeven_D_eq_rhoSeries hz.1 (le_of_lt hz.2)

theorem buy_by_breakeven_D_strictAntiOn_rho :
    StrictAntiOn (fun rho : ℝ => D rho 1) (Set.Ioo 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo (0 : ℝ) 1)
  · intro rho hrho
    exact (hasDerivAt_buy_by_breakeven_D_rho hrho.1 hrho.2).continuousAt.continuousWithinAt
  · intro rho hrho
    rw [interior_Ioo] at hrho
    rw [(hasDerivAt_buy_by_breakeven_D_rho hrho.1 hrho.2).deriv]
    exact buy_by_breakeven_DRhoDeriv_tsum_neg hrho.1 hrho.2

theorem buy_by_breakeven_D_eq_lowerRhoBridgeDSeries {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) :
    D rho 1 = lowerRhoBridgeDSeries rho := by
  rw [buy_by_breakeven_D_eq_rhoSeries hrho0 hrho1]
  unfold buyByBreakevenDRhoSeries lowerRhoBridgeDSeries lowerRhoBridgeSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have hrho : rho ≠ 0 := ne_of_gt hrho0
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hden : 1 + rho ^ n ≠ 0 := by positivity
  unfold buyByBreakevenDRhoTerm lowerRhoBridgeTerm
  rw [Nat.factorial_succ]
  norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [hrho, hn, hfac, hden]
  simp [hrho]

theorem buy_by_breakeven_lowerRhoBridgeTerm_succ_le {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (k : Nat) :
    lowerRhoBridgeTerm rho (k + 1) ≤ lowerRhoBridgeTerm rho k := by
  unfold lowerRhoBridgeTerm
  have hdenLeft :
      0 < (Nat.factorial (k + 2) : ℝ) * (1 + rho ^ (k + 1)) := by
    positivity
  have hdenRight :
      0 < (Nat.factorial (k + 1) : ℝ) * (1 + rho ^ k) := by
    positivity
  rw [div_le_div_iff₀ hdenLeft hdenRight]
  have hkExp : k + 2 ≤ 2 * (k + 1) := by omega
  have hpowCmp : rho ^ (2 * (k + 1)) ≤ rho ^ (k + 2) :=
    pow_le_pow_of_le_one hrho0 hrho1 hkExp
  have hmain :
      1 - rho ^ (k + 2) ≤
        (1 - rho ^ (k + 1)) * (1 + rho ^ (k + 1)) := by
    have hfirst :
        1 - rho ^ (k + 2) ≤ 1 - rho ^ (2 * (k + 1)) := by
      nlinarith
    have hid :
        1 - rho ^ (2 * (k + 1)) =
          (1 - rho ^ (k + 1)) * (1 + rho ^ (k + 1)) := by
      rw [show rho ^ (2 * (k + 1)) = (rho ^ (k + 1)) ^ 2 by
        rw [mul_comm, ← pow_mul]]
      ring
    linarith
  have hfactor : 1 + rho ^ k ≤ (k + 2 : ℝ) := by
    have hpowLe : rho ^ k ≤ 1 := pow_le_one₀ hrho0 hrho1
    have hk2 : (2 : ℝ) ≤ k + 2 := by exact_mod_cast Nat.le_add_left 2 k
    nlinarith
  have hmainNonneg :
      0 ≤ (1 - rho ^ (k + 1)) * (1 + rho ^ (k + 1)) := by
    have hp : rho ^ (k + 1) ≤ 1 := pow_le_one₀ hrho0 hrho1
    positivity
  have hprod :
      (1 - rho ^ (k + 2)) * (1 + rho ^ k) ≤
        ((1 - rho ^ (k + 1)) * (1 + rho ^ (k + 1))) * (k + 2) := by
    have hleftNonneg : 0 ≤ 1 + rho ^ k := by positivity
    have hrightNonneg : 0 ≤ 1 - rho ^ (k + 2) := by
      have hp : rho ^ (k + 2) ≤ 1 := pow_le_one₀ hrho0 hrho1
      nlinarith
    nlinarith [mul_le_mul hmain hfactor hleftNonneg hmainNonneg]
  have hfac : ((Nat.factorial (k + 2) : Nat) : ℝ) =
      (k + 2 : ℝ) * (Nat.factorial (k + 1) : ℝ) := by
    have hfacNat : Nat.factorial (k + 2) =
        (k + 2) * Nat.factorial (k + 1) := by
      rw [show k + 2 = (k + 1).succ by omega, Nat.factorial_succ]
    exact_mod_cast hfacNat
  rw [hfac]
  have hfacNonneg : 0 ≤ (Nat.factorial (k + 1) : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hprod hfacNonneg
  ring_nf at hmul ⊢
  nlinarith

theorem buy_by_breakeven_lowerRhoBridgeTerm_antitone {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    Antitone (fun k => lowerRhoBridgeTerm rho k) := by
  apply antitone_nat_of_succ_le
  exact buy_by_breakeven_lowerRhoBridgeTerm_succ_le hrho0 hrho1

theorem buy_by_breakeven_partial_even_le_series {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (k : Nat) :
    (Finset.range (2 * k)).sum
        (fun n => (-1 : ℝ) ^ n * lowerRhoBridgeTerm rho n) ≤
      lowerRhoBridgeSeries rho := by
  have hsum := lowerRhoBridgeTerm_summable hrho0 hrho1
  have htend := hsum.tendsto_alternating_series_tsum
  have hbound :=
    (buy_by_breakeven_lowerRhoBridgeTerm_antitone hrho0 hrho1).alternating_series_le_tendsto
      htend k
  simpa only [lowerRhoBridgeSeries] using hbound

theorem buy_by_breakeven_series_le_partial_odd {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (k : Nat) :
    lowerRhoBridgeSeries rho ≤
      (Finset.range (2 * k + 1)).sum
        (fun n => (-1 : ℝ) ^ n * lowerRhoBridgeTerm rho n) := by
  have hsum := lowerRhoBridgeTerm_summable hrho0 hrho1
  have htend := hsum.tendsto_alternating_series_tsum
  have hbound :=
    (buy_by_breakeven_lowerRhoBridgeTerm_antitone hrho0 hrho1).tendsto_le_alternating_series
      htend k
  simpa only [lowerRhoBridgeSeries] using hbound

theorem buy_by_breakeven_left_endpoint_gt_one :
    1 < D (31087 / 100000 : ℝ) 1 := by
  let rho : ℝ := 31087 / 100000
  let p : ℝ := (Finset.range 10).sum
    (fun n => (-1 : ℝ) ^ n * lowerRhoBridgeTerm rho n)
  have hrho0 : 0 < rho := by norm_num [rho]
  have hrho1 : rho ≤ 1 := by norm_num [rho]
  have hpartial : p ≤ lowerRhoBridgeSeries rho := by
    simpa [p] using
      buy_by_breakeven_partial_even_le_series (le_of_lt hrho0) hrho1 5
  have hpartial0 : 0 < p := by
    norm_num [p, rho, lowerRhoBridgeTerm, Finset.sum_range_succ]
  have heLower : (271828182 / 100000000 : ℝ) < Real.exp 1 :=
    (by norm_num : (271828182 / 100000000 : ℝ) < 2.7182818283).trans
      Real.exp_one_gt_d9
  have hfactor :
      (271828182 / 100000000 : ℝ) / rho < Real.exp 1 / rho :=
    div_lt_div_of_pos_right heLower hrho0
  have harith :
      1 < ((271828182 / 100000000 : ℝ) / rho) * p := by
    norm_num [p, rho, lowerRhoBridgeTerm, Finset.sum_range_succ]
  have hscale :
      ((271828182 / 100000000 : ℝ) / rho) * p <
        (Real.exp 1 / rho) * p :=
    mul_lt_mul_of_pos_right hfactor hpartial0
  have hseries :
      (Real.exp 1 / rho) * p ≤
        (Real.exp 1 / rho) * lowerRhoBridgeSeries rho :=
    mul_le_mul_of_nonneg_left hpartial (by positivity)
  rw [buy_by_breakeven_D_eq_lowerRhoBridgeDSeries hrho0 hrho1]
  unfold lowerRhoBridgeDSeries
  exact harith.trans (hscale.trans_le hseries)

theorem buy_by_breakeven_right_endpoint_lt_one :
    D (31088 / 100000 : ℝ) 1 < 1 := by
  let rho : ℝ := 31088 / 100000
  let p : ℝ := (Finset.range 11).sum
    (fun n => (-1 : ℝ) ^ n * lowerRhoBridgeTerm rho n)
  have hrho0 : 0 < rho := by norm_num [rho]
  have hrho1 : rho ≤ 1 := by norm_num [rho]
  have hpartial : lowerRhoBridgeSeries rho ≤ p := by
    simpa [p] using
      buy_by_breakeven_series_le_partial_odd (le_of_lt hrho0) hrho1 5
  have hpartial0 : 0 < p := by
    norm_num [p, rho, lowerRhoBridgeTerm, Finset.sum_range_succ]
  have heUpper : Real.exp 1 < (271828183 / 100000000 : ℝ) :=
    Real.exp_one_lt_d9.trans (by norm_num)
  have hfactor :
      Real.exp 1 / rho < (271828183 / 100000000 : ℝ) / rho :=
    div_lt_div_of_pos_right heUpper hrho0
  have hscale :
      (Real.exp 1 / rho) * p <
        ((271828183 / 100000000 : ℝ) / rho) * p :=
    mul_lt_mul_of_pos_right hfactor hpartial0
  have harith :
      ((271828183 / 100000000 : ℝ) / rho) * p < 1 := by
    norm_num [p, rho, lowerRhoBridgeTerm, Finset.sum_range_succ]
  have hseries :
      (Real.exp 1 / rho) * lowerRhoBridgeSeries rho ≤
        (Real.exp 1 / rho) * p :=
    mul_le_mul_of_nonneg_left hpartial (by positivity)
  rw [buy_by_breakeven_D_eq_lowerRhoBridgeDSeries hrho0 hrho1]
  unfold lowerRhoBridgeDSeries
  exact hseries.trans_lt (hscale.trans harith)

theorem buy_by_breakeven_D_continuousOn_rho :
    ContinuousOn (fun rho : ℝ => D rho 1) (Set.Ioo 0 1) := by
  intro rho hrho
  exact (hasDerivAt_buy_by_breakeven_D_rho hrho.1 hrho.2).continuousAt.continuousWithinAt

theorem buy_by_breakeven_rho_star_exists_unique_narrow :
    ∃! rho : ℝ,
      rho ∈ Set.Icc (31087 / 100000 : ℝ) (31088 / 100000 : ℝ) ∧
        D rho 1 = 1 := by
  let lo : ℝ := 31087 / 100000
  let hi : ℝ := 31088 / 100000
  have hlo0 : 0 < lo := by norm_num [lo]
  have hhi1 : hi < 1 := by norm_num [hi]
  have hlohi : lo ≤ hi := by norm_num [lo, hi]
  have hcont : ContinuousOn (fun rho : ℝ => D rho 1) (Set.Icc lo hi) := by
    intro rho hrho
    have hrho0 : 0 < rho := lt_of_lt_of_le hlo0 hrho.1
    have hrho1 : rho < 1 := lt_of_le_of_lt hrho.2 hhi1
    exact (hasDerivAt_buy_by_breakeven_D_rho hrho0 hrho1).continuousAt.continuousWithinAt
  have hone : (1 : ℝ) ∈ Set.Icc (D hi 1) (D lo 1) := by
    constructor
    · simpa [hi] using le_of_lt buy_by_breakeven_right_endpoint_lt_one
    · simpa [lo] using le_of_lt buy_by_breakeven_left_endpoint_gt_one
  have himage : (1 : ℝ) ∈
      (fun rho : ℝ => D rho 1) '' Set.Icc lo hi :=
    intermediate_value_Icc' hlohi hcont hone
  rcases himage with ⟨rhoStar, hrhoStar, hroot⟩
  change D rhoStar 1 = 1 at hroot
  refine ⟨rhoStar, ⟨?_, hroot⟩, ?_⟩
  · simpa [lo, hi] using hrhoStar
  · intro rho hrho
    have hstarMem : rhoStar ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_lt_of_le hlo0 hrhoStar.1, lt_of_le_of_lt hrhoStar.2 hhi1⟩
    have hrhoMem : rho ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 31087 / 100000) hrho.1.1
      · exact lt_of_le_of_lt hrho.1.2 (by norm_num : (31088 / 100000 : ℝ) < 1)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstrict := buy_by_breakeven_D_strictAntiOn_rho hrhoMem hstarMem hlt
      change D rhoStar 1 < D rho 1 at hstrict
      rw [hroot, hrho.2] at hstrict
      exact (lt_irrefl 1 hstrict)
    · have hstrict := buy_by_breakeven_D_strictAntiOn_rho hstarMem hrhoMem hgt
      change D rho 1 < D rhoStar 1 at hstrict
      rw [hroot, hrho.2] at hstrict
      exact (lt_irrefl 1 hstrict)

noncomputable def buyByBreakevenRhoStar : ℝ :=
  Classical.choose buy_by_breakeven_rho_star_exists_unique_narrow

theorem buy_by_breakeven_rho_star_mem :
    buyByBreakevenRhoStar ∈
      Set.Icc (31087 / 100000 : ℝ) (31088 / 100000 : ℝ) :=
  (Classical.choose_spec buy_by_breakeven_rho_star_exists_unique_narrow).1.1

theorem buy_by_breakeven_rho_star_eq :
    D buyByBreakevenRhoStar 1 = 1 :=
  (Classical.choose_spec buy_by_breakeven_rho_star_exists_unique_narrow).1.2

theorem buy_by_breakeven_rho_star_rounds_to_0311 :
    |buyByBreakevenRhoStar - (311 / 1000 : ℝ)| < 1 / 2000 := by
  rw [abs_lt]
  constructor <;> nlinarith [buy_by_breakeven_rho_star_mem.1,
    buy_by_breakeven_rho_star_mem.2]

theorem buy_by_breakeven_rho_star_unique {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho < 1) (hroot : D rho 1 = 1) :
    rho = buyByBreakevenRhoStar := by
  have hstar0 : 0 < buyByBreakevenRhoStar :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 31087 / 100000)
      buy_by_breakeven_rho_star_mem.1
  have hstar1 : buyByBreakevenRhoStar < 1 :=
    lt_of_le_of_lt buy_by_breakeven_rho_star_mem.2
      (by norm_num : (31088 / 100000 : ℝ) < 1)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstrict := buy_by_breakeven_D_strictAntiOn_rho
      ⟨hrho0, hrho1⟩ ⟨hstar0, hstar1⟩ hlt
    change D buyByBreakevenRhoStar 1 < D rho 1 at hstrict
    rw [buy_by_breakeven_rho_star_eq, hroot] at hstrict
    exact lt_irrefl 1 hstrict
  · have hstrict := buy_by_breakeven_D_strictAntiOn_rho
      ⟨hstar0, hstar1⟩ ⟨hrho0, hrho1⟩ hgt
    change D rho 1 < D buyByBreakevenRhoStar 1 at hstrict
    rw [buy_by_breakeven_rho_star_eq, hroot] at hstrict
    exact lt_irrefl 1 hstrict

theorem buy_by_breakeven_D_gt_one_below_rho_star {rho : ℝ}
    (hrho0 : 0 < rho) (hrhoStar : rho < buyByBreakevenRhoStar) :
    1 < D rho 1 := by
  have hstar1 : buyByBreakevenRhoStar < 1 :=
    lt_of_le_of_lt buy_by_breakeven_rho_star_mem.2
      (by norm_num : (31088 / 100000 : ℝ) < 1)
  have hstrict := buy_by_breakeven_D_strictAntiOn_rho
    ⟨hrho0, lt_trans hrhoStar hstar1⟩
    ⟨lt_trans hrho0 hrhoStar, hstar1⟩ hrhoStar
  simpa [buy_by_breakeven_rho_star_eq] using hstrict

theorem buy_by_breakeven_D_lt_one_above_rho_star {rho : ℝ}
    (hrho1 : rho < 1) (hrhoStar : buyByBreakevenRhoStar < rho) :
    D rho 1 < 1 := by
  have hstar0 : 0 < buyByBreakevenRhoStar :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 31087 / 100000)
      buy_by_breakeven_rho_star_mem.1
  have hstrict := buy_by_breakeven_D_strictAntiOn_rho
    ⟨hstar0, lt_trans hrhoStar hrho1⟩
    ⟨lt_trans hstar0 hrhoStar, hrho1⟩ hrhoStar
  simpa [buy_by_breakeven_rho_star_eq] using hstrict

end

end SkiRental.Analysis
