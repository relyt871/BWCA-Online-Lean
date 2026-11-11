import SkiRental.Analysis

/-!
# Entry point for `lem:buy-by-breakeven-threshold-bound`

This file gives stable Lean entry points for the checked parts of the paper
lemma with label `lem:buy-by-breakeven-threshold-bound`.
-/

namespace SkiRental.Analysis

open scoped BigOperators
open SkiRental.Scalar

noncomputable section

noncomputable abbrev buyByBreakevenOrbitWeight :=
  SkiRental.Scalar.scalarCertificateTightOrbitWeight

noncomputable abbrev buyByBreakevenMultiplier :=
  SkiRental.Scalar.scalarCertificateTightMultiplier

noncomputable abbrev buyByBreakevenDxiFinite :=
  SkiRental.Scalar.scalarCertificateTightDxiFinite

theorem buy_by_breakeven_U_nonneg {rho xi t : ℝ}
    (hrho0 : (31 / 100 : ℝ) ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ U rho xi t :=
  scalarCertificateTightU_nonneg_on_box hrho0 hrho1 hxi0 hxi1 ht0 ht1

theorem buy_by_breakeven_U_power_series (rho xi t : ℝ) :
    U rho xi t = ∑' n : Nat,
      (-t) ^ n / ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n)) :=
  scalarCertificateTightU_eq_power_series rho xi t

theorem buy_by_breakeven_U_functional_identity {rho xi t : ℝ}
    (hrho0 : 0 ≤ rho) (hxi0 : 0 ≤ xi) :
    U rho xi t + xi * U rho xi (rho * t) = Real.exp (-t) :=
  scalarCertificateTightU_functional_identity hrho0 hxi0

theorem buy_by_breakeven_multiplier_recurrence {rho gamma x : ℝ}
    (hrho0 : 0 ≤ rho) (hgamma : 0 < gamma) (k : Nat) :
    gamma * buyByBreakevenMultiplier rho gamma x k
      + buyByBreakevenMultiplier rho gamma x (k + 1)
      = buyByBreakevenOrbitWeight rho x k :=
  scalarCertificateTightMultiplier_recurrence hrho0 hgamma k

theorem buy_by_breakeven_multiplier_nonneg {rho gamma x : ℝ}
    (hrho0 : (31 / 100 : ℝ) ≤ rho) (hrho1 : rho ≤ 1)
    (hgamma : 0 < gamma) (hxi1 : rho / gamma ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : Nat) :
    0 ≤ buyByBreakevenMultiplier rho gamma x k :=
  scalarCertificateTightMultiplier_nonneg_on_box
    hrho0 hrho1 hgamma hxi1 hx0 hx1 k

theorem buy_by_breakeven_Dxi_finite_nonneg {rho xi : ℝ}
    (hrho0 : (31 / 100 : ℝ) ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    0 ≤ buyByBreakevenDxiFinite rho xi :=
  scalarCertificateTightDxiFinite_nonneg_on_box hrho0 hrho1 hxi0 hxi1

/-! ## The full `xi` derivative and endpoint comparison -/

def buyByBreakevenDxiCoeff (rho : ℝ) (n : Nat) : ℝ :=
  (1 - rho ^ (n + 1)) / (n + 1 : ℝ)

def buyByBreakevenDxiMag (rho xi : ℝ) (n : Nat) : ℝ :=
  buyByBreakevenDxiCoeff rho n /
    ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n) ^ 2)

def buyByBreakevenDxiTerm (rho xi : ℝ) (n : Nat) : ℝ :=
  (-1 : ℝ) ^ n * buyByBreakevenDxiMag rho xi n

def buyByBreakevenDxiFourTerm (rho xi : ℝ) : ℝ :=
  (Finset.range 4).sum (fun n => buyByBreakevenDxiTerm rho xi n)

noncomputable def buyByBreakevenDxiSeries (rho xi : ℝ) : ℝ :=
  ∑' n : Nat, buyByBreakevenDxiTerm rho xi n

theorem buy_by_breakeven_DxiCoeff_nonneg {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (n : Nat) :
    0 ≤ buyByBreakevenDxiCoeff rho n := by
  unfold buyByBreakevenDxiCoeff
  exact div_nonneg (sub_nonneg.mpr (pow_le_one₀ hrho0 hrho1)) (by positivity)

theorem buy_by_breakeven_DxiCoeff_le_one {rho : ℝ}
    (hrho0 : 0 ≤ rho) (_hrho1 : rho ≤ 1) (n : Nat) :
    buyByBreakevenDxiCoeff rho n ≤ 1 := by
  unfold buyByBreakevenDxiCoeff
  have hpow : 0 ≤ rho ^ (n + 1) := pow_nonneg hrho0 _
  have hden : (0 : ℝ) < n + 1 := by positivity
  rw [div_le_iff₀ hden]
  nlinarith

theorem buy_by_breakeven_DxiCoeff_succ_le {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (n : Nat) :
    buyByBreakevenDxiCoeff rho (n + 1)
      ≤ buyByBreakevenDxiCoeff rho n := by
  let S : ℝ := (Finset.range (n + 1)).sum (fun k => rho ^ k)
  have hlast : (n + 1 : ℝ) * rho ^ (n + 1) ≤ S := by
    dsimp [S]
    calc
      (n + 1 : ℝ) * rho ^ (n + 1)
          = (Finset.range (n + 1)).sum (fun _ => rho ^ (n + 1)) := by
              simp
      _ ≤ (Finset.range (n + 1)).sum (fun k => rho ^ k) := by
            apply Finset.sum_le_sum
            intro k hk
            exact pow_le_pow_of_le_one hrho0 hrho1 (Finset.mem_range.mp hk).le
  have hgeom_n : S * (1 - rho) = 1 - rho ^ (n + 1) := by
    dsimp [S]
    exact geom_sum_mul_neg rho (n + 1)
  have hgeom_succ :
      (S + rho ^ (n + 1)) * (1 - rho) = 1 - rho ^ (n + 2) := by
    have h := geom_sum_mul_neg rho (n + 2)
    rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ] at h
    simpa [S] using h
  have hone_sub_nonneg : 0 ≤ 1 - rho := sub_nonneg.mpr hrho1
  have hscaled :
      (n + 1 : ℝ) * (rho ^ (n + 1) * (1 - rho))
        ≤ S * (1 - rho) := by
    nlinarith [mul_le_mul_of_nonneg_right hlast hone_sub_nonneg]
  unfold buyByBreakevenDxiCoeff
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show n + 1 + 1 = n + 2 by omega]
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 1 + 1 := by positivity
  rw [div_le_div_iff₀ hn2 hn1]
  nlinarith

theorem buy_by_breakeven_DxiMag_nonneg {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (_hxi0 : 0 ≤ xi) (n : Nat) :
    0 ≤ buyByBreakevenDxiMag rho xi n := by
  unfold buyByBreakevenDxiMag
  exact div_nonneg (buy_by_breakeven_DxiCoeff_nonneg hrho0 hrho1 n)
    (mul_nonneg (by positivity) (sq_nonneg _))

theorem buy_by_breakeven_DxiMag_le_factorial {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (n : Nat) :
    buyByBreakevenDxiMag rho xi n ≤ 1 / (Nat.factorial n : ℝ) := by
  unfold buyByBreakevenDxiMag
  have hc_le := buy_by_breakeven_DxiCoeff_le_one hrho0 hrho1 n
  have hfac_pos : 0 < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hbase : 1 ≤ 1 + xi * rho ^ n := by
    nlinarith [mul_nonneg hxi0 (pow_nonneg hrho0 n)]
  have hsq : 1 ≤ (1 + xi * rho ^ n) ^ 2 := by nlinarith
  have hden_ge :
      (Nat.factorial n : ℝ)
        ≤ (Nat.factorial n : ℝ) * (1 + xi * rho ^ n) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq (le_of_lt hfac_pos)]
  have hden_pos :
      0 < (Nat.factorial n : ℝ) * (1 + xi * rho ^ n) ^ 2 := by
    positivity
  calc
    buyByBreakevenDxiCoeff rho n /
          ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n) ^ 2)
        ≤ 1 / ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n) ^ 2) := by
          exact div_le_div_of_nonneg_right hc_le (le_of_lt hden_pos)
    _ ≤ 1 / (Nat.factorial n : ℝ) := by
          exact div_le_div_of_nonneg_left (by norm_num) hfac_pos hden_ge

theorem buy_by_breakeven_DxiMag_summable {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hxi0 : 0 ≤ xi) :
    Summable (fun n => buyByBreakevenDxiMag rho xi n) := by
  have hfac : Summable (fun n : Nat => (1 : ℝ) / (Nat.factorial n : ℝ)) := by
    simpa [one_pow] using Real.summable_pow_div_factorial (1 : ℝ)
  exact Summable.of_nonneg_of_le
    (fun n => buy_by_breakeven_DxiMag_nonneg hrho0 hrho1 hxi0 n)
    (fun n => buy_by_breakeven_DxiMag_le_factorial hrho0 hrho1 hxi0 n)
    hfac

theorem buy_by_breakeven_DxiMag_succ_le {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    {n : Nat} (hn : 4 ≤ n) :
    buyByBreakevenDxiMag rho xi (n + 1)
      ≤ buyByBreakevenDxiMag rho xi n := by
  let A : ℝ := 1 + xi * rho ^ n
  let B : ℝ := 1 + xi * rho ^ (n + 1)
  have hA_nonneg : 0 ≤ A := by dsimp [A]; positivity
  have hB_pos : 0 < B := by dsimp [B]; positivity
  have hA_le_two : A ≤ 2 := by
    dsimp [A]
    have hp : rho ^ n ≤ 1 := pow_le_one₀ hrho0 hrho1
    have hmul : xi * rho ^ n ≤ 1 := by
      simpa using mul_le_mul hxi1 hp (pow_nonneg hrho0 n) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hB_ge_one : 1 ≤ B := by
    dsimp [B]
    nlinarith [mul_nonneg hxi0 (pow_nonneg hrho0 (n + 1))]
  have hA_le_twoB : A ≤ 2 * B := by nlinarith
  have hA_sq_le_fourB : A ^ 2 ≤ 4 * B ^ 2 := by
    have htwoB_nonneg : 0 ≤ 2 * B := by positivity
    have hsq := mul_le_mul hA_le_twoB hA_le_twoB hA_nonneg htwoB_nonneg
    nlinarith
  have hfour : (4 : ℝ) ≤ n + 1 := by exact_mod_cast (show 4 ≤ n + 1 by omega)
  have hA_sq_le_nB : A ^ 2 ≤ (n + 1 : ℝ) * B ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hfour (sq_nonneg B), hA_sq_le_fourB]
  have hc_le : buyByBreakevenDxiCoeff rho (n + 1)
      ≤ buyByBreakevenDxiCoeff rho n :=
    buy_by_breakeven_DxiCoeff_succ_le hrho0 hrho1 n
  have hc_nonneg : 0 ≤ buyByBreakevenDxiCoeff rho n :=
    buy_by_breakeven_DxiCoeff_nonneg hrho0 hrho1 n
  have hchain :
      buyByBreakevenDxiCoeff rho (n + 1) * A ^ 2
        ≤ buyByBreakevenDxiCoeff rho n * ((n + 1 : ℝ) * B ^ 2) := by
    calc
      buyByBreakevenDxiCoeff rho (n + 1) * A ^ 2
          ≤ buyByBreakevenDxiCoeff rho n * A ^ 2 :=
            mul_le_mul_of_nonneg_right hc_le (sq_nonneg A)
      _ ≤ buyByBreakevenDxiCoeff rho n * ((n + 1 : ℝ) * B ^ 2) :=
            mul_le_mul_of_nonneg_left hA_sq_le_nB hc_nonneg
  unfold buyByBreakevenDxiMag
  dsimp [A, B] at hchain
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hden_left :
      0 < ((n : ℝ) + 1) * (Nat.factorial n : ℝ)
        * (1 + xi * rho ^ (n + 1)) ^ 2 := by positivity
  have hden_right :
      0 < (Nat.factorial n : ℝ) * (1 + xi * rho ^ n) ^ 2 := by positivity
  rw [div_le_div_iff₀ hden_left hden_right]
  ring_nf at hchain ⊢
  have hfac_pos : 0 < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  nlinarith

theorem buy_by_breakeven_Dxi_fourTerm_eq_finite {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hxi0 : 0 ≤ xi) :
    buyByBreakevenDxiFourTerm rho xi = buyByBreakevenDxiFinite rho xi := by
  have h0 : 1 + xi ≠ 0 := by positivity
  have h1 : 1 + xi * rho ≠ 0 := by positivity
  have h2 : 1 + xi * rho ^ 2 ≠ 0 := by positivity
  have h3 : 1 + xi * rho ^ 3 ≠ 0 := by positivity
  unfold buyByBreakevenDxiFourTerm buyByBreakevenDxiTerm
    buyByBreakevenDxiMag buyByBreakevenDxiCoeff buyByBreakevenDxiFinite
    scalarCertificateTightDxiFinite lemma19DxiFinite
  norm_num [Finset.sum_range_succ]
  field_simp [h0, h1, h2, h3]
  ring

theorem buy_by_breakeven_DxiMag_shifted_antitone4 {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    Antitone (fun k => buyByBreakevenDxiMag rho xi (k + 4)) := by
  apply antitone_nat_of_succ_le
  intro k
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    buy_by_breakeven_DxiMag_succ_le (rho := rho) (xi := xi)
      hrho0 hrho1 hxi0 hxi1 (n := k + 4) (by omega)

theorem buy_by_breakeven_Dxi_tail4_nonneg {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    0 ≤ ∑' k : Nat, (-1 : ℝ) ^ k * buyByBreakevenDxiMag rho xi (k + 4) := by
  have hshift : Summable (fun k => buyByBreakevenDxiMag rho xi (k + 4)) := by
    exact (summable_nat_add_iff 4).mpr
      (buy_by_breakeven_DxiMag_summable hrho0 hrho1 hxi0)
  have hanti := buy_by_breakeven_DxiMag_shifted_antitone4 hrho0 hrho1 hxi0 hxi1
  have hbound := hanti.alternating_series_le_tendsto
    hshift.tendsto_alternating_series_tsum 0
  simpa using hbound

theorem buy_by_breakeven_Dxi_fourTerm_le_series {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    buyByBreakevenDxiFourTerm rho xi ≤ buyByBreakevenDxiSeries rho xi := by
  have hmag := buy_by_breakeven_DxiMag_summable hrho0 hrho1 hxi0
  have hterm : Summable (fun n => buyByBreakevenDxiTerm rho xi n) := by
    unfold buyByBreakevenDxiTerm
    exact hmag.alternating
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n => buyByBreakevenDxiTerm rho xi n) 4 hterm
  have htail : 0 ≤ ∑' k : Nat, buyByBreakevenDxiTerm rho xi (k + 4) := by
    unfold buyByBreakevenDxiTerm
    simpa [pow_add, show ((-1 : ℝ) ^ 4) = 1 by norm_num] using
      buy_by_breakeven_Dxi_tail4_nonneg hrho0 hrho1 hxi0 hxi1
  unfold buyByBreakevenDxiFourTerm buyByBreakevenDxiSeries
  linarith

theorem buy_by_breakeven_Dxi_series_nonneg {rho xi : ℝ}
    (hrho0 : (31 / 100 : ℝ) ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    0 ≤ buyByBreakevenDxiSeries rho xi := by
  have hrho_nonneg : 0 ≤ rho := by nlinarith
  have hfour : 0 ≤ buyByBreakevenDxiFourTerm rho xi := by
    rw [buy_by_breakeven_Dxi_fourTerm_eq_finite hrho_nonneg hxi0]
    exact buy_by_breakeven_Dxi_finite_nonneg hrho0 hrho1 hxi0 hxi1
  exact le_trans hfour
    (buy_by_breakeven_Dxi_fourTerm_le_series hrho_nonneg hrho1 hxi0 hxi1)

def buyByBreakevenDSeriesTerm (rho xi : ℝ) (n : Nat) : ℝ :=
  ((-1 : ℝ) ^ n * buyByBreakevenDxiCoeff rho n /
    (Nat.factorial n : ℝ)) * (xi / (1 + xi * rho ^ n))

noncomputable def buyByBreakevenDSeries (rho xi : ℝ) : ℝ :=
  Real.exp 1 / rho * ∑' n : Nat, buyByBreakevenDSeriesTerm rho xi n

theorem hasDerivAt_buyByBreakevenDSeriesTerm {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hxi0 : 0 ≤ xi) (n : Nat) :
    HasDerivAt (fun z => buyByBreakevenDSeriesTerm rho z n)
      (buyByBreakevenDxiTerm rho xi n) xi := by
  have hden : 1 + xi * rho ^ n ≠ 0 := by positivity
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
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  let c : ℝ := (-1 : ℝ) ^ n * buyByBreakevenDxiCoeff rho n /
    (Nat.factorial n : ℝ)
  have heq : c * (1 / (1 + xi * rho ^ n) ^ 2) =
      buyByBreakevenDxiTerm rho xi n := by
    dsimp [c]
    unfold buyByBreakevenDxiTerm buyByBreakevenDxiMag
    field_simp [hfac, hden]
  rw [← heq]
  simpa only [buyByBreakevenDSeriesTerm, c] using hquot.const_mul c

theorem buy_by_breakeven_DxiTerm_norm_le_factorial {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (n : Nat) :
    ‖buyByBreakevenDxiTerm rho xi n‖ ≤ 1 / (Nat.factorial n : ℝ) := by
  have hmag_nonneg := buy_by_breakeven_DxiMag_nonneg hrho0 hrho1 hxi0 n
  rw [buyByBreakevenDxiTerm, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul, abs_of_nonneg hmag_nonneg]
  exact buy_by_breakeven_DxiMag_le_factorial hrho0 hrho1 hxi0 n

set_option maxHeartbeats 800000 in
theorem hasDerivAt_buyByBreakevenDSeries {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hxi0 : 0 < xi) :
    HasDerivAt (fun z => buyByBreakevenDSeries rho z)
      (Real.exp 1 / rho * buyByBreakevenDxiSeries rho xi) xi := by
  have hfac : Summable (fun n : Nat => (1 : ℝ) / (Nat.factorial n : ℝ)) := by
    simpa [one_pow] using Real.summable_pow_div_factorial (1 : ℝ)
  have hbase : Summable (fun n => buyByBreakevenDSeriesTerm rho 1 n) := by
    refine Summable.of_norm_bounded hfac ?_
    intro n
    unfold buyByBreakevenDSeriesTerm
    simp only [one_mul]
    rw [norm_mul, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul, norm_div, norm_one]
    have hc_nonneg := buy_by_breakeven_DxiCoeff_nonneg hrho0 hrho1 n
    rw [abs_of_nonneg hc_nonneg, abs_of_pos (by positivity :
      0 < (Nat.factorial n : ℝ)), Real.norm_of_nonneg
        (by nlinarith [pow_nonneg hrho0 n] : 0 ≤ 1 + rho ^ n)]
    have hc_le := buy_by_breakeven_DxiCoeff_le_one hrho0 hrho1 n
    have hfac_pos : 0 < (Nat.factorial n : ℝ) := by
      exact_mod_cast Nat.factorial_pos n
    have hcdiv : buyByBreakevenDxiCoeff rho n / (Nat.factorial n : ℝ)
        ≤ 1 / (Nat.factorial n : ℝ) :=
      div_le_div_of_nonneg_right hc_le (le_of_lt hfac_pos)
    have hinv : 1 / (1 + rho ^ n) ≤ 1 := by
      exact div_le_one (by positivity) |>.2 (by nlinarith [pow_nonneg hrho0 n])
    have hcdiv_nonneg : 0 ≤ buyByBreakevenDxiCoeff rho n /
        (Nat.factorial n : ℝ) := div_nonneg hc_nonneg (le_of_lt hfac_pos)
    calc
      (buyByBreakevenDxiCoeff rho n / (Nat.factorial n : ℝ))
            * (1 / (1 + rho ^ n))
          ≤ (buyByBreakevenDxiCoeff rho n / (Nat.factorial n : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left hinv hcdiv_nonneg
      _ ≤ 1 / (Nat.factorial n : ℝ) := by simpa using hcdiv
  have hseries : HasDerivAt
      (fun z => ∑' n : Nat, buyByBreakevenDSeriesTerm rho z n)
      (buyByBreakevenDxiSeries rho xi) xi := by
    simpa [buyByBreakevenDxiSeries] using
      hasDerivAt_tsum_of_isPreconnected
        (α := Nat) (𝕜 := ℝ) (F := ℝ)
        (u := fun n : Nat => (1 : ℝ) / (Nat.factorial n : ℝ))
        (g := fun n z => buyByBreakevenDSeriesTerm rho z n)
        (g' := fun n z => buyByBreakevenDxiTerm rho z n)
        (t := Set.Ioi (0 : ℝ)) (y₀ := 1)
        hfac isOpen_Ioi isPreconnected_Ioi
        (fun n z hz => hasDerivAt_buyByBreakevenDSeriesTerm hrho0 (le_of_lt hz) n)
        (fun n z hz => buy_by_breakeven_DxiTerm_norm_le_factorial
          hrho0 hrho1 (le_of_lt hz) n)
        (by norm_num) hbase hxi0
  unfold buyByBreakevenDSeries
  exact hseries.const_mul (Real.exp 1 / rho)

noncomputable def buyByBreakevenUContinuousTerm
    (rho xi : ℝ) (n : Nat) : C(ℝ, ℝ) :=
  ⟨fun x => UpowerTerm rho xi n x, by
    unfold UpowerTerm
    fun_prop⟩

theorem buy_by_breakeven_UContinuousTerm_norm_le {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hxi0 : 0 ≤ xi) (n : Nat) :
    ‖(buyByBreakevenUContinuousTerm rho xi n).restrict
      (⟨Set.uIcc rho 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖
      ≤ 1 / (Nat.factorial n : ℝ) := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change ‖UpowerTerm rho xi n (x : ℝ)‖ ≤ 1 / (Nat.factorial n : ℝ)
  have hx : (x : ℝ) ∈ Set.Icc rho 1 := by
    simpa [Set.uIcc_of_le hrho1] using x.property
  have hx0 : 0 ≤ (x : ℝ) := le_trans hrho0 hx.1
  have hx1 : (x : ℝ) ≤ 1 := hx.2
  have hfac_pos : 0 < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hbase : 1 ≤ 1 + xi * rho ^ n := by
    nlinarith [mul_nonneg hxi0 (pow_nonneg hrho0 n)]
  have hden_pos : 0 < (Nat.factorial n : ℝ) * (1 + xi * rho ^ n) := by
    positivity
  have hden_ge : (Nat.factorial n : ℝ)
      ≤ (Nat.factorial n : ℝ) * (1 + xi * rho ^ n) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hbase (le_of_lt hfac_pos)
  unfold UpowerTerm
  rw [norm_div, norm_pow, norm_neg, Real.norm_of_nonneg hx0,
    Real.norm_of_nonneg (le_of_lt hden_pos)]
  calc
    (x : ℝ) ^ n /
          ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n))
        ≤ (x : ℝ) ^ n / (Nat.factorial n : ℝ) := by
          exact div_le_div_of_nonneg_left (pow_nonneg hx0 n) hfac_pos hden_ge
    _ ≤ 1 / (Nat.factorial n : ℝ) := by
          exact div_le_div_of_nonneg_right (pow_le_one₀ hx0 hx1) (le_of_lt hfac_pos)

theorem buy_by_breakeven_integral_U_eq_tsum {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hxi0 : 0 ≤ xi) :
    (∫ x in rho..1, U rho xi x)
      = ∑' n : Nat, ∫ x in rho..1, UpowerTerm rho xi n x := by
  have hfac : Summable (fun n : Nat => (1 : ℝ) / (Nat.factorial n : ℝ)) := by
    simpa [one_pow] using Real.summable_pow_div_factorial (1 : ℝ)
  have hnorm : Summable (fun n =>
      ‖(buyByBreakevenUContinuousTerm rho xi n).restrict
        (⟨Set.uIcc rho 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖) := by
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => buy_by_breakeven_UContinuousTerm_norm_le hrho0 hrho1 hxi0 n) hfac
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hnorm
  simpa [buyByBreakevenUContinuousTerm, U, Upower] using hswap.symm

theorem buy_by_breakeven_integral_UpowerTerm {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hxi0 : 0 ≤ xi) (n : Nat) :
    (∫ x in rho..1, UpowerTerm rho xi n x)
      = (-1 : ℝ) ^ n * buyByBreakevenDxiCoeff rho n /
          ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n)) := by
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hden : 1 + xi * rho ^ n ≠ 0 := by positivity
  calc
    (∫ x in rho..1, UpowerTerm rho xi n x)
        = ((-1 : ℝ) ^ n /
            ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n))) *
            (∫ x in rho..1, x ^ n) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro x _
          unfold UpowerTerm
          rw [show -x = (-1 : ℝ) * x by ring, mul_pow]
          ring
    _ = (-1 : ℝ) ^ n * buyByBreakevenDxiCoeff rho n /
          ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n)) := by
          rw [integral_pow]
          unfold buyByBreakevenDxiCoeff
          field_simp [hfac, hn, hden]
          ring

theorem buy_by_breakeven_D_eq_series {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hxi0 : 0 ≤ xi) :
    D rho xi = buyByBreakevenDSeries rho xi := by
  have hint := buy_by_breakeven_integral_U_eq_tsum hrho0 hrho1 hxi0
  have hterms :
      (∑' n : Nat, ∫ x in rho..1, UpowerTerm rho xi n x)
        = ∑' n : Nat, (-1 : ℝ) ^ n * buyByBreakevenDxiCoeff rho n /
            ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n)) := by
    exact tsum_congr (fun n => buy_by_breakeven_integral_UpowerTerm hrho0 hxi0 n)
  have hseries_terms :
      (∑' n : Nat, buyByBreakevenDSeriesTerm rho xi n)
        = xi * ∑' n : Nat, (-1 : ℝ) ^ n * buyByBreakevenDxiCoeff rho n /
            ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n)) := by
    calc
      (∑' n : Nat, buyByBreakevenDSeriesTerm rho xi n)
          = ∑' n : Nat, xi *
              ((-1 : ℝ) ^ n * buyByBreakevenDxiCoeff rho n /
                ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n))) := by
                apply tsum_congr
                intro n
                have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
                have hden : 1 + xi * rho ^ n ≠ 0 := by positivity
                unfold buyByBreakevenDSeriesTerm
                field_simp [hfac, hden]
      _ = xi * ∑' n : Nat, (-1 : ℝ) ^ n * buyByBreakevenDxiCoeff rho n /
              ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n)) := by
                rw [tsum_mul_left]
  unfold D buyByBreakevenDSeries
  rw [hint, hterms, hseries_terms]
  ring

theorem hasDerivAt_buy_by_breakeven_D {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hxi0 : 0 < xi) :
    HasDerivAt (fun z => D rho z)
      (Real.exp 1 / rho * buyByBreakevenDxiSeries rho xi) xi := by
  have hseries := hasDerivAt_buyByBreakevenDSeries hrho0 hrho1 hxi0
  apply hseries.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hxi0] with z hz
  exact buy_by_breakeven_D_eq_series hrho0 hrho1 (le_of_lt hz)

theorem buy_by_breakeven_D_le_endpoint {rho xi : ℝ}
    (hrho0 : (31 / 100 : ℝ) ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    D rho xi ≤ D rho 1 := by
  have hrho_pos : 0 < rho := by nlinarith
  have hrho_nonneg : 0 ≤ rho := le_of_lt hrho_pos
  rcases eq_or_lt_of_le hxi0 with rfl | hxi_pos
  · unfold D
    simp
    have hint_nonneg : 0 ≤ ∫ x in rho..1, U rho 1 x := by
      apply intervalIntegral.integral_nonneg hrho1
      intro x hx
      exact buy_by_breakeven_U_nonneg hrho0 hrho1 (by norm_num) (by norm_num)
        (le_trans hrho_nonneg hx.1) hx.2
    exact mul_nonneg (div_nonneg (le_of_lt (Real.exp_pos 1)) hrho_nonneg) hint_nonneg
  · have hderiv (z : ℝ) (hz0 : 0 < z) (hz1 : z ≤ 1) :
        HasDerivAt (fun w => D rho w)
          (Real.exp 1 / rho * buyByBreakevenDxiSeries rho z) z :=
        hasDerivAt_buy_by_breakeven_D hrho_nonneg hrho1 hz0
    have hcont : ContinuousOn (fun z => D rho z) (Set.Icc xi 1) := by
      intro z hz
      exact (hderiv z (lt_of_lt_of_le hxi_pos hz.1) hz.2).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (fun z => D rho z) (interior (Set.Icc xi 1)) := by
      intro z hz
      have hz' : z ∈ Set.Ioo xi 1 := by simpa [interior_Icc] using hz
      exact (hderiv z (lt_trans hxi_pos hz'.1) (le_of_lt hz'.2)).differentiableAt.differentiableWithinAt
    have hmono : MonotoneOn (fun z => D rho z) (Set.Icc xi 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc xi 1) hcont hdiff
      intro z hz
      have hz' : z ∈ Set.Ioo xi 1 := by simpa [interior_Icc] using hz
      have hd := hderiv z (lt_trans hxi_pos hz'.1) (le_of_lt hz'.2)
      rw [hd.deriv]
      exact mul_nonneg (div_nonneg (le_of_lt (Real.exp_pos 1)) (le_of_lt hrho_pos))
        (buy_by_breakeven_Dxi_series_nonneg hrho0 hrho1
          (le_of_lt (lt_trans hxi_pos hz'.1)) (le_of_lt hz'.2))
    exact hmono (by exact ⟨le_rfl, hxi1⟩) (by exact ⟨hxi1, le_rfl⟩) hxi1

theorem buy_by_breakeven_rho_star_left_check :
    SkiRental.Certificates.q 15 1000000 <
      SkiRental.Certificates.DLower031087MinusOne :=
  SkiRental.Certificates.D_031087_lower_bracket

theorem buy_by_breakeven_rho_star_right_check :
    SkiRental.Certificates.DUpper031088MinusOne <
      SkiRental.Certificates.q (-26) 1000000 :=
  SkiRental.Certificates.D_031088_upper_bracket

end

end SkiRental.Analysis
