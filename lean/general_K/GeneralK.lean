import SkiRental.Analysis

/-!
# Entry point for `lem:general-K`

This file gives stable Lean entry points for the finite algebraic certificates
in the paper lemma with label `lem:general-K`.

The analytic assembly around these facts remains in the paper text: termwise
differentiation of the series defining `K`, the connection from the displayed
series to the certified tails below, and the final intermediate-value argument
for the unique zero.
-/

namespace SkiRental.Scalar

open scoped BigOperators

noncomputable section

/-! ## Shared coefficient estimates -/

theorem general_K_sum_powers_lower {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (n : Nat) :
    (n : ℝ) * rho ^ (n + 1)
      ≤ (Finset.Icc 1 n).sum (fun k => rho ^ k) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hpow : rho ^ (n + 2) ≤ rho ^ (n + 1) :=
        pow_le_pow_of_le_one hrho0 hrho1 (by omega : n + 1 ≤ n + 2)
      have hsum :
          (Finset.Icc 1 (n + 1)).sum (fun k => rho ^ k)
            =
          (Finset.Icc 1 n).sum (fun k => rho ^ k) + rho ^ (n + 1) := by
        rw [Finset.sum_Icc_succ_top]
        omega
      rw [hsum]
      have hmain :
          (n : ℝ) * rho ^ (n + 2) + rho ^ (n + 2)
            ≤
          (Finset.Icc 1 n).sum (fun k => rho ^ k) + rho ^ (n + 1) := by
        have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hpow hn_nonneg, ih, hpow]
      have hcast :
          ((n + 1 : Nat) : ℝ) * rho ^ (n + 2)
            =
          (n : ℝ) * rho ^ (n + 2) + rho ^ (n + 2) := by
        norm_num [Nat.cast_add, Nat.cast_one, add_mul]
      rw [hcast]
      exact hmain

theorem general_K_sum_powers_upper {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (n : Nat) :
    (Finset.Icc 1 n).sum (fun k => rho ^ k) ≤ (n : ℝ) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hpow : rho ^ (n + 1) ≤ 1 := pow_le_one₀ hrho0 hrho1
      have hsum :
          (Finset.Icc 1 (n + 1)).sum (fun k => rho ^ k)
            =
          (Finset.Icc 1 n).sum (fun k => rho ^ k) + rho ^ (n + 1) := by
        rw [Finset.sum_Icc_succ_top]
        omega
      rw [hsum]
      norm_num [Nat.cast_add, Nat.cast_one]
      nlinarith

theorem general_K_dCoeff_nonneg {rho : ℝ}
    (hrho0 : 0 ≤ rho) (n : Nat) :
    0 ≤ dCoeff rho n := by
  unfold dCoeff
  positivity

theorem general_K_dCoeff_pos {rho : ℝ}
    (hrho0 : 0 ≤ rho) (n : Nat) :
    0 < dCoeff rho n := by
  unfold dCoeff
  have hden : 0 < ((n + 1 : ℝ) * (n + 2 : ℝ)) := by positivity
  have hnum : 0 < 1 + (n + 3 : ℝ) *
      (Finset.Icc 1 n).sum (fun k => rho ^ k) + rho ^ (n + 1) := by
    positivity
  exact div_pos hnum hden

theorem general_K_dCoeff_le_one {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (n : Nat) :
    dCoeff rho n ≤ 1 := by
  have hsum := general_K_sum_powers_upper hrho0 hrho1 n
  have hpow : rho ^ (n + 1) ≤ 1 := pow_le_one₀ hrho0 hrho1
  unfold dCoeff
  have hden_pos : 0 < ((n + 1 : ℝ) * (n + 2 : ℝ)) := by positivity
  rw [div_le_iff₀ hden_pos]
  nlinarith

theorem general_K_dCoeff_succ_le {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (n : Nat) :
    dCoeff rho (n + 1) ≤ dCoeff rho n := by
  let S : ℝ := (Finset.Icc 1 n).sum (fun k => rho ^ k)
  have hS : (n : ℝ) * rho ^ (n + 1) ≤ S := by
    dsimp [S]
    exact general_K_sum_powers_lower hrho0 hrho1 n
  have hp : rho ^ (n + 1) ≤ 1 := pow_le_one₀ hrho0 hrho1
  have hpow : rho ^ (n + 2) ≤ rho ^ (n + 1) :=
    pow_le_pow_of_le_one hrho0 hrho1 (by omega : n + 1 ≤ n + 2)
  have hnum_nonneg :
      0 ≤
        2 + ((n : ℝ) + 5) * S
          - ((n : ℝ) ^ 2 + 4 * (n : ℝ) + 1) * rho ^ (n + 1)
          - ((n : ℝ) + 1) * rho ^ (n + 2) := by
    have hscale :
        ((n : ℝ) + 5) * ((n : ℝ) * rho ^ (n + 1))
          ≤ ((n : ℝ) + 5) * S := by
      exact mul_le_mul_of_nonneg_left hS (by positivity)
    nlinarith
  have hsum_succ :
      (Finset.Icc 1 (n + 1)).sum (fun k => rho ^ k)
        =
      S + rho ^ (n + 1) := by
    dsimp [S]
    rw [Finset.sum_Icc_succ_top]
    omega
  unfold dCoeff
  rw [hsum_succ]
  change
    (1 + (((n + 1 : Nat) : ℝ) + 3) * (S + rho ^ (n + 1))
        + rho ^ ((n + 1) + 1))
      / ((((n + 1 : Nat) : ℝ) + 1) * (((n + 1 : Nat) : ℝ) + 2))
      ≤
    (1 + ((n : ℝ) + 3) * S + rho ^ (n + 1))
      / (((n : ℝ) + 1) * ((n : ℝ) + 2))
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show ((n : ℝ) + 1 + 3) = (n : ℝ) + 4 by ring]
  rw [show ((n : ℝ) + 1 + 1) = (n : ℝ) + 2 by ring]
  rw [show ((n : ℝ) + 1 + 2) = (n : ℝ) + 3 by ring]
  rw [show n + 1 + 1 = n + 2 by omega]
  have hden_left : 0 < ((n + 2 : ℝ) * (n + 3 : ℝ)) := by positivity
  have hden_right : 0 < ((n + 1 : ℝ) * (n + 2 : ℝ)) := by positivity
  rw [div_le_div_iff₀ hden_left hden_right]
  ring_nf at hnum_nonneg
  ring_nf
  nlinarith

/-! ## Alternating tails for the `xi`-derivative series -/

def generalKDxiMag (rho xi : ℝ) (n : Nat) : ℝ :=
  dCoeff rho n / ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n) ^ 2)

def generalKDxiTerm (rho xi : ℝ) (n : Nat) : ℝ :=
  (-1 : ℝ) ^ n * generalKDxiMag rho xi n

def generalKDxiFourTerm (rho xi : ℝ) : ℝ :=
  (Finset.range 4).sum (fun n => generalKDxiTerm rho xi n)

noncomputable def generalKDxiSeries (rho xi : ℝ) : ℝ :=
  ∑' n : Nat, generalKDxiTerm rho xi n

theorem general_K_DxiMag_nonneg {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (_hxi0 : 0 ≤ xi) (n : Nat) :
    0 ≤ generalKDxiMag rho xi n := by
  unfold generalKDxiMag
  exact div_nonneg (general_K_dCoeff_nonneg hrho0 n)
    (mul_nonneg (by positivity)
      (sq_nonneg (1 + xi * rho ^ n)))

theorem general_K_DxiMag_le_factorial {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (n : Nat) :
    generalKDxiMag rho xi n ≤ 1 / (Nat.factorial n : ℝ) := by
  unfold generalKDxiMag
  have hd_nonneg : 0 ≤ dCoeff rho n :=
    general_K_dCoeff_nonneg hrho0 n
  have hd_le : dCoeff rho n ≤ 1 :=
    general_K_dCoeff_le_one hrho0 hrho1 n
  have hfac_pos : 0 < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hden_pos : 0 < (Nat.factorial n : ℝ) * (1 + xi * rho ^ n) ^ 2 := by
    positivity
  have hden_ge :
      (Nat.factorial n : ℝ)
        ≤ (Nat.factorial n : ℝ) * (1 + xi * rho ^ n) ^ 2 := by
    have hfactor : 1 ≤ (1 + xi * rho ^ n) ^ 2 := by
      have hbase : 1 ≤ 1 + xi * rho ^ n := by
        nlinarith [mul_nonneg hxi0 (pow_nonneg hrho0 n)]
      have hbase_nonneg : 0 ≤ 1 + xi * rho ^ n := by linarith
      have hsq := mul_le_mul hbase hbase (by norm_num : (0 : ℝ) ≤ 1) hbase_nonneg
      nlinarith
    simpa [one_mul] using
      mul_le_mul_of_nonneg_left hfactor (le_of_lt hfac_pos)
  calc
    dCoeff rho n / ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n) ^ 2)
        ≤ 1 / ((Nat.factorial n : ℝ) * (1 + xi * rho ^ n) ^ 2) := by
          exact div_le_div_of_nonneg_right hd_le (le_of_lt hden_pos)
    _ ≤ 1 / (Nat.factorial n : ℝ) := by
          exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
            hfac_pos hden_ge

theorem general_K_DxiMag_summable {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hxi0 : 0 ≤ xi) :
    Summable (fun n => generalKDxiMag rho xi n) := by
  have hfac : Summable (fun n : Nat => (1 : ℝ) / (Nat.factorial n : ℝ)) := by
    simpa [one_pow] using Real.summable_pow_div_factorial (1 : ℝ)
  exact Summable.of_nonneg_of_le
    (fun n => general_K_DxiMag_nonneg hrho0 hxi0 n)
    (fun n => general_K_DxiMag_le_factorial hrho0 hrho1 hxi0 n)
    hfac

theorem general_K_DxiMag_succ_le {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    {n : Nat} (hn : 4 ≤ n) :
    generalKDxiMag rho xi (n + 1) ≤ generalKDxiMag rho xi n := by
  let A : ℝ := 1 + xi * rho ^ n
  let B : ℝ := 1 + xi * rho ^ (n + 1)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hA_le_two : A ≤ 2 := by
    dsimp [A]
    have hp : rho ^ n ≤ 1 := pow_le_one₀ hrho0 hrho1
    have hmul : xi * rho ^ n ≤ 1 :=
      by simpa using
        mul_le_mul hxi1 hp (pow_nonneg hrho0 n) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hB_ge_one : 1 ≤ B := by
    dsimp [B]
    nlinarith [mul_nonneg hxi0 (pow_nonneg hrho0 (n + 1))]
  have hA_le_twoB : A ≤ 2 * B := by nlinarith
  have hA_sq_le_fourB : A ^ 2 ≤ 4 * B ^ 2 := by
    have htwoB_nonneg : 0 ≤ 2 * B := by positivity
    have hsq := mul_le_mul hA_le_twoB hA_le_twoB hA_nonneg htwoB_nonneg
    nlinarith
  have hfourNat : 4 ≤ n + 1 := by omega
  have hfour : (4 : ℝ) ≤ n + 1 := by exact_mod_cast hfourNat
  have hA_sq_le_nB : A ^ 2 ≤ (n + 1 : ℝ) * B ^ 2 := by
    have hBsq : 0 ≤ B ^ 2 := sq_nonneg B
    nlinarith [mul_le_mul_of_nonneg_right hfour hBsq, hA_sq_le_fourB]
  have hd_le : dCoeff rho (n + 1) ≤ dCoeff rho n :=
    general_K_dCoeff_succ_le hrho0 hrho1 n
  have hd_nonneg : 0 ≤ dCoeff rho n :=
    general_K_dCoeff_nonneg hrho0 n
  have hchain :
      dCoeff rho (n + 1) * A ^ 2
        ≤ dCoeff rho n * ((n + 1 : ℝ) * B ^ 2) := by
    have h1 :
        dCoeff rho (n + 1) * A ^ 2 ≤ dCoeff rho n * A ^ 2 := by
      exact mul_le_mul_of_nonneg_right hd_le (sq_nonneg A)
    have h2 :
        dCoeff rho n * A ^ 2
          ≤ dCoeff rho n * ((n + 1 : ℝ) * B ^ 2) := by
      exact mul_le_mul_of_nonneg_left hA_sq_le_nB hd_nonneg
    exact le_trans h1 h2
  unfold generalKDxiMag
  dsimp [A, B] at hchain
  have hfac : ((Nat.factorial (n + 1) : Nat) : ℝ)
      = (n + 1 : ℝ) * (Nat.factorial n : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [hfac]
  have hden_left :
      0 < ((n + 1 : ℝ) * (Nat.factorial n : ℝ))
        * (1 + xi * rho ^ (n + 1)) ^ 2 := by
    positivity
  have hden_right :
      0 < (Nat.factorial n : ℝ) * (1 + xi * rho ^ n) ^ 2 := by
    positivity
  rw [div_le_div_iff₀ hden_left hden_right]
  ring_nf at hchain
  ring_nf
  have hfac_pos : 0 < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  nlinarith

theorem general_K_DxiMag_shifted_antitone4 {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    Antitone (fun k => generalKDxiMag rho xi (k + 4)) := by
  apply antitone_nat_of_succ_le
  intro k
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    general_K_DxiMag_succ_le (rho := rho) (xi := xi)
      hrho0 hrho1 hxi0 hxi1 (n := k + 4) (by omega)

theorem general_K_Dxi_tail4_nonneg {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    0 ≤ ∑' k : Nat, (-1 : ℝ) ^ k * generalKDxiMag rho xi (k + 4) := by
  have hshift : Summable (fun k => generalKDxiMag rho xi (k + 4)) := by
    exact (summable_nat_add_iff 4).mpr
      (general_K_DxiMag_summable hrho0 hrho1 hxi0)
  have htend := hshift.tendsto_alternating_series_tsum
  have hbound :=
    (general_K_DxiMag_shifted_antitone4 hrho0 hrho1 hxi0 hxi1).alternating_series_le_tendsto
      htend 0
  simpa using hbound

theorem general_K_Dxi_fourTerm_le_series {rho xi : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    generalKDxiFourTerm rho xi ≤ generalKDxiSeries rho xi := by
  have hmag : Summable (fun n => generalKDxiMag rho xi n) :=
    general_K_DxiMag_summable hrho0 hrho1 hxi0
  have hterm : Summable (fun n => generalKDxiTerm rho xi n) := by
    unfold generalKDxiTerm
    exact hmag.alternating
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n => generalKDxiTerm rho xi n) 4 hterm
  have htail_nonneg :
      0 ≤ ∑' i : Nat, generalKDxiTerm rho xi (i + 4) := by
    unfold generalKDxiTerm
    simpa [pow_add, show ((-1 : ℝ) ^ 4) = 1 by norm_num] using
      general_K_Dxi_tail4_nonneg hrho0 hrho1 hxi0 hxi1
  unfold generalKDxiFourTerm generalKDxiSeries
  linarith

/-! ## Alternating tails for the endpoint `K(rho)` series -/

def generalKSeriesMag (rho : ℝ) (n : Nat) : ℝ :=
  dCoeff rho n / ((1 + rho ^ n) * (Nat.factorial n : ℝ))

def generalKSeriesTerm (rho : ℝ) (n : Nat) : ℝ :=
  (-1 : ℝ) ^ n * generalKSeriesMag rho n

def generalKPartial (rho : ℝ) (N : Nat) : ℝ :=
  (Finset.range (N + 1)).sum (fun n => generalKSeriesTerm rho n)

noncomputable def generalKSeries (rho : ℝ) : ℝ :=
  ∑' n : Nat, generalKSeriesTerm rho n

theorem general_K_seriesMag_nonneg {rho : ℝ}
    (hrho0 : 0 ≤ rho) (n : Nat) :
    0 ≤ generalKSeriesMag rho n := by
  unfold generalKSeriesMag
  exact div_nonneg (general_K_dCoeff_nonneg hrho0 n)
    (mul_nonneg (by positivity) (by positivity))

theorem general_K_seriesMag_le_factorial {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (n : Nat) :
    generalKSeriesMag rho n ≤ 1 / (Nat.factorial n : ℝ) := by
  unfold generalKSeriesMag
  have hd_le : dCoeff rho n ≤ 1 :=
    general_K_dCoeff_le_one hrho0 hrho1 n
  have hfac_pos : 0 < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hden_pos : 0 < (1 + rho ^ n) * (Nat.factorial n : ℝ) := by
    positivity
  have hden_ge :
      (Nat.factorial n : ℝ) ≤ (1 + rho ^ n) * (Nat.factorial n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right
      (by nlinarith [pow_nonneg hrho0 n] : (1 : ℝ) ≤ 1 + rho ^ n)
      (le_of_lt hfac_pos)]
  calc
    dCoeff rho n / ((1 + rho ^ n) * (Nat.factorial n : ℝ))
        ≤ 1 / ((1 + rho ^ n) * (Nat.factorial n : ℝ)) := by
          exact div_le_div_of_nonneg_right hd_le (le_of_lt hden_pos)
    _ ≤ 1 / (Nat.factorial n : ℝ) := by
          exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
            hfac_pos hden_ge

theorem general_K_seriesMag_summable {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    Summable (fun n => generalKSeriesMag rho n) := by
  have hfac : Summable (fun n : Nat => (1 : ℝ) / (Nat.factorial n : ℝ)) := by
    simpa [one_pow] using Real.summable_pow_div_factorial (1 : ℝ)
  exact Summable.of_nonneg_of_le
    (fun n => general_K_seriesMag_nonneg hrho0 n)
    (fun n => general_K_seriesMag_le_factorial hrho0 hrho1 n)
    hfac

theorem general_K_seriesMag_succ_le {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    {n : Nat} (hn : 2 ≤ n) :
    generalKSeriesMag rho (n + 1) ≤ generalKSeriesMag rho n := by
  let A : ℝ := 1 + rho ^ n
  let B : ℝ := 1 + rho ^ (n + 1)
  have hA_nonneg : 0 ≤ A := by dsimp [A]; positivity
  have hB_nonneg : 0 ≤ B := by dsimp [B]; positivity
  have hA_le_two : A ≤ 2 := by
    dsimp [A]
    nlinarith [pow_le_one₀ hrho0 hrho1 (n := n)]
  have hB_ge_one : 1 ≤ B := by
    dsimp [B]
    nlinarith [pow_nonneg hrho0 (n + 1)]
  have hA_le_twoB : A ≤ 2 * B := by nlinarith
  have htwoNat : 2 ≤ n + 1 := by omega
  have htwo : (2 : ℝ) ≤ n + 1 := by exact_mod_cast htwoNat
  have hA_le_nB : A ≤ (n + 1 : ℝ) * B := by
    nlinarith [mul_le_mul_of_nonneg_right htwo hB_nonneg, hA_le_twoB]
  have hd_le : dCoeff rho (n + 1) ≤ dCoeff rho n :=
    general_K_dCoeff_succ_le hrho0 hrho1 n
  have hd_nonneg : 0 ≤ dCoeff rho n :=
    general_K_dCoeff_nonneg hrho0 n
  have hchain :
      dCoeff rho (n + 1) * A
        ≤ dCoeff rho n * ((n + 1 : ℝ) * B) := by
    have h1 :
        dCoeff rho (n + 1) * A ≤ dCoeff rho n * A := by
      exact mul_le_mul_of_nonneg_right hd_le hA_nonneg
    have h2 :
        dCoeff rho n * A
          ≤ dCoeff rho n * ((n + 1 : ℝ) * B) := by
      exact mul_le_mul_of_nonneg_left hA_le_nB hd_nonneg
    exact le_trans h1 h2
  unfold generalKSeriesMag
  dsimp [A, B] at hchain
  have hfac : ((Nat.factorial (n + 1) : Nat) : ℝ)
      = (n + 1 : ℝ) * (Nat.factorial n : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [hfac]
  have hden_left :
      0 < (1 + rho ^ (n + 1))
        * ((n + 1 : ℝ) * (Nat.factorial n : ℝ)) := by
    positivity
  have hden_right :
      0 < (1 + rho ^ n) * (Nat.factorial n : ℝ) := by
    positivity
  rw [div_le_div_iff₀ hden_left hden_right]
  ring_nf at hchain
  ring_nf
  have hfac_pos : 0 < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  nlinarith

theorem general_K_seriesMag_shifted_antitone {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) {m : Nat} (hm : 2 ≤ m) :
    Antitone (fun k => generalKSeriesMag rho (k + m)) := by
  apply antitone_nat_of_succ_le
  intro k
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    general_K_seriesMag_succ_le (rho := rho)
      hrho0 hrho1 (n := k + m) (by omega)

theorem general_K_series_tail_nonneg {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) {m : Nat} (hm : 2 ≤ m) :
    0 ≤ ∑' k : Nat, (-1 : ℝ) ^ k * generalKSeriesMag rho (k + m) := by
  have hshift : Summable (fun k => generalKSeriesMag rho (k + m)) := by
    exact (summable_nat_add_iff m).mpr
      (general_K_seriesMag_summable hrho0 hrho1)
  have htend := hshift.tendsto_alternating_series_tsum
  have hbound :=
    (general_K_seriesMag_shifted_antitone hrho0 hrho1 hm).alternating_series_le_tendsto
      htend 0
  simpa using hbound

theorem general_K_partial5_le_series {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    generalKPartial rho 5 ≤ generalKSeries rho := by
  have hmag : Summable (fun n => generalKSeriesMag rho n) :=
    general_K_seriesMag_summable hrho0 hrho1
  have hterm : Summable (fun n => generalKSeriesTerm rho n) := by
    unfold generalKSeriesTerm
    exact hmag.alternating
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n => generalKSeriesTerm rho n) 6 hterm
  have htail_nonneg :
      0 ≤ ∑' i : Nat, generalKSeriesTerm rho (i + 6) := by
    unfold generalKSeriesTerm
    simpa [pow_add, show ((-1 : ℝ) ^ 6) = 1 by norm_num] using
      general_K_series_tail_nonneg hrho0 hrho1 (m := 6) (by norm_num)
  unfold generalKPartial generalKSeries
  linarith

theorem general_K_series_le_partial2 {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    generalKSeries rho ≤ generalKPartial rho 2 := by
  have hmag : Summable (fun n => generalKSeriesMag rho n) :=
    general_K_seriesMag_summable hrho0 hrho1
  have hterm : Summable (fun n => generalKSeriesTerm rho n) := by
    unfold generalKSeriesTerm
    exact hmag.alternating
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n => generalKSeriesTerm rho n) 3 hterm
  have htail_nonpos :
      ∑' i : Nat, generalKSeriesTerm rho (i + 3) ≤ 0 := by
    have htail_nonneg :
        0 ≤ ∑' i : Nat, (-1 : ℝ) ^ i * generalKSeriesMag rho (i + 3) :=
      general_K_series_tail_nonneg hrho0 hrho1 (m := 3) (by norm_num)
    have heq :
        (∑' i : Nat, generalKSeriesTerm rho (i + 3))
          =
        -∑' i : Nat, (-1 : ℝ) ^ i * generalKSeriesMag rho (i + 3) := by
      rw [← tsum_neg]
      apply tsum_congr
      intro i
      unfold generalKSeriesTerm
      rw [pow_add]
      norm_num
    rw [heq]
    linarith
  unfold generalKPartial generalKSeries
  linarith

/-! ## Finite checks for monotonicity in `xi` -/

def generalKFirstPairClear (rho : ℝ) : ℝ :=
  3 * (1 + rho) ^ 4 - 8 * rho * (rho ^ 2 + 4 * rho + 1)

theorem general_K_first_pair_factor (rho : ℝ) :
    generalKFirstPairClear rho
      = (1 - rho) ^ 2 * (rho + 3) * (3 * rho + 1) := by
  unfold generalKFirstPairClear
  ring

theorem general_K_first_pair_nonneg {rho : ℝ}
    (hrho : 0 ≤ rho) :
    0 ≤ generalKFirstPairClear rho := by
  rw [general_K_first_pair_factor]
  positivity

def generalKSecondPairClear (rho : ℝ) : ℝ :=
  5 * rho ^ 12 + 24 * rho ^ 11 + 19 * rho ^ 10 + 11 * rho ^ 9
  + 51 * rho ^ 8 + 53 * rho ^ 7 - 6 * rho ^ 6
  + 53 * rho ^ 5 + 51 * rho ^ 4 + 11 * rho ^ 3
  + 19 * rho ^ 2 + 24 * rho + 5

theorem general_K_second_pair_nonneg {rho : ℝ}
    (hrho : 0 ≤ rho) :
    0 ≤ generalKSecondPairClear rho := by
  unfold generalKSecondPairClear
  have hsq : 0 ≤ (rho ^ 6 - 1) ^ 2 := sq_nonneg (rho ^ 6 - 1)
  have hmain : 0 ≤ 5 * rho ^ 12 - 10 * rho ^ 6 + 5 := by
    nlinarith
  have h6 : 0 ≤ rho ^ 6 := pow_nonneg hrho 6
  have h11 : 0 ≤ rho ^ 11 := pow_nonneg hrho 11
  have h10 : 0 ≤ rho ^ 10 := pow_nonneg hrho 10
  have h9 : 0 ≤ rho ^ 9 := pow_nonneg hrho 9
  have h8 : 0 ≤ rho ^ 8 := pow_nonneg hrho 8
  have h7 : 0 ≤ rho ^ 7 := pow_nonneg hrho 7
  have h5 : 0 ≤ rho ^ 5 := pow_nonneg hrho 5
  have h4 : 0 ≤ rho ^ 4 := pow_nonneg hrho 4
  have h3 : 0 ≤ rho ^ 3 := pow_nonneg hrho 3
  have h2 : 0 ≤ rho ^ 2 := pow_nonneg hrho 2
  nlinarith

/-! ## The numerator of `F(rho,1)` -/

def generalKFAtOne (rho : ℝ) : ℝ :=
  ((1 + rho) / 2) / 4
  - ((1 + 4 * rho + rho ^ 2) / 6) / (1 + rho) ^ 2
  + ((1 + 5 * rho + 5 * rho ^ 2 + rho ^ 3) / 12)
      / (2 * (1 + rho ^ 2) ^ 2)
  - ((1 + 6 * rho + 6 * rho ^ 2 + 6 * rho ^ 3 + rho ^ 4) / 20)
      / (6 * (1 + rho ^ 3) ^ 2)

def generalKFAtOneDen (rho : ℝ) : ℝ :=
  120 * (1 + rho) ^ 2 * (1 + rho ^ 2) ^ 2
    * (1 - rho + rho ^ 2) ^ 2

def generalKFAtOneNum (rho : ℝ) : ℝ :=
  15 * rho ^ 11 - 5 * rho ^ 10 - 5 * rho ^ 9 + 124 * rho ^ 8
  - 176 * rho ^ 7 + 302 * rho ^ 6 - 293 * rho ^ 5
  + 301 * rho ^ 4 - 183 * rho ^ 3 + 87 * rho ^ 2
  - 6 * rho - 1

theorem general_K_F_at_one_den_pos {rho : ℝ}
    (hrho : 0 ≤ rho) :
    0 < generalKFAtOneDen rho := by
  unfold generalKFAtOneDen
  have hquad : 0 < 1 - rho + rho ^ 2 := lowerRhoBridgeQuad_pos rho
  positivity

theorem general_K_F_at_one_cleared_eq_num {rho : ℝ}
    (h1 : 1 + rho ≠ 0)
    (h2 : 1 + rho ^ 2 ≠ 0)
    (h3 : 1 + rho ^ 3 ≠ 0) :
    generalKFAtOneDen rho * generalKFAtOne rho
      = generalKFAtOneNum rho := by
  unfold generalKFAtOneDen generalKFAtOne generalKFAtOneNum
  field_simp [h1, h2, h3]
  ring_nf

def generalKFAtOneShifted (s : ℝ) : ℝ :=
  54160 / 19683
  + (466880 / 19683) * s
  + (817872 / 19683) * s ^ 2
  + (1348974 / 19683) * s ^ 3
  + (3803598 / 19683) * s ^ 4
  + (3032397 / 19683) * s ^ 5
  + (5454378 / 19683) * s ^ 6
  + (3416094 / 19683) * s ^ 7
  + (3457647 / 19683) * s ^ 8
  + (1377810 / 19683) * s ^ 9
  + (984150 / 19683) * s ^ 10
  + (295245 / 19683) * s ^ 11

theorem general_K_shifted_coefficients_positive :
    SkiRental.Certificates.allPositive
      SkiRental.Certificates.generalKPolynomialShiftCoeffs = true :=
  SkiRental.Certificates.generalKPolynomialShiftCoeffs_positive

theorem general_K_F_at_one_num_shift_eq (s : ℝ) :
    generalKFAtOneNum (1 / 3 + s) = generalKFAtOneShifted s := by
  unfold generalKFAtOneNum generalKFAtOneShifted
  ring_nf

theorem general_K_F_at_one_shifted_pos {s : ℝ}
    (hs : 0 ≤ s) :
    0 < generalKFAtOneShifted s := by
  unfold generalKFAtOneShifted
  positivity

theorem general_K_F_at_one_num_pos {rho : ℝ}
    (hrho : (1 / 3 : ℝ) ≤ rho) :
    0 < generalKFAtOneNum rho := by
  let s : ℝ := rho - 1 / 3
  have hs : 0 ≤ s := by
    dsimp [s]
    linarith
  have hrho_eq : rho = 1 / 3 + s := by
    dsimp [s]
    ring
  rw [hrho_eq, general_K_F_at_one_num_shift_eq]
  exact general_K_F_at_one_shifted_pos hs

theorem general_K_F_at_one_pos {rho : ℝ}
    (hrho : (1 / 3 : ℝ) ≤ rho) :
    0 < generalKFAtOne rho := by
  have hrho_nonneg : 0 ≤ rho := by nlinarith
  have h1 : 1 + rho ≠ 0 := by positivity
  have h2 : 1 + rho ^ 2 ≠ 0 := by positivity
  have h3 : 1 + rho ^ 3 ≠ 0 := by positivity
  have hden : 0 < generalKFAtOneDen rho :=
    general_K_F_at_one_den_pos hrho_nonneg
  have hprod : 0 < generalKFAtOneDen rho * generalKFAtOne rho := by
    rw [general_K_F_at_one_cleared_eq_num h1 h2 h3]
    exact general_K_F_at_one_num_pos hrho
  exact (mul_pos_iff_of_pos_left hden).mp hprod

/-! ## Finite checks for the `rho`-monotonicity lower bound -/

def generalKF2SpecialClear (rho : ℝ) : ℝ :=
  23 * rho ^ 4 + 62 * rho ^ 2 - 32 * rho + 7

theorem general_K_f2_special_clear_pos (rho : ℝ) :
    0 < generalKF2SpecialClear rho := by
  unfold generalKF2SpecialClear
  have hsq : 0 ≤ (62 * rho - 16) ^ 2 := sq_nonneg (62 * rho - 16)
  have hquad : 0 < 62 * rho ^ 2 - 32 * rho + 7 := by
    nlinarith
  have hquartic : 0 ≤ 23 * rho ^ 4 := by
    positivity
  nlinarith

def generalKF4SpecialClear (rho : ℝ) : ℝ :=
  29 * rho ^ 8 + 7 * rho ^ 6 + 14 * rho ^ 5 + 76 * rho ^ 4
  - 24 * rho ^ 3 - 21 * rho ^ 2 - 14 * rho + 23

theorem general_K_f4_special_clear_nonneg {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    0 ≤ generalKF4SpecialClear rho := by
  unfold generalKF4SpecialClear
  by_cases hhalf : rho ≤ 1 / 2
  · have h2 : rho ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hrho0 hhalf 2
    have h3 : rho ^ 3 ≤ (1 / 2 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hrho0 hhalf 3
    have hbase : 0 ≤ 23 - 24 * rho ^ 3 - 21 * rho ^ 2 - 14 * rho := by
      nlinarith
    have hpos :
        0 ≤ 29 * rho ^ 8 + 7 * rho ^ 6 + 14 * rho ^ 5 + 76 * rho ^ 4 := by
      positivity
    nlinarith
  · have hhalf_ge : (1 / 2 : ℝ) ≤ rho := by linarith
    have hq : 0 < 28 * rho ^ 4 - 49 * rho ^ 2 + 23 := by
      have hsq : 0 ≤ (56 * rho ^ 2 - 49) ^ 2 :=
        sq_nonneg (56 * rho ^ 2 - 49)
      nlinarith
    have hdiff :
        0 ≤
          (29 * rho ^ 8 + 7 * rho ^ 6 + 14 * rho ^ 5 + 76 * rho ^ 4
            - 24 * rho ^ 3 - 21 * rho ^ 2 - 14 * rho + 23)
          - (28 * rho ^ 4 - 49 * rho ^ 2 + 23) := by
      have hdiff_eq :
          (29 * rho ^ 8 + 7 * rho ^ 6 + 14 * rho ^ 5 + 76 * rho ^ 4
            - 24 * rho ^ 3 - 21 * rho ^ 2 - 14 * rho + 23)
          - (28 * rho ^ 4 - 49 * rho ^ 2 + 23)
            =
          29 * rho ^ 8 + 7 * rho ^ 6 + 14 * rho ^ 5
            + 24 * rho ^ 3 * (2 * rho - 1)
            + 14 * rho * (2 * rho - 1) := by
        ring
      rw [hdiff_eq]
      have htworho : 0 ≤ 2 * rho - 1 := by nlinarith
      have hpos_poly : 0 ≤ 29 * rho ^ 8 + 7 * rho ^ 6 + 14 * rho ^ 5 := by
        positivity
      have hpos_cubic : 0 ≤ 24 * rho ^ 3 * (2 * rho - 1) := by
        positivity
      have hpos_linear : 0 ≤ 14 * rho * (2 * rho - 1) := by
        positivity
      nlinarith
    nlinarith

theorem general_K_factorial_tail_bound_arithmetic :
    (1 / 120 : ℝ) * (1 / (1 - 1 / 6))
      + (1 / 720) * (1 / (1 - 1 / 7))
      < 1 / 80 := by
  norm_num

theorem general_K_derivative_margin_arithmetic :
    (1 / 3 : ℝ) - 9 / 32 - 1 / 24 - 1 / 160
      =
      1 / 240 := by
  norm_num

/-! ## Endpoint arithmetic for the zero bracket -/

theorem general_K_left_partial_value :
    SkiRental.Certificates.KPartialSum
        SkiRental.Certificates.rhoOneThird 5
      =
      SkiRental.Certificates.q 3120653 25210080 :=
  SkiRental.Certificates.K_left_partial_value

theorem general_K_left_partial_gt_text_bound :
    SkiRental.Certificates.q 46 375 <
      SkiRental.Certificates.KPartialSum
        SkiRental.Certificates.rhoOneThird 5 :=
  SkiRental.Certificates.K_left_partial_gt_text_bound

theorem general_K_left_rho_times_recip_upper :
    SkiRental.Certificates.q 1 3 * SkiRental.Certificates.q 46 125
      =
      SkiRental.Certificates.q 46 375 :=
  SkiRental.Certificates.one_third_times_recip_upper

theorem general_K_left_endpoint_arithmetic :
    SkiRental.Certificates.q 1 3 * SkiRental.Certificates.q 46 125 <
      SkiRental.Certificates.KPartialSum
        SkiRental.Certificates.rhoOneThird 5 := by
  rw [general_K_left_rho_times_recip_upper]
  exact general_K_left_partial_gt_text_bound

theorem general_K_left_e_bound_arithmetic :
    SkiRental.Certificates.q 125 46 <
      SkiRental.Certificates.q 1957 720 :=
  SkiRental.Certificates.e_lower_for_K_left

theorem general_K_right_partial_value :
    SkiRental.Certificates.KPartialSum
        SkiRental.Certificates.rhoOneHalf 2
      =
      SkiRental.Certificates.q 127 720 :=
  SkiRental.Certificates.K_right_partial_value

theorem general_K_right_endpoint_margin :
    SkiRental.Certificates.q 11 60
      -
      SkiRental.Certificates.KPartialSum
        SkiRental.Certificates.rhoOneHalf 2
      =
      SkiRental.Certificates.q 1 144 := by
  rw [general_K_right_partial_value]
  exact SkiRental.Certificates.K_right_margin

theorem general_K_right_e_bound_arithmetic :
    SkiRental.Certificates.q 65 24 + SkiRental.Certificates.q 1 100 <
      SkiRental.Certificates.q 30 11 :=
  SkiRental.Certificates.e_upper_for_K_right

theorem general_K_at_xi_one_eq_series (rho : ℝ) :
    K rho 1 = rho / Real.exp 1 - generalKSeries rho := by
  unfold K generalKSeries generalKSeriesTerm generalKSeriesMag
  simp only [one_mul]
  have hseries :
      (∑' n : Nat,
          (-1 : ℝ) ^ n * dCoeff rho n /
            ((Nat.factorial n : ℝ) * (1 + rho ^ n)))
        =
      (∑' n : Nat,
          (-1 : ℝ) ^ n *
            (dCoeff rho n / ((1 + rho ^ n) * (Nat.factorial n : ℝ)))) := by
    apply tsum_congr
    intro n
    ring_nf
  rw [hseries]

theorem general_K_left_partial_value_real :
    generalKPartial (1 / 3 : ℝ) 5 = (3120653 : ℝ) / 25210080 := by
  unfold generalKPartial generalKSeriesTerm generalKSeriesMag dCoeff
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Finset.sum_Icc_succ_top]

theorem general_K_right_partial_value_real :
    generalKPartial (1 / 2 : ℝ) 2 = (127 : ℝ) / 720 := by
  unfold generalKPartial generalKSeriesTerm generalKSeriesMag dCoeff
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Finset.sum_Icc_succ_top]

theorem general_K_left_endpoint_negative
    (he : (125 / 46 : ℝ) < Real.exp 1) :
    K (1 / 3) 1 < 0 := by
  rw [general_K_at_xi_one_eq_series]
  have hseries_lower :
      generalKPartial (1 / 3 : ℝ) 5 ≤ generalKSeries (1 / 3) :=
    general_K_partial5_le_series (by norm_num) (by norm_num)
  have hpartial_gt :
      (46 / 375 : ℝ) < generalKPartial (1 / 3 : ℝ) 5 := by
    rw [general_K_left_partial_value_real]
    norm_num
  have hinv : 1 / Real.exp 1 < 46 / 125 := by
    have hrecip := one_div_lt_one_div_of_lt
      (by norm_num : (0 : ℝ) < 125 / 46) he
    norm_num at hrecip ⊢
    exact hrecip
  have hrho_exp : (1 / 3 : ℝ) / Real.exp 1 < 46 / 375 := by
    calc
      (1 / 3 : ℝ) / Real.exp 1
          = (1 / 3 : ℝ) * (1 / Real.exp 1) := by ring
      _ < (1 / 3 : ℝ) * (46 / 125) :=
          mul_lt_mul_of_pos_left hinv (by norm_num)
      _ = 46 / 375 := by norm_num
  have hlt_series : (1 / 3 : ℝ) / Real.exp 1 < generalKSeries (1 / 3) :=
    lt_of_lt_of_le (lt_trans hrho_exp hpartial_gt) hseries_lower
  linarith

theorem general_K_left_endpoint_negative_unconditional :
    K (1 / 3) 1 < 0 := by
  apply general_K_left_endpoint_negative
  exact (by norm_num : (125 / 46 : ℝ) < 2.7182818283).trans
    Real.exp_one_gt_d9

theorem general_K_right_endpoint_positive
    (he : Real.exp 1 < (30 / 11 : ℝ)) :
    0 < K (1 / 2) 1 := by
  rw [general_K_at_xi_one_eq_series]
  have hseries_upper :
      generalKSeries (1 / 2 : ℝ) ≤ generalKPartial (1 / 2) 2 :=
    general_K_series_le_partial2 (by norm_num) (by norm_num)
  have hpartial_eq :
      generalKPartial (1 / 2 : ℝ) 2 = (127 : ℝ) / 720 :=
    general_K_right_partial_value_real
  have hinv : (11 / 30 : ℝ) < 1 / Real.exp 1 := by
    have hrecip := one_div_lt_one_div_of_lt
      (Real.exp_pos 1) he
    norm_num at hrecip ⊢
    exact hrecip
  have hrho_exp : (11 / 60 : ℝ) < (1 / 2 : ℝ) / Real.exp 1 := by
    calc
      (11 / 60 : ℝ) = (1 / 2 : ℝ) * (11 / 30) := by norm_num
      _ < (1 / 2 : ℝ) * (1 / Real.exp 1) :=
          mul_lt_mul_of_pos_left hinv (by norm_num)
      _ = (1 / 2 : ℝ) / Real.exp 1 := by ring
  have hseries_bound : generalKSeries (1 / 2 : ℝ) ≤ (127 : ℝ) / 720 := by
    rw [← hpartial_eq]
    exact hseries_upper
  nlinarith

theorem general_K_right_endpoint_positive_unconditional :
    0 < K (1 / 2) 1 := by
  apply general_K_right_endpoint_positive
  exact Real.exp_one_lt_d9.trans (by norm_num)

end

end SkiRental.Scalar
