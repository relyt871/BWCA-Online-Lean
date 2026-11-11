import general_K.GeneralKAnalytic

/-!
# Monotonicity and the unique zero of the general endpoint quantity

This file completes the proof that `rho ↦ K rho 1` is strictly increasing on
`(0,1)` and has a unique zero between `1/3` and `1/2`.
-/

namespace SkiRental.Scalar

open scoped BigOperators

noncomputable section

def generalKRhoNumerator (rho : ℝ) (n : Nat) : ℝ :=
  1 + (n + 3 : ℝ) * (Finset.Icc 1 n).sum (fun k => rho ^ k)
    + rho ^ (n + 1)

def generalKRhoNumeratorDeriv (rho : ℝ) (n : Nat) : ℝ :=
  (n + 3 : ℝ) *
      (Finset.Icc 1 n).sum (fun k => (k : ℝ) * rho ^ (k - 1))
    + (n + 1 : ℝ) * rho ^ n

def generalKRhoCoeff (rho : ℝ) (n : Nat) : ℝ :=
  dCoeff rho n / (1 + rho ^ n)

def generalKRhoCoeffDeriv (rho : ℝ) (n : Nat) : ℝ :=
  (generalKRhoNumeratorDeriv rho n * (1 + rho ^ n)
      - (n : ℝ) * rho ^ (n - 1) * generalKRhoNumerator rho n)
    / (((n + 1 : ℝ) * (n + 2 : ℝ)) * (1 + rho ^ n) ^ 2)

theorem general_K_dCoeff_eq_numerator (rho : ℝ) (n : Nat) :
    dCoeff rho n =
      generalKRhoNumerator rho n / ((n + 1 : ℝ) * (n + 2 : ℝ)) := by
  rfl

theorem general_K_rhoCoeff_eq_numerator (rho : ℝ) (n : Nat) :
    generalKRhoCoeff rho n =
      generalKRhoNumerator rho n /
        (((n + 1 : ℝ) * (n + 2 : ℝ)) * (1 + rho ^ n)) := by
  unfold generalKRhoCoeff
  rw [general_K_dCoeff_eq_numerator]
  rw [div_div]

theorem hasDerivAt_generalKRhoNumerator (rho : ℝ) (n : Nat) :
    HasDerivAt (fun z => generalKRhoNumerator z n)
      (generalKRhoNumeratorDeriv rho n) rho := by
  have hsum : HasDerivAt
      (fun z : ℝ => (Finset.Icc 1 n).sum (fun k => z ^ k))
      ((Finset.Icc 1 n).sum (fun k => (k : ℝ) * rho ^ (k - 1))) rho := by
    simpa only [Finset.sum_fn, Pi.pow_apply, id_eq, mul_one] using
      (HasDerivAt.sum (u := Finset.Icc 1 n)
        (fun k _hk => (hasDerivAt_id rho).pow k))
  have hmain :=
    ((hasDerivAt_const rho 1).add
      (hsum.const_mul (n + 3 : ℝ))).add ((hasDerivAt_id rho).pow (n + 1))
  change HasDerivAt (fun z => generalKRhoNumerator z n) _ rho at hmain
  apply hmain.congr_deriv
  simp only [id_eq, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
    zero_add]
  unfold generalKRhoNumeratorDeriv
  ring

theorem hasDerivAt_generalKRhoCoeff {rho : ℝ} (hrho0 : 0 ≤ rho) (n : Nat) :
    HasDerivAt (fun z => generalKRhoCoeff z n)
      (generalKRhoCoeffDeriv rho n) rho := by
  have hden : 1 + rho ^ n ≠ 0 := by positivity
  have hc : ((n + 1 : ℝ) * (n + 2 : ℝ)) ≠ 0 := by positivity
  have hnum := hasDerivAt_generalKRhoNumerator rho n
  have hpow := (hasDerivAt_id rho).pow n
  have hquot := hnum.div
    ((hasDerivAt_const rho 1).add hpow) hden
  have hscaled := hquot.div_const ((n + 1 : ℝ) * (n + 2 : ℝ))
  have hfun : (fun z => generalKRhoCoeff z n) =
      (fun z => generalKRhoNumerator z n / (1 + z ^ n) /
        ((n + 1 : ℝ) * (n + 2 : ℝ))) := by
    funext z
    rw [general_K_rhoCoeff_eq_numerator]
    rw [div_div]
    congr 1
    ring
  rw [hfun]
  apply hscaled.congr_deriv
  simp only [Pi.add_apply, Pi.pow_apply, id_eq, zero_add, mul_one]
  change
    (generalKRhoNumeratorDeriv rho n * (1 + rho ^ n)
        - generalKRhoNumerator rho n * ((n : ℝ) * rho ^ (n - 1))) /
          (1 + rho ^ n) ^ 2 /
        ((n + 1 : ℝ) * (n + 2 : ℝ)) =
      generalKRhoCoeffDeriv rho n
  unfold generalKRhoCoeffDeriv
  field_simp [hden, hc]

theorem general_K_sum_Icc_cast (n : Nat) :
    (Finset.Icc 1 n).sum (fun k => (k : ℝ)) =
      (n : ℝ) * (n + 1 : ℝ) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top]
      · rw [ih]
        norm_num [Nat.cast_add, Nat.cast_one]
        ring
      · omega

theorem general_K_rhoNumerator_nonneg {rho : ℝ}
    (hrho0 : 0 ≤ rho) (n : Nat) :
    0 ≤ generalKRhoNumerator rho n := by
  unfold generalKRhoNumerator
  positivity

theorem general_K_rhoNumeratorDeriv_nonneg {rho : ℝ}
    (hrho0 : 0 ≤ rho) (n : Nat) :
    0 ≤ generalKRhoNumeratorDeriv rho n := by
  unfold generalKRhoNumeratorDeriv
  positivity

theorem general_K_rhoNumeratorDeriv_le {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (n : Nat) :
    generalKRhoNumeratorDeriv rho n ≤
      (n + 1 : ℝ) ^ 2 * (n + 2 : ℝ) / 2 := by
  have hsum :
      (Finset.Icc 1 n).sum (fun k => (k : ℝ) * rho ^ (k - 1)) ≤
        (Finset.Icc 1 n).sum (fun k => (k : ℝ)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hp : rho ^ (k - 1) ≤ 1 := pow_le_one₀ hrho0 hrho1
    exact mul_le_of_le_one_right (by positivity) hp
  rw [general_K_sum_Icc_cast] at hsum
  have hpow : rho ^ n ≤ 1 := pow_le_one₀ hrho0 hrho1
  unfold generalKRhoNumeratorDeriv
  have hn1 : 0 ≤ (n + 1 : ℝ) := by positivity
  have hn3 : 0 ≤ (n + 3 : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsum hn3,
    mul_le_mul_of_nonneg_left hpow hn1]

theorem general_K_rhoCoeffDeriv_le {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (n : Nat) :
    generalKRhoCoeffDeriv rho n ≤ (n + 1 : ℝ) / 2 := by
  let B : ℝ := 1 + rho ^ n
  let C : ℝ := (n + 1 : ℝ) * (n + 2 : ℝ)
  let M : ℝ := (n + 1 : ℝ) ^ 2 * (n + 2 : ℝ) / 2
  have hB : 1 ≤ B := by
    dsimp [B]
    nlinarith [pow_nonneg hrho0 n]
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hB2 : B ≤ B ^ 2 := by nlinarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hN : 0 ≤ generalKRhoNumerator rho n :=
    general_K_rhoNumerator_nonneg hrho0 n
  have hN' : 0 ≤ generalKRhoNumeratorDeriv rho n :=
    general_K_rhoNumeratorDeriv_nonneg hrho0 n
  have hN'le : generalKRhoNumeratorDeriv rho n ≤ M := by
    dsimp [M]
    exact general_K_rhoNumeratorDeriv_le hrho0 hrho1 n
  have hrpow : 0 ≤ (n : ℝ) * rho ^ (n - 1) := by positivity
  have hq :
      generalKRhoNumeratorDeriv rho n * B
          - (n : ℝ) * rho ^ (n - 1) * generalKRhoNumerator rho n
        ≤ M * B ^ 2 := by
    have hdrop :
        generalKRhoNumeratorDeriv rho n * B
            - (n : ℝ) * rho ^ (n - 1) * generalKRhoNumerator rho n
          ≤ generalKRhoNumeratorDeriv rho n * B := by
      nlinarith [mul_nonneg hrpow hN]
    have hmiddle : generalKRhoNumeratorDeriv rho n * B ≤ M * B :=
      mul_le_mul_of_nonneg_right hN'le hB0
    have hlast : M * B ≤ M * B ^ 2 :=
      mul_le_mul_of_nonneg_left hB2 hM
    exact hdrop.trans (hmiddle.trans hlast)
  unfold generalKRhoCoeffDeriv
  rw [div_le_iff₀ (mul_pos hC (sq_pos_of_pos (lt_of_lt_of_le (by norm_num) hB)))]
  dsimp [B, C, M] at hq ⊢
  nlinarith

theorem general_K_reflect_Icc_sum (rho : ℝ) {n : Nat} (hn : 1 ≤ n) :
    (Finset.Icc 1 (n - 1)).sum
        (fun k => (n - k : ℕ) * rho ^ ((n - k) - 1)) =
      (Finset.Icc 1 (n - 1)).sum
        (fun k => (k : ℝ) * rho ^ (k - 1)) := by
  apply Finset.sum_nbij (fun k => n - k)
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro a ha b hb hab
    rcases Finset.mem_Icc.mp ha with ⟨ha1, ha2⟩
    rcases Finset.mem_Icc.mp hb with ⟨hb1, hb2⟩
    have haN : a ≤ n := le_trans ha2 (Nat.sub_le n 1)
    have hbN : b ≤ n := le_trans hb2 (Nat.sub_le n 1)
    have hsum : (n - a) + a = (n - b) + b := by
      rw [Nat.sub_add_cancel haN, Nat.sub_add_cancel hbN]
    change n - a = n - b at hab
    have hsum' : (n - a) + a = (n - a) + b := by
      simpa only [hab] using hsum
    exact Nat.add_left_cancel hsum'
  · intro b hb
    rcases Finset.mem_Icc.mp hb with ⟨hb1, hb2⟩
    refine ⟨n - b, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · exact Nat.sub_sub_self (le_trans hb2 (Nat.sub_le n 1))
  · intro k hk
    rfl

theorem general_K_high_power_deficit_le {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) {n : Nat} (hn : 1 ≤ n) :
    (Finset.Icc 1 (n - 1)).sum
        (fun k => (n - k : ℕ) * rho ^ (n + k - 1)) ≤
      (Finset.Icc 1 (n - 1)).sum
        (fun k => (k : ℝ) * rho ^ (k - 1)) := by
  calc
    (Finset.Icc 1 (n - 1)).sum
        (fun k => (n - k : ℕ) * rho ^ (n + k - 1))
      ≤ (Finset.Icc 1 (n - 1)).sum
          (fun k => (n - k : ℕ) * rho ^ ((n - k) - 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [Finset.mem_Icc] at hk
        have hexp : (n - k) - 1 ≤ n + k - 1 := by omega
        have hp := pow_le_pow_of_le_one hrho0 hrho1 hexp
        exact mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (Finset.Icc 1 (n - 1)).sum
          (fun k => (k : ℝ) * rho ^ (k - 1)) :=
        general_K_reflect_Icc_sum rho hn

theorem general_K_rho_sum_deficit_eq {rho : ℝ} {n : Nat} (hn : 1 ≤ n) :
    (n : ℝ) * rho ^ (n - 1) *
          (Finset.Icc 1 n).sum (fun k => rho ^ k)
        - rho ^ n *
          (Finset.Icc 1 n).sum (fun k => (k : ℝ) * rho ^ (k - 1)) =
      (Finset.Icc 1 (n - 1)).sum
        (fun k => (n - k : ℕ) * rho ^ (n + k - 1)) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hterm (k : Nat) (hk : k ∈ Finset.Icc 1 n) :
      (n : ℝ) * rho ^ (n - 1) * rho ^ k
          - rho ^ n * ((k : ℝ) * rho ^ (k - 1)) =
        (n - k : ℕ) * rho ^ (n + k - 1) := by
    simp only [Finset.mem_Icc] at hk
    have hp₁ : rho ^ (n - 1) * rho ^ k = rho ^ (n + k - 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hp₂ : rho ^ n * rho ^ (k - 1) = rho ^ (n + k - 1) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      (n : ℝ) * rho ^ (n - 1) * rho ^ k
            - rho ^ n * ((k : ℝ) * rho ^ (k - 1))
          = (n : ℝ) * (rho ^ (n - 1) * rho ^ k)
              - (k : ℝ) * (rho ^ n * rho ^ (k - 1)) := by ring
      _ = ((n : ℝ) - (k : ℝ)) * rho ^ (n + k - 1) := by
            rw [hp₁, hp₂]
            ring
      _ = (n - k : ℕ) * rho ^ (n + k - 1) := by
            rw [Nat.cast_sub hk.2]
  rw [Finset.sum_congr rfl hterm]
  have hn_eq : n = (n - 1) + 1 := by omega
  have hsplit :
      (Finset.Icc 1 n).sum
          (fun k => (n - k : ℕ) * rho ^ (n + k - 1)) =
        (Finset.Icc 1 (n - 1)).sum
            (fun k => (n - k : ℕ) * rho ^ (n + k - 1))
          + (n - n : ℕ) * rho ^ (n + n - 1) := by
    conv_lhs => rw [hn_eq]
    have hlow : 1 ≤ n - 1 + 1 := by
      rw [← hn_eq]
      exact hn
    rw [Finset.sum_Icc_succ_top hlow]
    simp only [← hn_eq]
  rw [hsplit]
  simp

theorem general_K_rho_deriv_sum_split (rho : ℝ) {n : Nat} (hn : 1 ≤ n) :
    (Finset.Icc 1 n).sum (fun k => (k : ℝ) * rho ^ (k - 1)) =
      (Finset.Icc 1 (n - 1)).sum
          (fun k => (k : ℝ) * rho ^ (k - 1))
        + (n : ℝ) * rho ^ (n - 1) := by
  have hn_eq : n = (n - 1) + 1 := by omega
  conv_lhs => rw [hn_eq]
  have hlow : 1 ≤ n - 1 + 1 := by
    rw [← hn_eq]
    exact hn
  rw [Finset.sum_Icc_succ_top hlow]
  simp only [← hn_eq]

theorem general_K_rhoCoeffDeriv_nonneg {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (n : Nat) :
    0 ≤ generalKRhoCoeffDeriv rho n := by
  by_cases hn0 : n = 0
  · subst n
    norm_num [generalKRhoCoeffDeriv, generalKRhoNumerator,
      generalKRhoNumeratorDeriv]
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    let P : ℝ := (Finset.Icc 1 n).sum (fun k => rho ^ k)
    let S : ℝ :=
      (Finset.Icc 1 n).sum (fun k => (k : ℝ) * rho ^ (k - 1))
    let S₀ : ℝ :=
      (Finset.Icc 1 (n - 1)).sum
        (fun k => (k : ℝ) * rho ^ (k - 1))
    have hdefeq :
        (n : ℝ) * rho ^ (n - 1) * P - rho ^ n * S =
          (Finset.Icc 1 (n - 1)).sum
            (fun k => (n - k : ℕ) * rho ^ (n + k - 1)) := by
      dsimp [P, S]
      exact general_K_rho_sum_deficit_eq hn
    have hhigh :
        (Finset.Icc 1 (n - 1)).sum
            (fun k => (n - k : ℕ) * rho ^ (n + k - 1)) ≤ S₀ := by
      dsimp [S₀]
      exact general_K_high_power_deficit_le hrho0 hrho1 hn
    have hsplit : S = S₀ + (n : ℝ) * rho ^ (n - 1) := by
      dsimp [S, S₀]
      exact general_K_rho_deriv_sum_split rho hn
    have hinside :
        (n : ℝ) * rho ^ (n - 1) ≤
          S + rho ^ n * S - (n : ℝ) * rho ^ (n - 1) * P := by
      nlinarith
    have hpowers : rho ^ (n - 1) * rho ^ (n + 1) = rho ^ (2 * n) := by
      rw [← pow_add]
      congr 1
      omega
    have hsquare : rho ^ n * rho ^ n = rho ^ (2 * n) := by
      rw [← pow_add]
      congr 1
      omega
    have hqeq :
        generalKRhoNumeratorDeriv rho n * (1 + rho ^ n)
            - (n : ℝ) * rho ^ (n - 1) * generalKRhoNumerator rho n =
          (n + 3 : ℝ) *
              (S + rho ^ n * S - (n : ℝ) * rho ^ (n - 1) * P)
            + (n + 1 : ℝ) * rho ^ n
            - (n : ℝ) * rho ^ (n - 1)
            + rho ^ (2 * n) := by
      change
        (((n + 3 : ℝ) * S + (n + 1 : ℝ) * rho ^ n) * (1 + rho ^ n)
            - (n : ℝ) * rho ^ (n - 1) *
              (1 + (n + 3 : ℝ) * P + rho ^ (n + 1))) = _
      calc
        ((n + 3 : ℝ) * S + (n + 1 : ℝ) * rho ^ n) * (1 + rho ^ n)
              - (n : ℝ) * rho ^ (n - 1) *
                (1 + (n + 3 : ℝ) * P + rho ^ (n + 1))
            = (n + 3 : ℝ) *
                (S + rho ^ n * S - (n : ℝ) * rho ^ (n - 1) * P)
              + (n + 1 : ℝ) * rho ^ n
              - (n : ℝ) * rho ^ (n - 1)
              + (n + 1 : ℝ) * (rho ^ n * rho ^ n)
              - (n : ℝ) * (rho ^ (n - 1) * rho ^ (n + 1)) := by ring
        _ = (n + 3 : ℝ) *
                (S + rho ^ n * S - (n : ℝ) * rho ^ (n - 1) * P)
              + (n + 1 : ℝ) * rho ^ n
              - (n : ℝ) * rho ^ (n - 1)
              + rho ^ (2 * n) := by
            rw [hpowers, hsquare]
            ring
    have hmain :
        0 ≤ generalKRhoNumeratorDeriv rho n * (1 + rho ^ n)
            - (n : ℝ) * rho ^ (n - 1) * generalKRhoNumerator rho n := by
      rw [hqeq]
      have ha : 0 ≤ (n + 3 : ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hinside ha
      have hr₁ : 0 ≤ rho ^ (n - 1) := pow_nonneg hrho0 _
      have hrn : 0 ≤ rho ^ n := pow_nonneg hrho0 _
      have hr2n : 0 ≤ rho ^ (2 * n) := pow_nonneg hrho0 _
      have hbase :
          0 ≤ (n : ℝ) * (n + 2 : ℝ) * rho ^ (n - 1)
              + (n + 1 : ℝ) * rho ^ n + rho ^ (2 * n) := by
        positivity
      calc
        0 ≤ (n + 3 : ℝ) * ((n : ℝ) * rho ^ (n - 1))
              + (n + 1 : ℝ) * rho ^ n
              - (n : ℝ) * rho ^ (n - 1) + rho ^ (2 * n) := by
            nlinarith
        _ ≤ (n + 3 : ℝ) *
                (S + rho ^ n * S - (n : ℝ) * rho ^ (n - 1) * P)
              + (n + 1 : ℝ) * rho ^ n
              - (n : ℝ) * rho ^ (n - 1) + rho ^ (2 * n) := by
            linarith
    unfold generalKRhoCoeffDeriv
    exact div_nonneg hmain (by positivity)

theorem general_K_rhoCoeffDeriv_zero (rho : ℝ) :
    generalKRhoCoeffDeriv rho 0 = 1 / 4 := by
  norm_num [generalKRhoCoeffDeriv, generalKRhoNumerator,
    generalKRhoNumeratorDeriv]

theorem general_K_rhoCoeffDeriv_one (rho : ℝ) :
    generalKRhoCoeffDeriv rho 1 =
      (rho ^ 2 + 2 * rho + 3) / (6 * (1 + rho) ^ 2) := by
  norm_num [generalKRhoCoeffDeriv, generalKRhoNumerator,
    generalKRhoNumeratorDeriv, Finset.sum_Icc_succ_top]
  ring

theorem general_K_rhoCoeffDeriv_one_ge {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    1 / 4 ≤ generalKRhoCoeffDeriv rho 1 := by
  rw [general_K_rhoCoeffDeriv_one]
  have hden : 0 < 6 * (1 + rho) ^ 2 := by positivity
  rw [le_div_iff₀ hden]
  nlinarith [mul_nonneg (sub_nonneg.mpr hrho1) (by nlinarith : 0 ≤ rho + 3)]

theorem general_K_rhoCoeffDeriv_two_le {rho : ℝ}
    (_hrho0 : 0 ≤ rho) :
    generalKRhoCoeffDeriv rho 2 ≤ 9 / 16 := by
  have hpoly := general_K_f2_special_clear_pos rho
  have hden : 0 < 48 * (1 + rho ^ 2) ^ 2 := by positivity
  have hid :
      9 / 16 - generalKRhoCoeffDeriv rho 2 =
        generalKF2SpecialClear rho / (48 * (1 + rho ^ 2) ^ 2) := by
    unfold generalKRhoCoeffDeriv generalKRhoNumerator
      generalKRhoNumeratorDeriv generalKF2SpecialClear
    norm_num [Finset.sum_Icc_succ_top]
    field_simp
    ring
  have hdiff : 0 ≤ 9 / 16 - generalKRhoCoeffDeriv rho 2 := by
    rw [hid]
    exact div_nonneg (le_of_lt hpoly) (le_of_lt hden)
  linarith

theorem general_K_rhoCoeffDeriv_four_le {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    generalKRhoCoeffDeriv rho 4 ≤ 1 := by
  have hpoly := general_K_f4_special_clear_nonneg hrho0 hrho1
  have hden : 0 < 30 * (1 + rho ^ 4) ^ 2 := by positivity
  have hid :
      1 - generalKRhoCoeffDeriv rho 4 =
        generalKF4SpecialClear rho / (30 * (1 + rho ^ 4) ^ 2) := by
    unfold generalKRhoCoeffDeriv generalKRhoNumerator
      generalKRhoNumeratorDeriv generalKF4SpecialClear
    norm_num [Finset.sum_Icc_succ_top]
    field_simp
    ring
  have hdiff : 0 ≤ 1 - generalKRhoCoeffDeriv rho 4 := by
    rw [hid]
    exact div_nonneg hpoly (le_of_lt hden)
  linarith

def generalKRhoSeriesDerivTerm (rho : ℝ) (n : Nat) : ℝ :=
  (-1 : ℝ) ^ n * generalKRhoCoeffDeriv rho n /
    (Nat.factorial n : ℝ)

theorem general_K_seriesTerm_eq_rhoCoeff (rho : ℝ) (n : Nat) :
    generalKSeriesTerm rho n =
      (-1 : ℝ) ^ n * generalKRhoCoeff rho n /
        (Nat.factorial n : ℝ) := by
  unfold generalKSeriesTerm generalKSeriesMag generalKRhoCoeff
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem hasDerivAt_generalKRhoSeriesTerm {rho : ℝ}
    (hrho0 : 0 ≤ rho) (n : Nat) :
    HasDerivAt (fun z => generalKSeriesTerm z n)
      (generalKRhoSeriesDerivTerm rho n) rho := by
  have hcoeff := hasDerivAt_generalKRhoCoeff hrho0 n
  have hscaled :=
    ((hcoeff.const_mul ((-1 : ℝ) ^ n)).div_const (Nat.factorial n : ℝ))
  simpa only [general_K_seriesTerm_eq_rhoCoeff,
    generalKRhoSeriesDerivTerm] using hscaled

theorem general_K_nat_succ_le_two_pow_succ (n : Nat) :
    n + 1 ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      omega

theorem general_K_rhoSeriesDerivTerm_norm_le {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (n : Nat) :
    ‖generalKRhoSeriesDerivTerm rho n‖ ≤
      (2 : ℝ) ^ n / (Nat.factorial n : ℝ) := by
  have hnonneg := general_K_rhoCoeffDeriv_nonneg hrho0 hrho1 n
  have hupper := general_K_rhoCoeffDeriv_le hrho0 hrho1 n
  have hfac : 0 < (Nat.factorial n : ℝ) := by positivity
  have hpowNat := general_K_nat_succ_le_two_pow_succ n
  have hpowReal : (n + 1 : ℝ) ≤ 2 ^ (n + 1) := by exact_mod_cast hpowNat
  have hhalf : (n + 1 : ℝ) / 2 ≤ 2 ^ n := by
    rw [pow_succ] at hpowReal
    nlinarith
  unfold generalKRhoSeriesDerivTerm
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (le_of_lt hfac)]
  simpa using
    (div_le_div_of_nonneg_right (hupper.trans hhalf) (le_of_lt hfac))

theorem general_K_rhoSeriesDerivBound_summable :
    Summable (fun n : Nat => (2 : ℝ) ^ n / (Nat.factorial n : ℝ)) :=
  Real.summable_pow_div_factorial 2

theorem hasDerivAt_generalKSeries_rho {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    HasDerivAt generalKSeries
      (∑' n : Nat, generalKRhoSeriesDerivTerm rho n) rho := by
  have hbaseMag : Summable (fun n => generalKSeriesMag (1 / 2 : ℝ) n) :=
    general_K_seriesMag_summable (by norm_num) (by norm_num)
  have hbase : Summable (fun n => generalKSeriesTerm (1 / 2 : ℝ) n) := by
    unfold generalKSeriesTerm
    exact hbaseMag.alternating
  exact hasDerivAt_tsum_of_isPreconnected
    general_K_rhoSeriesDerivBound_summable isOpen_Ioo isPreconnected_Ioo
    (fun n y hy => hasDerivAt_generalKRhoSeriesTerm (le_of_lt hy.1) n)
    (fun n y hy => general_K_rhoSeriesDerivTerm_norm_le
      (le_of_lt hy.1) (le_of_lt hy.2) n)
    (by norm_num) hbase ⟨hrho0, hrho1⟩

theorem hasDerivAt_general_K_rho {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    HasDerivAt (fun z => K z 1)
      (1 / Real.exp 1 -
        ∑' n : Nat, generalKRhoSeriesDerivTerm rho n) rho := by
  have hseries := hasDerivAt_generalKSeries_rho hrho0 hrho1
  have hlinear := (hasDerivAt_id rho).div_const (Real.exp 1)
  have hraw := hlinear.sub hseries
  apply hraw.congr_of_eventuallyEq
  filter_upwards [] with z
  exact general_K_at_xi_one_eq_series z

theorem general_K_factorial_five_geometric (n : Nat) :
    120 * 6 ^ n ≤ Nat.factorial (n + 5) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        120 * 6 ^ (n + 1) = 6 * (120 * 6 ^ n) := by
          rw [pow_succ]
          omega
        _ ≤ 6 * Nat.factorial (n + 5) := Nat.mul_le_mul_left 6 ih
        _ ≤ (n + 6) * Nat.factorial (n + 5) := by
          exact Nat.mul_le_mul_right _ (by omega)
        _ = Nat.factorial (n + 1 + 5) := by
          rw [show n + 1 + 5 = (n + 5) + 1 by omega, Nat.factorial_succ]
          congr 1

theorem general_K_factorial_six_geometric (n : Nat) :
    720 * 7 ^ n ≤ Nat.factorial (n + 6) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        720 * 7 ^ (n + 1) = 7 * (720 * 7 ^ n) := by
          rw [pow_succ]
          omega
        _ ≤ 7 * Nat.factorial (n + 6) := Nat.mul_le_mul_left 7 ih
        _ ≤ (n + 7) * Nat.factorial (n + 6) := by
          exact Nat.mul_le_mul_right _ (by omega)
        _ = Nat.factorial (n + 1 + 6) := by
          rw [show n + 1 + 6 = (n + 6) + 1 by omega, Nat.factorial_succ]
          congr 1

theorem general_K_factorial_five_tail_le (n : Nat) :
    (1 : ℝ) / (Nat.factorial (n + 5) : ℝ) ≤
      (1 / 120 : ℝ) * (1 / 6 : ℝ) ^ n := by
  have hnat := general_K_factorial_five_geometric n
  have hreal : (120 * 6 ^ n : ℝ) ≤ Nat.factorial (n + 5) := by
    exact_mod_cast hnat
  have hrecip := one_div_le_one_div_of_le
    (by positivity : (0 : ℝ) < 120 * 6 ^ n) hreal
  calc
    (1 : ℝ) / (Nat.factorial (n + 5) : ℝ)
        ≤ 1 / (120 * 6 ^ n : ℝ) := hrecip
    _ = (1 / 120 : ℝ) * (1 / 6 : ℝ) ^ n := by
      simp only [one_div, mul_inv_rev, inv_pow]
      ring

theorem general_K_factorial_six_tail_le (n : Nat) :
    (1 : ℝ) / (Nat.factorial (n + 6) : ℝ) ≤
      (1 / 720 : ℝ) * (1 / 7 : ℝ) ^ n := by
  have hnat := general_K_factorial_six_geometric n
  have hreal : (720 * 7 ^ n : ℝ) ≤ Nat.factorial (n + 6) := by
    exact_mod_cast hnat
  have hrecip := one_div_le_one_div_of_le
    (by positivity : (0 : ℝ) < 720 * 7 ^ n) hreal
  calc
    (1 : ℝ) / (Nat.factorial (n + 6) : ℝ)
        ≤ 1 / (720 * 7 ^ n : ℝ) := hrecip
    _ = (1 / 720 : ℝ) * (1 / 7 : ℝ) ^ n := by
      simp only [one_div, mul_inv_rev, inv_pow]
      ring

theorem general_K_factorial_deriv_tail_term_eq (n : Nat) :
    (n + 7 : ℝ) / (Nat.factorial (n + 6) : ℝ) =
      1 / (Nat.factorial (n + 5) : ℝ) +
      1 / (Nat.factorial (n + 6) : ℝ) := by
  have hfac : (Nat.factorial (n + 5) : ℝ) ≠ 0 := by positivity
  rw [show n + 6 = (n + 5) + 1 by omega, Nat.factorial_succ]
  push_cast
  field_simp [hfac]
  ring

theorem general_K_factorial_deriv_tail_lt :
    (∑' n : Nat, (n + 7 : ℝ) / (Nat.factorial (n + 6) : ℝ))
      < 1 / 80 := by
  let g : Nat → ℝ := fun n =>
    (1 / 120 : ℝ) * (1 / 6 : ℝ) ^ n +
      (1 / 720 : ℝ) * (1 / 7 : ℝ) ^ n
  have hg6 : Summable (fun n : Nat => (1 / 6 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hg7 : Summable (fun n : Nat => (1 / 7 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hg : Summable g := (hg6.mul_left (1 / 120)).add (hg7.mul_left (1 / 720))
  have hnonneg (n : Nat) :
      0 ≤ (n + 7 : ℝ) / (Nat.factorial (n + 6) : ℝ) := by positivity
  have hle (n : Nat) :
      (n + 7 : ℝ) / (Nat.factorial (n + 6) : ℝ) ≤ g n := by
    rw [general_K_factorial_deriv_tail_term_eq]
    dsimp [g]
    exact add_le_add (general_K_factorial_five_tail_le n)
      (general_K_factorial_six_tail_le n)
  have hf : Summable
      (fun n : Nat => (n + 7 : ℝ) / (Nat.factorial (n + 6) : ℝ)) :=
    Summable.of_nonneg_of_le hnonneg hle hg
  calc
    (∑' n : Nat, (n + 7 : ℝ) / (Nat.factorial (n + 6) : ℝ))
        ≤ ∑' n : Nat, g n := hf.tsum_le_tsum hle hg
    _ = (1 / 120 : ℝ) * (1 / (1 - 1 / 6)) +
          (1 / 720 : ℝ) * (1 / (1 - 1 / 7)) := by
      dsimp [g]
      rw [(hg6.mul_left (1 / 120)).tsum_add (hg7.mul_left (1 / 720)),
        tsum_mul_left, tsum_mul_left,
        tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 6 : ℝ)‖ < 1),
        tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 7 : ℝ)‖ < 1)]
      norm_num
    _ < 1 / 80 := general_K_factorial_tail_bound_arithmetic

theorem general_K_rhoSeriesDerivTerm_summable {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    Summable (fun n : Nat => generalKRhoSeriesDerivTerm rho n) := by
  have hnorm : Summable
      (fun n : Nat => ‖generalKRhoSeriesDerivTerm rho n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => general_K_rhoSeriesDerivTerm_norm_le hrho0 hrho1 n)
      general_K_rhoSeriesDerivBound_summable
  exact hnorm.of_norm

theorem general_K_rhoSeriesDerivTerm_norm_le_half {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (n : Nat) :
    ‖generalKRhoSeriesDerivTerm rho n‖ ≤
      (1 / 2 : ℝ) * ((n + 1 : ℝ) / (Nat.factorial n : ℝ)) := by
  have hnonneg := general_K_rhoCoeffDeriv_nonneg hrho0 hrho1 n
  have hupper := general_K_rhoCoeffDeriv_le hrho0 hrho1 n
  have hfac : 0 < (Nat.factorial n : ℝ) := by positivity
  unfold generalKRhoSeriesDerivTerm
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (le_of_lt hfac)]
  have hdiv := div_le_div_of_nonneg_right hupper (le_of_lt hfac)
  simpa only [one_mul] using hdiv.trans_eq (by ring)

theorem general_K_rhoSeriesDeriv_firstSix_le {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    (Finset.range 6).sum (fun n => generalKRhoSeriesDerivTerm rho n)
      ≤ 9 / 32 + 1 / 24 := by
  have h0 := general_K_rhoCoeffDeriv_zero rho
  have h1 := general_K_rhoCoeffDeriv_one_ge hrho0 hrho1
  have h2 := general_K_rhoCoeffDeriv_two_le hrho0
  have h3 := general_K_rhoCoeffDeriv_nonneg hrho0 hrho1 3
  have h4 := general_K_rhoCoeffDeriv_four_le hrho0 hrho1
  have h5 := general_K_rhoCoeffDeriv_nonneg hrho0 hrho1 5
  norm_num [generalKRhoSeriesDerivTerm, Finset.sum_range_succ] at ⊢
  nlinarith

theorem general_K_rhoSeriesDeriv_tailSix_norm_lt {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    ‖∑' n : Nat, generalKRhoSeriesDerivTerm rho (n + 6)‖ < 1 / 160 := by
  have hfull := general_K_rhoSeriesDerivTerm_summable hrho0 hrho1
  have htailNorm : Summable
      (fun n : Nat => ‖generalKRhoSeriesDerivTerm rho (n + 6)‖) :=
    hfull.norm.comp_injective (add_left_injective 6)
  have hfacTail : Summable
      (fun n : Nat => (n + 7 : ℝ) / (Nat.factorial (n + 6) : ℝ)) := by
    have hshift := general_K_rhoSeriesDerivBound_summable.comp_injective
      (add_right_injective 6)
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hshift.mul_left 2)
    intro n
    have hfac : 0 < (Nat.factorial (n + 6) : ℝ) := by positivity
    have hpowNat := general_K_nat_succ_le_two_pow_succ (n + 6)
    have hpowReal : (n + 7 : ℝ) ≤ 2 ^ (n + 7) := by
      exact_mod_cast hpowNat
    have hnum : (n + 7 : ℝ) ≤ 2 ^ (n + 6) * 2 := by
      simpa [pow_succ] using hpowReal
    have hdiv := div_le_div_of_nonneg_right hnum (le_of_lt hfac)
    have hcalc :
        (n + 7 : ℝ) / (Nat.factorial (n + 6) : ℝ) ≤
          2 * (2 ^ (n + 6) / (Nat.factorial (n + 6) : ℝ)) := by
      calc
        (n + 7 : ℝ) / (Nat.factorial (n + 6) : ℝ)
            ≤ 2 ^ (n + 7) / (Nat.factorial (n + 6) : ℝ) := hdiv
        _ = 2 * (2 ^ (n + 6) / (Nat.factorial (n + 6) : ℝ)) := by
          rw [show n + 7 = (n + 6) + 1 by omega, pow_succ]
          ring
    simpa [Function.comp_apply, Nat.add_comm] using hcalc
  have hnorm := norm_tsum_le_tsum_norm htailNorm
  have hpoint (n : Nat) :
      ‖generalKRhoSeriesDerivTerm rho (n + 6)‖ ≤
        (1 / 2 : ℝ) *
          ((n + 7 : ℝ) / (Nat.factorial (n + 6) : ℝ)) := by
    convert general_K_rhoSeriesDerivTerm_norm_le_half hrho0 hrho1 (n + 6) using 1
    all_goals norm_num [Nat.cast_add, Nat.cast_ofNat]
    all_goals ring
  have hsumle := htailNorm.tsum_le_tsum hpoint (hfacTail.mul_left (1 / 2))
  have hfactor :
      (∑' n : Nat,
        (1 / 2 : ℝ) *
          ((n + 7 : ℝ) / (Nat.factorial (n + 6) : ℝ))) =
        (1 / 2 : ℝ) *
          (∑' n : Nat, (n + 7 : ℝ) /
            (Nat.factorial (n + 6) : ℝ)) := by
    rw [tsum_mul_left]
  have htail := general_K_factorial_deriv_tail_lt
  rw [hfactor] at hsumle
  nlinarith

theorem general_K_rho_derivative_pos {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    0 < 1 / Real.exp 1 -
      ∑' n : Nat, generalKRhoSeriesDerivTerm rho n := by
  have hrho0' : 0 ≤ rho := le_of_lt hrho0
  have hrho1' : rho ≤ 1 := le_of_lt hrho1
  have hsum := general_K_rhoSeriesDerivTerm_summable hrho0' hrho1'
  have hsplit := hsum.sum_add_tsum_nat_add 6
  have hfirst := general_K_rhoSeriesDeriv_firstSix_le hrho0' hrho1'
  have htailNorm := general_K_rhoSeriesDeriv_tailSix_norm_lt hrho0' hrho1'
  have htail :
      (∑' n : Nat, generalKRhoSeriesDerivTerm rho (n + 6)) < 1 / 160 :=
    lt_of_le_of_lt (Real.le_norm_self _) htailNorm
  have hseries :
      (∑' n : Nat, generalKRhoSeriesDerivTerm rho n) <
        9 / 32 + 1 / 24 + 1 / 160 := by
    linarith
  have he : 1 / 3 < 1 / Real.exp 1 := by
    exact one_div_lt_one_div_of_lt (Real.exp_pos 1) Real.exp_one_lt_three
  have hmargin := general_K_derivative_margin_arithmetic
  nlinarith

theorem general_K_strictMonoOn_rho :
    StrictMonoOn (fun rho : ℝ => K rho 1) (Set.Ioo 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) 1)
  · intro rho hrho
    exact (hasDerivAt_general_K_rho hrho.1 hrho.2).continuousAt.continuousWithinAt
  · intro rho hrho
    have hrho' : rho ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa using hrho
    rw [(hasDerivAt_general_K_rho hrho'.1 hrho'.2).deriv]
    exact general_K_rho_derivative_pos hrho'.1 hrho'.2

theorem general_K_existsUnique_zero :
    ∃! rho : ℝ, rho ∈ Set.Ioo (1 / 3 : ℝ) (1 / 2 : ℝ) ∧ K rho 1 = 0 := by
  have hcont : ContinuousOn (fun rho : ℝ => K rho 1)
      (Set.Icc (1 / 3 : ℝ) (1 / 2 : ℝ)) := by
    intro rho hrho
    have hrho0 : 0 < rho := lt_of_lt_of_le (by norm_num) hrho.1
    have hrho1 : rho < 1 := lt_of_le_of_lt hrho.2 (by norm_num)
    exact (hasDerivAt_general_K_rho hrho0 hrho1).continuousAt.continuousWithinAt
  have hzeroMem : (0 : ℝ) ∈
      Set.Icc (K (1 / 3) 1) (K (1 / 2) 1) :=
    ⟨le_of_lt general_K_left_endpoint_negative_unconditional,
      le_of_lt general_K_right_endpoint_positive_unconditional⟩
  have hzeroImage := intermediate_value_Icc
    (by norm_num : (1 / 3 : ℝ) ≤ 1 / 2) hcont hzeroMem
  rcases hzeroImage with ⟨rho, hrho, hzero⟩
  have hrhoLeft : (1 / 3 : ℝ) < rho := by
    apply lt_of_le_of_ne hrho.1
    intro heq
    rw [← heq] at hzero
    linarith [general_K_left_endpoint_negative_unconditional]
  have hrhoRight : rho < (1 / 2 : ℝ) := by
    apply lt_of_le_of_ne hrho.2
    intro heq
    rw [heq] at hzero
    linarith [general_K_right_endpoint_positive_unconditional]
  refine ⟨rho, ⟨⟨hrhoLeft, hrhoRight⟩, hzero⟩, ?_⟩
  intro rho' hrho'
  have hrho'01 : rho' ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_trans (by norm_num) hrho'.1.1, lt_trans hrho'.1.2 (by norm_num)⟩
  have hrho01 : rho ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_trans (by norm_num) hrhoLeft, lt_trans hrhoRight (by norm_num)⟩
  apply general_K_strictMonoOn_rho.injOn hrho'01 hrho01
  have hzero' : K rho 1 = 0 := hzero
  change K rho' 1 = K rho 1
  rw [hrho'.2, hzero']

end

end SkiRental.Scalar
