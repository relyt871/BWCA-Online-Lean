import general_K.GeneralK

/-!
# The second bound in `lem:one-third-kernel`

This file proves the paper's bound `D(1/3, xi) < 1` for `xi` in `[0,1]`.
The proof uses the five-term alternating upper bound for `U`, integrates that
finite expression exactly, and checks the remaining rational inequality after
clearing positive denominators.
-/

namespace SkiRental.Scalar

open scoped BigOperators Interval

noncomputable section

def oneThirdUUpper (xi t : ℝ) : ℝ :=
  1 / (1 + xi)
  - t / (1 + xi / 3)
  + t ^ 2 / (2 * (1 + xi / 9))
  - t ^ 3 / (6 * (1 + xi / 27))
  + t ^ 4 / (24 * (1 + xi / 81))

def oneThirdUUpperPrimitive (xi t : ℝ) : ℝ :=
  t / (1 + xi)
  - t ^ 2 / (2 * (1 + xi / 3))
  + t ^ 3 / (6 * (1 + xi / 9))
  - t ^ 4 / (24 * (1 + xi / 27))
  + t ^ 5 / (120 * (1 + xi / 81))

def oneThirdS (xi : ℝ) : ℝ :=
  2 * xi * (1 - xi) / ((1 + xi) * (3 + xi))
  + xi * (xi + 87) / ((xi + 9) * (xi + 27))
  + 121 * xi / (60 * (xi + 81))

theorem one_third_kernel_tail5_nonpos {xi t : ℝ}
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑' k : Nat, UpowerTerm (1 / 3) xi (k + 5) t) ≤ 0 := by
  have hmag : Summable (fun k => UpowerMag (1 / 3) xi t (k + 5)) := by
    exact (summable_nat_add_iff 5).mpr
      (UpowerMag_summable (by norm_num) hxi0 ht0)
  have hanti : Antitone (fun k => UpowerMag (1 / 3) xi t (k + 5)) := by
    apply antitone_nat_of_succ_le
    intro k
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      UpowerMag_succ_le (ρ := (1 / 3 : ℝ)) (ξ := xi) (t := t)
        (by norm_num) (by norm_num) hxi0 hxi1 ht0 ht1
        (n := k + 5) (by omega)
  have htail_nonneg :
      0 ≤ ∑' k : Nat, (-1 : ℝ) ^ k * UpowerMag (1 / 3) xi t (k + 5) := by
    exact hanti.alternating_series_le_tendsto
      hmag.tendsto_alternating_series_tsum 0
  have heq :
      (∑' k : Nat, UpowerTerm (1 / 3) xi (k + 5) t)
        = -∑' k : Nat, (-1 : ℝ) ^ k * UpowerMag (1 / 3) xi t (k + 5) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro k
    rw [UpowerTerm_eq_altMag]
    rw [pow_add]
    norm_num
  rw [heq]
  linarith

theorem one_third_kernel_U_le_upper {xi t : ℝ}
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    U (1 / 3) xi t ≤ oneThirdUUpper xi t := by
  have hterm : Summable fun n => UpowerTerm (1 / 3) xi n t :=
    UpowerTerm_summable (by norm_num) hxi0
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n => UpowerTerm (1 / 3) xi n t) 5 hterm
  have htail := one_third_kernel_tail5_nonpos hxi0 hxi1 ht0 ht1
  have hpartial :
      (Finset.range 5).sum (fun n => UpowerTerm (1 / 3) xi n t)
        = oneThirdUUpper xi t := by
    unfold oneThirdUUpper UpowerTerm
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    ring
  unfold U Upower
  rw [hpartial] at hsplit
  linarith

theorem one_third_kernel_upper_continuous (xi : ℝ) :
    Continuous (fun t => oneThirdUUpper xi t) := by
  unfold oneThirdUUpper
  fun_prop

theorem one_third_kernel_integral_pow_div_const
    (n : Nat) {c a b : ℝ} (hc : c ≠ 0) :
    (∫ t in a..b, t ^ n / c)
      = b ^ (n + 1) / ((n + 1 : ℝ) * c)
        - a ^ (n + 1) / ((n + 1 : ℝ) * c) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    have h := ((hasDerivAt_id' t).fun_pow (n + 1)).div_const ((n + 1 : ℝ) * c)
    convert h using 1 <;> try rfl
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp [hn, hc]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring
  · exact (by fun_prop : Continuous (fun t : ℝ => t ^ n / c)).intervalIntegrable _ _

theorem one_third_kernel_upper_integral {xi : ℝ} (hxi0 : 0 ≤ xi) :
    (∫ t in (1 / 3 : ℝ)..1, oneThirdUUpper xi t)
      = oneThirdUUpperPrimitive xi 1
        - oneThirdUUpperPrimitive xi (1 / 3) := by
  have h1 : 1 + xi ≠ 0 := by positivity
  have h3 : 1 + xi / 3 ≠ 0 := by positivity
  have h9 : 2 * (1 + xi / 9) ≠ 0 := by positivity
  have h27 : 6 * (1 + xi / 27) ≠ 0 := by positivity
  have h81 : 24 * (1 + xi / 81) ≠ 0 := by positivity
  let f0 := fun _ : ℝ => 1 / (1 + xi)
  let f1 := fun t : ℝ => t / (1 + xi / 3)
  let f2 := fun t : ℝ => t ^ 2 / (2 * (1 + xi / 9))
  let f3 := fun t : ℝ => t ^ 3 / (6 * (1 + xi / 27))
  let f4 := fun t : ℝ => t ^ 4 / (24 * (1 + xi / 81))
  have hf0 : IntervalIntegrable f0 MeasureTheory.volume (1 / 3) 1 :=
    (by dsimp [f0]; fun_prop : Continuous f0).intervalIntegrable _ _
  have hf1 : IntervalIntegrable f1 MeasureTheory.volume (1 / 3) 1 :=
    (by dsimp [f1]; fun_prop : Continuous f1).intervalIntegrable _ _
  have hf2 : IntervalIntegrable f2 MeasureTheory.volume (1 / 3) 1 :=
    (by dsimp [f2]; fun_prop : Continuous f2).intervalIntegrable _ _
  have hf3 : IntervalIntegrable f3 MeasureTheory.volume (1 / 3) 1 :=
    (by dsimp [f3]; fun_prop : Continuous f3).intervalIntegrable _ _
  have hf4 : IntervalIntegrable f4 MeasureTheory.volume (1 / 3) 1 :=
    (by dsimp [f4]; fun_prop : Continuous f4).intervalIntegrable _ _
  have hi0 := one_third_kernel_integral_pow_div_const 0
    (a := (1 / 3 : ℝ)) (b := 1) h1
  have hi1 := one_third_kernel_integral_pow_div_const 1
    (a := (1 / 3 : ℝ)) (b := 1) h3
  have hi2 := one_third_kernel_integral_pow_div_const 2
    (a := (1 / 3 : ℝ)) (b := 1) h9
  have hi3 := one_third_kernel_integral_pow_div_const 3
    (a := (1 / 3 : ℝ)) (b := 1) h27
  have hi4 := one_third_kernel_integral_pow_div_const 4
    (a := (1 / 3 : ℝ)) (b := 1) h81
  have hi0' := hi0
  have hi1' := hi1
  simp only [pow_zero] at hi0'
  simp only [pow_one] at hi1'
  unfold oneThirdUUpper
  change (∫ t in (1 / 3 : ℝ)..1, (((f0 t - f1 t) + f2 t) - f3 t) + f4 t)
      = oneThirdUUpperPrimitive xi 1 - oneThirdUUpperPrimitive xi (1 / 3)
  rw [intervalIntegral.integral_add (((hf0.sub hf1).add hf2).sub hf3) hf4,
    intervalIntegral.integral_sub ((hf0.sub hf1).add hf2) hf3,
    intervalIntegral.integral_add (hf0.sub hf1) hf2,
    intervalIntegral.integral_sub hf0 hf1]
  dsimp [f0, f1, f2, f3, f4]
  rw [hi0', hi1', hi2, hi3, hi4]
  unfold oneThirdUUpperPrimitive
  norm_num
  ring

theorem one_third_kernel_scaled_upper_integral_eq_s {xi : ℝ}
    (hxi0 : 0 ≤ xi) :
    3 * xi * (oneThirdUUpperPrimitive xi 1
      - oneThirdUUpperPrimitive xi (1 / 3)) = oneThirdS xi := by
  have h1 : 1 + xi ≠ 0 := by positivity
  have h3 : 3 + xi ≠ 0 := by positivity
  have h9 : 9 + xi ≠ 0 := by positivity
  have h27 : 27 + xi ≠ 0 := by positivity
  have h81 : 81 + xi ≠ 0 := by positivity
  unfold oneThirdUUpperPrimitive oneThirdS
  field_simp [h1, h3, h9, h27, h81]
  ring

def oneThirdSBoundPoly (xi : ℝ) : ℝ :=
  229720293 - 138614976 * xi + 13485654 * xi ^ 2
    - 225696 * xi ^ 3 + 7781 * xi ^ 4

theorem one_third_kernel_s_bound_identity {xi : ℝ}
    (hxi0 : 0 ≤ xi) :
    11480 * ((1 + xi) * (3 + xi) * (9 + xi) * (27 + xi) * (81 + xi))
        * ((11671 / 34440 : ℝ) - oneThirdS xi)
      = (1 - xi) * oneThirdSBoundPoly xi := by
  have h1 : 1 + xi ≠ 0 := by positivity
  have h3 : 3 + xi ≠ 0 := by positivity
  have h9 : 9 + xi ≠ 0 := by positivity
  have h27 : 27 + xi ≠ 0 := by positivity
  have h81 : 81 + xi ≠ 0 := by positivity
  unfold oneThirdS oneThirdSBoundPoly
  field_simp [h1, h3, h9, h27, h81]
  ring

theorem one_third_kernel_s_le {xi : ℝ}
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    oneThirdS xi ≤ 11671 / 34440 := by
  have hxi3 : xi ^ 3 ≤ 1 := pow_le_one₀ hxi0 hxi1
  have hpoly : 0 < oneThirdSBoundPoly xi := by
    unfold oneThirdSBoundPoly
    nlinarith [pow_nonneg hxi0 2, pow_nonneg hxi0 4]
  have hright : 0 ≤ (1 - xi) * oneThirdSBoundPoly xi :=
    mul_nonneg (by linarith) (le_of_lt hpoly)
  have hid := one_third_kernel_s_bound_identity hxi0
  have hfactor :
      0 < 11480 * ((1 + xi) * (3 + xi) * (9 + xi) * (27 + xi) * (81 + xi)) := by
    positivity
  have hmul :
      0 ≤ 11480 * ((1 + xi) * (3 + xi) * (9 + xi) * (27 + xi) * (81 + xi))
        * ((11671 / 34440 : ℝ) - oneThirdS xi) := by
    rw [hid]
    exact hright
  have := (mul_nonneg_iff_of_pos_left hfactor).mp hmul
  linarith

theorem one_third_kernel_D_lt_one {xi : ℝ}
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    D (1 / 3) xi < 1 := by
  have hUcont :
      ContinuousOn (fun t => U (1 / 3) xi t) (Set.uIcc (1 / 3 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (1 / 3 : ℝ) ≤ 1)]
    intro t ht
    simpa [U] using
      (hasDerivAt_Upower (ρ := (1 / 3 : ℝ)) (ξ := xi)
        (by norm_num) hxi0 (by linarith [ht.1]) (by linarith [ht.2])).continuousAt.continuousWithinAt
  have hUpperCont : Continuous (fun t => oneThirdUUpper xi t) := by
    exact one_third_kernel_upper_continuous xi
  have hint :
      (∫ t in (1 / 3 : ℝ)..1, U (1 / 3) xi t)
        ≤ ∫ t in (1 / 3 : ℝ)..1, oneThirdUUpper xi t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact hUcont.intervalIntegrable
    · exact hUpperCont.intervalIntegrable _ _
    · intro t ht
      exact one_third_kernel_U_le_upper hxi0 hxi1 (by linarith [ht.1]) ht.2
  have hscale : 0 ≤ 3 * Real.exp 1 * xi := by positivity
  have hDupper : D (1 / 3) xi ≤ Real.exp 1 * oneThirdS xi := by
    calc
      D (1 / 3) xi
          = (3 * Real.exp 1 * xi)
              * ∫ t in (1 / 3 : ℝ)..1, U (1 / 3) xi t := by
                unfold D
                ring
      _ ≤ (3 * Real.exp 1 * xi)
              * ∫ t in (1 / 3 : ℝ)..1, oneThirdUUpper xi t :=
            mul_le_mul_of_nonneg_left hint hscale
      _ = Real.exp 1 * oneThirdS xi := by
            rw [one_third_kernel_upper_integral hxi0]
            rw [← one_third_kernel_scaled_upper_integral_eq_s hxi0]
            ring
  have hs := one_third_kernel_s_le hxi0 hxi1
  have he : Real.exp 1 < 11 / 4 :=
    lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hfinal : Real.exp 1 * (11671 / 34440 : ℝ) < 1 := by
    have hspos : (0 : ℝ) < 11671 / 34440 := by norm_num
    calc
      Real.exp 1 * (11671 / 34440 : ℝ)
          < (11 / 4 : ℝ) * (11671 / 34440 : ℝ) :=
            mul_lt_mul_of_pos_right he hspos
      _ < 1 := by norm_num
  have hexp_nonneg : 0 ≤ Real.exp 1 := le_of_lt (Real.exp_pos 1)
  exact lt_of_le_of_lt hDupper
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hs hexp_nonneg) hfinal)

def oneThirdLateSeries : ℝ := generalKSeries (1 / 3)

theorem one_third_kernel_late_series_positive :
    (1 / 3 : ℝ) / Real.exp 1 < oneThirdLateSeries := by
  have hK : K (1 / 3) 1 < 0 := general_K_left_endpoint_negative_unconditional
  rw [general_K_at_xi_one_eq_series] at hK
  unfold oneThirdLateSeries
  linarith

end

end SkiRental.Scalar
