import Mathlib

/-!
Elementary list-polynomial helpers.

`eval cs x` interprets `cs` as ascending power-basis coefficients:
`[c₀,c₁,...,cₙ] ↦ c₀ + x(c₁ + x(...))`.
-/

namespace SkiRental.Polynomial

open scoped BigOperators

def eval : List ℝ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => c + x * eval cs x

theorem eval_nonneg_of_nonneg_coeffs {cs : List ℝ} {x : ℝ}
    (hx : 0 ≤ x) (hc : ∀ c ∈ cs, 0 ≤ c) :
    0 ≤ eval cs x := by
  induction cs with
  | nil =>
      simp [eval]
  | cons c cs ih =>
      have hc0 : 0 ≤ c := hc c (by simp)
      have hcs : ∀ d ∈ cs, 0 ≤ d := by
        intro d hd
        exact hc d (by simp [hd])
      have htail : 0 ≤ eval cs x := ih hcs
      have hmul : 0 ≤ x * eval cs x := mul_nonneg hx htail
      simp [eval]
      linarith

theorem eval_pos_of_all_pos {cs : List ℝ} {x : ℝ}
    (hne : cs ≠ []) (hx : 0 ≤ x) (hc : ∀ c ∈ cs, 0 < c) :
    0 < eval cs x := by
  cases cs with
  | nil => exact False.elim (hne rfl)
  | cons c cs =>
      have hc0 : 0 < c := hc c (by simp)
      have htail : 0 ≤ eval cs x :=
        eval_nonneg_of_nonneg_coeffs hx (by
          intro d hd
          exact le_of_lt (hc d (by simp [hd])))
      have hmul : 0 ≤ x * eval cs x := mul_nonneg hx htail
      simp [eval]
      linarith

def bernstein5 (b0 b1 b2 b3 b4 b5 x : ℝ) : ℝ :=
  b0 * (1 - x) ^ 5
  + 5 * b1 * x * (1 - x) ^ 4
  + 10 * b2 * x ^ 2 * (1 - x) ^ 3
  + 10 * b3 * x ^ 3 * (1 - x) ^ 2
  + 5 * b4 * x ^ 4 * (1 - x)
  + b5 * x ^ 5

theorem bernstein5_pos {b0 b1 b2 b3 b4 b5 x : ℝ}
    (hb0 : 0 < b0) (hb1 : 0 < b1) (hb2 : 0 < b2)
    (hb3 : 0 < b3) (hb4 : 0 < b4) (hb5 : 0 < b5)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 < bernstein5 b0 b1 b2 b3 b4 b5 x := by
  by_cases hx_zero : x = 0
  · subst x
    simp [bernstein5]
    exact hb0
  · have hx_pos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx_zero)
    have hlast : 0 < b5 * x ^ 5 := by positivity
    have hnonneg : 0 ≤
        b0 * (1 - x) ^ 5
        + 5 * b1 * x * (1 - x) ^ 4
        + 10 * b2 * x ^ 2 * (1 - x) ^ 3
        + 10 * b3 * x ^ 3 * (1 - x) ^ 2
        + 5 * b4 * x ^ 4 * (1 - x) := by
      positivity
    unfold bernstein5
    linarith

def bernsteinBasis (n i : Nat) (x : ℝ) : ℝ :=
  (Nat.choose n i : ℝ) * x ^ i * (1 - x) ^ (n - i)

def bernsteinEval (n : Nat) (coeff : Nat → ℝ) (x : ℝ) : ℝ :=
  (Finset.range (n + 1)).sum (fun i => coeff i * bernsteinBasis n i x)

theorem bernsteinBasis_nonneg {n i : Nat} {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ bernsteinBasis n i x := by
  unfold bernsteinBasis
  positivity

theorem exists_bernsteinBasis_pos (n : Nat) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ i, i ∈ Finset.range (n + 1) ∧ 0 < bernsteinBasis n i x := by
  by_cases hx_one : x = 1
  · refine ⟨n, by simp, ?_⟩
    subst x
    simp [bernsteinBasis]
  · have hx_lt_one : x < 1 := lt_of_le_of_ne hx1 hx_one
    refine ⟨0, by simp, ?_⟩
    have h_one_sub : 0 < 1 - x := by linarith
    simp [bernsteinBasis]
    positivity

theorem bernsteinEval_pos {n : Nat} {coeff : Nat → ℝ} {x : ℝ}
    (hc : ∀ i, i ≤ n → 0 < coeff i)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 < bernsteinEval n coeff x := by
  unfold bernsteinEval
  obtain ⟨i, hi, hbasis⟩ := exists_bernsteinBasis_pos n hx0 hx1
  apply Finset.sum_pos'
  · intro j hj
    have hj_le : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact mul_nonneg (le_of_lt (hc j hj_le)) (bernsteinBasis_nonneg hx0 hx1)
  · exact ⟨i, hi, mul_pos (hc i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) hbasis⟩

theorem bernsteinEval_nonneg {n : Nat} {coeff : Nat → ℝ} {x : ℝ}
    (hc : ∀ i, i ≤ n → 0 ≤ coeff i)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ bernsteinEval n coeff x := by
  unfold bernsteinEval
  apply Finset.sum_nonneg
  intro i hi
  have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact mul_nonneg (hc i hi_le) (bernsteinBasis_nonneg hx0 hx1)

end SkiRental.Polynomial
