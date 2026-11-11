import Mathlib
import SkiRental.LemmaCertificates
import SkiRental.Polynomial

/-!
Mathlib-backed analytic objects and first reductions.

This module defines the functions used in the tight
ski-rental analysis and proves some finite/closed-form facts used by the
paper's reductions.

What is formalized here:
* the functions `U`, `D`, `dCoeff`, and `K`;
* basic finite partial sums for the `U` series;
* positivity of the cleared cubic from the `U` lower-bound check on
  `ρ ∈ [0.31,1]`, via an exact Bernstein certificate.

The full finite/infinite functional identities, convergence arguments, and the
theorem equating the two representations of `U` are intentionally left for the
next layer.
-/

namespace SkiRental.Scalar

open scoped BigOperators
noncomputable section

noncomputable def Ugeom (ρ ξ t : ℝ) : ℝ :=
  ∑' j : Nat, (-ξ) ^ j * Real.exp (-(t * ρ ^ j))

def UpowerTerm (ρ ξ : ℝ) (n : Nat) (t : ℝ) : ℝ :=
  (-t) ^ n / ((Nat.factorial n : ℝ) * (1 + ξ * ρ ^ n))

noncomputable def Upower (ρ ξ t : ℝ) : ℝ :=
  ∑' n : Nat, UpowerTerm ρ ξ n t

noncomputable def U (ρ ξ t : ℝ) : ℝ :=
  Upower ρ ξ t

def UpowerShiftTerm (ρ ξ : ℝ) (n : Nat) (t : ℝ) : ℝ :=
  (-t) ^ n / ((Nat.factorial n : ℝ) * (1 + ξ * ρ ^ (n + 1)))

def UpowerDerivTerm (ρ ξ : ℝ) : Nat → ℝ → ℝ
  | 0, _ => 0
  | n + 1, t => -UpowerShiftTerm ρ ξ n t

noncomputable def UpowerDerivSeries (ρ ξ t : ℝ) : ℝ :=
  ∑' n : Nat, UpowerDerivTerm ρ ξ n t

noncomputable def lemma20VFromUpower (ρ ξ t : ℝ) : ℝ :=
  Upower ρ ξ t + ρ * deriv (fun z => Upower ρ ξ z) t

def UpowerDerivBound : Nat → ℝ
  | 0 => 0
  | n + 1 => (2 : ℝ) ^ n / (Nat.factorial n : ℝ)

noncomputable def D (ρ ξ : ℝ) : ℝ :=
  (Real.exp 1 * ξ / ρ) * ∫ x in ρ..1, U ρ ξ x

noncomputable def dCoeff (ρ : ℝ) (n : Nat) : ℝ :=
  (1 + (n + 3 : ℝ) * (Finset.Icc 1 n).sum (fun k => ρ ^ k) + ρ ^ (n + 1))
  / ((n + 1 : ℝ) * (n + 2 : ℝ))

noncomputable def K (ρ ξ : ℝ) : ℝ :=
  ρ / Real.exp 1
  - ξ * (∑' n : Nat,
      (-1 : ℝ) ^ n * dCoeff ρ n
      / ((Nat.factorial n : ℝ) * (1 + ξ * ρ ^ n)))

def lemma20VMag (ρ ξ t : ℝ) (n : Nat) : ℝ :=
  t ^ n / ((Nat.factorial n : ℝ) * (1 + ξ * ρ ^ n) * (1 + ξ * ρ ^ (n + 1)))

def lemma20VTerm (ρ ξ t : ℝ) (n : Nat) : ℝ :=
  (-1 : ℝ) ^ n * lemma20VMag ρ ξ t n

noncomputable def lemma20Vbar (ρ ξ t : ℝ) : ℝ :=
  ∑' n : Nat, lemma20VTerm ρ ξ t n

noncomputable def lemma20V (ρ ξ t : ℝ) : ℝ :=
  (1 - ρ) * lemma20Vbar ρ ξ t

noncomputable def lemma20P5T (ρ ξ t : ℝ) : ℝ :=
  (Finset.range 6).sum (fun n => lemma20VTerm ρ ξ t n)

noncomputable def lemma20P5 (ρ ξ : ℝ) : ℝ :=
  1 / ((1 + ξ) * (1 + ξ * ρ))
  - 1 / ((1 + ξ * ρ) * (1 + ξ * ρ ^ 2))
  + 1 / (2 * (1 + ξ * ρ ^ 2) * (1 + ξ * ρ ^ 3))
  - 1 / (6 * (1 + ξ * ρ ^ 3) * (1 + ξ * ρ ^ 4))
  + 1 / (24 * (1 + ξ * ρ ^ 4) * (1 + ξ * ρ ^ 5))
  - 1 / (120 * (1 + ξ * ρ ^ 5) * (1 + ξ * ρ ^ 6))

def lemma20P5Den (ρ ξ : ℝ) : ℝ :=
  120 * (1 + ξ) * (1 + ξ * ρ) * (1 + ξ * ρ ^ 2)
    * (1 + ξ * ρ ^ 3) * (1 + ξ * ρ ^ 4)
    * (1 + ξ * ρ ^ 5) * (1 + ξ * ρ ^ 6)

def lemma20P5Num (ρ ξ : ℝ) : ℝ :=
  120 * (1 + ξ * ρ ^ 2) * (1 + ξ * ρ ^ 3)
      * (1 + ξ * ρ ^ 4) * (1 + ξ * ρ ^ 5)
      * (1 + ξ * ρ ^ 6)
  - 120 * (1 + ξ) * (1 + ξ * ρ ^ 3)
      * (1 + ξ * ρ ^ 4) * (1 + ξ * ρ ^ 5)
      * (1 + ξ * ρ ^ 6)
  + 60 * (1 + ξ) * (1 + ξ * ρ)
      * (1 + ξ * ρ ^ 4) * (1 + ξ * ρ ^ 5)
      * (1 + ξ * ρ ^ 6)
  - 20 * (1 + ξ) * (1 + ξ * ρ)
      * (1 + ξ * ρ ^ 2) * (1 + ξ * ρ ^ 5)
      * (1 + ξ * ρ ^ 6)
  + 5 * (1 + ξ) * (1 + ξ * ρ)
      * (1 + ξ * ρ ^ 2) * (1 + ξ * ρ ^ 3)
      * (1 + ξ * ρ ^ 6)
  - (1 + ξ) * (1 + ξ * ρ) * (1 + ξ * ρ ^ 2)
      * (1 + ξ * ρ ^ 3) * (1 + ξ * ρ ^ 4)

def lemma20P5TNum (ρ ξ t : ℝ) : ℝ :=
  120 * (1 + ξ * ρ ^ 2) * (1 + ξ * ρ ^ 3)
      * (1 + ξ * ρ ^ 4) * (1 + ξ * ρ ^ 5)
      * (1 + ξ * ρ ^ 6)
  - 120 * t * (1 + ξ) * (1 + ξ * ρ ^ 3)
      * (1 + ξ * ρ ^ 4) * (1 + ξ * ρ ^ 5)
      * (1 + ξ * ρ ^ 6)
  + 60 * t ^ 2 * (1 + ξ) * (1 + ξ * ρ)
      * (1 + ξ * ρ ^ 4) * (1 + ξ * ρ ^ 5)
      * (1 + ξ * ρ ^ 6)
  - 20 * t ^ 3 * (1 + ξ) * (1 + ξ * ρ)
      * (1 + ξ * ρ ^ 2) * (1 + ξ * ρ ^ 5)
      * (1 + ξ * ρ ^ 6)
  + 5 * t ^ 4 * (1 + ξ) * (1 + ξ * ρ)
      * (1 + ξ * ρ ^ 2) * (1 + ξ * ρ ^ 3)
      * (1 + ξ * ρ ^ 6)
  - t ^ 5 * (1 + ξ) * (1 + ξ * ρ) * (1 + ξ * ρ ^ 2)
      * (1 + ξ * ρ ^ 3) * (1 + ξ * ρ ^ 4)

def lemma20P5CoeffQ (i j : Nat) : SkiRental.Certificates.Q :=
  (((SkiRental.Certificates.lemma20P5BernsteinCoeffs.getD i []).getD j 0 :
    SkiRental.Certificates.Q))

def lemma20P5Coeff (i j : Nat) : ℝ :=
  (lemma20P5CoeffQ i j : ℝ)

def lemma20P5CoeffFin (i : Fin 21) (j : Fin 6) : SkiRental.Certificates.Q :=
  lemma20P5CoeffQ i j

def lemma20P5Bernstein (α β : ℝ) : ℝ :=
  SkiRental.Polynomial.bernsteinEval 20
    (fun i => SkiRental.Polynomial.bernsteinEval 5
      (fun j => lemma20P5Coeff i j) β)
    α

def lemma20P5TCoeffQ (i j k : Nat) : SkiRental.Certificates.Q :=
  ((((SkiRental.Certificates.lemma20P5TBernsteinCoeffs.getD i []).getD j []).getD k 0 :
    SkiRental.Certificates.Q))

def lemma20P5TCoeff (i j k : Nat) : ℝ :=
  (lemma20P5TCoeffQ i j k : ℝ)

def lemma20P5TCoeffFin
    (i : Fin 21) (j : Fin 6) (k : Fin 6) : SkiRental.Certificates.Q :=
  lemma20P5TCoeffQ i j k

def lemma20P5TBernstein (α β τ : ℝ) : ℝ :=
  SkiRental.Polynomial.bernsteinEval 20
    (fun i => SkiRental.Polynomial.bernsteinEval 5
      (fun j => SkiRental.Polynomial.bernsteinEval 5
        (fun k => lemma20P5TCoeff i j k) τ) β)
    α

def UPartial (N : Nat) (ρ ξ t : ℝ) : ℝ :=
  (Finset.range N).sum (fun j => (-ξ) ^ j * Real.exp (-(t * ρ ^ j)))

theorem UPartial_zero (ρ ξ t : ℝ) :
    UPartial 0 ρ ξ t = 0 := by
  simp [UPartial]

theorem UPartial_one (ρ ξ t : ℝ) :
    UPartial 1 ρ ξ t = Real.exp (-t) := by
  simp [UPartial]

theorem lemma20VMag_nonneg {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ) (ht0 : 0 ≤ t)
    (n : Nat) :
    0 ≤ lemma20VMag ρ ξ t n := by
  unfold lemma20VMag
  positivity

theorem lemma20VMag_succ_le {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {n : Nat} (hn : 6 ≤ n) :
    lemma20VMag ρ ξ t (n + 1) ≤ lemma20VMag ρ ξ t n := by
  have hρn_nonneg : 0 ≤ ρ ^ n := pow_nonneg hρ0 n
  have hρn2_nonneg : 0 ≤ ρ ^ (n + 2) := pow_nonneg hρ0 (n + 2)
  have hρn_le_one : ρ ^ n ≤ 1 := pow_le_one₀ hρ0 hρ1
  have hξρn_le_one : ξ * ρ ^ n ≤ 1 := by
    nlinarith [mul_le_mul hξ1 hρn_le_one hρn_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  have hnum_le_two : 1 + ξ * ρ ^ n ≤ 2 := by nlinarith
  have hden_pos : 0 < 1 + ξ * ρ ^ (n + 2) := by positivity
  have hratio_factor : (1 + ξ * ρ ^ n) / (1 + ξ * ρ ^ (n + 2)) ≤ 2 := by
    rw [div_le_iff₀ hden_pos]
    nlinarith [mul_nonneg hξ0 hρn2_nonneg]
  have hn_pos : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
  have hn_ge_seven : (7 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ hn
  have htwo_over : (2 : ℝ) / (n + 1) ≤ 1 := by
    rw [div_le_iff₀ hn_pos]
    nlinarith
  have hratio_le_one :
      t / (n + 1) * ((1 + ξ * ρ ^ n) / (1 + ξ * ρ ^ (n + 2))) ≤ 1 := by
    calc
      t / (n + 1) * ((1 + ξ * ρ ^ n) / (1 + ξ * ρ ^ (n + 2)))
          ≤ (1 / (n + 1)) * 2 := by
            gcongr
      _ = 2 / (n + 1) := by ring
      _ ≤ 1 := htwo_over
  have hcur_nonneg : 0 ≤ lemma20VMag ρ ξ t n := lemma20VMag_nonneg hρ0 hξ0 ht0 n
  have hratio_eq :
      lemma20VMag ρ ξ t (n + 1)
        = (t / (n + 1) * ((1 + ξ * ρ ^ n) / (1 + ξ * ρ ^ (n + 2))))
            * lemma20VMag ρ ξ t n := by
    unfold lemma20VMag
    have hfac : ((Nat.factorial n.succ : Nat) : ℝ)
        = (n + 1 : ℝ) * (Nat.factorial n : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [hfac]
    field_simp [hn_pos.ne', hden_pos.ne']
    ring_nf
  rw [hratio_eq]
  exact mul_le_of_le_one_left hcur_nonneg hratio_le_one

theorem lemma20VMag_shifted_antitone {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Antitone (fun k => lemma20VMag ρ ξ t (k + 6)) := by
  apply antitone_nat_of_succ_le
  intro k
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    lemma20VMag_succ_le (ρ := ρ) (ξ := ξ) (t := t)
      hρ0 hρ1 hξ0 hξ1 ht0 ht1 (n := k + 6) (by omega)

theorem lemma20VMag_le_expTerm {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ) (ht0 : 0 ≤ t)
    (n : Nat) :
    lemma20VMag ρ ξ t n ≤ t ^ n / (Nat.factorial n : ℝ) := by
  unfold lemma20VMag
  have hnum : 0 ≤ t ^ n := pow_nonneg ht0 n
  have hfac_pos : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hA_ge : 1 ≤ 1 + ξ * ρ ^ n := by
    nlinarith [mul_nonneg hξ0 (pow_nonneg hρ0 n)]
  have hB_ge : 1 ≤ 1 + ξ * ρ ^ (n + 1) := by
    nlinarith [mul_nonneg hξ0 (pow_nonneg hρ0 (n + 1))]
  have hden_ge : (Nat.factorial n : ℝ)
      ≤ (Nat.factorial n : ℝ) * (1 + ξ * ρ ^ n) * (1 + ξ * ρ ^ (n + 1)) := by
    nlinarith [mul_le_mul_of_nonneg_left hA_ge (le_of_lt hfac_pos),
      mul_le_mul_of_nonneg_left hB_ge
        (mul_nonneg (le_of_lt hfac_pos) (by positivity : 0 ≤ 1 + ξ * ρ ^ n))]
  exact div_le_div_of_nonneg_left hnum hfac_pos hden_ge

theorem lemma20VMag_summable {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ) (ht0 : 0 ≤ t) :
    Summable (fun n => lemma20VMag ρ ξ t n) := by
  exact Summable.of_nonneg_of_le
    (fun n => lemma20VMag_nonneg hρ0 hξ0 ht0 n)
    (fun n => lemma20VMag_le_expTerm hρ0 hξ0 ht0 n)
    (Real.summable_pow_div_factorial t)

theorem lemma20_shifted_tail_nonneg {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ ∑' k : Nat, (-1 : ℝ) ^ k * lemma20VMag ρ ξ t (k + 6) := by
  have hshift : Summable (fun k => lemma20VMag ρ ξ t (k + 6)) := by
    exact (summable_nat_add_iff 6).mpr (lemma20VMag_summable hρ0 hξ0 ht0)
  have htend := hshift.tendsto_alternating_series_tsum
  have hbound := (lemma20VMag_shifted_antitone hρ0 hρ1 hξ0 hξ1 ht0 ht1).alternating_series_le_tendsto
    htend 0
  simpa using hbound

theorem lemma20P5T_le_Vbar {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    lemma20P5T ρ ξ t ≤ lemma20Vbar ρ ξ t := by
  have hmag : Summable (fun n => lemma20VMag ρ ξ t n) :=
    lemma20VMag_summable hρ0 hξ0 ht0
  have hterm : Summable (fun n => lemma20VTerm ρ ξ t n) := by
    unfold lemma20VTerm
    exact hmag.alternating
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n => lemma20VTerm ρ ξ t n) 6 hterm
  have htail_nonneg : 0 ≤ ∑' i : Nat, lemma20VTerm ρ ξ t (i + 6) := by
    unfold lemma20VTerm
    simpa [pow_add, show ((-1 : ℝ) ^ 6) = 1 by norm_num] using
      lemma20_shifted_tail_nonneg hρ0 hρ1 hξ0 hξ1 ht0 ht1
  unfold lemma20P5T lemma20Vbar
  linarith

set_option maxRecDepth 50000 in
theorem lemma20P5Den_mul_P5T_eq_num {ρ ξ t : ℝ}
    (h0 : 1 + ξ ≠ 0)
    (h1 : 1 + ξ * ρ ≠ 0)
    (h2 : 1 + ξ * ρ ^ 2 ≠ 0)
    (h3 : 1 + ξ * ρ ^ 3 ≠ 0)
    (h4 : 1 + ξ * ρ ^ 4 ≠ 0)
    (h5 : 1 + ξ * ρ ^ 5 ≠ 0)
    (h6 : 1 + ξ * ρ ^ 6 ≠ 0) :
    lemma20P5Den ρ ξ * lemma20P5T ρ ξ t = lemma20P5TNum ρ ξ t := by
  unfold lemma20P5Den lemma20P5T lemma20VTerm lemma20VMag lemma20P5TNum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  field_simp [h0, h1, h2, h3, h4, h5, h6]
  ring_nf

theorem lemma20P5Den_mul_P5_eq_num {ρ ξ : ℝ}
    (h0 : 1 + ξ ≠ 0)
    (h1 : 1 + ξ * ρ ≠ 0)
    (h2 : 1 + ξ * ρ ^ 2 ≠ 0)
    (h3 : 1 + ξ * ρ ^ 3 ≠ 0)
    (h4 : 1 + ξ * ρ ^ 4 ≠ 0)
    (h5 : 1 + ξ * ρ ^ 5 ≠ 0)
    (h6 : 1 + ξ * ρ ^ 6 ≠ 0) :
    lemma20P5Den ρ ξ * lemma20P5 ρ ξ = lemma20P5Num ρ ξ := by
  unfold lemma20P5Den lemma20P5 lemma20P5Num
  field_simp [h0, h1, h2, h3, h4, h5, h6]
  ring_nf

theorem lemma20P5Den_pos {ρ ξ : ℝ}
    (hρ : 0 ≤ ρ) (hξ : 0 ≤ ξ) :
    0 < lemma20P5Den ρ ξ := by
  unfold lemma20P5Den
  positivity

theorem lemma20P5_pos_of_num_pos {ρ ξ : ℝ}
    (hρ : 0 ≤ ρ) (hξ : 0 ≤ ξ)
    (hnum : 0 < lemma20P5Num ρ ξ) :
    0 < lemma20P5 ρ ξ := by
  have h0 : 1 + ξ ≠ 0 := by positivity
  have h1 : 1 + ξ * ρ ≠ 0 := by positivity
  have h2 : 1 + ξ * ρ ^ 2 ≠ 0 := by positivity
  have h3 : 1 + ξ * ρ ^ 3 ≠ 0 := by positivity
  have h4 : 1 + ξ * ρ ^ 4 ≠ 0 := by positivity
  have h5 : 1 + ξ * ρ ^ 5 ≠ 0 := by positivity
  have h6 : 1 + ξ * ρ ^ 6 ≠ 0 := by positivity
  have hden : 0 < lemma20P5Den ρ ξ := lemma20P5Den_pos hρ hξ
  have hprod : 0 < lemma20P5Den ρ ξ * lemma20P5 ρ ξ := by
    rw [lemma20P5Den_mul_P5_eq_num h0 h1 h2 h3 h4 h5 h6]
    exact hnum
  exact (mul_pos_iff_of_pos_left hden).mp hprod

theorem lemma20P5Coeff_pos {i j : Nat}
    (hi : i ≤ 20) (hj : j ≤ 5) :
    0 < lemma20P5Coeff i j := by
  have hfinite :
      ∀ i : Fin 21, ∀ j : Fin 6, (0 : SkiRental.Certificates.Q) < lemma20P5CoeffFin i j := by
    native_decide
  have hq : (0 : SkiRental.Certificates.Q) < lemma20P5CoeffQ i j := by
    simpa [lemma20P5CoeffFin] using
      hfinite ⟨i, Nat.lt_succ_iff.mpr hi⟩ ⟨j, Nat.lt_succ_iff.mpr hj⟩
  unfold lemma20P5Coeff
  exact_mod_cast hq

theorem lemma20P5Bernstein_pos {α β : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    0 < lemma20P5Bernstein α β := by
  unfold lemma20P5Bernstein
  apply SkiRental.Polynomial.bernsteinEval_pos
  · intro i hi
    apply SkiRental.Polynomial.bernsteinEval_pos
    · intro j hj
      exact lemma20P5Coeff_pos (i := i) (j := j) hi hj
    · exact hβ0
    · exact hβ1
  · exact hα0
  · exact hα1

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lemma20P5Num_shift_eq_bernstein (α β : ℝ) :
    lemma20P5Num (1 / 3 + (2 / 3) * α) β = lemma20P5Bernstein α β := by
  unfold lemma20P5Num lemma20P5Bernstein lemma20P5Coeff lemma20P5CoeffQ
    SkiRental.Polynomial.bernsteinEval SkiRental.Polynomial.bernsteinBasis
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [SkiRental.Certificates.lemma20P5BernsteinCoeffs,
    SkiRental.Certificates.q, List.getD, Nat.choose]
  ring_nf

theorem lemma20P5Num_pos_on_box {ρ ξ : ℝ}
    (hρ0 : (1 / 3 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) :
    0 < lemma20P5Num ρ ξ := by
  let α : ℝ := (ρ - 1 / 3) / (2 / 3)
  have hα0 : 0 ≤ α := by
    dsimp [α]
    apply div_nonneg
    · linarith
    · norm_num
  have hα1 : α ≤ 1 := by
    dsimp [α]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2 / 3)]
    nlinarith
  have hρ : ρ = 1 / 3 + (2 / 3) * α := by
    dsimp [α]
    ring
  rw [hρ, lemma20P5Num_shift_eq_bernstein]
  exact lemma20P5Bernstein_pos hα0 hα1 hξ0 hξ1

theorem lemma20P5_pos_on_box {ρ ξ : ℝ}
    (hρ0 : (1 / 3 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) :
    0 < lemma20P5 ρ ξ := by
  have hρ_nonneg : 0 ≤ ρ := by nlinarith
  exact lemma20P5_pos_of_num_pos hρ_nonneg hξ0
    (lemma20P5Num_pos_on_box hρ0 hρ1 hξ0 hξ1)

theorem lemma20P5T_pos_of_num_pos {ρ ξ t : ℝ}
    (hρ : 0 ≤ ρ) (hξ : 0 ≤ ξ)
    (hnum : 0 < lemma20P5TNum ρ ξ t) :
    0 < lemma20P5T ρ ξ t := by
  have h0 : 1 + ξ ≠ 0 := by positivity
  have h1 : 1 + ξ * ρ ≠ 0 := by positivity
  have h2 : 1 + ξ * ρ ^ 2 ≠ 0 := by positivity
  have h3 : 1 + ξ * ρ ^ 3 ≠ 0 := by positivity
  have h4 : 1 + ξ * ρ ^ 4 ≠ 0 := by positivity
  have h5 : 1 + ξ * ρ ^ 5 ≠ 0 := by positivity
  have h6 : 1 + ξ * ρ ^ 6 ≠ 0 := by positivity
  have hden : 0 < lemma20P5Den ρ ξ := lemma20P5Den_pos hρ hξ
  have hprod : 0 < lemma20P5Den ρ ξ * lemma20P5T ρ ξ t := by
    rw [lemma20P5Den_mul_P5T_eq_num h0 h1 h2 h3 h4 h5 h6]
    exact hnum
  exact (mul_pos_iff_of_pos_left hden).mp hprod

theorem lemma20P5TCoeff_pos {i j k : Nat}
    (hi : i ≤ 20) (hj : j ≤ 5) (hk : k ≤ 5) :
    0 < lemma20P5TCoeff i j k := by
  have hfinite :
      ∀ i : Fin 21, ∀ j : Fin 6, ∀ k : Fin 6,
        (0 : SkiRental.Certificates.Q) < lemma20P5TCoeffFin i j k := by
    native_decide
  have hq : (0 : SkiRental.Certificates.Q) < lemma20P5TCoeffQ i j k := by
    simpa [lemma20P5TCoeffFin] using
      hfinite ⟨i, Nat.lt_succ_iff.mpr hi⟩
        ⟨j, Nat.lt_succ_iff.mpr hj⟩
        ⟨k, Nat.lt_succ_iff.mpr hk⟩
  unfold lemma20P5TCoeff
  exact_mod_cast hq

theorem lemma20P5TBernstein_pos {α β τ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    0 < lemma20P5TBernstein α β τ := by
  unfold lemma20P5TBernstein
  apply SkiRental.Polynomial.bernsteinEval_pos
  · intro i hi
    apply SkiRental.Polynomial.bernsteinEval_pos
    · intro j hj
      apply SkiRental.Polynomial.bernsteinEval_pos
      · intro k hk
        exact lemma20P5TCoeff_pos (i := i) (j := j) (k := k) hi hj hk
      · exact hτ0
      · exact hτ1
    · exact hβ0
    · exact hβ1
  · exact hα0
  · exact hα1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lemma20P5TNum_shift_eq_bernstein (α β τ : ℝ) :
    lemma20P5TNum (1 / 3 + (2 / 3) * α) β τ = lemma20P5TBernstein α β τ := by
  unfold lemma20P5TNum lemma20P5TBernstein lemma20P5TCoeff lemma20P5TCoeffQ
    SkiRental.Polynomial.bernsteinEval SkiRental.Polynomial.bernsteinBasis
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [SkiRental.Certificates.lemma20P5TBernsteinCoeffs,
    SkiRental.Certificates.q, List.getD, Nat.choose]
  ring_nf

theorem lemma20P5TNum_pos_on_box {ρ ξ t : ℝ}
    (hρ0 : (1 / 3 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < lemma20P5TNum ρ ξ t := by
  let α : ℝ := (ρ - 1 / 3) / (2 / 3)
  have hα0 : 0 ≤ α := by
    dsimp [α]
    apply div_nonneg
    · linarith
    · norm_num
  have hα1 : α ≤ 1 := by
    dsimp [α]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2 / 3)]
    nlinarith
  have hρ : ρ = 1 / 3 + (2 / 3) * α := by
    dsimp [α]
    ring
  rw [hρ, lemma20P5TNum_shift_eq_bernstein]
  exact lemma20P5TBernstein_pos hα0 hα1 hξ0 hξ1 ht0 ht1

theorem lemma20P5T_pos_on_box {ρ ξ t : ℝ}
    (hρ0 : (1 / 3 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < lemma20P5T ρ ξ t := by
  have hρ_nonneg : 0 ≤ ρ := by nlinarith
  exact lemma20P5T_pos_of_num_pos hρ_nonneg hξ0
    (lemma20P5TNum_pos_on_box hρ0 hρ1 hξ0 hξ1 ht0 ht1)

theorem lemma20Vbar_pos_on_box {ρ ξ t : ℝ}
    (hρ0 : (1 / 3 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < lemma20Vbar ρ ξ t := by
  have hρ_nonneg : 0 ≤ ρ := by nlinarith
  exact lt_of_lt_of_le
    (lemma20P5T_pos_on_box hρ0 hρ1 hξ0 hξ1 ht0 ht1)
    (lemma20P5T_le_Vbar hρ_nonneg hρ1 hξ0 hξ1 ht0 ht1)

theorem lemma20V_nonneg_on_box {ρ ξ t : ℝ}
    (hρ0 : (1 / 3 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ lemma20V ρ ξ t := by
  unfold lemma20V
  exact mul_nonneg (by nlinarith) (le_of_lt <|
    lemma20Vbar_pos_on_box hρ0 hρ1 hξ0 hξ1 ht0 ht1)

theorem UpowerDerivBound_summable :
    Summable UpowerDerivBound := by
  apply (summable_nat_add_iff 1).mp
  simpa [UpowerDerivBound] using Real.summable_pow_div_factorial (2 : ℝ)

theorem hasDerivAt_UpowerTerm {ρ ξ : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ) (n : Nat) (y : ℝ) :
    HasDerivAt (fun z : ℝ => UpowerTerm ρ ξ n z)
      (UpowerDerivTerm ρ ξ n y) y := by
  cases n with
  | zero =>
      change
        HasDerivAt
          (fun z : ℝ => (-z) ^ 0
            / ((Nat.factorial 0 : ℝ) * (1 + ξ * ρ ^ 0)))
          0 y
      simpa using
        (hasDerivAt_const (x := y) (c := (1 + ξ)⁻¹))
  | succ n =>
      unfold UpowerTerm UpowerDerivTerm UpowerShiftTerm
      have hden : (Nat.factorial n : ℝ) * (1 + ξ * ρ ^ (n + 1)) ≠ 0 := by
        positivity
      have hpow : HasDerivAt (fun z : ℝ => (-z) ^ (n + 1))
          (-((-y) ^ n * (n + 1 : ℝ))) y := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          ((hasDerivAt_id' (x := y)).neg.fun_pow (n + 1))
      have hdiv := hpow.div_const
        ((Nat.factorial (n + 1) : ℝ) * (1 + ξ * ρ ^ (n + 1)))
      have hfac : ((Nat.factorial (n + 1) : Nat) : ℝ)
          = (n + 1 : ℝ) * (Nat.factorial n : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hn_pos : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
      have hderiv :
          -((-y) ^ n * (n + 1 : ℝ))
              / ((Nat.factorial (n + 1) : ℝ) * (1 + ξ * ρ ^ (n + 1)))
            = -((-y) ^ n / ((Nat.factorial n : ℝ) * (1 + ξ * ρ ^ (n + 1)))) := by
        rw [hfac]
        field_simp [hn_pos.ne', hden]
      simpa [hderiv] using hdiv

theorem UpowerDerivTerm_norm_le_bound {ρ ξ y : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 2) (n : Nat) :
    ‖UpowerDerivTerm ρ ξ n y‖ ≤ UpowerDerivBound n := by
  cases n with
  | zero =>
      simp [UpowerDerivTerm, UpowerDerivBound]
  | succ n =>
      unfold UpowerDerivTerm UpowerShiftTerm UpowerDerivBound
      have hyabs : ‖y‖ ≤ 2 := by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have hpow_le : ‖y‖ ^ n ≤ (2 : ℝ) ^ n :=
        pow_le_pow_left₀ (norm_nonneg y) hyabs n
      have hfac_pos : 0 < (Nat.factorial n : ℝ) := by
        exact_mod_cast Nat.factorial_pos n
      have hA_ge : 1 ≤ 1 + ξ * ρ ^ (n + 1) := by
        nlinarith [mul_nonneg hξ0 (pow_nonneg hρ0 (n + 1))]
      have hden_pos : 0 < (Nat.factorial n : ℝ) * (1 + ξ * ρ ^ (n + 1)) := by
        positivity
      have hden_ge : (Nat.factorial n : ℝ)
          ≤ (Nat.factorial n : ℝ) * (1 + ξ * ρ ^ (n + 1)) := by
        nlinarith [mul_le_mul_of_nonneg_left hA_ge (le_of_lt hfac_pos)]
      calc
        ‖-((-y) ^ n / ((Nat.factorial n : ℝ) * (1 + ξ * ρ ^ (n + 1))))‖
            = ‖y‖ ^ n / ((Nat.factorial n : ℝ) * (1 + ξ * ρ ^ (n + 1))) := by
              rw [norm_neg, norm_div, norm_pow, norm_neg,
                Real.norm_of_nonneg (le_of_lt hden_pos)]
        _ ≤ (2 : ℝ) ^ n / ((Nat.factorial n : ℝ) * (1 + ξ * ρ ^ (n + 1))) := by
              exact div_le_div_of_nonneg_right hpow_le (le_of_lt hden_pos)
        _ ≤ (2 : ℝ) ^ n / (Nat.factorial n : ℝ) := by
              exact div_le_div_of_nonneg_left (pow_nonneg (by norm_num) n)
                hfac_pos hden_ge

theorem UpowerTerm_zero_summable (ρ ξ : ℝ) :
    Summable fun n => UpowerTerm ρ ξ n 0 := by
  apply (summable_nat_add_iff 1).mp
  simp [UpowerTerm]

theorem hasDerivAt_Upower {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    HasDerivAt (fun z : ℝ => Upower ρ ξ z)
      (UpowerDerivSeries ρ ξ t) t := by
  have htmem : t ∈ Set.Ioo (-1 : ℝ) 2 := by
    constructor <;> linarith
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 2 := by
    constructor <;> norm_num
  simpa [Upower, UpowerTerm, UpowerDerivSeries] using
    hasDerivAt_tsum_of_isPreconnected
      (α := Nat) (𝕜 := ℝ) (F := ℝ)
      (u := UpowerDerivBound)
      (g := UpowerTerm ρ ξ)
      (g' := UpowerDerivTerm ρ ξ)
      (t := Set.Ioo (-1 : ℝ) 2) (y₀ := 0)
      UpowerDerivBound_summable
      isOpen_Ioo isPreconnected_Ioo
      (fun n y _ => hasDerivAt_UpowerTerm hρ0 hξ0 n y)
      (fun n y hy => UpowerDerivTerm_norm_le_bound hρ0 hξ0 hy n)
      h0mem
      (UpowerTerm_zero_summable ρ ξ)
      htmem

theorem UpowerTerm_summable {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ) :
    Summable fun n => UpowerTerm ρ ξ n t := by
  refine (Real.summable_pow_div_factorial ‖t‖).of_norm_bounded ?_
  intro n
  unfold UpowerTerm
  have hfac_pos : 0 < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hA_ge : 1 ≤ 1 + ξ * ρ ^ n := by
    nlinarith [mul_nonneg hξ0 (pow_nonneg hρ0 n)]
  have hden_pos : 0 < (Nat.factorial n : ℝ) * (1 + ξ * ρ ^ n) := by
    positivity
  have hden_ge : (Nat.factorial n : ℝ)
      ≤ (Nat.factorial n : ℝ) * (1 + ξ * ρ ^ n) := by
    nlinarith [mul_le_mul_of_nonneg_left hA_ge (le_of_lt hfac_pos)]
  calc
    ‖(-t) ^ n / ((Nat.factorial n : ℝ) * (1 + ξ * ρ ^ n))‖
        = ‖t‖ ^ n / ((Nat.factorial n : ℝ) * (1 + ξ * ρ ^ n)) := by
          rw [norm_div, norm_pow, norm_neg, Real.norm_of_nonneg (le_of_lt hden_pos)]
    _ ≤ ‖t‖ ^ n / (Nat.factorial n : ℝ) := by
          exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg t) n)
            hfac_pos hden_ge

theorem UpowerShiftTerm_summable {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ) :
    Summable fun n => UpowerShiftTerm ρ ξ n t := by
  refine (Real.summable_pow_div_factorial ‖t‖).of_norm_bounded ?_
  intro n
  unfold UpowerShiftTerm
  have hfac_pos : 0 < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hA_ge : 1 ≤ 1 + ξ * ρ ^ (n + 1) := by
    nlinarith [mul_nonneg hξ0 (pow_nonneg hρ0 (n + 1))]
  have hden_pos : 0 < (Nat.factorial n : ℝ) * (1 + ξ * ρ ^ (n + 1)) := by
    positivity
  have hden_ge : (Nat.factorial n : ℝ)
      ≤ (Nat.factorial n : ℝ) * (1 + ξ * ρ ^ (n + 1)) := by
    nlinarith [mul_le_mul_of_nonneg_left hA_ge (le_of_lt hfac_pos)]
  calc
    ‖(-t) ^ n / ((Nat.factorial n : ℝ) * (1 + ξ * ρ ^ (n + 1)))‖
        = ‖t‖ ^ n / ((Nat.factorial n : ℝ) * (1 + ξ * ρ ^ (n + 1))) := by
          rw [norm_div, norm_pow, norm_neg, Real.norm_of_nonneg (le_of_lt hden_pos)]
    _ ≤ ‖t‖ ^ n / (Nat.factorial n : ℝ) := by
          exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg t) n)
            hfac_pos hden_ge

theorem UpowerDerivSeries_eq_neg_shifted {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ) :
    UpowerDerivSeries ρ ξ t
      = -∑' n : Nat, UpowerShiftTerm ρ ξ n t := by
  have hshift : Summable fun n => UpowerShiftTerm ρ ξ n t :=
    UpowerShiftTerm_summable hρ0 hξ0
  have hderiv : Summable fun n => UpowerDerivTerm ρ ξ n t := by
    apply (summable_nat_add_iff 1).mp
    simpa [UpowerDerivTerm, UpowerShiftTerm] using hshift.neg
  unfold UpowerDerivSeries
  rw [hderiv.tsum_eq_zero_add]
  simp [UpowerDerivTerm, UpowerShiftTerm, tsum_neg]

theorem Upower_term_sub_rho_shift_eq {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ) (n : Nat) :
    UpowerTerm ρ ξ n t - ρ * UpowerShiftTerm ρ ξ n t
      = (1 - ρ) * lemma20VTerm ρ ξ t n := by
  unfold UpowerTerm UpowerShiftTerm lemma20VTerm lemma20VMag
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hA : 1 + ξ * ρ ^ n ≠ 0 := by positivity
  have hB : 1 + ξ * ρ ^ (n + 1) ≠ 0 := by positivity
  rw [← neg_one_mul t, mul_pow]
  field_simp [hfac, hA, hB]
  ring

theorem Upower_add_rho_UpowerDerivSeries_eq_lemma20V {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ) (ht0 : 0 ≤ t) :
    Upower ρ ξ t + ρ * UpowerDerivSeries ρ ξ t = lemma20V ρ ξ t := by
  have hterm : Summable fun n => UpowerTerm ρ ξ n t :=
    UpowerTerm_summable hρ0 hξ0
  have hshift : Summable fun n => UpowerShiftTerm ρ ξ n t :=
    UpowerShiftTerm_summable hρ0 hξ0
  have hvterm : Summable fun n => lemma20VTerm ρ ξ t n := by
    unfold lemma20VTerm
    exact (lemma20VMag_summable hρ0 hξ0 ht0).alternating
  calc
    Upower ρ ξ t + ρ * UpowerDerivSeries ρ ξ t
        = (∑' n : Nat, UpowerTerm ρ ξ n t)
            - ρ * (∑' n : Nat, UpowerShiftTerm ρ ξ n t) := by
          rw [UpowerDerivSeries_eq_neg_shifted hρ0 hξ0]
          unfold Upower
          simp [UpowerTerm]
          ring
    _ = ∑' n : Nat, (UpowerTerm ρ ξ n t - ρ * UpowerShiftTerm ρ ξ n t) := by
          rw [← hshift.tsum_mul_left ρ]
          rw [← hterm.tsum_sub (hshift.mul_left ρ)]
    _ = ∑' n : Nat, (1 - ρ) * lemma20VTerm ρ ξ t n := by
          exact tsum_congr (fun n => Upower_term_sub_rho_shift_eq hρ0 hξ0 n)
    _ = lemma20V ρ ξ t := by
          rw [hvterm.tsum_mul_left (1 - ρ)]
          rfl

theorem deriv_Upower_eq_UpowerDerivSeries {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    deriv (fun z => Upower ρ ξ z) t = UpowerDerivSeries ρ ξ t :=
  (hasDerivAt_Upower hρ0 hξ0 ht0 ht1).deriv

theorem lemma20VFromUpower_eq_lemma20V {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    lemma20VFromUpower ρ ξ t = lemma20V ρ ξ t := by
  unfold lemma20VFromUpower
  rw [deriv_Upower_eq_UpowerDerivSeries hρ0 hξ0 ht0 ht1]
  exact Upower_add_rho_UpowerDerivSeries_eq_lemma20V hρ0 hξ0 ht0

theorem lemma20VFromUpower_nonneg_on_box {ρ ξ t : ℝ}
    (hρ0 : (1 / 3 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ lemma20VFromUpower ρ ξ t := by
  rw [lemma20VFromUpower_eq_lemma20V (by nlinarith) hξ0 ht0 ht1]
  exact lemma20V_nonneg_on_box hρ0 hρ1 hξ0 hξ1 ht0 ht1

noncomputable abbrev generalVPositiveExpression (ρ ξ t : ℝ) : ℝ :=
  lemma20VFromUpower ρ ξ t

noncomputable abbrev generalVPositiveRawSeries (ρ ξ t : ℝ) : ℝ :=
  lemma20Vbar ρ ξ t

noncomputable abbrev generalVPositiveSeries (ρ ξ t : ℝ) : ℝ :=
  lemma20V ρ ξ t

noncomputable abbrev generalVPositiveSixTerm (ρ ξ t : ℝ) : ℝ :=
  lemma20P5T ρ ξ t

theorem generalVPositiveExpression_eq_series {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    generalVPositiveExpression ρ ξ t = generalVPositiveSeries ρ ξ t :=
  lemma20VFromUpower_eq_lemma20V hρ0 hξ0 ht0 ht1

theorem generalVPositiveSixTerm_pos_on_box {ρ ξ t : ℝ}
    (hρ0 : (1 / 3 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < generalVPositiveSixTerm ρ ξ t :=
  lemma20P5T_pos_on_box hρ0 hρ1 hξ0 hξ1 ht0 ht1

theorem generalVPositiveSixTerm_le_rawSeries {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    generalVPositiveSixTerm ρ ξ t ≤ generalVPositiveRawSeries ρ ξ t :=
  lemma20P5T_le_Vbar hρ0 hρ1 hξ0 hξ1 ht0 ht1

theorem generalVPositiveSeries_nonneg_on_box {ρ ξ t : ℝ}
    (hρ0 : (1 / 3 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ generalVPositiveSeries ρ ξ t :=
  lemma20V_nonneg_on_box hρ0 hρ1 hξ0 hξ1 ht0 ht1

theorem generalVPositive_nonneg_on_box {ρ ξ t : ℝ}
    (hρ0 : (1 / 3 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ generalVPositiveExpression ρ ξ t :=
  lemma20VFromUpower_nonneg_on_box hρ0 hρ1 hξ0 hξ1 ht0 ht1

def U3CubicLower (ρ ξ t : ℝ) : ℝ :=
  1 / (1 + ξ)
  - t / (1 + ξ * ρ)
  + t ^ 2 / (2 * (1 + ξ * ρ ^ 2))
  - t ^ 3 / (6 * (1 + ξ * ρ ^ 3))

def lemma19P3Den (ρ ξ : ℝ) : ℝ :=
  6 * (1 + ξ) * (1 + ξ * ρ) * (1 + ξ * ρ ^ 2) * (1 + ξ * ρ ^ 3)

def lemma19P3Num (ρ ξ t : ℝ) : ℝ :=
  6 * (1 + ξ * ρ) * (1 + ξ * ρ ^ 2) * (1 + ξ * ρ ^ 3)
  - 6 * t * (1 + ξ) * (1 + ξ * ρ ^ 2) * (1 + ξ * ρ ^ 3)
  + 3 * t ^ 2 * (1 + ξ) * (1 + ξ * ρ) * (1 + ξ * ρ ^ 3)
  - t ^ 3 * (1 + ξ) * (1 + ξ * ρ) * (1 + ξ * ρ ^ 2)

def lemma19P3CoeffQ (i j k : Nat) : SkiRental.Certificates.Q :=
  ((((SkiRental.Certificates.lemma19P3BernsteinCoeffs.getD i []).getD j []).getD k 0 :
    SkiRental.Certificates.Q))

def lemma19P3Coeff (i j k : Nat) : ℝ :=
  (lemma19P3CoeffQ i j k : ℝ)

def lemma19P3CoeffFin
    (i : Fin 7) (j : Fin 4) (k : Fin 4) : SkiRental.Certificates.Q :=
  lemma19P3CoeffQ i j k

def lemma19P3Bernstein (α β τ : ℝ) : ℝ :=
  SkiRental.Polynomial.bernsteinEval 6
    (fun i => SkiRental.Polynomial.bernsteinEval 3
      (fun j => SkiRental.Polynomial.bernsteinEval 3
        (fun k => lemma19P3Coeff i j k) τ) β)
    α

theorem lemma19P3Den_mul_U3CubicLower_eq_num {ρ ξ t : ℝ}
    (h0 : 1 + ξ ≠ 0)
    (h1 : 1 + ξ * ρ ≠ 0)
    (h2 : 1 + ξ * ρ ^ 2 ≠ 0)
    (h3 : 1 + ξ * ρ ^ 3 ≠ 0) :
    lemma19P3Den ρ ξ * U3CubicLower ρ ξ t = lemma19P3Num ρ ξ t := by
  unfold lemma19P3Den U3CubicLower lemma19P3Num
  field_simp [h0, h1, h2, h3]
  ring_nf

theorem lemma19P3Den_pos {ρ ξ : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ) :
    0 < lemma19P3Den ρ ξ := by
  unfold lemma19P3Den
  positivity

theorem lemma19P3_pos_of_num_pos {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ)
    (hnum : 0 < lemma19P3Num ρ ξ t) :
    0 < U3CubicLower ρ ξ t := by
  have h0 : 1 + ξ ≠ 0 := by positivity
  have h1 : 1 + ξ * ρ ≠ 0 := by positivity
  have h2 : 1 + ξ * ρ ^ 2 ≠ 0 := by positivity
  have h3 : 1 + ξ * ρ ^ 3 ≠ 0 := by positivity
  have hden : 0 < lemma19P3Den ρ ξ := lemma19P3Den_pos hρ0 hξ0
  have hprod : 0 < lemma19P3Den ρ ξ * U3CubicLower ρ ξ t := by
    rw [lemma19P3Den_mul_U3CubicLower_eq_num h0 h1 h2 h3]
    exact hnum
  exact (mul_pos_iff_of_pos_left hden).mp hprod

theorem lemma19P3Coeff_pos {i j k : Nat}
    (hi : i ≤ 6) (hj : j ≤ 3) (hk : k ≤ 3) :
    0 < lemma19P3Coeff i j k := by
  have hfinite :
      ∀ i : Fin 7, ∀ j : Fin 4, ∀ k : Fin 4,
        (0 : SkiRental.Certificates.Q) < lemma19P3CoeffFin i j k := by
    native_decide
  have hq : (0 : SkiRental.Certificates.Q) < lemma19P3CoeffQ i j k := by
    simpa [lemma19P3CoeffFin] using
      hfinite ⟨i, Nat.lt_succ_iff.mpr hi⟩
        ⟨j, Nat.lt_succ_iff.mpr hj⟩
        ⟨k, Nat.lt_succ_iff.mpr hk⟩
  unfold lemma19P3Coeff
  exact_mod_cast hq

theorem lemma19P3Bernstein_pos {α β τ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    0 < lemma19P3Bernstein α β τ := by
  unfold lemma19P3Bernstein
  apply SkiRental.Polynomial.bernsteinEval_pos
  · intro i hi
    apply SkiRental.Polynomial.bernsteinEval_pos
    · intro j hj
      apply SkiRental.Polynomial.bernsteinEval_pos
      · intro k hk
        exact lemma19P3Coeff_pos (i := i) (j := j) (k := k) hi hj hk
      · exact hτ0
      · exact hτ1
    · exact hβ0
    · exact hβ1
  · exact hα0
  · exact hα1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lemma19P3Num_shift_eq_bernstein (α β τ : ℝ) :
    lemma19P3Num (31 / 100 + (69 / 100) * α) β τ
      = lemma19P3Bernstein α β τ := by
  unfold lemma19P3Num lemma19P3Bernstein lemma19P3Coeff lemma19P3CoeffQ
    SkiRental.Polynomial.bernsteinEval SkiRental.Polynomial.bernsteinBasis
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [SkiRental.Certificates.lemma19P3BernsteinCoeffs,
    SkiRental.Certificates.q, List.getD, Nat.choose]
  ring_nf

theorem lemma19P3Num_pos_on_box {ρ ξ t : ℝ}
    (hρ0 : (31 / 100 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < lemma19P3Num ρ ξ t := by
  let α : ℝ := (ρ - 31 / 100) / (69 / 100)
  have hα0 : 0 ≤ α := by
    dsimp [α]
    apply div_nonneg
    · linarith
    · norm_num
  have hα1 : α ≤ 1 := by
    dsimp [α]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 69 / 100)]
    nlinarith
  have hρ : ρ = 31 / 100 + (69 / 100) * α := by
    dsimp [α]
    ring
  rw [hρ, lemma19P3Num_shift_eq_bernstein]
  exact lemma19P3Bernstein_pos hα0 hα1 hξ0 hξ1 ht0 ht1

theorem U3CubicLower_pos_on_box {ρ ξ t : ℝ}
    (hρ0 : (31 / 100 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < U3CubicLower ρ ξ t := by
  have hρ_nonneg : 0 ≤ ρ := by nlinarith
  exact lemma19P3_pos_of_num_pos hρ_nonneg hξ0
    (lemma19P3Num_pos_on_box hρ0 hρ1 hξ0 hξ1 ht0 ht1)

def UpowerMag (ρ ξ t : ℝ) (n : Nat) : ℝ :=
  t ^ n / ((Nat.factorial n : ℝ) * (1 + ξ * ρ ^ n))

theorem UpowerTerm_eq_altMag (ρ ξ t : ℝ) (n : Nat) :
    UpowerTerm ρ ξ n t = (-1 : ℝ) ^ n * UpowerMag ρ ξ t n := by
  unfold UpowerTerm UpowerMag
  rw [← neg_one_mul t, mul_pow]
  ring

theorem UpowerMag_nonneg {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ) (ht0 : 0 ≤ t)
    (n : Nat) :
    0 ≤ UpowerMag ρ ξ t n := by
  unfold UpowerMag
  positivity

theorem UpowerMag_succ_le {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {n : Nat} (hn : 3 ≤ n) :
    UpowerMag ρ ξ t (n + 1) ≤ UpowerMag ρ ξ t n := by
  have hρn_nonneg : 0 ≤ ρ ^ n := pow_nonneg hρ0 n
  have hρn1_nonneg : 0 ≤ ρ ^ (n + 1) := pow_nonneg hρ0 (n + 1)
  have hρn_le_one : ρ ^ n ≤ 1 := pow_le_one₀ hρ0 hρ1
  have hξρn_le_one : ξ * ρ ^ n ≤ 1 := by
    nlinarith [mul_le_mul hξ1 hρn_le_one hρn_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  have hnum_le_two : 1 + ξ * ρ ^ n ≤ 2 := by nlinarith
  have hden_pos : 0 < 1 + ξ * ρ ^ (n + 1) := by positivity
  have hratio_factor : (1 + ξ * ρ ^ n) / (1 + ξ * ρ ^ (n + 1)) ≤ 2 := by
    rw [div_le_iff₀ hden_pos]
    nlinarith [mul_nonneg hξ0 hρn1_nonneg]
  have hn_pos : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
  have hn_ge_four : (4 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ hn
  have htwo_over : (2 : ℝ) / (n + 1) ≤ 1 := by
    rw [div_le_iff₀ hn_pos]
    nlinarith
  have hratio_le_one :
      t / (n + 1) * ((1 + ξ * ρ ^ n) / (1 + ξ * ρ ^ (n + 1))) ≤ 1 := by
    calc
      t / (n + 1) * ((1 + ξ * ρ ^ n) / (1 + ξ * ρ ^ (n + 1)))
          ≤ (1 / (n + 1)) * 2 := by
            gcongr
      _ = 2 / (n + 1) := by ring
      _ ≤ 1 := htwo_over
  have hcur_nonneg : 0 ≤ UpowerMag ρ ξ t n := UpowerMag_nonneg hρ0 hξ0 ht0 n
  have hratio_eq :
      UpowerMag ρ ξ t (n + 1)
        = (t / (n + 1) * ((1 + ξ * ρ ^ n) / (1 + ξ * ρ ^ (n + 1))))
            * UpowerMag ρ ξ t n := by
    unfold UpowerMag
    have hfac : ((Nat.factorial n.succ : Nat) : ℝ)
        = (n + 1 : ℝ) * (Nat.factorial n : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [hfac]
    field_simp [hn_pos.ne', hden_pos.ne']
    ring_nf
  rw [hratio_eq]
  exact mul_le_of_le_one_left hcur_nonneg hratio_le_one

theorem UpowerMag_shifted_antitone4 {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Antitone (fun k => UpowerMag ρ ξ t (k + 4)) := by
  apply antitone_nat_of_succ_le
  intro k
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    UpowerMag_succ_le (ρ := ρ) (ξ := ξ) (t := t)
      hρ0 hρ1 hξ0 hξ1 ht0 ht1 (n := k + 4) (by omega)

theorem UpowerMag_le_expTerm {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ) (ht0 : 0 ≤ t)
    (n : Nat) :
    UpowerMag ρ ξ t n ≤ t ^ n / (Nat.factorial n : ℝ) := by
  unfold UpowerMag
  have hnum : 0 ≤ t ^ n := pow_nonneg ht0 n
  have hfac_pos : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hA_ge : 1 ≤ 1 + ξ * ρ ^ n := by
    nlinarith [mul_nonneg hξ0 (pow_nonneg hρ0 n)]
  have hden_ge : (Nat.factorial n : ℝ)
      ≤ (Nat.factorial n : ℝ) * (1 + ξ * ρ ^ n) := by
    nlinarith [mul_le_mul_of_nonneg_left hA_ge (le_of_lt hfac_pos)]
  exact div_le_div_of_nonneg_left hnum hfac_pos hden_ge

theorem UpowerMag_summable {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ) (ht0 : 0 ≤ t) :
    Summable (fun n => UpowerMag ρ ξ t n) := by
  exact Summable.of_nonneg_of_le
    (fun n => UpowerMag_nonneg hρ0 hξ0 ht0 n)
    (fun n => UpowerMag_le_expTerm hρ0 hξ0 ht0 n)
    (Real.summable_pow_div_factorial t)

theorem Upower_shifted_tail4_nonneg {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ ∑' k : Nat, (-1 : ℝ) ^ k * UpowerMag ρ ξ t (k + 4) := by
  have hshift : Summable (fun k => UpowerMag ρ ξ t (k + 4)) := by
    exact (summable_nat_add_iff 4).mpr (UpowerMag_summable hρ0 hξ0 ht0)
  have htend := hshift.tendsto_alternating_series_tsum
  have hbound := (UpowerMag_shifted_antitone4 hρ0 hρ1 hξ0 hξ1 ht0 ht1).alternating_series_le_tendsto
    htend 0
  simpa using hbound

theorem U3CubicLower_eq_Upower_partial (ρ ξ t : ℝ) :
    U3CubicLower ρ ξ t = (Finset.range 4).sum (fun n => UpowerTerm ρ ξ n t) := by
  unfold U3CubicLower UpowerTerm
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

theorem U3CubicLower_le_Upower {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    U3CubicLower ρ ξ t ≤ Upower ρ ξ t := by
  have hterm : Summable fun n => UpowerTerm ρ ξ n t :=
    UpowerTerm_summable hρ0 hξ0
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n => UpowerTerm ρ ξ n t) 4 hterm
  have htail_nonneg : 0 ≤ ∑' i : Nat, UpowerTerm ρ ξ (i + 4) t := by
    have htail_eq :
        (∑' i : Nat, UpowerTerm ρ ξ (i + 4) t)
          = ∑' i : Nat, (-1 : ℝ) ^ i * UpowerMag ρ ξ t (i + 4) := by
      apply tsum_congr
      intro i
      rw [UpowerTerm_eq_altMag]
      have hpow : (-1 : ℝ) ^ (i + 4) = (-1 : ℝ) ^ i := by
        rw [pow_add]
        norm_num
      rw [hpow]
    rw [htail_eq]
    exact Upower_shifted_tail4_nonneg hρ0 hρ1 hξ0 hξ1 ht0 ht1
  change U3CubicLower ρ ξ t ≤ ∑' n : Nat, UpowerTerm ρ ξ n t
  have hpartial := U3CubicLower_eq_Upower_partial ρ ξ t
  linarith

theorem Upower_nonneg_on_lemma19_box {ρ ξ t : ℝ}
    (hρ0 : (31 / 100 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ Upower ρ ξ t := by
  have hρ_nonneg : 0 ≤ ρ := by nlinarith
  exact le_trans (le_of_lt <| U3CubicLower_pos_on_box hρ0 hρ1 hξ0 hξ1 ht0 ht1)
    (U3CubicLower_le_Upower hρ_nonneg hρ1 hξ0 hξ1 ht0 ht1)

theorem scalarCertificateTightU_nonneg_on_box {ρ ξ t : ℝ}
    (hρ0 : (31 / 100 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ U ρ ξ t := by
  simpa [U] using
    Upower_nonneg_on_lemma19_box hρ0 hρ1 hξ0 hξ1 ht0 ht1

theorem scalarCertificateTightU_eq_power_series (ρ ξ t : ℝ) :
    U ρ ξ t = ∑' n : Nat,
      (-t) ^ n / ((Nat.factorial n : ℝ) * (1 + ξ * ρ ^ n)) := by
  rfl

theorem Upower_functional_term_identity {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ) (n : Nat) :
    UpowerTerm ρ ξ n t + ξ * UpowerTerm ρ ξ n (ρ * t)
      = (-t) ^ n / (Nat.factorial n : ℝ) := by
  unfold UpowerTerm
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hden : 1 + ξ * ρ ^ n ≠ 0 := by positivity
  have hpow : (-(ρ * t)) ^ n = ρ ^ n * (-t) ^ n := by
    rw [show -(ρ * t) = ρ * (-t) by ring, mul_pow]
  rw [hpow]
  field_simp [hfac, hden]

theorem real_exp_eq_tsum_pow_div_factorial (t : ℝ) :
    (∑' n : Nat, (-t) ^ n / (Nat.factorial n : ℝ)) = Real.exp (-t) := by
  have h := congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) (-t)
  rw [← Real.exp_eq_exp_ℝ] at h
  exact h.symm

theorem scalarCertificateTightU_functional_identity {ρ ξ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ) :
    U ρ ξ t + ξ * U ρ ξ (ρ * t) = Real.exp (-t) := by
  have hterm : Summable fun n => UpowerTerm ρ ξ n t :=
    UpowerTerm_summable hρ0 hξ0
  have hterm_scaled : Summable fun n => ξ * UpowerTerm ρ ξ n (ρ * t) :=
    (UpowerTerm_summable hρ0 hξ0).mul_left ξ
  calc
    U ρ ξ t + ξ * U ρ ξ (ρ * t)
        = (∑' n : Nat, UpowerTerm ρ ξ n t)
            + ξ * (∑' n : Nat, UpowerTerm ρ ξ n (ρ * t)) := by
          rfl
    _ = (∑' n : Nat, UpowerTerm ρ ξ n t)
            + (∑' n : Nat, ξ * UpowerTerm ρ ξ n (ρ * t)) := by
          rw [Summable.tsum_mul_left ξ (UpowerTerm_summable hρ0 hξ0)]
    _ = ∑' n : Nat, (UpowerTerm ρ ξ n t + ξ * UpowerTerm ρ ξ n (ρ * t)) := by
          rw [← hterm.tsum_add hterm_scaled]
    _ = ∑' n : Nat, (-t) ^ n / (Nat.factorial n : ℝ) := by
          exact tsum_congr (fun n => Upower_functional_term_identity hρ0 hξ0 n)
    _ = Real.exp (-t) := real_exp_eq_tsum_pow_div_factorial t

noncomputable def scalarCertificateTightOrbitWeight (ρ x : ℝ) (k : Nat) : ℝ :=
  ρ ^ k * Real.exp (-(ρ ^ k * x))

noncomputable def scalarCertificateTightMultiplier
    (ρ γ x : ℝ) (k : Nat) : ℝ :=
  ρ ^ k / γ * U ρ (ρ / γ) (ρ ^ k * x)

theorem scalarCertificateTightMultiplier_recurrence {ρ γ x : ℝ}
    (hρ0 : 0 ≤ ρ) (hγ : 0 < γ) (k : Nat) :
    γ * scalarCertificateTightMultiplier ρ γ x k
      + scalarCertificateTightMultiplier ρ γ x (k + 1)
      = scalarCertificateTightOrbitWeight ρ x k := by
  have hξ0 : 0 ≤ ρ / γ := div_nonneg hρ0 (le_of_lt hγ)
  have hγne : γ ≠ 0 := ne_of_gt hγ
  have ht :
      ρ ^ (k + 1) * x = ρ * (ρ ^ k * x) := by
    rw [show k + 1 = Nat.succ k by omega, pow_succ]
    ring
  have hpow_factor : ρ ^ (k + 1) = ρ * ρ ^ k := by
    rw [show k + 1 = Nat.succ k by omega, pow_succ]
    ring
  have hfunc := scalarCertificateTightU_functional_identity
    (ρ := ρ) (ξ := ρ / γ) (t := ρ ^ k * x) hρ0 hξ0
  unfold scalarCertificateTightMultiplier scalarCertificateTightOrbitWeight
  rw [ht]
  calc
    γ * (ρ ^ k / γ * U ρ (ρ / γ) (ρ ^ k * x))
        + ρ ^ (k + 1) / γ * U ρ (ρ / γ) (ρ * (ρ ^ k * x))
        =
        ρ ^ k *
          (U ρ (ρ / γ) (ρ ^ k * x)
            + (ρ / γ) * U ρ (ρ / γ) (ρ * (ρ ^ k * x))) := by
          rw [hpow_factor]
          field_simp [hγne]
    _ = ρ ^ k * Real.exp (-(ρ ^ k * x)) := by
          rw [hfunc]

theorem scalarCertificateTightMultiplier_nonneg_on_box {ρ γ x : ℝ}
    (hρ0 : (31 / 100 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hγ : 0 < γ) (hξ1 : ρ / γ ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : Nat) :
    0 ≤ scalarCertificateTightMultiplier ρ γ x k := by
  unfold scalarCertificateTightMultiplier
  have hρ_nonneg : 0 ≤ ρ := by nlinarith
  have hξ0 : 0 ≤ ρ / γ := div_nonneg hρ_nonneg (le_of_lt hγ)
  have hpow_nonneg : 0 ≤ ρ ^ k := pow_nonneg hρ_nonneg k
  have hpow_le_one : ρ ^ k ≤ 1 := pow_le_one₀ hρ_nonneg hρ1
  have ht0 : 0 ≤ ρ ^ k * x := mul_nonneg hpow_nonneg hx0
  have ht1 : ρ ^ k * x ≤ 1 := by
    have hprod : ρ ^ k * x ≤ 1 * 1 :=
      mul_le_mul hpow_le_one hx1 hx0 (by norm_num)
    nlinarith
  have hfactor : 0 ≤ ρ ^ k / γ := div_nonneg hpow_nonneg (le_of_lt hγ)
  have hU : 0 ≤ U ρ (ρ / γ) (ρ ^ k * x) :=
    scalarCertificateTightU_nonneg_on_box hρ0 hρ1 hξ0 hξ1 ht0 ht1
  exact mul_nonneg hfactor hU

def lemma19DxiFinite (ρ ξ : ℝ) : ℝ :=
  (1 - ρ) / (1 + ξ) ^ 2
  - (1 - ρ ^ 2) / (2 * (1 + ξ * ρ) ^ 2)
  + (1 - ρ ^ 3) / (6 * (1 + ξ * ρ ^ 2) ^ 2)
  - (1 - ρ ^ 4) / (24 * (1 + ξ * ρ ^ 3) ^ 2)

def lemma19DxiFiniteDen (ρ ξ : ℝ) : ℝ :=
  24 * (1 + ξ) ^ 2 * (1 + ξ * ρ) ^ 2
    * (1 + ξ * ρ ^ 2) ^ 2 * (1 + ξ * ρ ^ 3) ^ 2

def lemma19DxiFiniteNum (ρ ξ : ℝ) : ℝ :=
  24 * (1 - ρ) * (1 + ξ * ρ) ^ 2
      * (1 + ξ * ρ ^ 2) ^ 2 * (1 + ξ * ρ ^ 3) ^ 2
  - 12 * (1 - ρ ^ 2) * (1 + ξ) ^ 2
      * (1 + ξ * ρ ^ 2) ^ 2 * (1 + ξ * ρ ^ 3) ^ 2
  + 4 * (1 - ρ ^ 3) * (1 + ξ) ^ 2
      * (1 + ξ * ρ) ^ 2 * (1 + ξ * ρ ^ 3) ^ 2
  - (1 - ρ ^ 4) * (1 + ξ) ^ 2
      * (1 + ξ * ρ) ^ 2 * (1 + ξ * ρ ^ 2) ^ 2

def lemma19DxiFiniteCoeffQ (i j : Nat) : SkiRental.Certificates.Q :=
  (((SkiRental.Certificates.lemma19DxiFiniteBernsteinCoeffs.getD i []).getD j 0 :
    SkiRental.Certificates.Q))

def lemma19DxiFiniteCoeff (i j : Nat) : ℝ :=
  (lemma19DxiFiniteCoeffQ i j : ℝ)

def lemma19DxiFiniteCoeffFin
    (i : Fin 14) (j : Fin 7) : SkiRental.Certificates.Q :=
  lemma19DxiFiniteCoeffQ i j

def lemma19DxiFiniteBernstein (α β : ℝ) : ℝ :=
  SkiRental.Polynomial.bernsteinEval 13
    (fun i => SkiRental.Polynomial.bernsteinEval 6
      (fun j => lemma19DxiFiniteCoeff i j) β)
    α

theorem lemma19DxiFiniteDen_mul_eq_num {ρ ξ : ℝ}
    (h0 : 1 + ξ ≠ 0)
    (h1 : 1 + ξ * ρ ≠ 0)
    (h2 : 1 + ξ * ρ ^ 2 ≠ 0)
    (h3 : 1 + ξ * ρ ^ 3 ≠ 0) :
    lemma19DxiFiniteDen ρ ξ * lemma19DxiFinite ρ ξ
      = lemma19DxiFiniteNum ρ ξ := by
  unfold lemma19DxiFiniteDen lemma19DxiFinite lemma19DxiFiniteNum
  field_simp [h0, h1, h2, h3]
  ring_nf

theorem lemma19DxiFiniteDen_pos {ρ ξ : ℝ}
    (hρ0 : 0 ≤ ρ) (hξ0 : 0 ≤ ξ) :
    0 < lemma19DxiFiniteDen ρ ξ := by
  unfold lemma19DxiFiniteDen
  positivity

theorem lemma19DxiFiniteCoeff_nonneg {i j : Nat}
    (hi : i ≤ 13) (hj : j ≤ 6) :
    0 ≤ lemma19DxiFiniteCoeff i j := by
  have hfinite :
      ∀ i : Fin 14, ∀ j : Fin 7,
        (0 : SkiRental.Certificates.Q) ≤ lemma19DxiFiniteCoeffFin i j := by
    native_decide
  have hq : (0 : SkiRental.Certificates.Q) ≤ lemma19DxiFiniteCoeffQ i j := by
    simpa [lemma19DxiFiniteCoeffFin] using
      hfinite ⟨i, Nat.lt_succ_iff.mpr hi⟩
        ⟨j, Nat.lt_succ_iff.mpr hj⟩
  unfold lemma19DxiFiniteCoeff
  exact_mod_cast hq

theorem lemma19DxiFiniteBernstein_nonneg {α β : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    0 ≤ lemma19DxiFiniteBernstein α β := by
  unfold lemma19DxiFiniteBernstein
  apply SkiRental.Polynomial.bernsteinEval_nonneg
  · intro i hi
    apply SkiRental.Polynomial.bernsteinEval_nonneg
    · intro j hj
      exact lemma19DxiFiniteCoeff_nonneg (i := i) (j := j) hi hj
    · exact hβ0
    · exact hβ1
  · exact hα0
  · exact hα1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lemma19DxiFiniteNum_shift_eq_bernstein (α β : ℝ) :
    lemma19DxiFiniteNum (31 / 100 + (69 / 100) * α) β
      = lemma19DxiFiniteBernstein α β := by
  unfold lemma19DxiFiniteNum lemma19DxiFiniteBernstein
    lemma19DxiFiniteCoeff lemma19DxiFiniteCoeffQ
    SkiRental.Polynomial.bernsteinEval SkiRental.Polynomial.bernsteinBasis
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [SkiRental.Certificates.lemma19DxiFiniteBernsteinCoeffs,
    SkiRental.Certificates.q, List.getD, Nat.choose]
  ring_nf

theorem lemma19DxiFiniteNum_nonneg_on_box {ρ ξ : ℝ}
    (hρ0 : (31 / 100 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) :
    0 ≤ lemma19DxiFiniteNum ρ ξ := by
  let α : ℝ := (ρ - 31 / 100) / (69 / 100)
  have hα0 : 0 ≤ α := by
    dsimp [α]
    apply div_nonneg
    · linarith
    · norm_num
  have hα1 : α ≤ 1 := by
    dsimp [α]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 69 / 100)]
    nlinarith
  have hρ : ρ = 31 / 100 + (69 / 100) * α := by
    dsimp [α]
    ring
  rw [hρ, lemma19DxiFiniteNum_shift_eq_bernstein]
  exact lemma19DxiFiniteBernstein_nonneg hα0 hα1 hξ0 hξ1

theorem lemma19DxiFinite_nonneg_on_box {ρ ξ : ℝ}
    (hρ0 : (31 / 100 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) :
    0 ≤ lemma19DxiFinite ρ ξ := by
  have hρ_nonneg : 0 ≤ ρ := by nlinarith
  have h0 : 1 + ξ ≠ 0 := by positivity
  have h1 : 1 + ξ * ρ ≠ 0 := by positivity
  have h2 : 1 + ξ * ρ ^ 2 ≠ 0 := by positivity
  have h3 : 1 + ξ * ρ ^ 3 ≠ 0 := by positivity
  have hden : 0 < lemma19DxiFiniteDen ρ ξ :=
    lemma19DxiFiniteDen_pos hρ_nonneg hξ0
  have hprod : 0 ≤ lemma19DxiFiniteDen ρ ξ * lemma19DxiFinite ρ ξ := by
    rw [lemma19DxiFiniteDen_mul_eq_num h0 h1 h2 h3]
    exact lemma19DxiFiniteNum_nonneg_on_box hρ0 hρ1 hξ0 hξ1
  exact (mul_nonneg_iff_of_pos_left hden).mp hprod

noncomputable abbrev scalarCertificateTightDxiFinite (ρ ξ : ℝ) : ℝ :=
  lemma19DxiFinite ρ ξ

theorem scalarCertificateTightDxiFinite_nonneg_on_box {ρ ξ : ℝ}
    (hρ0 : (31 / 100 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) :
    0 ≤ scalarCertificateTightDxiFinite ρ ξ :=
  lemma19DxiFinite_nonneg_on_box hρ0 hρ1 hξ0 hξ1

def lowerRhoBridgeTerm (ρ : ℝ) (k : Nat) : ℝ :=
  (1 - ρ ^ (k + 1)) / ((Nat.factorial (k + 1) : ℝ) * (1 + ρ ^ k))

noncomputable def lowerRhoBridgeSeries (ρ : ℝ) : ℝ :=
  ∑' k : Nat, (-1 : ℝ) ^ k * lowerRhoBridgeTerm ρ k

noncomputable def lowerRhoBridgeDSeries (ρ : ℝ) : ℝ :=
  Real.exp 1 / ρ * lowerRhoBridgeSeries ρ

def lowerRhoBridgeS6 (ρ : ℝ) : ℝ :=
  (Finset.range 6).sum (fun k => (-1 : ℝ) ^ k * lowerRhoBridgeTerm ρ k)

def lowerRhoBridgeP3 (ρ : ℝ) : ℝ :=
  ((1 - ρ) * (3 * ρ ^ 4 + 2 * ρ ^ 2 + 3))
    / (24 * (1 + ρ ^ 2) * (1 - ρ + ρ ^ 2))

def lowerRhoBridgeP5 (ρ : ℝ) : ℝ :=
  ((1 - ρ) * (5 * ρ ^ 8 + 5 * ρ ^ 6 + 4 * ρ ^ 4 + 5 * ρ ^ 2 + 5))
    / (720 * (1 + ρ ^ 4) * (1 - ρ + ρ ^ 2 - ρ ^ 3 + ρ ^ 4))

def lowerRhoBridgeMarginNum (ρ : ℝ) : ℝ :=
  2280
  - (207600 / 19) * ρ
  + (360480 / 19) * ρ ^ 2
  - (632040 / 19) * ρ ^ 3
  + (836904 / 19) * ρ ^ 4
  - (1119408 / 19) * ρ ^ 5
  + (1105272 / 19) * ρ ^ 6
  - (1226232 / 19) * ρ ^ 7
  + (1119408 / 19) * ρ ^ 8
  - (1078824 / 19) * ρ ^ 9
  + (753000 / 19) * ρ ^ 10
  - (602400 / 19) * ρ ^ 11
  + (328560 / 19) * ρ ^ 12
  - (164280 / 19) * ρ ^ 13

def lowerRhoBridgeMarginDen (ρ : ℝ) : ℝ :=
  (24 * (1 + ρ ^ 2) * (1 - ρ + ρ ^ 2))
    * (720 * (1 + ρ ^ 4) * (1 - ρ + ρ ^ 2 - ρ ^ 3 + ρ ^ 4))

def lowerRhoBridgeCoeffQ (i : Nat) : SkiRental.Certificates.Q :=
  ((SkiRental.Certificates.lowerRhoBridgeBernsteinCoeffs.getD i 0 :
    SkiRental.Certificates.Q))

def lowerRhoBridgeCoeff (i : Nat) : ℝ :=
  (lowerRhoBridgeCoeffQ i : ℝ)

def lowerRhoBridgeCoeffFin (i : Fin 14) : SkiRental.Certificates.Q :=
  lowerRhoBridgeCoeffQ i

def lowerRhoBridgeBernstein (α : ℝ) : ℝ :=
  SkiRental.Polynomial.bernsteinEval 13
    (fun i => lowerRhoBridgeCoeff i) α

theorem lowerRhoBridgeCoeff_pos {i : Nat} (hi : i ≤ 13) :
    0 < lowerRhoBridgeCoeff i := by
  have hfinite :
      ∀ i : Fin 14, (0 : SkiRental.Certificates.Q) < lowerRhoBridgeCoeffFin i := by
    native_decide
  have hq : (0 : SkiRental.Certificates.Q) < lowerRhoBridgeCoeffQ i := by
    simpa [lowerRhoBridgeCoeffFin] using
      hfinite ⟨i, Nat.lt_succ_iff.mpr hi⟩
  unfold lowerRhoBridgeCoeff
  exact_mod_cast hq

theorem lowerRhoBridgeBernstein_pos {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 < lowerRhoBridgeBernstein α := by
  unfold lowerRhoBridgeBernstein
  apply SkiRental.Polynomial.bernsteinEval_pos
  · intro i hi
    exact lowerRhoBridgeCoeff_pos (i := i) hi
  · exact hα0
  · exact hα1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lowerRhoBridgeMarginNum_shift_eq_bernstein (α : ℝ) :
    lowerRhoBridgeMarginNum ((31 / 100) * α)
      = lowerRhoBridgeBernstein α := by
  unfold lowerRhoBridgeMarginNum lowerRhoBridgeBernstein
    lowerRhoBridgeCoeff lowerRhoBridgeCoeffQ
    SkiRental.Polynomial.bernsteinEval SkiRental.Polynomial.bernsteinBasis
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [SkiRental.Certificates.lowerRhoBridgeBernsteinCoeffs,
    SkiRental.Certificates.q, List.getD, Nat.choose]
  ring_nf

theorem lowerRhoBridgeMarginNum_pos {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 31 / 100) :
    0 < lowerRhoBridgeMarginNum ρ := by
  let α : ℝ := ρ / (31 / 100)
  have hα0 : 0 ≤ α := by
    dsimp [α]
    positivity
  have hα1 : α ≤ 1 := by
    dsimp [α]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 31 / 100)]
    nlinarith
  have hρ : ρ = (31 / 100) * α := by
    dsimp [α]
    field_simp
  rw [hρ, lowerRhoBridgeMarginNum_shift_eq_bernstein]
  exact lowerRhoBridgeBernstein_pos hα0 hα1

theorem lowerRhoBridgeP3_add_P5_sub_bound_eq_num_div_den {ρ : ℝ}
    (h1 : 1 + ρ ^ 2 ≠ 0)
    (h2 : 1 - ρ + ρ ^ 2 ≠ 0)
    (h3 : 1 + ρ ^ 4 ≠ 0)
    (h4 : 1 - ρ + ρ ^ 2 - ρ ^ 3 + ρ ^ 4 ≠ 0) :
    lowerRhoBridgeP3 ρ + lowerRhoBridgeP5 ρ - (7 / 19) * ρ
      = lowerRhoBridgeMarginNum ρ / lowerRhoBridgeMarginDen ρ := by
  unfold lowerRhoBridgeP3 lowerRhoBridgeP5
    lowerRhoBridgeMarginNum lowerRhoBridgeMarginDen
  field_simp [h1, h2, h3, h4]
  ring_nf

theorem lowerRhoBridgeQuad_pos (ρ : ℝ) :
    0 < 1 - ρ + ρ ^ 2 := by
  have hs : 0 ≤ (ρ - 1 / 2) ^ 2 := sq_nonneg (ρ - 1 / 2)
  nlinarith

theorem lowerRhoBridgeQuartic_pos {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    0 < 1 - ρ + ρ ^ 2 - ρ ^ 3 + ρ ^ 4 := by
  have hfactor : 1 - ρ + ρ ^ 2 - ρ ^ 3 + ρ ^ 4
      = (1 - ρ) * (1 + ρ ^ 2) + ρ ^ 4 := by ring
  have hleft : 0 ≤ (1 - ρ) * (1 + ρ ^ 2) := by positivity
  have hright : 0 ≤ ρ ^ 4 := pow_nonneg hρ0 4
  have hsum : 0 ≤ (1 - ρ) * (1 + ρ ^ 2) + ρ ^ 4 :=
    add_nonneg hleft hright
  by_cases hρzero : ρ = 0
  · subst ρ
    norm_num
  · have hρpos : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm hρzero)
    have hright_pos : 0 < ρ ^ 4 := pow_pos hρpos 4
    rw [hfactor]
    exact add_pos_of_nonneg_of_pos hleft hright_pos

theorem lowerRhoBridgeMarginDen_pos {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 31 / 100) :
    0 < lowerRhoBridgeMarginDen ρ := by
  have hρ_nonneg : 0 ≤ ρ := le_of_lt hρ0
  have hρ_le_one : ρ ≤ 1 := by nlinarith
  have hquad : 0 < 1 - ρ + ρ ^ 2 := lowerRhoBridgeQuad_pos ρ
  have hquartic : 0 < 1 - ρ + ρ ^ 2 - ρ ^ 3 + ρ ^ 4 :=
    lowerRhoBridgeQuartic_pos hρ_nonneg hρ_le_one
  unfold lowerRhoBridgeMarginDen
  positivity

theorem lowerRhoBridgeP3_add_P5_gt_bound {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 31 / 100) :
    (7 / 19) * ρ < lowerRhoBridgeP3 ρ + lowerRhoBridgeP5 ρ := by
  have hρ_nonneg : 0 ≤ ρ := le_of_lt hρ0
  have h1 : 1 + ρ ^ 2 ≠ 0 := by positivity
  have h2 : 1 - ρ + ρ ^ 2 ≠ 0 := by
    exact ne_of_gt (lowerRhoBridgeQuad_pos ρ)
  have h3 : 1 + ρ ^ 4 ≠ 0 := by positivity
  have h4 : 1 - ρ + ρ ^ 2 - ρ ^ 3 + ρ ^ 4 ≠ 0 :=
    ne_of_gt (lowerRhoBridgeQuartic_pos hρ_nonneg (by nlinarith))
  have hden : 0 < lowerRhoBridgeMarginDen ρ :=
    lowerRhoBridgeMarginDen_pos hρ0 hρ1
  have hnum : 0 < lowerRhoBridgeMarginNum ρ :=
    lowerRhoBridgeMarginNum_pos hρ_nonneg hρ1
  have heq := lowerRhoBridgeP3_add_P5_sub_bound_eq_num_div_den
    (ρ := ρ) h1 h2 h3 h4
  have hsub : 0 < lowerRhoBridgeP3 ρ + lowerRhoBridgeP5 ρ - (7 / 19) * ρ := by
    rw [heq]
    positivity
  linarith

theorem lowerRhoBridgeS6_eq_P3_add_P5 {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 31 / 100) :
    lowerRhoBridgeS6 ρ = lowerRhoBridgeP3 ρ + lowerRhoBridgeP5 ρ := by
  have hρ_nonneg : 0 ≤ ρ := le_of_lt hρ0
  have hρ_lt_one : ρ < 1 := by nlinarith
  have h0 : 1 + ρ ≠ 0 := by positivity
  have h1 : 1 + ρ ^ 2 ≠ 0 := by positivity
  have h2 : 1 + ρ ^ 3 ≠ 0 := by positivity
  have h3 : 1 + ρ ^ 4 ≠ 0 := by positivity
  have h4 : 1 + ρ ^ 5 ≠ 0 := by positivity
  have hquad : 1 - ρ + ρ ^ 2 ≠ 0 :=
    ne_of_gt (lowerRhoBridgeQuad_pos ρ)
  have hquartic : 1 - ρ + ρ ^ 2 - ρ ^ 3 + ρ ^ 4 ≠ 0 :=
    ne_of_gt (lowerRhoBridgeQuartic_pos hρ_nonneg (by nlinarith))
  unfold lowerRhoBridgeS6 lowerRhoBridgeTerm lowerRhoBridgeP3 lowerRhoBridgeP5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  field_simp [h0, h1, h2, h3, h4, hquad, hquartic]
  ring_nf

theorem lowerRhoBridgeS6_gt_bound {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 31 / 100) :
    (7 / 19) * ρ < lowerRhoBridgeS6 ρ := by
  rw [lowerRhoBridgeS6_eq_P3_add_P5 hρ0 hρ1]
  exact lowerRhoBridgeP3_add_P5_gt_bound hρ0 hρ1

theorem lowerRhoBridgeTerm_nonneg {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (k : Nat) :
    0 ≤ lowerRhoBridgeTerm ρ k := by
  unfold lowerRhoBridgeTerm
  have hpow_le_one : ρ ^ (k + 1) ≤ 1 := pow_le_one₀ hρ0 hρ1
  have hnum : 0 ≤ 1 - ρ ^ (k + 1) := by nlinarith
  positivity

theorem lowerRhoBridgeTerm_le_factorial_tail {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (k : Nat) :
    lowerRhoBridgeTerm ρ k ≤ (1 : ℝ) / (Nat.factorial (k + 1) : ℝ) := by
  unfold lowerRhoBridgeTerm
  have hpow_nonneg : 0 ≤ ρ ^ k := pow_nonneg hρ0 k
  have hpow_le_one : ρ ^ (k + 1) ≤ 1 := pow_le_one₀ hρ0 hρ1
  have hnum_nonneg : 0 ≤ 1 - ρ ^ (k + 1) := by nlinarith
  have hnum_le_one : 1 - ρ ^ (k + 1) ≤ 1 := by nlinarith [pow_nonneg hρ0 (k + 1)]
  have hfac_pos : 0 < (Nat.factorial (k + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (k + 1)
  have hden_pos : 0 < (Nat.factorial (k + 1) : ℝ) * (1 + ρ ^ k) := by
    positivity
  calc
    (1 - ρ ^ (k + 1)) / ((Nat.factorial (k + 1) : ℝ) * (1 + ρ ^ k))
        ≤ 1 / ((Nat.factorial (k + 1) : ℝ) * (1 + ρ ^ k)) := by
          exact div_le_div_of_nonneg_right hnum_le_one (le_of_lt hden_pos)
    _ ≤ 1 / (Nat.factorial (k + 1) : ℝ) := by
          have hden_ge : (Nat.factorial (k + 1) : ℝ)
              ≤ (Nat.factorial (k + 1) : ℝ) * (1 + ρ ^ k) := by
            nlinarith [mul_le_mul_of_nonneg_left (by nlinarith : (1 : ℝ) ≤ 1 + ρ ^ k)
              (le_of_lt hfac_pos)]
          exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hfac_pos hden_ge

theorem lowerRhoBridgeTerm_summable {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    Summable (fun k => lowerRhoBridgeTerm ρ k) := by
  have htail : Summable (fun k : Nat => (1 : ℝ) / (Nat.factorial (k + 1) : ℝ)) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial (1 : ℝ))
    simpa [Nat.add_comm, one_pow] using h
  exact Summable.of_nonneg_of_le
    (fun k => lowerRhoBridgeTerm_nonneg hρ0 hρ1 k)
    (fun k => lowerRhoBridgeTerm_le_factorial_tail hρ0 hρ1 k)
    htail

theorem lowerRhoBridgeTerm_succ_le {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 31 / 100) (k : Nat) :
    lowerRhoBridgeTerm ρ (k + 1) ≤ lowerRhoBridgeTerm ρ k := by
  have hρle1 : ρ ≤ 1 := by nlinarith
  unfold lowerRhoBridgeTerm
  have hden_left : 0 < (Nat.factorial (k + 2) : ℝ) * (1 + ρ ^ (k + 1)) := by
    positivity
  have hden_right : 0 < (Nat.factorial (k + 1) : ℝ) * (1 + ρ ^ k) := by
    positivity
  rw [div_le_div_iff₀ hden_left hden_right]
  have hk_exp : k + 2 ≤ 2 * (k + 1) := by omega
  have hpow_cmp : ρ ^ (2 * (k + 1)) ≤ ρ ^ (k + 2) :=
    pow_le_pow_of_le_one hρ0 hρle1 hk_exp
  have hmain :
      1 - ρ ^ (k + 2) ≤ (1 - ρ ^ (k + 1)) * (1 + ρ ^ (k + 1)) := by
    have hfirst : 1 - ρ ^ (k + 2) ≤ 1 - ρ ^ (2 * (k + 1)) := by nlinarith
    have hid : 1 - ρ ^ (2 * (k + 1))
        = (1 - ρ ^ (k + 1)) * (1 + ρ ^ (k + 1)) := by
      rw [show ρ ^ (2 * (k + 1)) = (ρ ^ (k + 1)) ^ 2 by
        rw [mul_comm, ← pow_mul]]
      ring
    linarith
  have hfactor : 1 + ρ ^ k ≤ (k + 2 : ℝ) := by
    have hpow_le : ρ ^ k ≤ 1 := pow_le_one₀ hρ0 hρle1
    have hk2 : (2 : ℝ) ≤ k + 2 := by exact_mod_cast Nat.le_add_left 2 k
    nlinarith
  have hmain_nonneg : 0 ≤ (1 - ρ ^ (k + 1)) * (1 + ρ ^ (k + 1)) := by
    have hp : ρ ^ (k + 1) ≤ 1 := pow_le_one₀ hρ0 hρle1
    positivity
  have hprod :
      (1 - ρ ^ (k + 2)) * (1 + ρ ^ k)
        ≤ ((1 - ρ ^ (k + 1)) * (1 + ρ ^ (k + 1))) * (k + 2) := by
    have hleft_nonneg : 0 ≤ 1 + ρ ^ k := by positivity
    have hright_nonneg : 0 ≤ 1 - ρ ^ (k + 2) := by
      have hp : ρ ^ (k + 2) ≤ 1 := pow_le_one₀ hρ0 hρle1
      nlinarith
    nlinarith [mul_le_mul hmain hfactor hleft_nonneg hmain_nonneg]
  have hfac : ((Nat.factorial (k + 2) : Nat) : ℝ)
      = (k + 2 : ℝ) * (Nat.factorial (k + 1) : ℝ) := by
    have hfacNat : Nat.factorial (k + 2) = (k + 2) * Nat.factorial (k + 1) := by
      rw [show k + 2 = (k + 1).succ by omega, Nat.factorial_succ]
    exact_mod_cast hfacNat
  rw [hfac]
  have hfact_nonneg : 0 ≤ (Nat.factorial (k + 1) : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hprod hfact_nonneg
  ring_nf at hmul ⊢
  nlinarith

theorem lowerRhoBridgeTerm_antitone {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 31 / 100) :
    Antitone (fun k => lowerRhoBridgeTerm ρ k) := by
  apply antitone_nat_of_succ_le
  exact lowerRhoBridgeTerm_succ_le hρ0 hρ1

theorem lowerRhoBridgeS6_le_series {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 31 / 100) :
    lowerRhoBridgeS6 ρ ≤ lowerRhoBridgeSeries ρ := by
  have hρle1 : ρ ≤ 1 := by nlinarith
  have hsum : Summable (fun k => lowerRhoBridgeTerm ρ k) :=
    lowerRhoBridgeTerm_summable hρ0 hρle1
  have htend := hsum.tendsto_alternating_series_tsum
  have hbound := (lowerRhoBridgeTerm_antitone hρ0 hρ1).alternating_series_le_tendsto
    htend 3
  simpa [lowerRhoBridgeS6, lowerRhoBridgeSeries] using hbound

theorem lowerRhoBridgeDSeries_gt_one {ρ : ℝ}
    (he : (19 / 7 : ℝ) < Real.exp 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 31 / 100) :
    1 < lowerRhoBridgeDSeries ρ := by
  have hρ_nonneg : 0 ≤ ρ := le_of_lt hρ0
  have hS_bound : (7 / 19) * ρ < lowerRhoBridgeS6 ρ :=
    lowerRhoBridgeS6_gt_bound hρ0 hρ1
  have hseries_bound : (7 / 19) * ρ < lowerRhoBridgeSeries ρ :=
    lt_of_lt_of_le hS_bound (lowerRhoBridgeS6_le_series hρ_nonneg hρ1)
  unfold lowerRhoBridgeDSeries
  have hfactor_pos : 0 < Real.exp 1 / ρ := div_pos (Real.exp_pos 1) hρ0
  have htarget : 1 < (Real.exp 1 / ρ) * ((7 / 19) * ρ) := by
    field_simp [ne_of_gt hρ0]
    nlinarith
  exact lt_of_lt_of_le htarget (mul_le_mul_of_nonneg_left (le_of_lt hseries_bound) (le_of_lt hfactor_pos))

def UInnerPoly (ρ : ℝ) : ℝ :=
  3 * ρ ^ 5 - 6 * ρ ^ 4 + 12 * ρ ^ 3 - 10 * ρ ^ 2 + 6 * ρ - 1

def UClearPoly (ρ : ℝ) : ℝ :=
  (1 + ρ) * UInnerPoly ρ

def UBernstein (s : ℝ) : ℝ :=
  SkiRental.Polynomial.bernstein5
    (2096694853 / 10000000000)
    (289971689 / 500000000)
    (4416419 / 5000000)
    (6821 / 5000)
    (1103 / 500)
    4
    s

theorem UInnerPoly_shift_eq (s : ℝ) :
    UInnerPoly (31 / 100 + (69 / 100) * s) = UBernstein s := by
  unfold UInnerPoly UBernstein SkiRental.Polynomial.bernstein5
  ring_nf

theorem UBernstein_pos {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < UBernstein s := by
  unfold UBernstein
  exact SkiRental.Polynomial.bernstein5_pos
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    hs0 hs1

theorem UClearPoly_pos_on_interval {ρ : ℝ}
    (hρ0 : (31 / 100 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1) :
    0 < UClearPoly ρ := by
  let s : ℝ := (ρ - 31 / 100) / (69 / 100)
  have hs0 : 0 ≤ s := by
    dsimp [s]
    apply div_nonneg
    · linarith
    · norm_num
  have hs1 : s ≤ 1 := by
    dsimp [s]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 69 / 100)]
    nlinarith
  have hρ : ρ = 31 / 100 + (69 / 100) * s := by
    dsimp [s]
    ring
  rw [hρ]
  unfold UClearPoly
  have hfactor : 0 < 1 + (31 / 100 + (69 / 100) * s : ℝ) := by
    nlinarith
  have hinner : 0 < UInnerPoly (31 / 100 + (69 / 100) * s) := by
    rw [UInnerPoly_shift_eq]
    exact UBernstein_pos hs0 hs1
  positivity

theorem U3CubicLower_cleared_at_one_eq {ρ : ℝ}
    (h1 : 1 + ρ ≠ 0) (h2 : 1 + ρ ^ 2 ≠ 0) (h3 : 1 + ρ ^ 3 ≠ 0) :
    6 * (1 + ρ) * (1 + ρ ^ 2) * (1 + ρ ^ 3)
      * U3CubicLower ρ 1 1
    = UClearPoly ρ := by
  unfold U3CubicLower UClearPoly UInnerPoly
  field_simp [h1, h2, h3]
  ring_nf

theorem U3CubicLower_at_one_pos {ρ : ℝ}
    (hρ0 : (31 / 100 : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1) :
    0 < U3CubicLower ρ 1 1 := by
  have hρnonneg : 0 ≤ ρ := by nlinarith
  have h1pos : 0 < 1 + ρ := by nlinarith
  have h2pos : 0 < 1 + ρ ^ 2 := by positivity
  have h3pos : 0 < 1 + ρ ^ 3 := by positivity
  have hden : 0 < 6 * (1 + ρ) * (1 + ρ ^ 2) * (1 + ρ ^ 3) := by positivity
  have hclear : 0 < UClearPoly ρ := UClearPoly_pos_on_interval hρ0 hρ1
  have heq := U3CubicLower_cleared_at_one_eq
    (ρ := ρ) (ne_of_gt h1pos) (ne_of_gt h2pos) (ne_of_gt h3pos)
  nlinarith

end

end SkiRental.Scalar
