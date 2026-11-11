import Std

/-!
Exact rational checks for the numeric certificates in the ski-rental section.

This first file deliberately stays in pure Lean/Std: decimal endpoints from the
paper are encoded as exact rationals, and the certificate statements are proved
by exact computation over `Rat`.

Scope of this layer:
* checks the outward-rounded arithmetic once exponential/Taylor enclosures are
  supplied;
* checks the finite truncation arithmetic used to bracket the thresholds;
* checks listed positive-coefficient certificates.

It does not yet prove the analytic facts that justify the exponential
enclosures, alternating-series truncation signs, or Bernstein-basis positivity.
Those are natural next Mathlib-backed layers.
-/

namespace SkiRental.Certificates

abbrev Q := Rat

def q (n d : Int) : Q := (n : Q) / (d : Q)

def allPositive (xs : List Q) : Bool :=
  xs.all (fun x => decide (0 < x))

def eLower : Q := q 271828182 100000000
def eUpper : Q := q 271828183 100000000

theorem e_interval_nonempty : eLower < eUpper := by
  native_decide

/-! ## Buy-by-breakeven-time threshold bracket -/

def factNat : Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * factNat n

def factQ (n : Nat) : Q := (factNat n : Q)

def DTerm (rho : Q) (n : Nat) : Q :=
  (1 - rho ^ n) / (factQ n * (1 + rho ^ (n - 1)))

def DPartial (rho : Q) : Nat -> Q
  | 0 => 0
  | n + 1 =>
      let k := n + 1
      DPartial rho n + if k % 2 = 1 then DTerm rho k else -DTerm rho k

def rho031087 : Q := q 31087 100000
def rho031088 : Q := q 31088 100000

def DLower031087MinusOne : Q :=
  eLower / rho031087 * DPartial rho031087 10 - 1

def DUpper031088MinusOne : Q :=
  eUpper / rho031088 * DPartial rho031088 11 - 1

theorem D_031087_lower_bracket :
    q 15 1000000 < DLower031087MinusOne := by
  native_decide

theorem D_031088_upper_bracket :
    DUpper031088MinusOne < q (-26) 1000000 := by
  native_decide

def rho031 : Q := q 31 100

def lowerRhoBridgeS6Margin : Q :=
  DPartial rho031 6 - q 7 19 * rho031

theorem lower_rho_bridge_S6_margin_value :
    lowerRhoBridgeS6Margin
      =
      q 1538190334986700888894969 20237843235225380172556254400 := by
  native_decide

theorem lower_rho_bridge_S6_margin_positive :
    0 < lowerRhoBridgeS6Margin := by
  native_decide

theorem lower_rho_bridge_P3_text_bound_positive :
    0 < q 1315 243 := by
  native_decide

theorem lower_rho_bridge_P5_text_bound_positive :
    0 < q 8460422 531441 := by
  native_decide

theorem lower_rho_bridge_e_partial_gt :
    q 19 7 < q 163 60 := by
  native_decide

def lowerRhoBridgeBernsteinCoeffs : List Q :=
  [ q 2280 1,
    q 498804 247,
    q 55027711 30875,
    q 16354342893 10450000,
    q 17827149026721 13062500000,
    q 6006586988300479 5094375000000,
    q 1366381833603027493 1358500000000000,
    q 114536490183302231777 135850000000000000,
    q 3511598491188190929661 5094375000000000000,
    q 48517168081786843229823 89375000000000000000,
    q 1092929162912025317517957 2717000000000000000000,
    q 102687730728320765263059 385937500000000000000,
    q 410054667526034005335557427 3087500000000000000000000,
    q 41531139044640924000164163 47500000000000000000000000 ]

theorem lowerRhoBridgeBernsteinCoeffs_positive :
    allPositive lowerRhoBridgeBernsteinCoeffs = true := by
  native_decide

/-! ## General-algorithm threshold endpoint arithmetic -/

def sumPowersFromOne (rho : Q) : Nat -> Q
  | 0 => 0
  | n + 1 => sumPowersFromOne rho n + rho ^ (n + 1)

def dCoeff (rho : Q) (n : Nat) : Q :=
  (1 + ((n + 3 : Nat) : Q) * sumPowersFromOne rho n + rho ^ (n + 1))
  / (((n + 1) * (n + 2) : Nat) : Q)

def fCoeff (rho : Q) (n : Nat) : Q :=
  dCoeff rho n / (1 + rho ^ n)

def KTerm (rho : Q) (n : Nat) : Q :=
  let t := fCoeff rho n / factQ n
  if n % 2 = 0 then t else -t

def KPartialSum (rho : Q) : Nat -> Q
  | 0 => KTerm rho 0
  | n + 1 => KPartialSum rho n + KTerm rho (n + 1)

def rhoOneThird : Q := q 1 3
def rhoOneHalf : Q := q 1 2

theorem K_left_partial_value :
    KPartialSum rhoOneThird 5 = q 3120653 25210080 := by
  native_decide

theorem K_left_partial_gt_text_bound :
    q 46 375 < KPartialSum rhoOneThird 5 := by
  native_decide

theorem e_lower_for_K_left :
    q 125 46 < q 1957 720 := by
  native_decide

theorem one_third_times_recip_upper :
    q 1 3 * q 46 125 = q 46 375 := by
  native_decide

theorem K_right_partial_value :
    KPartialSum rhoOneHalf 2 = q 127 720 := by
  native_decide

theorem e_upper_for_K_right :
    q 65 24 + q 1 100 < q 30 11 := by
  native_decide

theorem K_right_margin :
    q 11 60 - q 127 720 = q 1 144 := by
  native_decide

/-! ## Listed positive-coefficient certificates -/

-- Polynomial P(rho) from the nearby-rate positivity claim after rho = 4/5 + z.
def nearbyQPolynomialShiftCoeffs : List Q :=
  [ q 195312500 48828125,
    q 1425781250 48828125,
    q 5117187500 48828125,
    q 11597656250 48828125,
    q 18501562500 48828125,
    q 22005500000 48828125,
    q 20063337500 48828125,
    q 14275721875 48828125,
    q 7888413750 48828125,
    q 3329469500 48828125,
    q 958670470 48828125,
    q 166978261 48828125 ]

theorem nearbyQPolynomialShiftCoeffs_positive :
    allPositive nearbyQPolynomialShiftCoeffs = true := by
  native_decide

theorem nearbyQ_at_four_fifths_positive :
    0 < q 198283 2975616 := by
  native_decide

-- Polynomial P(rho) in the proof of K(rho,xi) >= K(rho,1), after rho = 1/3 + s.
def generalKPolynomialShiftCoeffs : List Q :=
  [ q 54160 19683,
    q 466880 19683,
    q 817872 19683,
    q 1348974 19683,
    q 3803598 19683,
    q 3032397 19683,
    q 5454378 19683,
    q 3416094 19683,
    q 3457647 19683,
    q 1377810 19683,
    q 984150 19683,
    q 295245 19683 ]

theorem generalKPolynomialShiftCoeffs_positive :
    allPositive generalKPolynomialShiftCoeffs = true := by
  native_decide

-- Bernstein coefficients for the U-polynomial on rho in [0.31,1].
def uPolynomialBernsteinCoeffs : List Q :=
  [ q 2096694853 10000000000,
    q 289971689 500000000,
    q 4416419 5000000,
    q 6821 5000,
    q 1103 500,
    q 4 1 ]

theorem uPolynomialBernsteinCoeffs_positive :
    allPositive uPolynomialBernsteinCoeffs = true := by
  native_decide

end SkiRental.Certificates
