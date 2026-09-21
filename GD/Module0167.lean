import GD.Module0166
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic














open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1052

noncomputable section

open MeasureTheory Set
open _root_.GD.N0232.N0720.N1051




def d001963 (y : ℝ) : ℝ :=
  y ^ ((5 : ℝ) / 2) * Real.exp (-y)


theorem d001964
    {y : ℝ} (hy : 0 < y) :
    _root_.GD.N0232.N0720.N1052.d001963 y ≤
      ((5 : ℝ) / (2 * Real.exp 1)) ^ ((5 : ℝ) / 2) := by
  let t : ℝ := 2 * y / 5
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hbasic : t * Real.exp (-t) ≤ Real.exp (-1) :=
    Real.mul_exp_neg_le_exp_neg_one t
  have hscaled : y * Real.exp (-(2 * y / 5)) ≤ 5 / (2 * Real.exp 1) := by
    have hexpneg : Real.exp (-1) = (Real.exp 1)⁻¹ := by
      rw [Real.exp_neg]
    dsimp [t] at hbasic
    rw [hexpneg] at hbasic
    have hepos : 0 < Real.exp 1 := Real.exp_pos _
    calc
      y * Real.exp (-(2 * y / 5)) =
          (5 / 2) * ((2 * y / 5) * Real.exp (-(2 * y / 5))) := by ring
      _ ≤ (5 / 2) * (Real.exp 1)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hbasic (by norm_num)
      _ = 5 / (2 * Real.exp 1) := by field_simp
  have hleft : 0 ≤ y * Real.exp (-(2 * y / 5)) := by positivity
  have hright : 0 ≤ 5 / (2 * Real.exp 1) := by positivity
  have hrpow := Real.rpow_le_rpow hleft hscaled (by norm_num : (0 : ℝ) ≤ 5 / 2)
  have hpowexp :
      (y * Real.exp (-(2 * y / 5))) ^ ((5 : ℝ) / 2) =
        _root_.GD.N0232.N0720.N1052.d001963 y := by
    rw [Real.mul_rpow (le_of_lt hy) (Real.exp_pos _).le]
    unfold _root_.GD.N0232.N0720.N1052.d001963
    rw [← Real.exp_mul]
    congr 1
    ring
  rwa [hpowexp] at hrpow

theorem d001965 :
    _root_.GD.N0232.N0720.N1052.d001963 ((5 : ℝ) / 2) =
      ((5 : ℝ) / (2 * Real.exp 1)) ^ ((5 : ℝ) / 2) := by
  unfold _root_.GD.N0232.N0720.N1052.d001963
  have hbase : 0 ≤ (5 : ℝ) / 2 := by norm_num
  rw [show -((5 : ℝ) / 2) = (-1) * ((5 : ℝ) / 2) by ring,
    Real.exp_mul, ← Real.mul_rpow hbase (Real.exp_pos (-1)).le]
  congr 1
  rw [Real.exp_neg]
  field_simp






def d001966 (a b : ℝ) : Set ℝ :=
  Ioc (-b) (-a) ∪ Ioc a b

theorem d001967 (a b : ℝ) :
    MeasurableSet (_root_.GD.N0232.N0720.N1052.d001966 a b) := by
  exact measurableSet_Ioc.union measurableSet_Ioc

theorem d001968
    {a b : ℝ} (ha : 0 ≤ a) :
    Disjoint (Ioc (-b) (-a)) (Ioc a b) := by
  rw [Set.disjoint_left]
  intro x hxLeft hxRight
  linarith [hxLeft.2, hxRight.1]

theorem d001969
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (volume : Measure ℝ) (_root_.GD.N0232.N0720.N1052.d001966 a b) =
      ENNReal.ofReal (2 * (b - a)) := by
  rw [_root_.GD.N0232.N0720.N1052.d001966,
    measure_union (_root_.GD.N0232.N0720.N1052.d001968 ha) measurableSet_Ioc,
    Real.volume_Ioc, Real.volume_Ioc]
  rw [← ENNReal.ofReal_add (by linarith : 0 ≤ -a - -b)
    (sub_nonneg.mpr hab)]
  congr 1
  ring


def d001970 : Measure ((ℝ × ℝ) × ℝ) :=
  ((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure ℝ)


def d001971 (rho : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  (_root_.GD.N0232.N0720.N1052.d001966 1 2 ×ˢ
      _root_.GD.N0232.N0720.N1052.d001966 (Real.sqrt rho) (2 * Real.sqrt rho)) ×ˢ
    _root_.GD.N0232.N0720.N1052.d001966 1 2

theorem d001972 (rho : ℝ) :
    MeasurableSet (_root_.GD.N0232.N0720.N1052.d001971 rho) := by
  exact (_root_.GD.N0232.N0720.N1052.d001967 1 2).prod
    (_root_.GD.N0232.N0720.N1052.d001967 (Real.sqrt rho) (2 * Real.sqrt rho)) |>.prod
      (_root_.GD.N0232.N0720.N1052.d001967 1 2)

theorem d001973
    {rho : ℝ} (hrho : 0 ≤ rho) :
    _root_.GD.N0232.N0720.N1052.d001970 (_root_.GD.N0232.N0720.N1052.d001971 rho) = ENNReal.ofReal (8 * Real.sqrt rho) := by
  have hsqrt : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg _
  rw [_root_.GD.N0232.N0720.N1052.d001970, _root_.GD.N0232.N0720.N1052.d001971, Measure.prod_prod, Measure.prod_prod,
    _root_.GD.N0232.N0720.N1052.d001969 (by norm_num : (0 : ℝ) ≤ 1) (by norm_num),
    _root_.GD.N0232.N0720.N1052.d001969 hsqrt (by linarith)]
  simp only [show (2 : ℝ) * (2 - 1) = 2 by norm_num,
    show 2 * (2 * Real.sqrt rho - Real.sqrt rho) =
      2 * Real.sqrt rho by ring]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← ENNReal.ofReal_mul
    (by positivity : (0 : ℝ) ≤ 2 * (2 * Real.sqrt rho))]
  congr 1
  ring

theorem d001974
    {rho : ℝ} (hrho : 0 ≤ rho) :
    (_root_.GD.N0232.N0720.N1052.d001970 (_root_.GD.N0232.N0720.N1052.d001971 rho)).toReal = 8 * Real.sqrt rho := by
  rw [_root_.GD.N0232.N0720.N1052.d001973 hrho, ENNReal.toReal_ofReal]
  positivity




def d001975 (S p : ℝ) (z : (ℝ × ℝ) × ℝ) : ℝ :=
  z.1.1 ^ 2 / (S * (1 - p)) +
    z.1.2 ^ 2 / (S * p) + z.2 ^ 2 / S



def d001976 (S p : ℝ) (z : (ℝ × ℝ) × ℝ) : ℝ :=
  Real.exp (-_root_.GD.N0232.N0720.N1052.d001975 S p z) /
    ((Real.pi * S) ^ ((3 : ℝ) / 2) * Real.sqrt (p * (1 - p)))

theorem d001977
    {a b x : ℝ} (ha : 0 ≤ a) (hx : x ∈ _root_.GD.N0232.N0720.N1052.d001966 a b) :
    a ≤ |x| := by
  rcases hx with hx | hx
  · rw [abs_of_nonpos (by linarith [hx.2])]
    linarith [hx.2]
  · rw [abs_of_pos (lt_of_le_of_lt ha hx.1)]
    exact hx.1.le

theorem d001978
    {x : ℝ} (hx : x ∈ _root_.GD.N0232.N0720.N1052.d001966 1 2) :
    1 ≤ x ^ 2 := by
  have habs := _root_.GD.N0232.N0720.N1052.d001977 (a := (1 : ℝ)) (by norm_num) hx
  nlinarith [sq_abs x]

theorem d001979
    {rho x : ℝ} (hrho : 0 ≤ rho)
    (hx : x ∈ _root_.GD.N0232.N0720.N1052.d001966 (Real.sqrt rho) (2 * Real.sqrt rho)) :
    rho ≤ x ^ 2 := by
  have habs := _root_.GD.N0232.N0720.N1052.d001977 (Real.sqrt_nonneg rho) hx
  have hsquare : (Real.sqrt rho) ^ 2 ≤ |x| ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg rho) (abs_nonneg x)).2 habs
  simpa [sq_abs, Real.sq_sqrt hrho] using hsquare



theorem d001980
    {S p rho : ℝ} (hS : 0 < S) (hp : 0 < p) (hp1 : p < 1)
    (hrho : 0 ≤ rho) {z : (ℝ × ℝ) × ℝ}
    (hz : z ∈ _root_.GD.N0232.N0720.N1052.d001971 rho) :
    _root_.GD.N0232.N0720.N1051.d001938 rho p / (S * (p * (1 - p))) ≤
      _root_.GD.N0232.N0720.N1052.d001975 S p z := by
  rcases hz with ⟨⟨huBand, hvBand⟩, hDBand⟩
  have hu : 1 ≤ z.1.1 ^ 2 := _root_.GD.N0232.N0720.N1052.d001978 huBand
  have hv : rho ≤ z.1.2 ^ 2 :=
    _root_.GD.N0232.N0720.N1052.d001979 hrho hvBand
  have hD : 1 ≤ z.2 ^ 2 := _root_.GD.N0232.N0720.N1052.d001978 hDBand
  have hSp : 0 < S * p := mul_pos hS hp
  have hSone : 0 < S * (1 - p) := mul_pos hS (sub_pos.mpr hp1)
  have huDiv : 1 / (S * (1 - p)) ≤ z.1.1 ^ 2 / (S * (1 - p)) :=
    div_le_div_of_nonneg_right hu hSone.le
  have hvDiv : rho / (S * p) ≤ z.1.2 ^ 2 / (S * p) :=
    div_le_div_of_nonneg_right hv hSp.le
  have hDDiv : 1 / S ≤ z.2 ^ 2 / S :=
    div_le_div_of_nonneg_right hD hS.le
  have hidentity :
      1 / (S * (1 - p)) + rho / (S * p) + 1 / S =
        _root_.GD.N0232.N0720.N1051.d001938 rho p / (S * (p * (1 - p))) := by
    field_simp [hS.ne', hp.ne', (sub_pos.mpr hp1).ne']
    unfold _root_.GD.N0232.N0720.N1051.d001938
    ring
  rw [← hidentity]
  unfold _root_.GD.N0232.N0720.N1052.d001975
  linarith

theorem d001981
    {S p : ℝ} (hS : 0 < S) (hp : 0 < p) (hp1 : p < 1)
    (z : (ℝ × ℝ) × ℝ) :
    0 ≤ _root_.GD.N0232.N0720.N1052.d001976 S p z := by
  unfold _root_.GD.N0232.N0720.N1052.d001976
  positivity [Real.pi_pos]


theorem d001982
    {S p rho : ℝ} (hS : 0 < S) (hp : 0 < p) (hp1 : p < 1)
    (hrho : 0 ≤ rho) {z : (ℝ × ℝ) × ℝ}
    (hz : z ∈ _root_.GD.N0232.N0720.N1052.d001971 rho) :
    _root_.GD.N0232.N0720.N1052.d001976 S p z ≤
      Real.exp (-(_root_.GD.N0232.N0720.N1051.d001938 rho p / (S * (p * (1 - p))))) /
        ((Real.pi * S) ^ ((3 : ℝ) / 2) * Real.sqrt (p * (1 - p))) := by
  have hexp := _root_.GD.N0232.N0720.N1052.d001980 hS hp hp1 hrho hz
  have hnum :
      Real.exp (-_root_.GD.N0232.N0720.N1052.d001975 S p z) ≤
        Real.exp (-(_root_.GD.N0232.N0720.N1051.d001938 rho p / (S * (p * (1 - p))))) := by
    exact Real.exp_le_exp.mpr (neg_le_neg hexp)
  unfold _root_.GD.N0232.N0720.N1052.d001976
  exact div_le_div_of_nonneg_right hnum (by positivity [Real.pi_pos])



def d001983 (S p rho : ℝ) : ℝ :=
  ∫ z in _root_.GD.N0232.N0720.N1052.d001971 rho, _root_.GD.N0232.N0720.N1052.d001976 S p z ∂_root_.GD.N0232.N0720.N1052.d001970


theorem d001984
    {S p rho : ℝ} (hS : 0 < S) (hp : 0 < p) (hp1 : p < 1)
    (hrho : 0 ≤ rho) :
    _root_.GD.N0232.N0720.N1052.d001983 S p rho ≤
      8 * Real.sqrt rho *
        (Real.exp (-(_root_.GD.N0232.N0720.N1051.d001938 rho p / (S * (p * (1 - p))))) /
          ((Real.pi * S) ^ ((3 : ℝ) / 2) * Real.sqrt (p * (1 - p)))) := by
  let C : ℝ :=
    Real.exp (-(_root_.GD.N0232.N0720.N1051.d001938 rho p / (S * (p * (1 - p))))) /
      ((Real.pi * S) ^ ((3 : ℝ) / 2) * Real.sqrt (p * (1 - p)))
  have hfinite : _root_.GD.N0232.N0720.N1052.d001970 (_root_.GD.N0232.N0720.N1052.d001971 rho) < ∞ := by
    rw [_root_.GD.N0232.N0720.N1052.d001973 hrho]
    exact ENNReal.ofReal_lt_top
  have hnorm :
      ‖∫ z in _root_.GD.N0232.N0720.N1052.d001971 rho, _root_.GD.N0232.N0720.N1052.d001976 S p z ∂_root_.GD.N0232.N0720.N1052.d001970‖ ≤
        C * (_root_.GD.N0232.N0720.N1052.d001970 (_root_.GD.N0232.N0720.N1052.d001971 rho)).toReal := by
    apply norm_setIntegral_le_of_norm_le_const hfinite
    intro z hz
    rw [Real.norm_eq_abs, abs_of_nonneg
      (_root_.GD.N0232.N0720.N1052.d001981 hS hp hp1 z)]
    exact _root_.GD.N0232.N0720.N1052.d001982 hS hp hp1 hrho hz
  have hnonneg :
      0 ≤ ∫ z in _root_.GD.N0232.N0720.N1052.d001971 rho, _root_.GD.N0232.N0720.N1052.d001976 S p z ∂_root_.GD.N0232.N0720.N1052.d001970 := by
    apply integral_nonneg_of_ae
    filter_upwards [] with z
    exact _root_.GD.N0232.N0720.N1052.d001981 hS hp hp1 z
  unfold _root_.GD.N0232.N0720.N1052.d001983
  calc
    (∫ z in _root_.GD.N0232.N0720.N1052.d001971 rho, _root_.GD.N0232.N0720.N1052.d001976 S p z ∂_root_.GD.N0232.N0720.N1052.d001970) ≤
        ‖∫ z in _root_.GD.N0232.N0720.N1052.d001971 rho, _root_.GD.N0232.N0720.N1052.d001976 S p z ∂_root_.GD.N0232.N0720.N1052.d001970‖ :=
      le_abs_self _
    _ ≤ C * (_root_.GD.N0232.N0720.N1052.d001970 (_root_.GD.N0232.N0720.N1052.d001971 rho)).toReal := hnorm
    _ = 8 * Real.sqrt rho *
        (Real.exp (-(_root_.GD.N0232.N0720.N1051.d001938 rho p / (S * (p * (1 - p))))) /
          ((Real.pi * S) ^ ((3 : ℝ) / 2) * Real.sqrt (p * (1 - p)))) := by
      rw [_root_.GD.N0232.N0720.N1052.d001974 hrho]
      dsimp [C]
      ring




def d001985 : ℝ :=
  Real.pi ^ (-(3 : ℝ) / 2) *
    ((5 : ℝ) / (2 * Real.exp 1)) ^ ((5 : ℝ) / 2)

theorem d001986 : 0 ≤ _root_.GD.N0232.N0720.N1052.d001985 := by
  unfold _root_.GD.N0232.N0720.N1052.d001985
  positivity [Real.pi_pos]



theorem d001987
    {A S b : ℝ} (hA : 0 < A) (hS : 0 < S) (hb : 0 < b) :
    Real.exp (-(A / (S * b))) /
        ((Real.pi * S) ^ ((3 : ℝ) / 2) * Real.sqrt b) =
      Real.pi ^ (-(3 : ℝ) / 2) * S * b ^ 2 /
          A ^ ((5 : ℝ) / 2) *
        _root_.GD.N0232.N0720.N1052.d001963 (A / (S * b)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hSb : 0 < S * b := mul_pos hS hb
  have hy : 0 < A / (S * b) := div_pos hA hSb
  refine Real.log_injOn_pos
    (show 0 < Real.exp (-(A / (S * b))) /
        ((Real.pi * S) ^ ((3 : ℝ) / 2) * Real.sqrt b) by positivity)
    (show 0 < Real.pi ^ (-(3 : ℝ) / 2) * S * b ^ 2 /
          A ^ ((5 : ℝ) / 2) *
        _root_.GD.N0232.N0720.N1052.d001963 (A / (S * b)) by
      unfold _root_.GD.N0232.N0720.N1052.d001963
      positivity) ?_
  unfold _root_.GD.N0232.N0720.N1052.d001963
  rw [Real.log_div (Real.exp_ne_zero _)
      (mul_ne_zero (Real.rpow_pos_of_pos (mul_pos hpi hS) _).ne'
        (Real.sqrt_ne_zero'.mpr hb)),
    Real.log_mul (Real.rpow_pos_of_pos (mul_pos hpi hS) _).ne'
      (Real.sqrt_ne_zero'.mpr hb),
    Real.log_exp,
    Real.log_rpow (mul_pos hpi hS),
    Real.log_mul hpi.ne' hS.ne',
    Real.log_sqrt hb.le,
    Real.log_mul
      (div_ne_zero
        (mul_ne_zero
          (mul_ne_zero (Real.rpow_pos_of_pos hpi _).ne' hS.ne')
          (pow_ne_zero 2 hb.ne'))
        (Real.rpow_pos_of_pos hA _).ne')
      (mul_ne_zero (Real.rpow_pos_of_pos hy _).ne' (Real.exp_ne_zero _)),
    Real.log_div
      (mul_ne_zero
        (mul_ne_zero (Real.rpow_pos_of_pos hpi _).ne' hS.ne')
        (pow_ne_zero 2 hb.ne'))
      (Real.rpow_pos_of_pos hA _).ne',
    Real.log_mul
      (mul_ne_zero (Real.rpow_pos_of_pos hpi _).ne' hS.ne')
      (pow_ne_zero 2 hb.ne'),
    Real.log_mul (Real.rpow_pos_of_pos hpi _).ne' hS.ne',
    Real.log_rpow hpi,
    Real.log_pow,
    Real.log_rpow hA,
    Real.log_mul (Real.rpow_pos_of_pos hy _).ne' (Real.exp_ne_zero _),
    Real.log_rpow hy,
    Real.log_exp,
    Real.log_div hA.ne' hSb.ne',
    Real.log_mul hS.ne' hb.ne']
  ring



theorem d001988
    {S p rho : ℝ} (hS : 0 < S) (hp : 0 < p) (hp1 : p < 1)
    (hrho : 0 < rho) :
    _root_.GD.N0232.N0720.N1052.d001983 S p rho ≤
      8 * _root_.GD.N0232.N0720.N1052.d001985 * S * p ^ 2 * (1 - p) ^ 2 *
        _root_.GD.N0232.N0720.N1051.d001946 rho p := by
  let b : ℝ := p * (1 - p)
  let A : ℝ := _root_.GD.N0232.N0720.N1051.d001938 rho p
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hA : 0 < A := by
    dsimp [A]
    exact _root_.GD.N0232.N0720.N1051.d001940 hrho hp hp1.le
  have hraw := _root_.GD.N0232.N0720.N1052.d001984 hS hp hp1 hrho.le
  rw [_root_.GD.N0232.N0720.N1052.d001987 hA hS hb] at hraw
  have hprofile := _root_.GD.N0232.N0720.N1052.d001964 (div_pos hA (mul_pos hS hb))
  have hfactor :
      0 ≤ 8 * Real.sqrt rho *
        (Real.pi ^ (-(3 : ℝ) / 2) * S * b ^ 2 /
          A ^ ((5 : ℝ) / 2)) := by
    positivity [Real.pi_pos]
  have hbounded := mul_le_mul_of_nonneg_left hprofile hfactor
  calc
    _root_.GD.N0232.N0720.N1052.d001983 S p rho ≤
        8 * Real.sqrt rho *
          (Real.pi ^ (-(3 : ℝ) / 2) * S * b ^ 2 /
            A ^ ((5 : ℝ) / 2) *
              _root_.GD.N0232.N0720.N1052.d001963 (A / (S * b))) := by
      simpa [A, b] using hraw
    _ ≤ 8 * Real.sqrt rho *
          (Real.pi ^ (-(3 : ℝ) / 2) * S * b ^ 2 /
            A ^ ((5 : ℝ) / 2) *
              ((5 : ℝ) / (2 * Real.exp 1)) ^ ((5 : ℝ) / 2)) := by
      nlinarith
    _ = 8 * _root_.GD.N0232.N0720.N1052.d001985 * S * p ^ 2 * (1 - p) ^ 2 *
          _root_.GD.N0232.N0720.N1051.d001946 rho p := by
      unfold _root_.GD.N0232.N0720.N1052.d001985 _root_.GD.N0232.N0720.N1051.d001946
      dsimp [A, b]
      field_simp [(Real.rpow_pos_of_pos hA _).ne']

end

end N1052
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1052.d001964
#print axioms _root_.GD.N0232.N0720.N1052.d001965
#print axioms _root_.GD.N0232.N0720.N1052.d001973
#print axioms _root_.GD.N0232.N0720.N1052.d001980
#print axioms _root_.GD.N0232.N0720.N1052.d001984
#print axioms _root_.GD.N0232.N0720.N1052.d001987
#print axioms _root_.GD.N0232.N0720.N1052.d001988
