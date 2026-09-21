import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1683
noncomputable section

open Complex

def d029048 (z : ℂ) : ℂ :=
  -z ^ 2 + 32 * (3 * z ^ 2 - 1) / (z ^ 2 + 1) ^ 3

def d029049 (z : ℂ) : ℂ := Complex.exp (_root_.GD.N0106.N0428.N0765.N1683.d029048 z)

def d029050 (x : ℝ) : ℝ :=
  Real.exp (-x ^ 2 + 32 * (3 * x ^ 2 - 1) / (x ^ 2 + 1) ^ 3)

def d029051 (x : ℝ) : ℝ :=
  32 * (3 * x ^ 2 - 4) / (x ^ 2 + 4) ^ 3

def d029052 (x : ℝ) : ℂ := if x = 0 then 0 else _root_.GD.N0106.N0428.N0765.N1683.d029049 ((x : ℂ) + Complex.I)

def d029053 (x : ℝ) : ℂ := if x = 0 then 0 else _root_.GD.N0106.N0428.N0765.N1683.d029049 ((x : ℂ) - Complex.I)

theorem d029054 (x : ℝ) :
    32 * (3 * x ^ 2 - 1) / (x ^ 2 + 1) ^ 3 ≤ 8 := by
  have hden : 0 < (x ^ 2 + 1) ^ 3 := by positivity
  apply (div_le_iff₀ hden).mpr
  have hid : (x ^ 2 + 1) ^ 3 - 4 * (3 * x ^ 2 - 1) =
      (x ^ 2 - 1) ^ 2 * (x ^ 2 + 5) := by ring
  have hpos : 0 ≤ (x ^ 2 - 1) ^ 2 * (x ^ 2 + 5) := by positivity
  nlinarith

theorem d029055 (x : ℝ) : _root_.GD.N0106.N0428.N0765.N1683.d029051 x ≤ 1 / 2 := by
  have hden : 0 < (x ^ 2 + 4) ^ 3 := by positivity
  unfold _root_.GD.N0106.N0428.N0765.N1683.d029051
  apply (div_le_iff₀ hden).mpr
  have hid : (x ^ 2 + 4) ^ 3 - 64 * (3 * x ^ 2 - 4) =
      (x ^ 2 - 4) ^ 2 * (x ^ 2 + 20) := by ring
  have hpos : 0 ≤ (x ^ 2 - 4) ^ 2 * (x ^ 2 + 20) := by positivity
  nlinarith

theorem d029056 (x : ℝ) : _root_.GD.N0106.N0428.N0765.N1683.d029049 (x : ℂ) = (_root_.GD.N0106.N0428.N0765.N1683.d029050 x : ℂ) := by
  have he : _root_.GD.N0106.N0428.N0765.N1683.d029048 (x : ℂ) =
      ((-x ^ 2 + 32 * (3 * x ^ 2 - 1) / (x ^ 2 + 1) ^ 3 : ℝ) : ℂ) := by
    unfold _root_.GD.N0106.N0428.N0765.N1683.d029048
    push_cast <;> rfl
  rw [_root_.GD.N0106.N0428.N0765.N1683.d029049, he, ← Complex.ofReal_exp]
  rfl

theorem d029057 (x : ℝ) : 0 < _root_.GD.N0106.N0428.N0765.N1683.d029050 x := Real.exp_pos _

theorem d029058 (x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1683.d029050 x ≤ Real.exp 8 * Real.exp (-x ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := _root_.GD.N0106.N0428.N0765.N1683.d029054 x
  change -x ^ 2 + 32 * (3 * x ^ 2 - 1) / (x ^ 2 + 1) ^ 3 ≤ 8 + -x ^ 2
  linarith

theorem d029059 : _root_.GD.N0106.N0428.N0765.N1683.d029050 1 = Real.exp 7 := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1683.d029050]

theorem d029060 {z : ℂ}
    (hm : z - Complex.I ≠ 0) (hp : z + Complex.I ≠ 0) :
    _root_.GD.N0106.N0428.N0765.N1683.d029048 z = -z ^ 2 - (16 * Complex.I) / (z - Complex.I) ^ 3 +
      (16 * Complex.I) / (z + Complex.I) ^ 3 := by
  have hfactor : z ^ 2 + 1 = (z - Complex.I) * (z + Complex.I) := by
    calc
      _ = z ^ 2 - Complex.I ^ 2 := by norm_num
      _ = _ := by ring
  unfold _root_.GD.N0106.N0428.N0765.N1683.d029048
  rw [hfactor]
  field_simp [hm, hp] <;> ring_nf <;> norm_num [pow_succ] <;> ring



theorem d029061 (x y : ℝ) :
    ((16 * Complex.I) / ((x : ℂ) + (y : ℂ) * Complex.I) ^ 3).re =
      16 * (3 * x ^ 2 * y - y ^ 3) / (x ^ 2 + y ^ 2) ^ 3 := by
  have him : (((x : ℂ) + (y : ℂ) * Complex.I) ^ 3).im =
      3 * x ^ 2 * y - y ^ 3 := by
    simp [pow_succ, Complex.mul_re, Complex.mul_im]
    <;> ring
  simp only [Complex.div_re, map_pow, Complex.normSq_add_mul_I, him]
  norm_num

theorem d029062 {x : ℝ} (hx : x ≠ 0) :
    (_root_.GD.N0106.N0428.N0765.N1683.d029048 ((x : ℂ) + Complex.I)).re = -x ^ 2 + 1 + _root_.GD.N0106.N0428.N0765.N1683.d029051 x := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hm : (x : ℂ) + Complex.I - Complex.I ≠ 0 := by simpa using hxC
  have hp : (x : ℂ) + Complex.I + Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hsquare : (((x : ℂ) + Complex.I) ^ 2).re = x ^ 2 - 1 := by
    simp [pow_two, Complex.mul_re]
    <;> ring
  have hzero : ((16 * Complex.I) / (x : ℂ) ^ 3).re = 0 := by
    simpa using _root_.GD.N0106.N0428.N0765.N1683.d029061 x 0
  have htwo : ((16 * Complex.I) / ((x : ℂ) + 2 * Complex.I) ^ 3).re =
      _root_.GD.N0106.N0428.N0765.N1683.d029051 x := by
    have h := _root_.GD.N0106.N0428.N0765.N1683.d029061 x 2
    norm_num at h
    rw [h]
    unfold _root_.GD.N0106.N0428.N0765.N1683.d029051
    norm_num
    <;> ring
  rw [_root_.GD.N0106.N0428.N0765.N1683.d029060 hm hp, Complex.add_re, Complex.sub_re,
    Complex.neg_re, hsquare]
  rw [show (x : ℂ) + Complex.I - Complex.I = (x : ℂ) by ring,
    show (x : ℂ) + Complex.I + Complex.I = (x : ℂ) + 2 * Complex.I by ring,
    hzero, htwo]
  ring

theorem d029063 {x : ℝ} (hx : x ≠ 0) :
    (_root_.GD.N0106.N0428.N0765.N1683.d029048 ((x : ℂ) - Complex.I)).re = -x ^ 2 + 1 + _root_.GD.N0106.N0428.N0765.N1683.d029051 x := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hm : (x : ℂ) - Complex.I - Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hp : (x : ℂ) - Complex.I + Complex.I ≠ 0 := by simpa using hxC
  have hsquare : (((x : ℂ) - Complex.I) ^ 2).re = x ^ 2 - 1 := by
    simp [pow_two, Complex.mul_re]
    <;> ring
  have hzero : ((16 * Complex.I) / (x : ℂ) ^ 3).re = 0 := by
    simpa using _root_.GD.N0106.N0428.N0765.N1683.d029061 x 0
  have htwo : ((16 * Complex.I) / ((x : ℂ) + (-2) * Complex.I) ^ 3).re =
      -_root_.GD.N0106.N0428.N0765.N1683.d029051 x := by
    have h := _root_.GD.N0106.N0428.N0765.N1683.d029061 x (-2)
    norm_num at h
    rw [neg_mul, h]
    unfold _root_.GD.N0106.N0428.N0765.N1683.d029051
    norm_num
    <;> ring
  rw [_root_.GD.N0106.N0428.N0765.N1683.d029060 hm hp, Complex.add_re, Complex.sub_re,
    Complex.neg_re, hsquare]
  rw [show (x : ℂ) - Complex.I - Complex.I = (x : ℂ) + (-2) * Complex.I by ring,
    show (x : ℂ) - Complex.I + Complex.I = (x : ℂ) by ring,
    htwo, hzero]
  ring

theorem d029064 (x : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1683.d029052 x‖ ≤ Real.exp (3 / 2) * Real.exp (-x ^ 2) := by
  by_cases hx : x = 0
  · simp [_root_.GD.N0106.N0428.N0765.N1683.d029052, hx, (Real.exp_pos (3 / 2)).le]
  · rw [_root_.GD.N0106.N0428.N0765.N1683.d029052, if_neg hx, _root_.GD.N0106.N0428.N0765.N1683.d029049, Complex.norm_exp, _root_.GD.N0106.N0428.N0765.N1683.d029062 hx,
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [_root_.GD.N0106.N0428.N0765.N1683.d029055 x]

theorem d029065 (x : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1683.d029053 x‖ ≤ Real.exp (3 / 2) * Real.exp (-x ^ 2) := by
  by_cases hx : x = 0
  · simp [_root_.GD.N0106.N0428.N0765.N1683.d029053, hx, (Real.exp_pos (3 / 2)).le]
  · rw [_root_.GD.N0106.N0428.N0765.N1683.d029053, if_neg hx, _root_.GD.N0106.N0428.N0765.N1683.d029049, Complex.norm_exp, _root_.GD.N0106.N0428.N0765.N1683.d029063 hx,
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [_root_.GD.N0106.N0428.N0765.N1683.d029055 x]

theorem d029066 : 1 < Real.sqrt Real.pi ∧ Real.sqrt Real.pi < 2 := by
  have hsq := Real.sq_sqrt Real.pi_pos.le
  have hnonneg := Real.sqrt_nonneg Real.pi
  constructor
  · nlinarith [Real.pi_gt_three]
  · nlinarith [Real.pi_lt_four]

theorem d029067 :
    Real.exp 8 * Real.sqrt Real.pi < 6 * Real.exp 7 := by
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hprod : Real.exp 1 * Real.sqrt Real.pi < 6 := by
    calc
      _ < 3 * Real.sqrt Real.pi := mul_lt_mul_of_pos_right Real.exp_one_lt_three hs
      _ < 3 * 2 := mul_lt_mul_of_pos_left _root_.GD.N0106.N0428.N0765.N1683.d029066.2 (by norm_num)
      _ = 6 := by norm_num
  have h8 : Real.exp 8 = Real.exp 1 * Real.exp 7 := by
    rw [← Real.exp_add]
    norm_num
  rw [h8]
  nlinarith [mul_lt_mul_of_pos_right hprod (Real.exp_pos 7)]

theorem d029068 {Bminus Bplus : ℝ}
    (hm : Bminus ≤ Real.exp (3 / 2) * Real.sqrt Real.pi)
    (hp : Bplus ≤ Real.exp (3 / 2) * Real.sqrt Real.pi) :
    (Bminus + Bplus) / (Real.exp (Real.pi / 8) - 1) < 16 * Real.exp (3 / 2) := by
  have hden : Real.pi / 8 ≤ Real.exp (Real.pi / 8) - 1 := by
    linarith [Real.add_one_le_exp (Real.pi / 8)]
  have hdenpos : 0 < Real.exp (Real.pi / 8) - 1 :=
    lt_of_lt_of_le (by positivity) hden
  have hslt : Real.sqrt Real.pi < Real.pi := by
    nlinarith [_root_.GD.N0106.N0428.N0765.N1683.d029066.1, Real.sq_sqrt Real.pi_pos.le,
      sq_nonneg (Real.sqrt Real.pi - 1)]
  have hnum := mul_lt_mul_of_pos_left hslt (by positivity : 0 < 2 * Real.exp (3 / 2))
  have hscale := mul_le_mul_of_nonneg_left hden
    (by positivity : 0 ≤ 16 * Real.exp (3 / 2))
  apply (div_lt_iff₀ hdenpos).mpr
  nlinarith

theorem d029069 : 16 * Real.exp (3 / 2) < 10 * Real.exp 7 := by
  have hlarge : 2 < Real.exp (11 / 2) :=
    Real.exp_one_gt_two.trans (Real.exp_lt_exp.mpr (by norm_num))
  have h7 : Real.exp 7 = Real.exp (3 / 2) * Real.exp (11 / 2) := by
    rw [← Real.exp_add]
    norm_num
  rw [h7]
  nlinarith [Real.exp_pos (3 / 2),
    mul_lt_mul_of_pos_left hlarge (Real.exp_pos (3 / 2))]




theorem d029070 {I T Bminus Bplus : ℝ}
    (hI : I ≤ Real.exp 8 * Real.sqrt Real.pi)
    (hT : 16 * Real.exp 7 ≤ T)
    (hm : Bminus ≤ Real.exp (3 / 2) * Real.sqrt Real.pi)
    (hp : Bplus ≤ Real.exp (3 / 2) * Real.sqrt Real.pi) :
    (Bminus + Bplus) / (Real.exp (Real.pi / 8) - 1) < |I - T| := by
  have hI' : I < 6 * Real.exp 7 := hI.trans_lt _root_.GD.N0106.N0428.N0765.N1683.d029067
  have hgap : 10 * Real.exp 7 < T - I := by linarith
  calc
    _ < 16 * Real.exp (3 / 2) := _root_.GD.N0106.N0428.N0765.N1683.d029068 hm hp
    _ < 10 * Real.exp 7 := _root_.GD.N0106.N0428.N0765.N1683.d029069
    _ < T - I := hgap
    _ ≤ |I - T| := by simpa only [abs_sub_comm] using le_abs_self (T - I)

end
end GD.N0106.N0428.N0765.N1683

#print axioms _root_.GD.N0106.N0428.N0765.N1683.d029054
#print axioms _root_.GD.N0106.N0428.N0765.N1683.d029055
#print axioms _root_.GD.N0106.N0428.N0765.N1683.d029056
#print axioms _root_.GD.N0106.N0428.N0765.N1683.d029060
#print axioms _root_.GD.N0106.N0428.N0765.N1683.d029062
#print axioms _root_.GD.N0106.N0428.N0765.N1683.d029063
#print axioms _root_.GD.N0106.N0428.N0765.N1683.d029064
#print axioms _root_.GD.N0106.N0428.N0765.N1683.d029065
#print axioms _root_.GD.N0106.N0428.N0765.N1683.d029070
