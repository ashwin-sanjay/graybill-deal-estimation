import GD.Module1015
import GD.Module0873















open Set

namespace GD
namespace N0232
namespace N0720
namespace N1152

noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1435
open _root_.GD.N0232.N0720.N1492
open _root_.GD.N0232.N0720.N1151

private abbrev d016189 : ℝ := (1 : ℝ) / 2


def d016190 (r F q : ℝ) : ℝ :=
  r * (1 - q) + (1 - r) * q + F * q * (1 - q)


def d016191 (q : ℝ) (p : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  q * (1 - q) / (2 * Real.pi) *
    (p.1 * (1 - p.1) * p.2) ^ (-_root_.GD.N0232.N0720.N1152.d016189) *
    _root_.GD.N0232.N0720.N1152.d016190 p.1 p.2 q ^ (-((3 : ℝ) / 2))

theorem d016192 (r F q : ℝ) :
    _root_.GD.N0232.N0720.N1152.d016190 r F q = _root_.GD.N0232.N0720.N1492.d016123 r F q := by
  unfold _root_.GD.N0232.N0720.N1152.d016190 _root_.GD.N0232.N0720.N1492.d016123
  ring

theorem d016193 :
    Real.Gamma ((3 : ℝ) / 2) = Real.sqrt Real.pi / 2 := by
  rw [show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num]
  rw [Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  rw [Real.Gamma_one_half_eq]
  ring

theorem d016194 :
    _root_.GD.N0116.d006506 _root_.GD.N0232.N0720.N1152.d016189 _root_.GD.N0232.N0720.N1152.d016189 *
        Real.Gamma ((3 : ℝ) / 2) * (2 : ℝ) ^ ((3 : ℝ) / 2) =
      1 / (2 * Real.pi) := by
  have hhalf : (0 : ℝ) < _root_.GD.N0232.N0720.N1152.d016189 := by norm_num
  have hhalfPow : _root_.GD.N0232.N0720.N1152.d016189 ^ _root_.GD.N0232.N0720.N1152.d016189 * _root_.GD.N0232.N0720.N1152.d016189 ^ _root_.GD.N0232.N0720.N1152.d016189 = _root_.GD.N0232.N0720.N1152.d016189 := by
    rw [← Real.rpow_add hhalf]
    norm_num [_root_.GD.N0232.N0720.N1152.d016189]
  have hsqrt : Real.sqrt Real.pi ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ ((3 : ℝ) / 2) ≠ 0 := by positivity
  have hsqrtSq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := by
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  unfold _root_.GD.N0116.d006506
  rw [Real.Gamma_one_half_eq, _root_.GD.N0232.N0720.N1152.d016193, hhalfPow]
  field_simp [hsqrt, hpow]
  nlinarith

theorem d016195 :
    Real.Gamma ((5 : ℝ) / 2) =
      (3 / 2 : ℝ) * Real.Gamma ((3 : ℝ) / 2) := by
  rw [show (5 : ℝ) / 2 = 3 / 2 + 1 by norm_num]
  rw [Real.Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0)]

theorem d016196 :
    _root_.GD.N0116.d006506 _root_.GD.N0232.N0720.N1152.d016189 _root_.GD.N0232.N0720.N1152.d016189 *
        Real.Gamma ((5 : ℝ) / 2) * (2 : ℝ) ^ ((5 : ℝ) / 2) =
      3 / (2 * Real.pi) := by
  have hpow :
      (2 : ℝ) ^ ((5 : ℝ) / 2) =
        (2 : ℝ) ^ ((3 : ℝ) / 2) * 2 := by
    rw [show (5 : ℝ) / 2 = (3 : ℝ) / 2 + 1 by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  rw [_root_.GD.N0232.N0720.N1152.d016195, hpow]
  calc
    _root_.GD.N0116.d006506 _root_.GD.N0232.N0720.N1152.d016189 _root_.GD.N0232.N0720.N1152.d016189 *
          ((3 / 2 : ℝ) * Real.Gamma ((3 : ℝ) / 2)) *
          ((2 : ℝ) ^ ((3 : ℝ) / 2) * 2) =
        3 * (_root_.GD.N0116.d006506 _root_.GD.N0232.N0720.N1152.d016189 _root_.GD.N0232.N0720.N1152.d016189 *
          Real.Gamma ((3 : ℝ) / 2) *
          (2 : ℝ) ^ ((3 : ℝ) / 2)) := by ring
    _ = 3 / (2 * Real.pi) := by
      rw [_root_.GD.N0232.N0720.N1152.d016194]
      ring

theorem d016197 {x : ℝ} (hx : 0 < x) :
    x ^ _root_.GD.N0232.N0720.N1152.d016189 = x * x ^ (-_root_.GD.N0232.N0720.N1152.d016189) := by
  calc
    x ^ _root_.GD.N0232.N0720.N1152.d016189 = x ^ ((1 : ℝ) + (-_root_.GD.N0232.N0720.N1152.d016189)) := by
      congr 1
      norm_num [_root_.GD.N0232.N0720.N1152.d016189]
    _ = x ^ (1 : ℝ) * x ^ (-_root_.GD.N0232.N0720.N1152.d016189) := by rw [Real.rpow_add hx]
    _ = x * x ^ (-_root_.GD.N0232.N0720.N1152.d016189) := by rw [Real.rpow_one]

theorem d016198 {x : ℝ} (hx : 0 < x) :
    x ^ (-((5 : ℝ) / 2)) =
      (1 / x) * x ^ (-((3 : ℝ) / 2)) := by
  rw [one_div, ← Real.rpow_neg_one]
  rw [← Real.rpow_add hx]
  congr 1
  norm_num

theorem d016199 {x : ℝ} (hx : 0 < x) :
    (x / 2) ^ (-((5 : ℝ) / 2)) =
      (2 : ℝ) ^ ((5 : ℝ) / 2) *
        x ^ (-((5 : ℝ) / 2)) := by
  rw [Real.div_rpow hx.le (by norm_num : (0 : ℝ) ≤ 2)]
  rw [div_eq_mul_inv, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [inv_inv]
  ring

theorem d016200 {r F : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hF : 0 < F) :
    r ^ (-_root_.GD.N0232.N0720.N1152.d016189) * (1 - r) ^ (-_root_.GD.N0232.N0720.N1152.d016189) * F ^ _root_.GD.N0232.N0720.N1152.d016189 =
      F * (r * (1 - r) * F) ^ (-_root_.GD.N0232.N0720.N1152.d016189) := by
  have hprod :
      r ^ (-_root_.GD.N0232.N0720.N1152.d016189) * (1 - r) ^ (-_root_.GD.N0232.N0720.N1152.d016189) * F ^ (-_root_.GD.N0232.N0720.N1152.d016189) =
        (r * (1 - r) * F) ^ (-_root_.GD.N0232.N0720.N1152.d016189) := by
    rw [Real.mul_rpow
        (mul_nonneg hr0.le (sub_pos.mpr hr1).le) hF.le,
      Real.mul_rpow hr0.le (sub_pos.mpr hr1).le]
  rw [_root_.GD.N0232.N0720.N1152.d016197 hF]
  rw [← hprod]
  ring


theorem d016201
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    {p : _root_.GD.N0232.N0720.N1436.d013217} (hp : p ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1436.d013273 2 2 q p =
      (3 * p.2 * q * (1 - q) /
        _root_.GD.N0232.N0720.N1152.d016190 p.1 p.2 q) *
      _root_.GD.N0232.N0720.N1152.d016191 q p := by
  have hQ : 0 < _root_.GD.N0232.N0720.N1152.d016190 p.1 p.2 q := by
    unfold _root_.GD.N0232.N0720.N1152.d016190
    exact add_pos
      (add_pos
        (mul_pos hp.1.1 (sub_pos.mpr hq.2))
        (mul_pos (sub_pos.mpr hp.1.2) hq.1))
      (mul_pos (mul_pos hp.2 hq.1) (sub_pos.mpr hq.2))
  have hden :
      _root_.GD.N0232.N0720.N1152.d016189 * q * (1 - p.1) + _root_.GD.N0232.N0720.N1152.d016189 * (1 - q) * p.1 +
          p.2 * q * (1 - q) / 2 =
        _root_.GD.N0232.N0720.N1152.d016190 p.1 p.2 q / 2 := by
    unfold _root_.GD.N0232.N0720.N1152.d016190
    norm_num [_root_.GD.N0232.N0720.N1152.d016189]
    ring
  have hang := _root_.GD.N0232.N0720.N1152.d016200 hp.1.1 hp.1.2 hp.2
  have hQsplit := _root_.GD.N0232.N0720.N1152.d016198 hQ
  rw [_root_.GD.N0232.N0720.N1435.d013489
    (by norm_num) (by norm_num) hq.1 hq.2 hp]
  rw [show _root_.GD.N0232.N0720.N1436.d013207 2 = _root_.GD.N0232.N0720.N1152.d016189 by
      norm_num [_root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1152.d016189],
    show _root_.GD.N0232.N0720.N1436.d013208 2 = _root_.GD.N0232.N0720.N1152.d016189 by
      norm_num [_root_.GD.N0232.N0720.N1436.d013208, _root_.GD.N0232.N0720.N1152.d016189]]
  change _root_.GD.N0116.d006511 _root_.GD.N0232.N0720.N1152.d016189 _root_.GD.N0232.N0720.N1152.d016189 q p = _
  calc
    _root_.GD.N0116.d006511 _root_.GD.N0232.N0720.N1152.d016189 _root_.GD.N0232.N0720.N1152.d016189 q p =
        (_root_.GD.N0116.d006506 _root_.GD.N0232.N0720.N1152.d016189 _root_.GD.N0232.N0720.N1152.d016189 *
          Real.Gamma ((5 : ℝ) / 2) * (2 : ℝ) ^ ((5 : ℝ) / 2)) *
          (q ^ 2 * (1 - q) ^ 2) *
          (p.1 ^ (-_root_.GD.N0232.N0720.N1152.d016189) * (1 - p.1) ^ (-_root_.GD.N0232.N0720.N1152.d016189) * p.2 ^ _root_.GD.N0232.N0720.N1152.d016189) *
          _root_.GD.N0232.N0720.N1152.d016190 p.1 p.2 q ^ (-((5 : ℝ) / 2)) := by
      unfold _root_.GD.N0116.d006511
        _root_.GD.N0116.d006507
        _root_.GD.N0116.d006508 _root_.GD.N0116.d006509
      rw [hden]
      norm_num [_root_.GD.N0232.N0720.N1152.d016189]
      rw [_root_.GD.N0232.N0720.N1152.d016199 hQ]
      ring
    _ = (3 / (2 * Real.pi)) *
          (q ^ 2 * (1 - q) ^ 2) *
          (p.1 ^ (-_root_.GD.N0232.N0720.N1152.d016189) * (1 - p.1) ^ (-_root_.GD.N0232.N0720.N1152.d016189) * p.2 ^ _root_.GD.N0232.N0720.N1152.d016189) *
          _root_.GD.N0232.N0720.N1152.d016190 p.1 p.2 q ^ (-((5 : ℝ) / 2)) := by
      rw [_root_.GD.N0232.N0720.N1152.d016196]
    _ = (3 * p.2 * q * (1 - q) /
          _root_.GD.N0232.N0720.N1152.d016190 p.1 p.2 q) *
          _root_.GD.N0232.N0720.N1152.d016191 q p := by
      unfold _root_.GD.N0232.N0720.N1152.d016191
      rw [hang, hQsplit]
      ring



theorem d016202
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    {v : _root_.GD.N0232.N0720.N1151.d016145} (hv : v ∈ _root_.GD.N0232.N0720.N1151.d016146) :
    _root_.GD.N0232.N0720.N1436.d013273 2 2 q (_root_.GD.N0232.N0720.N1151.d016153 q v) =
      3 * _root_.GD.N0232.N0720.N1151.d016148 v * _root_.GD.N0232.N0720.N1152.d016191 q (_root_.GD.N0232.N0720.N1151.d016153 q v) := by
  calc
    _root_.GD.N0232.N0720.N1436.d013273 2 2 q (_root_.GD.N0232.N0720.N1151.d016153 q v) =
        (3 * (_root_.GD.N0232.N0720.N1151.d016153 q v).2 * q * (1 - q) /
          _root_.GD.N0232.N0720.N1152.d016190 (_root_.GD.N0232.N0720.N1151.d016153 q v).1 (_root_.GD.N0232.N0720.N1151.d016153 q v).2 q) *
          _root_.GD.N0232.N0720.N1152.d016191 q (_root_.GD.N0232.N0720.N1151.d016153 q v) :=
      _root_.GD.N0232.N0720.N1152.d016201
        hq (_root_.GD.N0232.N0720.N1151.d016169 hq hv)
    _ = (3 * _root_.GD.N0232.N0720.N1151.d016152 q v * q * (1 - q) /
          _root_.GD.N0232.N0720.N1492.d016123
            (_root_.GD.N0232.N0720.N1151.d016153 q v).1 (_root_.GD.N0232.N0720.N1151.d016153 q v).2 q) *
          _root_.GD.N0232.N0720.N1152.d016191 q (_root_.GD.N0232.N0720.N1151.d016153 q v) := by
      rw [_root_.GD.N0232.N0720.N1152.d016192]
      rfl
    _ = 3 * _root_.GD.N0232.N0720.N1151.d016148 v *
          _root_.GD.N0232.N0720.N1152.d016191 q (_root_.GD.N0232.N0720.N1151.d016153 q v) := by
      rw [_root_.GD.N0232.N0720.N1151.d016185 hq hv]



theorem d016203
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    {v : _root_.GD.N0232.N0720.N1151.d016145} (hv : v ∈ _root_.GD.N0232.N0720.N1151.d016146)
    (commonFactor : ℝ) :
    _root_.GD.N0232.N0720.N1436.d013273 2 2 q (_root_.GD.N0232.N0720.N1151.d016153 q v) * commonFactor =
      3 * _root_.GD.N0232.N0720.N1151.d016148 v *
        (_root_.GD.N0232.N0720.N1152.d016191 q (_root_.GD.N0232.N0720.N1151.d016153 q v) * commonFactor) := by
  rw [_root_.GD.N0232.N0720.N1152.d016202 hq hv]
  ring

end

end N1152
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1152.d016194
#print axioms _root_.GD.N0232.N0720.N1152.d016196
#print axioms _root_.GD.N0232.N0720.N1152.d016201
#print axioms _root_.GD.N0232.N0720.N1152.d016203
