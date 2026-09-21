import GD.Module0869
import GD.Module0279












open MeasureTheory Set

namespace GD.N0232.N0720.N1271

noncomputable section

open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1290

def d013403 (t : ℝ) : ℝ := t * (1 - t)

def d013404 (x : _root_.GD.N0232.N0720.N1436.d013217) (t : _root_.GD.N0232.N0720.N1290.d004131) : ℝ :=
  x.1 * (1 - (t : ℝ)) + (1 - x.1) * (t : ℝ) + x.2 * _root_.GD.N0232.N0720.N1271.d013403 t

theorem d013405 :
    Continuous (fun p : _root_.GD.N0232.N0720.N1436.d013217 × _root_.GD.N0232.N0720.N1290.d004131 ↦ _root_.GD.N0232.N0720.N1271.d013404 p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1271.d013404 _root_.GD.N0232.N0720.N1271.d013403
  fun_prop

theorem d013406 {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) (t : _root_.GD.N0232.N0720.N1290.d004131) :
    min x.1 (1 - x.1) ≤ _root_.GD.N0232.N0720.N1271.d013404 x t := by
  have h1 := mul_le_mul_of_nonneg_right (min_le_left x.1 (1 - x.1))
    (sub_nonneg.mpr t.2.2)
  have h2 := mul_le_mul_of_nonneg_right (min_le_right x.1 (1 - x.1)) t.2.1
  have h3 : 0 ≤ x.2 * _root_.GD.N0232.N0720.N1271.d013403 t :=
    mul_nonneg hx.2.le (mul_nonneg t.2.1 (sub_nonneg.mpr t.2.2))
  unfold _root_.GD.N0232.N0720.N1271.d013404
  nlinarith

theorem d013407 {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) (t : _root_.GD.N0232.N0720.N1290.d004131) : 0 < _root_.GD.N0232.N0720.N1271.d013404 x t :=
  (lt_min hx.1.1 (sub_pos.mpr hx.1.2)).trans_le (_root_.GD.N0232.N0720.N1271.d013406 hx t)

theorem d013408 {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < _root_.GD.N0232.N0720.N1271.d013403 t := mul_pos ht0 (sub_pos.mpr ht1)


theorem d013409 (x : _root_.GD.N0232.N0720.N1436.d013217)
    (t : _root_.GD.N0232.N0720.N1290.d004131) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    _root_.GD.N0232.N0720.N1271.d013403 t * _root_.GD.N0232.N0720.N1436.d013267 2 2 t x = _root_.GD.N0232.N0720.N1271.d013404 x t := by
  simp only [_root_.GD.N0232.N0720.N1271.d013403, _root_.GD.N0232.N0720.N1436.d013267, _root_.GD.N0232.N0720.N1271.d013404]
  norm_num
  field_simp [ht0.ne', (sub_pos.mpr ht1).ne']
  ring

theorem d013410 (t : _root_.GD.N0232.N0720.N1290.d004131)
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    _root_.GD.N0232.N0720.N1436.d013270 2 2 t = (_root_.GD.N0232.N0720.N1271.d013403 t) ^ (-(1 / 2 : ℝ)) := by
  unfold _root_.GD.N0232.N0720.N1436.d013270 _root_.GD.N0232.N0720.N1436.d013207 _root_.GD.N0232.N0720.N1436.d013208 _root_.GD.N0232.N0720.N1271.d013403
  norm_num
  rw [Real.mul_rpow ht0.le (sub_pos.mpr ht1).le]
  ring



def d013411 (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  _root_.GD.N0232.N0720.N1436.d013271 2 2 * _root_.GD.N0232.N0720.N1436.d013269 2 2 x *
    (2 : ℝ) ^ (5 / 2 : ℝ) * Real.Gamma (5 / 2)

theorem d013412 {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) : 0 < _root_.GD.N0232.N0720.N1271.d013411 x := by
  unfold _root_.GD.N0232.N0720.N1271.d013411
  exact mul_pos (mul_pos
    (mul_pos (_root_.GD.N0232.N0720.N1436.d013284 (by omega) (by omega)) (_root_.GD.N0232.N0720.N1436.d013282 hx))
    (Real.rpow_pos_of_pos (by norm_num) _)) (Real.Gamma_pos_of_pos (by norm_num))


theorem d013413
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218)
    (t : _root_.GD.N0232.N0720.N1290.d004131) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    _root_.GD.N0232.N0720.N1436.d013273 2 2 t x = _root_.GD.N0232.N0720.N1271.d013411 x *
      (_root_.GD.N0232.N0720.N1271.d013403 t) ^ 2 * (_root_.GD.N0232.N0720.N1271.d013404 x t) ^ (-(5 / 2 : ℝ)) := by
  have hv := _root_.GD.N0232.N0720.N1271.d013408 ht0 ht1
  have hp := _root_.GD.N0232.N0720.N1271.d013407 hx t
  have hq : _root_.GD.N0232.N0720.N1436.d013210 2 2 = (5 / 2 : ℝ) := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013210, _root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208, _root_.GD.N0232.N0720.N1436.d013209]
  have hrate : 1 / _root_.GD.N0232.N0720.N1436.d013268 2 2 t x =
      2 * _root_.GD.N0232.N0720.N1271.d013403 t / _root_.GD.N0232.N0720.N1271.d013404 x t := by
    unfold _root_.GD.N0232.N0720.N1436.d013268
    have h := _root_.GD.N0232.N0720.N1271.d013409 x t ht0 ht1
    have hr := _root_.GD.N0232.N0720.N1436.d013280 (by omega : 2 ≤ 2) (by omega : 2 ≤ 2) ht0 ht1 hx
    field_simp [hp.ne', hr.ne']
    nlinarith
  have hvpow : (_root_.GD.N0232.N0720.N1271.d013403 t) ^ (-(1 / 2 : ℝ)) *
      (_root_.GD.N0232.N0720.N1271.d013403 t) ^ (5 / 2 : ℝ) = (_root_.GD.N0232.N0720.N1271.d013403 t) ^ 2 := by
    rw [← Real.rpow_add hv]
    norm_num
  unfold _root_.GD.N0232.N0720.N1436.d013273 _root_.GD.N0232.N0720.N1271.d013411
  rw [hq, _root_.GD.N0232.N0720.N1271.d013410 t ht0 ht1, hrate,
    Real.div_rpow (mul_pos (by norm_num) hv).le hp.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hv.le,
    Real.rpow_neg hp.le]
  rw [div_eq_mul_inv]
  calc
    _ = (_root_.GD.N0232.N0720.N1436.d013271 2 2 * _root_.GD.N0232.N0720.N1436.d013269 2 2 x *
        (2 : ℝ) ^ (5 / 2 : ℝ) * Real.Gamma (5 / 2)) *
        ((_root_.GD.N0232.N0720.N1271.d013403 t) ^ (-(1 / 2 : ℝ)) * (_root_.GD.N0232.N0720.N1271.d013403 t) ^ (5 / 2 : ℝ)) *
        ((_root_.GD.N0232.N0720.N1271.d013404 x t) ^ (5 / 2 : ℝ))⁻¹ := by ring
    _ = _ := by rw [hvpow]

end
end GD.N0232.N0720.N1271

#print axioms _root_.GD.N0232.N0720.N1271.d013406
#print axioms _root_.GD.N0232.N0720.N1271.d013413
