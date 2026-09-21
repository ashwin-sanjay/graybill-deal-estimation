import GD.Module0557
import GD.Module0337

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0016
noncomputable section

open _root_.GD.N0232.N0720.N1089
open _root_.GD.N0082.N0334
open _root_.GD.N0149.N0432
open _root_.GD.N0013

def d008306 (r x : ℝ) : ℝ :=
  ((2 * x - r * (1 + x ^ 2)) / ((1 + x ^ 2) * (1 - r * x))) ^ 2

def d008307 (r x : ℝ) : ℝ :=
  (_root_.GD.N0016.d008306 r x + _root_.GD.N0016.d008306 r (-x)) / 2

theorem d008308 {r x : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1)
    (hx : x ∈ Icc (-1 : ℝ) 1) : 0 < 1 - r * x := by
  have hr' : |r| < 1 := abs_lt.mpr hr
  have hx' : |x| ≤ 1 := abs_le.mpr hx
  have hm : |r * x| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hx' (abs_nonneg r)).trans_lt (by simpa using hr')
  exact sub_pos.mpr ((le_abs_self _).trans_lt hm)

theorem d008309 {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    ContinuousOn (_root_.GD.N0016.d008306 r) (Icc (-1 : ℝ) 1) := by
  unfold _root_.GD.N0016.d008306
  apply ContinuousOn.pow
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro x hx
    exact mul_ne_zero (by positivity) (_root_.GD.N0016.d008308 hr hx).ne'

theorem d008310 {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    IntervalIntegrable (_root_.GD.N0016.d008306 r) volume (-1) 1 := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using
    _root_.GD.N0016.d008309 hr

theorem d008311 {t x : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    ((_root_.GD.N0232.N0720.N1089.d003092 (x / 2 + 1 / 2) - t) /
      _root_.GD.N0082.N0334.d008256 t (x / 2 + 1 / 2)) ^ 2 = _root_.GD.N0016.d008306 (2 * t - 1) x := by
  have hr : 2 * t - 1 ∈ Ioo (-1 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  have hd := _root_.GD.N0016.d008308 hr hx
  have hquad : (x / 2 + 1 / 2) ^ 2 + (1 - (x / 2 + 1 / 2)) ^ 2 =
      (1 + x ^ 2) / 2 := by ring
  have hden : _root_.GD.N0082.N0334.d008256 t (x / 2 + 1 / 2) = (1 - (2 * t - 1) * x) / 2 := by
    unfold _root_.GD.N0082.N0334.d008256
    ring
  unfold _root_.GD.N0232.N0720.N1089.d003092 _root_.GD.N0016.d008306
  rw [hquad, hden]
  congr 1
  field_simp [hd.ne', (by positivity : (1 + x ^ 2) ≠ 0)]
  ring

theorem d008312 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0082.N0334.d008258 _root_.GD.N0232.N0720.N1089.d003092 t =
      (∫ x in (-1 : ℝ)..1, _root_.GD.N0016.d008306 (2 * t - 1) x) / 2 := by
  have h := intervalIntegral.integral_comp_div_add
    (a := (-1 : ℝ)) (b := 1)
    (fun u => ((_root_.GD.N0232.N0720.N1089.d003092 u - t) / _root_.GD.N0082.N0334.d008256 t u) ^ 2)
    (c := (2 : ℝ)) (by norm_num) (1 / 2)
  norm_num only [neg_div, one_div, neg_add_cancel, add_halves, smul_eq_mul] at h
  have he : (∫ x in (-1 : ℝ)..1,
      ((_root_.GD.N0232.N0720.N1089.d003092 (x / 2 + 1 / 2) - t) / _root_.GD.N0082.N0334.d008256 t (x / 2 + 1 / 2)) ^ 2) =
      ∫ x in (-1 : ℝ)..1, _root_.GD.N0016.d008306 (2 * t - 1) x := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply _root_.GD.N0016.d008311 ht
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
  rw [he] at h
  rw [_root_.GD.N0082.N0334.d008258, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  linarith

theorem d008313 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0082.N0334.d008258 _root_.GD.N0232.N0720.N1089.d003092 t = ∫ x in (0 : ℝ)..1, _root_.GD.N0016.d008307 (2 * t - 1) x := by
  have hr : 2 * t - 1 ∈ Ioo (-1 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  have hi := _root_.GD.N0016.d008310 hr
  have hiL : IntervalIntegrable (_root_.GD.N0016.d008306 (2 * t - 1)) volume (-1) 0 :=
    hi.mono_set (by simp only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0),
      uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact Icc_subset_Icc le_rfl (by norm_num))
  have hiR : IntervalIntegrable (_root_.GD.N0016.d008306 (2 * t - 1)) volume 0 1 :=
    hi.mono_set (by simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact Icc_subset_Icc (by norm_num) le_rfl)
  have hiN : IntervalIntegrable (fun x => _root_.GD.N0016.d008306 (2 * t - 1) (-x)) volume 0 1 := by
    simpa using ((IntervalIntegrable.iff_comp_neg).mp hiL).symm
  have hsum := intervalIntegral.integral_add_adjacent_intervals hiL hiR
  have hneg := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1)
    (_root_.GD.N0016.d008306 (2 * t - 1))
  norm_num only [neg_zero] at hneg
  rw [_root_.GD.N0016.d008312 ht]
  unfold _root_.GD.N0016.d008307
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hiR hiN, hneg, ← hsum]
  ring

def d008314 (q x : ℝ) : ℝ :=
  (q * (1 - q) ^ 2 / (1 + q) ^ 2) * ((1 + q * x ^ 2) / (1 - q * x ^ 2) ^ 2) +
    (4 * q * (1 - q) ^ 2 / (1 + q) ^ 3) * (1 - q * x ^ 2)⁻¹ +
    (-4 * (1 - q) / (1 + q) ^ 2) * ((1 + x ^ 2) ^ 2)⁻¹ +
    (4 * (2 * q ^ 2 - q + 1) / (1 + q) ^ 3) * (1 + x ^ 2)⁻¹

theorem d008315 {r x : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0016.d008307 r x = _root_.GD.N0016.d008314 (r ^ 2) x := by
  have hxm : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hxN : -x ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hminus := _root_.GD.N0016.d008308 hr hxm
  have hplus : 0 < 1 + r * x := by simpa using _root_.GD.N0016.d008308 hr hxN
  have hprod : 0 < 1 - r ^ 2 * x ^ 2 := by nlinarith [mul_pos hminus hplus]
  have hrp : (1 + r ^ 2) ≠ 0 := by positivity
  have hxp : (1 + x ^ 2) ≠ 0 := by positivity
  have heq : 1 - r ^ 2 * x ^ 2 = (1 - r * x) * (1 + r * x) := by ring
  have hm2 : 1 - x * r * 2 + x ^ 2 * r ^ 2 ≠ 0 := by
    rw [show 1 - x * r * 2 + x ^ 2 * r ^ 2 = (1 - r * x) ^ 2 by ring]
    exact pow_ne_zero 2 hminus.ne'
  have hp2 : 1 + x * r * 2 + x ^ 2 * r ^ 2 ≠ 0 := by
    rw [show 1 + x * r * 2 + x ^ 2 * r ^ 2 = (1 + r * x) ^ 2 by ring]
    exact pow_ne_zero 2 hplus.ne'
  have hprod2 : 1 - x ^ 2 * r ^ 2 * 2 + x ^ 4 * r ^ 4 ≠ 0 := by
    rw [show 1 - x ^ 2 * r ^ 2 * 2 + x ^ 4 * r ^ 4 = (1 - r ^ 2 * x ^ 2) ^ 2 by ring]
    exact pow_ne_zero 2 hprod.ne'
  unfold _root_.GD.N0016.d008307 _root_.GD.N0016.d008306 _root_.GD.N0016.d008314
  simp only [neg_sq, mul_neg, sub_neg_eq_add, heq, div_pow, mul_pow]
  field_simp [hminus.ne', hplus.ne', hrp, hxp]
  ring_nf
  field_simp [hm2, hp2, hprod2]
  ring

def d008316 (q j : ℝ) : ℝ :=
  -(1 - q) ^ 2 / (1 + q) ^ 2 +
    (Real.pi / 2) * (5 * q ^ 2 - 2 * q + 1) / (1 + q) ^ 3 +
    (4 * q * (1 - q) ^ 2 / (1 + q) ^ 3) * j

theorem d008317 {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∫ x in (0 : ℝ)..1, _root_.GD.N0016.d008314 q x) = _root_.GD.N0016.d008316 q (_root_.GD.N0013.d005011 q) := by
  let A := q * (1 - q) ^ 2 / (1 + q) ^ 2
  let B := 4 * q * (1 - q) ^ 2 / (1 + q) ^ 3
  let C := -4 * (1 - q) / (1 + q) ^ 2
  let D := 4 * (2 * q ^ 2 - q + 1) / (1 + q) ^ 3
  have hA := (_root_.GD.N0013.d005014 hq0 hq1).const_mul A
  have hB := (_root_.GD.N0013.d005013 hq0 hq1).const_mul B
  have hC := _root_.GD.N0013.d005019.const_mul C
  have hD := _root_.GD.N0013.d005018.const_mul D
  change (∫ x in (0 : ℝ)..1,
    A * ((1 + q * x ^ 2) / (1 - q * x ^ 2) ^ 2) + B * (1 - q * x ^ 2)⁻¹ +
      C * ((1 + x ^ 2) ^ 2)⁻¹ + D * (1 + x ^ 2)⁻¹) = _
  rw [intervalIntegral.integral_add ((hA.add hB).add hC) hD,
    intervalIntegral.integral_add (hA.add hB) hC, intervalIntegral.integral_add hA hB]
  simp only [intervalIntegral.integral_const_mul]
  rw [_root_.GD.N0013.d005015 hq0 hq1,
    _root_.GD.N0013.d005021, _root_.GD.N0013.d005020]
  change A * (1 / (1 - q)) + B * _root_.GD.N0013.d005011 q + C * (1 / 4 + Real.pi / 8) + D * (Real.pi / 4) = _
  dsimp [A, B, C, D, _root_.GD.N0016.d008316]
  field_simp [(sub_pos.mpr hq1).ne', (by positivity : (1 + q) ≠ 0)]
  ring

theorem d008318 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0082.N0334.d008258 _root_.GD.N0232.N0720.N1089.d003092 t = _root_.GD.N0016.d008316 ((2 * t - 1) ^ 2) (_root_.GD.N0013.d005011 ((2 * t - 1) ^ 2)) := by
  have hr : 2 * t - 1 ∈ Ioo (-1 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  have hq : (2 * t - 1) ^ 2 < 1 := by
    nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  rw [_root_.GD.N0016.d008313 ht]
  calc
    _ = ∫ x in (0 : ℝ)..1, _root_.GD.N0016.d008314 ((2 * t - 1) ^ 2) x := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply _root_.GD.N0016.d008315 hr
      simpa only [uIcc_of_le zero_le_one] using hx
    _ = _ := _root_.GD.N0016.d008317 (sq_nonneg _) hq

theorem d008319 {q j : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hj : j ≤ 1 + q / (3 * (1 - q))) : _root_.GD.N0016.d008316 q j < Real.pi / 4 := by
  have hplus : 0 < 1 + q := by positivity
  have hminus : 0 < 1 - q := sub_pos.mpr hq1
  have hcoef : 0 ≤ 4 * q * (1 - q) ^ 2 / (1 + q) ^ 3 := by positivity
  have hbound : _root_.GD.N0016.d008316 q j ≤ _root_.GD.N0016.d008316 q (1 + q / (3 * (1 - q))) := by
    unfold _root_.GD.N0016.d008316
    linarith [mul_le_mul_of_nonneg_left hj hcoef]
  have hid : Real.pi / 4 - _root_.GD.N0016.d008316 q (1 + q / (3 * (1 - q))) =
      (1 - q) / (1 + q) ^ 3 *
        ((1 - Real.pi / 4) + (3 * Real.pi / 2 - 4) * q +
          (5 / 3 - Real.pi / 4) * q ^ 2) := by
    unfold _root_.GD.N0016.d008316
    field_simp [hplus.ne', hminus.ne']
    ring
  have hconst : 0 < 1 - Real.pi / 4 := by linarith [Real.pi_lt_four]
  have hlinear : 0 ≤ 3 * Real.pi / 2 - 4 := by linarith [Real.pi_gt_three]
  have hquadratic : 0 ≤ 5 / 3 - Real.pi / 4 := by linarith [Real.pi_lt_four]
  have hpoly : 0 < (1 - Real.pi / 4) + (3 * Real.pi / 2 - 4) * q +
      (5 / 3 - Real.pi / 4) * q ^ 2 :=
    add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg hconst (mul_nonneg hlinear hq0))
      (mul_nonneg hquadratic (sq_nonneg q))
  have hgap : 0 < Real.pi / 4 - _root_.GD.N0016.d008316 q (1 + q / (3 * (1 - q))) := by
    rw [hid]
    exact mul_pos (div_pos hminus (pow_pos hplus 3)) hpoly
  exact hbound.trans_lt (sub_pos.mp hgap)



theorem d008320 (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0082.N0334.d008258 _root_.GD.N0232.N0720.N1089.d003092 t < Real.pi / 4 := by
  have hq : (2 * t - 1) ^ 2 < 1 := by
    nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  rw [_root_.GD.N0016.d008318 ht]
  exact _root_.GD.N0016.d008319 (sq_nonneg _) hq (_root_.GD.N0013.d005017 (sq_nonneg _) hq)



theorem d008321 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0082.N0334.d008258 _root_.GD.N0232.N0720.N1089.d003092 t ≤ Real.pi / 4 := by
  rcases eq_or_lt_of_le ht.1 with hzero | ht0
  · subst t
    exact _root_.GD.N0149.N0432.d008285.le
  rcases lt_or_eq_of_le ht.2 with ht1 | hone
  · exact (_root_.GD.N0016.d008320 t ⟨ht0, ht1⟩).le
  · subst t
    have h := _root_.GD.N0082.N0334.d008276 _root_.GD.N0149.N0432.d008283 (0 : ℝ)
    norm_num only [sub_zero] at h
    exact (h.trans _root_.GD.N0149.N0432.d008285).le

end
end GD.N0016

#print axioms _root_.GD.N0016.d008312
#print axioms _root_.GD.N0016.d008313
#print axioms _root_.GD.N0016.d008315
#print axioms _root_.GD.N0016.d008317
#print axioms _root_.GD.N0016.d008318
#print axioms _root_.GD.N0016.d008320
#print axioms _root_.GD.N0016.d008321
