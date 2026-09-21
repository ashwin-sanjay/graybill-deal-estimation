import GD.Module0925

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set

namespace GD.N0001
noncomputable section
open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1091 _root_.GD.N0232.N0720.N1092
open _root_.GD.N0232.N0720.N1045

def d014462 (u t : ℝ) : ℝ := (1 - t) * u + t * (1 - u)

def d014463 (u t : ℝ) : ℝ := (u - t) / _root_.GD.N0001.d014462 u t ^ 2

def d014464 (r : ℝ) : ℝ := r ^ 2 / (1 + r ^ 2)

theorem d014465 {r : ℝ} (hr : 0 < r) : _root_.GD.N0001.d014464 r ∈ Ioo (0 : ℝ) 1 := by
  have hd : 0 < 1 + r ^ 2 := by positivity
  exact ⟨div_pos (sq_pos_of_pos hr) hd, (div_lt_one hd).mpr (by linarith)⟩

theorem d014466 {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < _root_.GD.N0001.d014462 u t :=
  add_pos (mul_pos (sub_pos.mpr ht.2) hu.1) (mul_pos ht.1 (sub_pos.mpr hu.2))

theorem d014467 {r t : ℝ} (hr : 0 < r) (ht : t ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0001.d014463 (_root_.GD.N0001.d014464 r) t =
      ((2 - 4 * _root_.GD.N0001.d014464 r) * _root_.GD.N0232.N0720.N1091.d012763 (r ^ 2) t ^ 2 +
        (4 * _root_.GD.N0001.d014464 r - 1) * _root_.GD.N0232.N0720.N1091.d012763 (r ^ 2) t - _root_.GD.N0001.d014464 r) /
        (_root_.GD.N0001.d014464 r * (1 - _root_.GD.N0001.d014464 r)) := by
  have hD := (_root_.GD.N0001.d014466 (_root_.GD.N0001.d014465 hr) ht).ne'
  have hB := (_root_.GD.N0232.N0720.N1091.d012779 (sq_pos_of_pos hr) ht.1 ht.2).ne'
  have hDform : _root_.GD.N0001.d014462 (_root_.GD.N0001.d014464 r) t =
      (t + r ^ 2 * (1 - t)) / (1 + r ^ 2) := by
    unfold _root_.GD.N0001.d014462 _root_.GD.N0001.d014464
    field_simp [show 1 + r ^ 2 ≠ 0 by positivity]
    ring
  have hW : _root_.GD.N0232.N0720.N1091.d012763 (r ^ 2) t =
      _root_.GD.N0001.d014464 r * (1 - t) / _root_.GD.N0001.d014462 (_root_.GD.N0001.d014464 r) t := by
    rw [hDform]
    unfold _root_.GD.N0001.d014464 _root_.GD.N0232.N0720.N1091.d012763
    field_simp [hB, show 1 + r ^ 2 ≠ 0 by positivity]
  rw [hW]
  unfold _root_.GD.N0001.d014463
  field_simp [hD, (_root_.GD.N0001.d014465 hr).1.ne', (sub_pos.mpr (_root_.GD.N0001.d014465 hr).2).ne']
  unfold _root_.GD.N0001.d014462
  ring

theorem d014468 {r : ℝ} (hr : 0 < r) :
    Integrable (_root_.GD.N0001.d014463 (_root_.GD.N0001.d014464 r)) (betaMeasure (1 / 2) (1 / 2)) := by
  letI : IsProbabilityMeasure (betaMeasure (1 / 2) (1 / 2)) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  have hW := _root_.GD.N0232.N0720.N1045.d014456 hr
  have hW₂ := _root_.GD.N0232.N0720.N1045.d014457 hr
  have hp := (((hW₂.const_mul (2 - 4 * _root_.GD.N0001.d014464 r)).add
    (hW.const_mul (4 * _root_.GD.N0001.d014464 r - 1))).sub (integrable_const (_root_.GD.N0001.d014464 r))).div_const
      (_root_.GD.N0001.d014464 r * (1 - _root_.GD.N0001.d014464 r))
  apply hp.congr
  filter_upwards [_root_.GD.N0232.N0720.N1092.d013031 (1 / 2) (1 / 2)] with t ht
  exact (_root_.GD.N0001.d014467 hr ht).symm

theorem d014469 {r : ℝ} (hr : 0 < r) :
    (∫ t, _root_.GD.N0001.d014463 (_root_.GD.N0001.d014464 r) t ∂betaMeasure (1 / 2) (1 / 2)) = 0 := by
  letI : IsProbabilityMeasure (betaMeasure (1 / 2) (1 / 2)) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  have hW := _root_.GD.N0232.N0720.N1045.d014456 hr
  have hW₂ := _root_.GD.N0232.N0720.N1045.d014457 hr
  have hp : _root_.GD.N0001.d014463 (_root_.GD.N0001.d014464 r) =ᵐ[betaMeasure (1 / 2) (1 / 2)]
      fun t => ((2 - 4 * _root_.GD.N0001.d014464 r) * _root_.GD.N0232.N0720.N1091.d012763 (r ^ 2) t ^ 2 +
        (4 * _root_.GD.N0001.d014464 r - 1) * _root_.GD.N0232.N0720.N1091.d012763 (r ^ 2) t - _root_.GD.N0001.d014464 r) /
        (_root_.GD.N0001.d014464 r * (1 - _root_.GD.N0001.d014464 r)) := by
    filter_upwards [_root_.GD.N0232.N0720.N1092.d013031 (1 / 2) (1 / 2)] with t ht
    exact _root_.GD.N0001.d014467 hr ht
  rw [integral_congr_ae hp, integral_div,
    integral_sub (f := fun t => (2 - 4 * _root_.GD.N0001.d014464 r) * _root_.GD.N0232.N0720.N1091.d012763 (r ^ 2) t ^ 2 +
      (4 * _root_.GD.N0001.d014464 r - 1) * _root_.GD.N0232.N0720.N1091.d012763 (r ^ 2) t)
      (g := fun _t => _root_.GD.N0001.d014464 r)
      ((hW₂.const_mul _).add (hW.const_mul _)) (integrable_const _),
    integral_add (f := fun t => (2 - 4 * _root_.GD.N0001.d014464 r) * _root_.GD.N0232.N0720.N1091.d012763 (r ^ 2) t ^ 2)
      (g := fun t => (4 * _root_.GD.N0001.d014464 r - 1) * _root_.GD.N0232.N0720.N1091.d012763 (r ^ 2) t)
      (hW₂.const_mul _) (hW.const_mul _)]
  simp only [integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [_root_.GD.N0232.N0720.N1045.d014454 hr, _root_.GD.N0232.N0720.N1045.d014455 hr]
  unfold _root_.GD.N0001.d014464
  field_simp [hr.ne', show 1 + r ≠ 0 by linarith, show 1 + r ^ 2 ≠ 0 by positivity]
  ring

theorem d014470 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0001.d014464 (Real.sqrt (u / (1 - u))) = u := by
  unfold _root_.GD.N0001.d014464
  rw [Real.sq_sqrt (div_pos hu.1 (sub_pos.mpr hu.2)).le]
  field_simp [(sub_pos.mpr hu.2).ne']
  ring

theorem d014471 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    Integrable (_root_.GD.N0001.d014463 u) (betaMeasure (1 / 2) (1 / 2)) := by
  have h := _root_.GD.N0001.d014468 (Real.sqrt_pos.mpr (div_pos hu.1 (sub_pos.mpr hu.2)))
  simpa only [_root_.GD.N0001.d014470 hu] using h

theorem d014472 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∫ t, (u - t) / ((1 - t) * u + t * (1 - u)) ^ 2
      ∂betaMeasure (1 / 2) (1 / 2)) = 0 := by
  have h := _root_.GD.N0001.d014469 (Real.sqrt_pos.mpr (div_pos hu.1 (sub_pos.mpr hu.2)))
  simpa only [_root_.GD.N0001.d014470 hu, _root_.GD.N0001.d014463, _root_.GD.N0001.d014462] using h

theorem d014473 {u t : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (u - t) ^ 2 / _root_.GD.N0001.d014462 u t ^ 2 ≤ 1 := by
  apply (div_le_one (sq_pos_of_pos (_root_.GD.N0001.d014466 hu ht))).mpr
  have h := mul_nonneg (mul_nonneg hu.1.le ht.1.le)
    (mul_nonneg (sub_pos.mpr hu.2).le (sub_pos.mpr ht.2).le)
  unfold _root_.GD.N0001.d014462
  nlinarith

#print axioms _root_.GD.N0001.d014467
#print axioms _root_.GD.N0001.d014471
#print axioms _root_.GD.N0001.d014472
#print axioms _root_.GD.N0001.d014473

end
end GD.N0001
