import Mathlib










set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace GD.N0178
noncomputable section

def d007129 (t u s : ℝ) : ℝ := s + 2 * (1 - u) / (1 - t) + 2 * u / t

def d007130 (x : ℝ) : ℝ := x ^ 3 * Real.sqrt x

def d007131 (t u s : ℝ) : ℝ :=
  15 * Real.sqrt s / (t ^ 2 * (1 - t) ^ 2 * _root_.GD.N0178.d007130 (_root_.GD.N0178.d007129 t u s))

def d007132 (q d : ℝ) : ℝ := q ^ 2 * _root_.GD.N0178.d007130 (1 - d)

theorem d007133 {x : ℝ} (hx : 0 ≤ x) : 0 ≤ _root_.GD.N0178.d007130 x := by
  unfold _root_.GD.N0178.d007130
  positivity

theorem d007134 {x : ℝ} (hx : 0 < x) : 0 < _root_.GD.N0178.d007130 x := by
  unfold _root_.GD.N0178.d007130
  positivity

theorem d007135 {x y : ℝ} (hx : 0 ≤ x) :
    _root_.GD.N0178.d007130 (x * y) = _root_.GD.N0178.d007130 x * _root_.GD.N0178.d007130 y := by
  unfold _root_.GD.N0178.d007130
  rw [mul_pow, Real.sqrt_mul hx]
  ring

theorem d007136 {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    _root_.GD.N0178.d007130 x ≤ _root_.GD.N0178.d007130 y := by
  unfold _root_.GD.N0178.d007130
  exact mul_le_mul (pow_le_pow_left₀ hx hxy 3) (Real.sqrt_le_sqrt hxy)
    (Real.sqrt_nonneg _) (pow_nonneg (hx.trans hxy) 3)

theorem d007137 {x : ℝ} (hx : 0 < x) :
    _root_.GD.N0178.d007130 x = x ^ (7 / 2 : ℝ) := by
  unfold _root_.GD.N0178.d007130
  rw [show (7 / 2 : ℝ) = (3 : ℕ) + (1 / 2 : ℝ) by norm_num,
    Real.rpow_add hx, Real.rpow_natCast, Real.sqrt_eq_rpow]

theorem d007138 {t u s : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hs : 0 < s) :
    0 < _root_.GD.N0178.d007129 t u s := by
  unfold _root_.GD.N0178.d007129
  positivity


theorem d007139 {t t₀ d u s : ℝ}
    (ht : 0 < t) (htt₀ : t ≤ t₀) (ht₀d : t₀ ≤ d) (hd : d < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hs : 0 ≤ s) :
    (1 - d) * _root_.GD.N0178.d007129 t₀ u s ≤ _root_.GD.N0178.d007129 t u s := by
  have ht₀ : 0 < t₀ := ht.trans_le htt₀
  have hd0 : 0 ≤ d := (ht₀.trans_le ht₀d).le
  have hdt : 0 < 1 - t := by linarith
  have hdt₀ : 0 < 1 - t₀ := by linarith
  have hd1 : 0 ≤ 1 - d := by linarith
  have hleft : (1 - d) * (2 * (1 - u) / (1 - t₀)) ≤
      2 * (1 - u) / (1 - t) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hdt₀ hdt]
    have hbase : (1 - d) * (1 - t) ≤ 1 - t₀ := by
      calc (1 - d) * (1 - t) ≤ 1 - d :=
          mul_le_of_le_one_right hd1 (by linarith)
        _ ≤ 1 - t₀ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hbase
      (show 0 ≤ 2 * (1 - u) by positivity)]
  have hright : (1 - d) * (2 * u / t₀) ≤ 2 * u / t := by
    calc (1 - d) * (2 * u / t₀) ≤ 2 * u / t₀ :=
        mul_le_of_le_one_left (by positivity) (by linarith)
      _ ≤ 2 * u / t := div_le_div_of_nonneg_left (by positivity) ht htt₀
  have hmass : (1 - d) * s ≤ s :=
    mul_le_of_le_one_left hs (by linarith)
  unfold _root_.GD.N0178.d007129
  nlinarith


theorem d007140 {q t t₀ d u s : ℝ}
    (hq : 0 ≤ q) (ht : 0 < t) (hqt : q * t₀ ≤ t)
    (htt₀ : t ≤ t₀) (ht₀d : t₀ ≤ d) (hd : d < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hs : 0 < s) :
    _root_.GD.N0178.d007132 q d * _root_.GD.N0178.d007131 t u s ≤ _root_.GD.N0178.d007131 t₀ u s := by
  have ht₀ : 0 < t₀ := ht.trans_le htt₀
  have ht1 : t < 1 := lt_of_le_of_lt (htt₀.trans ht₀d) hd
  have ht₀1 : t₀ < 1 := ht₀d.trans_lt hd
  have hd1 : 0 < 1 - d := sub_pos.mpr hd
  have hD₀ : 0 < _root_.GD.N0178.d007129 t₀ u s := _root_.GD.N0178.d007138 ht₀ ht₀1 hu hu1 hs
  have hDt : 0 < _root_.GD.N0178.d007129 t u s := _root_.GD.N0178.d007138 ht ht1 hu hu1 hs
  have hpow := _root_.GD.N0178.d007136 (mul_nonneg hd1.le hD₀.le)
    (_root_.GD.N0178.d007139 ht htt₀ ht₀d hd hu hu1 hs.le)
  rw [_root_.GD.N0178.d007135 hd1.le] at hpow
  have htime : q ^ 2 * t₀ ^ 2 ≤ t ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (mul_nonneg hq ht₀.le) hqt 2
  have hone : (1 - t₀) ^ 2 ≤ (1 - t) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hden : _root_.GD.N0178.d007132 q d *
      (t₀ ^ 2 * (1 - t₀) ^ 2 * _root_.GD.N0178.d007130 (_root_.GD.N0178.d007129 t₀ u s)) ≤
      t ^ 2 * (1 - t) ^ 2 * _root_.GD.N0178.d007130 (_root_.GD.N0178.d007129 t u s) := by
    unfold _root_.GD.N0178.d007132
    calc q ^ 2 * _root_.GD.N0178.d007130 (1 - d) *
          (t₀ ^ 2 * (1 - t₀) ^ 2 * _root_.GD.N0178.d007130 (_root_.GD.N0178.d007129 t₀ u s)) =
          (q ^ 2 * t₀ ^ 2) * (1 - t₀) ^ 2 *
            (_root_.GD.N0178.d007130 (1 - d) * _root_.GD.N0178.d007130 (_root_.GD.N0178.d007129 t₀ u s)) := by ring
      _ ≤ t ^ 2 * (1 - t) ^ 2 * _root_.GD.N0178.d007130 (_root_.GD.N0178.d007129 t u s) := by
        exact mul_le_mul (mul_le_mul htime hone (sq_nonneg _) (sq_nonneg _)) hpow
          (mul_nonneg (_root_.GD.N0178.d007133 hd1.le) (_root_.GD.N0178.d007133 hD₀.le))
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hdenpos : 0 < t ^ 2 * (1 - t) ^ 2 * _root_.GD.N0178.d007130 (_root_.GD.N0178.d007129 t u s) :=
    mul_pos (mul_pos (sq_pos_of_pos ht) (sq_pos_of_pos (sub_pos.mpr ht1)))
      (_root_.GD.N0178.d007134 hDt)
  have hdenpos₀ : 0 < t₀ ^ 2 * (1 - t₀) ^ 2 * _root_.GD.N0178.d007130 (_root_.GD.N0178.d007129 t₀ u s) :=
    mul_pos (mul_pos (sq_pos_of_pos ht₀) (sq_pos_of_pos (sub_pos.mpr ht₀1)))
      (_root_.GD.N0178.d007134 hD₀)
  unfold _root_.GD.N0178.d007131
  rw [← mul_div_assoc, div_le_div_iff₀ hdenpos hdenpos₀]
  nlinarith [mul_le_mul_of_nonneg_left hden (show 0 ≤ 15 * Real.sqrt s by positivity)]

theorem d007141 {t u s : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hs : 0 < s) : 0 ≤ _root_.GD.N0178.d007131 t u s := by
  unfold _root_.GD.N0178.d007131
  exact div_nonneg (by positivity)
    (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (_root_.GD.N0178.d007133 (_root_.GD.N0178.d007138 ht ht1 hu hu1 hs).le))


theorem d007142 {v t t₀ : ℝ}
    (hv : v ≤ 1) (ht : 0 ≤ t) (htt₀ : t ≤ t₀) :
    (v - t) ^ 2 - 2 * (t₀ - t) ≤ (v - t₀) ^ 2 := by
  have h : 0 ≤ (t₀ - t) * (t₀ + t + 2 * (1 - v)) :=
    mul_nonneg (sub_nonneg.mpr htt₀) (by linarith)
  nlinarith


theorem d007143 {q t t₀ d u s v : ℝ}
    (hq : 0 ≤ q) (ht : 0 < t) (hqt : q * t₀ ≤ t)
    (htt₀ : t ≤ t₀) (ht₀d : t₀ ≤ d) (hd : d < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hs : 0 < s) (hv : v ≤ 1) :
    _root_.GD.N0178.d007132 q d * _root_.GD.N0178.d007131 t u s * (v - t) ^ 2 -
        2 * _root_.GD.N0178.d007132 q d * (t₀ - t) * _root_.GD.N0178.d007131 t u s ≤
      _root_.GD.N0178.d007131 t₀ u s * (v - t₀) ^ 2 := by
  have hkernel := _root_.GD.N0178.d007140 hq ht hqt htt₀ ht₀d hd hu hu1 hs
  have hk : 0 ≤ _root_.GD.N0178.d007131 t u s :=
    _root_.GD.N0178.d007141 ht (lt_of_le_of_lt (htt₀.trans ht₀d) hd) hu hu1 hs
  have hc : 0 ≤ _root_.GD.N0178.d007132 q d :=
    mul_nonneg (sq_nonneg _) (_root_.GD.N0178.d007133 (sub_pos.mpr hd).le)
  have hpert := mul_le_mul_of_nonneg_left (_root_.GD.N0178.d007142 hv ht.le htt₀)
    (mul_nonneg hc hk)
  have hdom := mul_le_mul_of_nonneg_right hkernel (sq_nonneg (v - t₀))
  nlinarith


theorem d007144 {q t t₀ d : ℝ}
    (hq : 0 < q) (ht : 0 < t) (hqt : q * t₀ ≤ t)
    (htt₀ : t ≤ t₀) (ht₀d : t₀ ≤ d) (hd : d < 1) :
    (t₀ - t) / (t * (1 - t)) ≤ (q⁻¹ - 1) / (1 - d) := by
  have ht1 : t < 1 := lt_of_le_of_lt (htt₀.trans ht₀d) hd
  have hratio : (t₀ - t) / t ≤ q⁻¹ - 1 := by
    rw [div_le_iff₀ ht]
    have ht₀ : t₀ ≤ t / q := (le_div_iff₀ hq).mpr (by nlinarith [hqt])
    rw [div_eq_mul_inv] at ht₀
    nlinarith
  have hnonneg : 0 ≤ q⁻¹ - 1 :=
    (div_nonneg (sub_nonneg.mpr htt₀) ht.le).trans hratio
  calc (t₀ - t) / (t * (1 - t)) = ((t₀ - t) / t) / (1 - t) := by rw [div_div]
    _ ≤ (q⁻¹ - 1) / (1 - t) :=
      div_le_div_of_nonneg_right hratio (sub_pos.mpr ht1).le
    _ ≤ (q⁻¹ - 1) / (1 - d) :=
      div_le_div_of_nonneg_left hnonneg (sub_pos.mpr hd) (by linarith)

end
end GD.N0178

#print axioms _root_.GD.N0178.d007137
#print axioms _root_.GD.N0178.d007139
#print axioms _root_.GD.N0178.d007140
#print axioms _root_.GD.N0178.d007143
#print axioms _root_.GD.N0178.d007144
