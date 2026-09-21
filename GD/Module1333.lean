import GD.Module1018

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0101.N0376
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1236


def d021692 (u r t : ℝ) : ℝ := u + (1 - 2 * u) * t + r * (1 - t)


def d021693 (u r t : ℝ) : ℝ :=
  r ^ (1 / 2 : ℝ) * (1 - t) ^ 2 * _root_.GD.N0101.N0376.d021692 u r t ^ (-(5 / 2 : ℝ))

theorem d021694 {u r t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hr : 0 < r) (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < _root_.GD.N0101.N0376.d021692 u r t := by
  have heq : _root_.GD.N0101.N0376.d021692 u r t = (u + r) * (1 - t) + t * (1 - u) := by
    unfold _root_.GD.N0101.N0376.d021692
    ring
  rw [heq]
  exact add_pos (mul_pos (add_pos hu.1 hr) (sub_pos.mpr ht.2))
    (mul_pos ht.1 (sub_pos.mpr hu.2))



theorem d021695 {u r t δ ε c : ℝ}
    (hu : 0 < u) (hr : 0 < r) (hδu : δ ≤ u)
    (ht : 0 ≤ t) (hte : t ≤ ε) (hc : 1 ≤ c) (he : ε ≤ δ * (c - 1)) :
    _root_.GD.N0101.N0376.d021692 u r t ≤ c * (u + r) := by
  have htr : t ≤ (u + r) * (c - 1) :=
    hte.trans (he.trans (mul_le_mul_of_nonneg_right
      (hδu.trans (le_add_of_nonneg_right hr.le)) (sub_nonneg.mpr hc)))
  have hnon := mul_nonneg ht (by linarith : 0 ≤ 2 * u + r)
  unfold _root_.GD.N0101.N0376.d021692
  nlinarith



theorem d021696 {t u s : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) :
    _root_.GD.N0232.N0720.N1436.d013273 2 2 t (u, s) * t ^ (-(3 / 2 : ℝ)) =
      (3 / (2 * Real.pi)) * (u ^ (-(1 / 2 : ℝ)) * (1 - u) ^ (-(1 / 2 : ℝ))) *
        _root_.GD.N0101.N0376.d021693 u (s * t) t := by
  have htprod : t ^ 2 * t ^ (-(3 / 2 : ℝ)) = t ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_add ht.1]
    norm_num
  have hden : _root_.GD.N0232.N0720.N1242.d002130 t u + _root_.GD.N0232.N0720.N1236.d016210 t * s =
      _root_.GD.N0101.N0376.d021692 u (s * t) t := by
    unfold _root_.GD.N0232.N0720.N1242.d002130 _root_.GD.N0232.N0720.N1236.d016210 _root_.GD.N0101.N0376.d021692
    ring
  rw [_root_.GD.N0232.N0720.N1236.d016218 ht hu hs]
  unfold _root_.GD.N0232.N0720.N1236.d016211
  rw [hden]
  unfold _root_.GD.N0232.N0720.N1236.d016210 _root_.GD.N0101.N0376.d021693 _root_.GD.N0232.N0720.N1236.d016209
  rw [mul_pow, Real.mul_rpow hs.le ht.1.le]
  calc
    _ = (3 / (2 * Real.pi)) *
        (u ^ (-(1 / 2 : ℝ)) * (1 - u) ^ (-(1 / 2 : ℝ))) *
        s ^ (1 / 2 : ℝ) * (t ^ 2 * t ^ (-(3 / 2 : ℝ))) *
        (1 - t) ^ 2 * _root_.GD.N0101.N0376.d021692 u (s * t) t ^ (-(5 / 2 : ℝ)) := by ring
    _ = _ := by rw [htprod]; ring



theorem d021697 {u r t δ ε c : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hr : 0 < r) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hδu : δ ≤ u) (hte : t ≤ ε) (he1 : ε < 1)
    (hc : 1 ≤ c) (he : ε ≤ δ * (c - 1)) :
    ((1 - ε) ^ 2 * c ^ (-(5 / 2 : ℝ))) * _root_.GD.N0232.N0720.N1236.d016213 u 1 r ≤
      _root_.GD.N0101.N0376.d021693 u r t := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hur : 0 < u + r := add_pos hu.1 hr
  have hQ := _root_.GD.N0101.N0376.d021694 hu hr ht
  have hQu := _root_.GD.N0101.N0376.d021695 hu.1 hr hδu ht.1.le hte hc he
  have hp := Real.rpow_le_rpow_of_nonpos hQ hQu (by norm_num : -(5 / 2 : ℝ) ≤ 0)
  have hs : (1 - ε) ^ 2 ≤ (1 - t) ^ 2 := by
    nlinarith [sub_pos.mpr he1, sub_pos.mpr ht.2]
  unfold _root_.GD.N0101.N0376.d021693 _root_.GD.N0232.N0720.N1236.d016213 _root_.GD.N0232.N0720.N1236.d016209
  rw [one_mul]
  calc
    _ = r ^ (1 / 2 : ℝ) *
        ((1 - ε) ^ 2 * (c * (u + r)) ^ (-(5 / 2 : ℝ))) := by
      rw [Real.mul_rpow hc0.le hur.le]
      ring
    _ ≤ r ^ (1 / 2 : ℝ) *
        ((1 - t) ^ 2 * _root_.GD.N0101.N0376.d021692 u r t ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left
      (mul_le_mul hs hp (Real.rpow_nonneg (mul_pos hc0 hur).le _)
        (sq_nonneg _)) (Real.rpow_nonneg hr.le _)
    _ = _ := by ring

end
end GD.N0101.N0376

#print axioms _root_.GD.N0101.N0376.d021695
#print axioms _root_.GD.N0101.N0376.d021696
#print axioms _root_.GD.N0101.N0376.d021697
