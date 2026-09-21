import GD.Module0533
import GD.Module0574

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped BigOperators

namespace GD.N0213.N0506
noncomputable section
open _root_.GD.N0230.N0665 _root_.GD.N0213.N0525 _root_.GD.N0213.N0518
variable {k : ℕ}

theorem d008438 [NeZero k] (t b w : Fin k → ℝ) (c : ℝ)
    (ht : ∀ i, 0 < t i) (hw : ∑ i, w i = 1) :
    (∑ i, (c * t i + b i) * _root_.GD.N0230.N0665.d000407 t i ^ 2) -
        (∑ i, (c * t i + b i) * w i ^ 2) =
      ∑ i, (-(c * t i) * (w i - _root_.GD.N0230.N0665.d000407 t i) ^ 2 +
        (-b i * (_root_.GD.N0230.N0665.d000407 t i + w i)) * (w i - _root_.GD.N0230.N0665.d000407 t i)) := by
  have hid := _root_.GD.N0230.N0665.d000412 ht hw
  have hor := _root_.GD.N0230.N0665.d000411 ht
  calc
    _ = c * ((∑ i, t i * _root_.GD.N0230.N0665.d000407 t i ^ 2) - (∑ i, t i * w i ^ 2)) +
        ∑ i, b i * (_root_.GD.N0230.N0665.d000407 t i ^ 2 - w i ^ 2) := by
      simp only [add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        mul_sub, mul_assoc, ← Finset.mul_sum]
      ring
    _ = _ := by
      rw [hor, hid]
      simp only [Finset.sum_add_distrib]
      rw [show (∑ i, -(c * t i) * (w i - _root_.GD.N0230.N0665.d000407 t i) ^ 2) =
          -c * ∑ i, t i * (w i - _root_.GD.N0230.N0665.d000407 t i) ^ 2 by
            simp only [neg_mul, mul_assoc, Finset.mul_sum]]
      have hb : (∑ i, b i * (_root_.GD.N0230.N0665.d000407 t i ^ 2 - w i ^ 2)) =
          ∑ i, (-b i * (_root_.GD.N0230.N0665.d000407 t i + w i)) * (w i - _root_.GD.N0230.N0665.d000407 t i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hb]
      ring

theorem d008439 [NeZero k] (t b w : Fin k → ℝ) (c : ℝ)
    (ht : ∀ i, 0 < t i) (hc : 0 < c) (hw : ∑ i, w i = 1) :
    (∑ i, (c * t i + b i) * _root_.GD.N0230.N0665.d000407 t i ^ 2) -
        (∑ i, (c * t i + b i) * w i ^ 2) ≤
      ∑ i, ∑ j, (b i * (_root_.GD.N0230.N0665.d000407 t i + w i) -
        b j * (_root_.GD.N0230.N0665.d000407 t j + w j)) ^ 2 / (8 * c * (t i + t j)) := by
  have hd : (∑ i, (w i - _root_.GD.N0230.N0665.d000407 t i)) = 0 := by
    rw [Finset.sum_sub_distrib, hw, _root_.GD.N0230.N0665.d000409 ht, sub_self]
  rw [_root_.GD.N0213.N0506.d008438 t b w c ht hw]
  have h := _root_.GD.N0213.N0525.d008437
    (fun i => c * t i) (fun i => -b i * (_root_.GD.N0230.N0665.d000407 t i + w i))
    (fun i => w i - _root_.GD.N0230.N0665.d000407 t i) (fun i => mul_pos hc (ht i)) hd
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem d008440 [NeZero k] (t s e D w : Fin k → ℝ) (m : ℝ)
    (ht : ∀ i, 0 < t i) (hs : ∀ i, 0 < s i)
    (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1) (hCS : ∀ i, e i ^ 2 ≤ m * D i)
    (i : Fin k) :
    (-(2 * e i / s i) * (_root_.GD.N0230.N0665.d000407 t i + w i)) ^ 2 ≤
      16 * m * (D i / s i ^ 2) := by
  have hp := _root_.GD.N0213.N0518.d007963 ht i
  have hsum : (_root_.GD.N0230.N0665.d000407 t i + w i) ^ 2 ≤ 4 := by
    nlinarith [hp.1, hp.2, (hw i).1, (hw i).2]
  calc
    _ = (4 * (e i ^ 2 / s i ^ 2)) * (_root_.GD.N0230.N0665.d000407 t i + w i) ^ 2 := by ring
    _ ≤ (4 * (e i ^ 2 / s i ^ 2)) * 4 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 16 * (e i ^ 2 / s i ^ 2) := by ring
    _ ≤ 16 * (m * D i / s i ^ 2) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (hCS i) (sq_pos_of_pos (hs i)).le) (by norm_num)
    _ = _ := by ring

theorem d008441 [NeZero k]
    (t s e D w : Fin k → ℝ) (c m : ℝ)
    (ht : ∀ i, 0 < t i) (hs : ∀ i, 0 < s i) (hc : 0 < c) (hm : 0 < m)
    (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1) (hunit : ∑ i, w i = 1)
    (hCS : ∀ i, e i ^ 2 ≤ m * D i) :
    (∑ i, (c * m * t i - 2 * e i / s i) * _root_.GD.N0230.N0665.d000407 t i ^ 2) -
        (∑ i, (c * m * t i - 2 * e i / s i) * w i ^ 2) ≤
      ∑ i, ∑ j, if i = j then 0 else
        4 * (D i / s i ^ 2 + D j / s j ^ 2) / (c * (t i + t j)) := by
  have h := _root_.GD.N0213.N0506.d008439 t (fun i => -(2 * e i / s i)) w
    (c * m) ht (mul_pos hc hm) hunit
  simp only [← sub_eq_add_neg] at h
  apply h.trans
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · subst j
    simp
  · rw [if_neg hij]
    have hi := _root_.GD.N0213.N0506.d008440 t s e D w m ht hs hw hCS i
    have hj := _root_.GD.N0213.N0506.d008440 t s e D w m ht hs hw hCS j
    have hnum : (-(2 * e i / s i) * (_root_.GD.N0230.N0665.d000407 t i + w i) -
        -(2 * e j / s j) * (_root_.GD.N0230.N0665.d000407 t j + w j)) ^ 2 ≤
        32 * m * (D i / s i ^ 2 + D j / s j ^ 2) := by
      nlinarith [sq_nonneg (-(2 * e i / s i) * (_root_.GD.N0230.N0665.d000407 t i + w i) +
        -(2 * e j / s j) * (_root_.GD.N0230.N0665.d000407 t j + w j))]
    calc
      _ ≤ (32 * m * (D i / s i ^ 2 + D j / s j ^ 2)) /
          (8 * (c * m) * (t i + t j)) := div_le_div_of_nonneg_right hnum
            (mul_pos (mul_pos (by norm_num) (mul_pos hc hm)) (add_pos (ht i) (ht j))).le
      _ = _ := by
        field_simp [hc.ne', hm.ne', (add_pos (ht i) (ht j)).ne']
        ring

end
end GD.N0213.N0506

#print axioms _root_.GD.N0213.N0506.d008438
#print axioms _root_.GD.N0213.N0506.d008439
#print axioms _root_.GD.N0213.N0506.d008441
