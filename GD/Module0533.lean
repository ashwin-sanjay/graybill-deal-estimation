import GD.Module0035

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped BigOperators

namespace GD.N0213.N0518
noncomputable section
open _root_.GD.N0230.N0665

theorem d007962 (a b w p : ℝ)
    (ha : 0 < a) (hw : w ∈ Icc (0 : ℝ) 1) (hp : p ∈ Icc (0 : ℝ) 1) :
    -a * (w - p) ^ 2 + b * (p ^ 2 - w ^ 2) ≤ b ^ 2 / a := by
  apply (le_div_iff₀ ha).mpr
  have hs : (p + w) ^ 2 ≤ 4 := by nlinarith [hw.1, hw.2, hp.1, hp.2]
  have hb := mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hs)
  nlinarith [sq_nonneg (2 * a * (w - p) + b * (p + w))]

variable {k : ℕ}

theorem d007963 [NeZero k]
    {t : Fin k → ℝ} (ht : ∀ i, 0 < t i) (i : Fin k) :
    _root_.GD.N0230.N0665.d000407 t i ∈ Icc (0 : ℝ) 1 := by
  have hp : ∀ j, 0 ≤ _root_.GD.N0230.N0665.d000407 t j := fun j =>
    div_nonneg (inv_nonneg.mpr (ht j).le) (_root_.GD.N0230.N0665.d000408 ht).le
  refine ⟨hp i, ?_⟩
  have h := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  simpa only [_root_.GD.N0230.N0665.d000409 ht] using h

theorem d007964 [NeZero k]
    (t b w : Fin k → ℝ) (c : ℝ)
    (ht : ∀ i, 0 < t i) (hc : 0 < c)
    (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1) (hunit : ∑ i, w i = 1) :
    (∑ i, (c * t i + b i) * _root_.GD.N0230.N0665.d000407 t i ^ 2) -
        (∑ i, (c * t i + b i) * w i ^ 2) ≤
      ∑ i, b i ^ 2 / (c * t i) := by
  have hid := _root_.GD.N0230.N0665.d000412 ht hunit
  have hor := _root_.GD.N0230.N0665.d000411 ht
  have heq : (∑ i, (c * t i + b i) * _root_.GD.N0230.N0665.d000407 t i ^ 2) -
      (∑ i, (c * t i + b i) * w i ^ 2) =
      ∑ i, (-(c * t i) * (w i - _root_.GD.N0230.N0665.d000407 t i) ^ 2 +
        b i * (_root_.GD.N0230.N0665.d000407 t i ^ 2 - w i ^ 2)) := by
    simp only [add_mul, ← Finset.sum_sub_distrib]
    calc
      _ = c * ((∑ i, t i * _root_.GD.N0230.N0665.d000407 t i ^ 2) - (∑ i, t i * w i ^ 2)) +
          ∑ i, b i * (_root_.GD.N0230.N0665.d000407 t i ^ 2 - w i ^ 2) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          mul_sub, mul_assoc, ← Finset.mul_sum]
        ring
      _ = _ := by
        rw [hor, hid]
        simp only [Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib,
          mul_assoc, ← Finset.mul_sum]
        ring
  rw [heq]
  exact Finset.sum_le_sum (fun i _ => _root_.GD.N0213.N0518.d007962
    (c * t i) (b i) (w i) (_root_.GD.N0230.N0665.d000407 t i) (mul_pos hc (ht i))
    (hw i) (_root_.GD.N0213.N0518.d007963 ht i))

theorem d007965 [NeZero k]
    (t s e D w : Fin k → ℝ) (c m : ℝ)
    (ht : ∀ i, 0 < t i) (hs : ∀ i, 0 < s i)
    (hc : 0 < c) (hm : 0 < m)
    (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1) (hunit : ∑ i, w i = 1)
    (hCS : ∀ i, e i ^ 2 ≤ m * D i) :
    (∑ i, (c * m * t i - 2 * e i / s i) * _root_.GD.N0230.N0665.d000407 t i ^ 2) -
        (∑ i, (c * m * t i - 2 * e i / s i) * w i ^ 2) ≤
      ∑ i, 4 * D i / (s i ^ 2 * c * t i) := by
  have h := _root_.GD.N0213.N0518.d007964 t (fun i => -(2 * e i / s i)) w
    (c * m) ht (mul_pos hc hm) hw hunit
  simp only [← sub_eq_add_neg] at h
  apply h.trans
  apply Finset.sum_le_sum
  intro i _
  have heq : (-(2 * e i / s i)) ^ 2 / (c * m * t i) =
      4 * (e i ^ 2 / m) / (s i ^ 2 * c * t i) := by ring
  rw [heq]
  apply div_le_div_of_nonneg_right _
    (mul_pos (mul_pos (sq_pos_of_pos (hs i)) hc) (ht i)).le
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (div_le_iff₀ hm).mpr (by simpa only [mul_comm] using hCS i)

end
end GD.N0213.N0518

#print axioms _root_.GD.N0213.N0518.d007962
#print axioms _root_.GD.N0213.N0518.d007964
#print axioms _root_.GD.N0213.N0518.d007965
