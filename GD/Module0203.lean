import GD.Module0192
import Mathlib.Tactic










open MeasureTheory

namespace GD.N0232.N0720



theorem d002825
    {m n j k : ℝ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    |j ^ 2 / m - k ^ 2 / n| ≤
      |j - k| * (|j| + |k|) + k ^ 2 * |m - n| := by
  have hm0 : m ≠ 0 := by linarith
  have hn0 : n ≠ 0 := by linarith
  have hmn : 1 ≤ m * n := by nlinarith
  have hdecomp :
      j ^ 2 / m - k ^ 2 / n =
        (j - k) * (j + k) / m + k ^ 2 * (n - m) / (m * n) := by
    field_simp [hm0, hn0]
    ring
  rw [hdecomp]
  calc
    |(j - k) * (j + k) / m + k ^ 2 * (n - m) / (m * n)| ≤
        |(j - k) * (j + k) / m| +
          |k ^ 2 * (n - m) / (m * n)| := abs_add_le _ _
    _ = |j - k| * |j + k| / m +
          k ^ 2 * |m - n| / (m * n) := by
      rw [abs_div, abs_mul, abs_div, abs_mul, abs_pow,
        abs_of_nonneg (by linarith : 0 ≤ m),
        abs_of_nonneg (mul_nonneg (by linarith : 0 ≤ m)
          (by linarith : 0 ≤ n)),
        sq_abs]
      rw [abs_sub_comm n m]
    _ ≤ |j - k| * |j + k| + k ^ 2 * |m - n| := by
      apply add_le_add
      · exact div_le_self (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hm
      · exact div_le_self (mul_nonneg (sq_nonneg _) (abs_nonneg _)) hmn
    _ ≤ |j - k| * (|j| + |k|) + k ^ 2 * |m - n| := by
      gcongr
      exact abs_add_le j k



theorem d002826
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (m n j k : X → ℝ)
    (hm : ∀ᵐ x ∂μ, 1 ≤ m x)
    (hn : ∀ᵐ x ∂μ, 1 ≤ n x)
    (hfirst : Integrable (fun x ↦ j x ^ 2 / m x) μ)
    (hsecond : Integrable (fun x ↦ k x ^ 2 / n x) μ)
    (hbound : Integrable
      (fun x ↦ |j x - k x| * (|j x| + |k x|) +
        k x ^ 2 * |m x - n x|) μ) :
    |(∫ x, j x ^ 2 / m x ∂μ) - (∫ x, k x ^ 2 / n x ∂μ)| ≤
      ∫ x, |j x - k x| * (|j x| + |k x|) +
        k x ^ 2 * |m x - n x| ∂μ := by
  rw [← integral_sub hfirst hsecond]
  calc
    |∫ x, (j x ^ 2 / m x - k x ^ 2 / n x) ∂μ| ≤
        ∫ x, |j x ^ 2 / m x - k x ^ 2 / n x| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, |j x - k x| * (|j x| + |k x|) +
          k x ^ 2 * |m x - n x| ∂μ := by
      apply integral_mono_ae (hfirst.sub hsecond).abs hbound
      filter_upwards [hm, hn] with x hmx hnx
      exact _root_.GD.N0232.N0720.d002825 hmx hnx

end GD.N0232.N0720

#print axioms _root_.GD.N0232.N0720.d002825
#print axioms _root_.GD.N0232.N0720.d002826
