import Mathlib





















open scoped BigOperators

namespace GD
namespace N0230
namespace N0615

noncomputable section

variable {I : Type*} [Fintype I]


def d000151 (p : I -> ℝ) : ℝ := ∑ i, p i


def d000152 (p y : I -> ℝ) : ℝ :=
  (∑ i, p i * y i) / _root_.GD.N0230.N0615.d000151 p


def d000153 (p : I -> ℝ) (i : I) : ℝ :=
  p i / _root_.GD.N0230.N0615.d000151 p

theorem d000154
    (p : I -> ℝ) (htotal : _root_.GD.N0230.N0615.d000151 p ≠ 0) :
    ∑ i, _root_.GD.N0230.N0615.d000153 p i = 1 := by
  unfold _root_.GD.N0230.N0615.d000153
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ htotal

theorem d000155
    (p : I -> ℝ) (hp : ∀ i, 0 ≤ p i)
    (htotal : 0 < _root_.GD.N0230.N0615.d000151 p) (i : I) :
    0 ≤ _root_.GD.N0230.N0615.d000153 p i := by
  exact div_nonneg (hp i) htotal.le



theorem d000156
    (p y : I -> ℝ) :
    _root_.GD.N0230.N0615.d000152 p y = ∑ i, _root_.GD.N0230.N0615.d000153 p i * y i := by
  unfold _root_.GD.N0230.N0615.d000152 _root_.GD.N0230.N0615.d000153
  calc
    (∑ i, p i * y i) / _root_.GD.N0230.N0615.d000151 p =
        (∑ i, p i * y i) * (_root_.GD.N0230.N0615.d000151 p)⁻¹ := by
          rw [div_eq_mul_inv]
    _ = ∑ i, (p i * y i) * (_root_.GD.N0230.N0615.d000151 p)⁻¹ := by
          rw [Finset.sum_mul]
    _ = ∑ i, (p i / _root_.GD.N0230.N0615.d000151 p) * y i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [div_eq_mul_inv]
      ring


theorem d000157
    (p y : I -> ℝ) (htotal : _root_.GD.N0230.N0615.d000151 p ≠ 0) :
    (∑ i, p i * (y i - _root_.GD.N0230.N0615.d000152 p y)) = 0 := by
  unfold _root_.GD.N0230.N0615.d000152
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  calc
    (∑ x, p x * y x) -
        ∑ x, p x * ((∑ i, p i * y i) / _root_.GD.N0230.N0615.d000151 p) =
      (∑ x, p x * y x) -
        (∑ x, p x) * ((∑ i, p i * y i) / _root_.GD.N0230.N0615.d000151 p) := by
          rw [Finset.sum_mul]
    _ = 0 := by
      unfold _root_.GD.N0230.N0615.d000151 at htotal ⊢
      field_simp [htotal]
      ring


theorem d000158
    (p y : I -> ℝ) (mu : ℝ)
    (htotal : _root_.GD.N0230.N0615.d000151 p ≠ 0) :
    (∑ i, p i * (y i - mu) ^ 2) =
      (∑ i, p i * (y i - _root_.GD.N0230.N0615.d000152 p y) ^ 2) +
        _root_.GD.N0230.N0615.d000151 p * (mu - _root_.GD.N0230.N0615.d000152 p y) ^ 2 := by
  let b := _root_.GD.N0230.N0615.d000152 p y
  have hcenter : (∑ i, p i * (y i - b)) = 0 := by
    simpa [b] using
      _root_.GD.N0230.N0615.d000157 p y htotal
  have hexpand :
      (∑ i, p i * (y i - mu) ^ 2) =
        (∑ i, p i * (y i - b) ^ 2) +
          2 * (b - mu) * (∑ i, p i * (y i - b)) +
          _root_.GD.N0230.N0615.d000151 p * (b - mu) ^ 2 := by
    unfold _root_.GD.N0230.N0615.d000151
    calc
      (∑ i, p i * (y i - mu) ^ 2) =
          ∑ i, (p i * (y i - b) ^ 2 +
            2 * (b - mu) * (p i * (y i - b)) +
            p i * (b - mu) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i, p i * (y i - b) ^ 2) +
            (∑ i, 2 * (b - mu) * (p i * (y i - b))) +
            ∑ i, p i * (b - mu) ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (∑ i, p i * (y i - b) ^ 2) +
            2 * (b - mu) * (∑ i, p i * (y i - b)) +
            (∑ i, p i) * (b - mu) ^ 2 := by
              rw [Finset.mul_sum, Finset.sum_mul]
  rw [hexpand, hcenter]
  ring



theorem d000159
    (w y : I -> ℝ) (hi : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hy : ∀ i, y i ≤ hi) :
    (∑ i, w i * y i) ≤ hi := by
  calc
    (∑ i, w i * y i) ≤ ∑ i, w i * hi := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hy i) (hw i)
    _ = hi := by rw [← Finset.sum_mul, hsum, one_mul]



theorem d000160
    (w y : I -> ℝ) (lo : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hy : ∀ i, lo ≤ y i) :
    lo ≤ ∑ i, w i * y i := by
  calc
    lo = ∑ i, w i * lo := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ i, w i * y i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hy i) (hw i)



theorem d000161
    (p y : I -> ℝ) (lo hi : ℝ)
    (hp : ∀ i, 0 ≤ p i) (htotal : 0 < _root_.GD.N0230.N0615.d000151 p)
    (hlo : ∀ i, lo ≤ y i) (hhi : ∀ i, y i ≤ hi) :
    lo ≤ _root_.GD.N0230.N0615.d000152 p y ∧ _root_.GD.N0230.N0615.d000152 p y ≤ hi := by
  rw [_root_.GD.N0230.N0615.d000156]
  have hw := _root_.GD.N0230.N0615.d000155 p hp htotal
  have hsum := _root_.GD.N0230.N0615.d000154 p htotal.ne'
  exact ⟨_root_.GD.N0230.N0615.d000160 (_root_.GD.N0230.N0615.d000153 p) y lo hw hsum hlo,
    _root_.GD.N0230.N0615.d000159 (_root_.GD.N0230.N0615.d000153 p) y hi hw hsum hhi⟩



theorem d000162
    (p q y : I -> ℝ) (lo hi : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpTotal : 0 < _root_.GD.N0230.N0615.d000151 p) (hqTotal : 0 < _root_.GD.N0230.N0615.d000151 q)
    (hlo : ∀ i, lo ≤ y i) (hhi : ∀ i, y i ≤ hi) :
    |_root_.GD.N0230.N0615.d000152 p y - _root_.GD.N0230.N0615.d000152 q y| ≤ hi - lo := by
  obtain ⟨hpl, hpu⟩ := _root_.GD.N0230.N0615.d000161
    p y lo hi hp hpTotal hlo hhi
  obtain ⟨hql, hqu⟩ := _root_.GD.N0230.N0615.d000161
    q y lo hi hq hqTotal hlo hhi
  rw [abs_le]
  constructor <;> linarith

end

end N0615
end N0230
end GD

#print axioms _root_.GD.N0230.N0615.d000158
#print axioms _root_.GD.N0230.N0615.d000161
#print axioms _root_.GD.N0230.N0615.d000162
