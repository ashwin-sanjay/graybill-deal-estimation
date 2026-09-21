import GD.Module0626
















namespace GD.N0232.N0719.N0921

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0901



def d009169 (ε : ℝ) (s : _root_.GD.N0232.N0719.N0900.d009096 3) : ℝ :=
  ε * _root_.GD.N0232.N0719.N0900.d009108 s 0 ^ 2 + _root_.GD.N0232.N0719.N0900.d009108 s 1 ^ 2 + _root_.GD.N0232.N0719.N0900.d009108 s 2 ^ 2


theorem d009170
    {ε q₀ q : ℝ} (hq : q ≠ 0) :
    (ε * q₀ / q) ^ 2 = ε ^ 2 * q₀ ^ 2 * q⁻¹ ^ 2 := by
  field_simp [hq]





theorem d009171
    {ε q₀ q₁ q₂ : ℝ} (hε : 0 < ε)
    (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (s : _root_.GD.N0232.N0719.N0900.d009096 3)
    (ht₀ : s.meanVariance 0 = ε * q₀)
    (ht₁ : s.meanVariance 1 = q₁)
    (ht₂ : s.meanVariance 2 = q₂) :
    _root_.GD.N0232.N0719.N0921.d009169 ε s ≤
      ε + ε ^ 2 * q₀ ^ 2 * (q₁⁻¹ ^ 2 + q₂⁻¹ ^ 2) := by
  have ht0pos : 0 < s.meanVariance 0 := by
    rw [ht₀]
    exact mul_pos hε hq₀
  have ht1pos : 0 < s.meanVariance 1 := by simpa [ht₁] using hq₁
  have ht2pos : 0 < s.meanVariance 2 := by simpa [ht₂] using hq₂
  have hw0 : _root_.GD.N0232.N0719.N0900.d009108 s 0 ^ 2 ≤ 1 := by
    have hnonneg : 0 ≤ _root_.GD.N0232.N0719.N0900.d009108 s 0 := _root_.GD.N0232.N0719.N0900.d009132 (by norm_num) s 0
    have hle : _root_.GD.N0232.N0719.N0900.d009108 s 0 ≤ 1 := _root_.GD.N0232.N0719.N0900.d009133 (by norm_num) s 0
    nlinarith
  have hw1 : _root_.GD.N0232.N0719.N0900.d009108 s 1 ^ 2 ≤ (ε * q₀ / q₁) ^ 2 := by
    simpa [ht₀, ht₁] using
      _root_.GD.N0232.N0719.N0901.d009162 (by norm_num) s 1 0 ht1pos ht0pos
  have hw2 : _root_.GD.N0232.N0719.N0900.d009108 s 2 ^ 2 ≤ (ε * q₀ / q₂) ^ 2 := by
    simpa [ht₀, ht₂] using
      _root_.GD.N0232.N0719.N0901.d009162 (by norm_num) s 2 0 ht2pos ht0pos
  have hfirst : ε * _root_.GD.N0232.N0719.N0900.d009108 s 0 ^ 2 ≤ ε := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hw0 hε.le
  unfold _root_.GD.N0232.N0719.N0921.d009169
  rw [_root_.GD.N0232.N0719.N0921.d009170 hq₁.ne'] at hw1
  rw [_root_.GD.N0232.N0719.N0921.d009170 hq₂.ne'] at hw2
  nlinarith [hfirst, hw1, hw2]

end

end GD.N0232.N0719.N0921

#print axioms _root_.GD.N0232.N0719.N0921.d009171
