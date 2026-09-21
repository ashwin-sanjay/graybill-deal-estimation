import GD.Module1786











set_option autoImplicit false
set_option warningAsError true

open Set

namespace GD.N0106.N0428.N0765.N1630
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1529 _root_.GD.N0106.N0428.N0765.N1607 _root_.GD.N0106.N0428.N0765.N1627
open _root_.GD.N0232.N0720.N1249

def d029891 : ℝ := 1 / (12 * Real.sqrt 3)

def d029892 : ℝ := (Real.sqrt ((3 : ℝ) / 20)) ^ 3 / 10

def d029893 (k : ℕ) : ℝ := if k = 1 then _root_.GD.N0106.N0428.N0765.N1630.d029891 else _root_.GD.N0106.N0428.N0765.N1630.d029892

theorem d029894 : 0 ≤ _root_.GD.N0106.N0428.N0765.N1630.d029891 := by
  unfold _root_.GD.N0106.N0428.N0765.N1630.d029891
  positivity

theorem d029895 : 0 ≤ _root_.GD.N0106.N0428.N0765.N1630.d029892 := by
  unfold _root_.GD.N0106.N0428.N0765.N1630.d029892
  positivity

theorem d029896 (k : ℕ) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1630.d029893 k := by
  unfold _root_.GD.N0106.N0428.N0765.N1630.d029893
  split_ifs <;> first | exact _root_.GD.N0106.N0428.N0765.N1630.d029894 | exact _root_.GD.N0106.N0428.N0765.N1630.d029895

theorem d029897 : _root_.GD.N0106.N0428.N0765.N1630.d029891 ^ 2 = (1 : ℝ) / 432 := by
  unfold _root_.GD.N0106.N0428.N0765.N1630.d029891
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem d029898 : _root_.GD.N0106.N0428.N0765.N1630.d029892 ^ 2 = (27 : ℝ) / 800000 := by
  calc
    _root_.GD.N0106.N0428.N0765.N1630.d029892 ^ 2 = ((Real.sqrt ((3 : ℝ) / 20)) ^ 2) ^ 3 / 100 := by
      unfold _root_.GD.N0106.N0428.N0765.N1630.d029892
      ring
    _ = (27 : ℝ) / 800000 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 20)]
      norm_num

theorem d029899 {H : ℝ} (hH : H ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1249.d002197 1 H ^ 2 ≤ (1 : ℝ) / 432 := by
  let s : ℝ := (H - 1 / 2) ^ 2
  have hs : s ≤ (1 : ℝ) / 4 := by
    dsimp [s]
    nlinarith [mul_nonneg hH.1 (sub_nonneg.mpr hH.2)]
  have hgap : 0 ≤ (s - 1 / 12) ^ 2 * (1 / 3 - s) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hid : (1 : ℝ) / 432 - s * (1 / 4 - s) ^ 2 =
      (s - 1 / 12) ^ 2 * (1 / 3 - s) := by ring
  have heq : _root_.GD.N0232.N0720.N1249.d002197 1 H ^ 2 = s * (1 / 4 - s) ^ 2 := by
    dsimp [s, _root_.GD.N0232.N0720.N1249.d002197]
    ring
  rw [heq]
  linarith only [hid, hgap]

theorem d029900 {H : ℝ} (hH : H ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1249.d002197 3 H ^ 2 ≤ (27 : ℝ) / 800000 := by
  let t : ℝ := 4 * (H - 1 / 2) ^ 2
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    nlinarith [mul_nonneg hH.1 (sub_nonneg.mpr hH.2)]
  have hrest : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hR : 0 ≤ t ^ 2 * (1 - t) + (1 / 5 : ℝ) * t * (1 - t) +
      (3 / 25 : ℝ) * t + 12 / 125 := by positivity
  have hgap : 0 ≤ (t - 3 / 5) ^ 2 *
      (t ^ 2 * (1 - t) + (1 / 5 : ℝ) * t * (1 - t) +
        (3 / 25 : ℝ) * t + 12 / 125) := mul_nonneg (sq_nonneg _) hR
  have hid : (108 : ℝ) / 3125 - t ^ 3 * (1 - t) ^ 2 =
      (t - 3 / 5) ^ 2 *
        (t ^ 2 * (1 - t) + (1 / 5 : ℝ) * t * (1 - t) +
          (3 / 25 : ℝ) * t + 12 / 125) := by ring
  have hpoly : t ^ 3 * (1 - t) ^ 2 ≤ (108 : ℝ) / 3125 := by
    linarith only [hid, hgap]
  have heq : _root_.GD.N0232.N0720.N1249.d002197 3 H ^ 2 = t ^ 3 * (1 - t) ^ 2 / 1024 := by
    dsimp [t, _root_.GD.N0232.N0720.N1249.d002197]
    ring
  rw [heq]
  linarith only [hpoly]

theorem d029901 {H : ℝ} (hH : H ∈ Icc (0 : ℝ) 1) :
    |_root_.GD.N0232.N0720.N1249.d002197 1 H| ≤ 1 / (12 * Real.sqrt 3) := by
  change |_root_.GD.N0232.N0720.N1249.d002197 1 H| ≤ _root_.GD.N0106.N0428.N0765.N1630.d029891
  apply (sq_le_sq₀ (abs_nonneg _) _root_.GD.N0106.N0428.N0765.N1630.d029894).mp
  rw [sq_abs, _root_.GD.N0106.N0428.N0765.N1630.d029897]
  exact _root_.GD.N0106.N0428.N0765.N1630.d029899 hH

theorem d029902 {H : ℝ} (hH : H ∈ Icc (0 : ℝ) 1) :
    |_root_.GD.N0232.N0720.N1249.d002197 3 H| ≤ (Real.sqrt ((3 : ℝ) / 20)) ^ 3 / 10 := by
  change |_root_.GD.N0232.N0720.N1249.d002197 3 H| ≤ _root_.GD.N0106.N0428.N0765.N1630.d029892
  apply (sq_le_sq₀ (abs_nonneg _) _root_.GD.N0106.N0428.N0765.N1630.d029895).mp
  rw [sq_abs, _root_.GD.N0106.N0428.N0765.N1630.d029898]
  exact _root_.GD.N0106.N0428.N0765.N1630.d029900 hH

theorem d029903 {k : ℕ} (hk : k = 1 ∨ k = 3)
    {H : ℝ} (hH : H ∈ Icc (0 : ℝ) 1) :
    |_root_.GD.N0232.N0720.N1249.d002197 k H| ≤ _root_.GD.N0106.N0428.N0765.N1630.d029893 k := by
  rcases hk with rfl | rfl
  · simpa [_root_.GD.N0106.N0428.N0765.N1630.d029893, _root_.GD.N0106.N0428.N0765.N1630.d029891] using _root_.GD.N0106.N0428.N0765.N1630.d029901 hH
  · simpa [_root_.GD.N0106.N0428.N0765.N1630.d029893, _root_.GD.N0106.N0428.N0765.N1630.d029892] using _root_.GD.N0106.N0428.N0765.N1630.d029902 hH

theorem d029904 {k : ℕ} (hk : k = 1 ∨ k = 3)
    {H O : ℝ} (hH : H ∈ Icc (0 : ℝ) 1) (hO : O ∈ Icc (0 : ℝ) 1) :
    |(H - O) * _root_.GD.N0232.N0720.N1249.d002197 k H| ≤ _root_.GD.N0106.N0428.N0765.N1630.d029893 k := by
  have hdiff : |H - O| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hH.1, hO.2], by linarith [hH.2, hO.1]⟩
  rw [abs_mul]
  exact (mul_le_mul hdiff (_root_.GD.N0106.N0428.N0765.N1630.d029903 hk hH)
    (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem d029905 (k : Fin 5) (hk : k.val = 1 ∨ k.val = 3)
    {eta : ℝ} (heta : 0 < eta) (p : ℝ × ℝ) :
    |(_root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 p) - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) *
      _root_.GD.N0232.N0720.N1249.d002197 k.val (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 p))| ≤
        _root_.GD.N0106.N0428.N0765.N1630.d029893 k.val :=
  _root_.GD.N0106.N0428.N0765.N1630.d029904 hk
    (_root_.GD.N0106.N0428.N0765.N1514.d029694 heta p)
    (_root_.GD.N0106.N0428.N0765.N1607.d012680 eta heta)

end
end GD.N0106.N0428.N0765.N1630

#print axioms _root_.GD.N0106.N0428.N0765.N1630.d029901
#print axioms _root_.GD.N0106.N0428.N0765.N1630.d029902
#print axioms _root_.GD.N0106.N0428.N0765.N1630.d029905
