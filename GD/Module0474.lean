import GD.Module0472







set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace GD.N0171
noncomputable section
open _root_.GD.N0181

def d007331 (N : ℕ) : ℝ := (_root_.GD.N0181.d007268 N) ^ 2 * (1 - _root_.GD.N0181.d007269 N) ^ ((7 : ℝ) / 2)
def d007332 (N : ℕ) : ℝ := 2 * _root_.GD.N0171.d007331 N * (1 / _root_.GD.N0181.d007268 N - 1) / (1 - _root_.GD.N0181.d007269 N)


theorem d007333 {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - (1 - x) ^ ((7 : ℝ) / 2) ≤ (7 / 2 : ℝ) * x := by
  have h := _root_.one_add_mul_self_le_rpow_one_add
    (s := -x) (by linarith : -1 ≤ -x) (p := (7 : ℝ) / 2) (by norm_num)
  have he : (1 + -x : ℝ) = 1 - x := by ring
  rw [he] at h
  linarith

theorem d007334 {N : ℕ} (hN : 2 ≤ N) : 0 < 1 - _root_.GD.N0181.d007269 N := by
  linarith [_root_.GD.N0181.d007282 hN]

theorem d007335 {N : ℕ} (hN : 2 ≤ N) : 0 < _root_.GD.N0171.d007331 N := by
  exact mul_pos (pow_pos (_root_.GD.N0181.d007276 hN) 2)
    (Real.rpow_pos_of_pos (_root_.GD.N0171.d007334 hN) _)

theorem d007336 {N : ℕ} (hN : 2 ≤ N) : _root_.GD.N0171.d007331 N ≤ 1 := by
  have hq := pow_le_one₀ (_root_.GD.N0181.d007276 hN).le (_root_.GD.N0181.d007277 hN).le (n := 2)
  have hd := Real.rpow_le_one (_root_.GD.N0171.d007334 hN).le
    (show 1 - _root_.GD.N0181.d007269 N ≤ 1 by linarith [_root_.GD.N0181.d007278 hN]) (by norm_num : (0 : ℝ) ≤ 7 / 2)
  exact (mul_le_mul hq hd
    (Real.rpow_nonneg (_root_.GD.N0171.d007334 hN).le _) (by norm_num)).trans_eq (one_mul 1)

theorem d007337 {N : ℕ} (hN : 2 ≤ N) :
    1 - (_root_.GD.N0181.d007268 N) ^ 2 ≤ 2 / (N : ℝ) := by
  unfold _root_.GD.N0181.d007268
  have hdiv : (2 : ℝ) / (N : ℝ) = 2 * (1 / (N : ℝ)) := by ring
  rw [hdiv]
  nlinarith [sq_nonneg ((1 : ℝ) / (N : ℝ))]

theorem d007338 {N : ℕ} (hN : 16 ≤ N) :
    0 ≤ 1 - _root_.GD.N0171.d007331 N ∧ 1 - _root_.GD.N0171.d007331 N ≤ 2 / (N : ℝ) + 7 / (2 * (N : ℝ) ^ 4) := by
  have hn2 : 2 ≤ N := by omega
  have hd0 := _root_.GD.N0181.d007278 hn2
  have hd1 : _root_.GD.N0181.d007269 N ≤ 1 := by linarith [_root_.GD.N0181.d007282 hn2]
  have hpow0 := Real.rpow_nonneg (_root_.GD.N0171.d007334 hn2).le ((7 : ℝ) / 2)
  have hpow1 := Real.rpow_le_one (_root_.GD.N0171.d007334 hn2).le
    (show 1 - _root_.GD.N0181.d007269 N ≤ 1 by linarith) (by norm_num : (0 : ℝ) ≤ 7 / 2)
  have hq := pow_le_one₀ (_root_.GD.N0181.d007276 hn2).le (_root_.GD.N0181.d007277 hn2).le (n := 2)
  have hbern := _root_.GD.N0171.d007333 hd0.le hd1
  have hmul := mul_le_mul_of_nonneg_right hq
    (show 0 ≤ 1 - (1 - _root_.GD.N0181.d007269 N) ^ ((7 : ℝ) / 2) by linarith)
  have hdec := mul_le_mul_of_nonneg_left (_root_.GD.N0181.d007290 hN)
    (by norm_num : (0 : ℝ) ≤ 7 / 2)
  have hqdec := _root_.GD.N0171.d007337 hn2
  refine ⟨by linarith [_root_.GD.N0171.d007336 hn2], ?_⟩
  unfold _root_.GD.N0171.d007331
  have he : (7 / 2 : ℝ) * (1 / (N : ℝ) ^ 4) = 7 / (2 * (N : ℝ) ^ 4) := by ring
  rw [he] at hdec
  nlinarith

theorem d007339 {N : ℕ} (hN : 2 ≤ N) :
    1 / _root_.GD.N0181.d007268 N - 1 = 1 / ((N : ℝ) - 1) := by
  have hn : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hm0 : (N : ℝ) - 1 ≠ 0 := by linarith
  unfold _root_.GD.N0181.d007268
  field_simp [hn0, hm0]
  <;> ring

theorem d007340 {N : ℕ} (hN : 2 ≤ N) : 0 ≤ _root_.GD.N0171.d007332 N := by
  have hn : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  unfold _root_.GD.N0171.d007332
  rw [_root_.GD.N0171.d007339 hN]
  exact div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (_root_.GD.N0171.d007335 hN).le)
      (one_div_nonneg.mpr (by linarith))) (_root_.GD.N0171.d007334 hN).le

theorem d007341 {N : ℕ} (hN : 2 ≤ N) :
    _root_.GD.N0171.d007332 N ≤ 4 / ((N : ℝ) - 1) := by
  have hn : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hm : 0 < (N : ℝ) - 1 := by linarith
  have hd := _root_.GD.N0171.d007334 hN
  have he := _root_.GD.N0181.d007282 hN
  have h1 := mul_le_mul_of_nonneg_left (_root_.GD.N0171.d007336 hN) (by norm_num : (0 : ℝ) ≤ 2)
  have h2 := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ 1 - _root_.GD.N0181.d007269 N by linarith)
    (by norm_num : (0 : ℝ) ≤ 4)
  have hprod : (2 * _root_.GD.N0171.d007331 N) * (1 / ((N : ℝ) - 1)) ≤
      (4 * (1 - _root_.GD.N0181.d007269 N)) * (1 / ((N : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_right (by linarith) (one_div_nonneg.mpr hm.le)
  unfold _root_.GD.N0171.d007332
  rw [_root_.GD.N0171.d007339 hN]
  apply (div_le_iff₀ hd).2
  calc
    _ ≤ (4 * (1 - _root_.GD.N0181.d007269 N)) * (1 / ((N : ℝ) - 1)) := hprod
    _ = (4 / ((N : ℝ) - 1)) * (1 - _root_.GD.N0181.d007269 N) := by ring

theorem d007342 {N : ℕ} (hN : 16 ≤ N) :
    0 ≤ _root_.GD.N0171.d007332 N ∧ _root_.GD.N0171.d007332 N ≤ 4 / ((N : ℝ) - 1) ∧ _root_.GD.N0171.d007332 N ≤ 5 / (N : ℝ) := by
  have hn : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hm : 0 < (N : ℝ) - 1 := by linarith
  have hb : (4 : ℝ) / ((N : ℝ) - 1) ≤ 5 / (N : ℝ) := by
    apply (div_le_div_iff₀ hm hn0).2
    linarith
  exact ⟨_root_.GD.N0171.d007340 (by omega), _root_.GD.N0171.d007341 (by omega), (_root_.GD.N0171.d007341 (by omega)).trans hb⟩

end
end GD.N0171

#print axioms _root_.GD.N0171.d007333
#print axioms _root_.GD.N0171.d007338
#print axioms _root_.GD.N0171.d007342
