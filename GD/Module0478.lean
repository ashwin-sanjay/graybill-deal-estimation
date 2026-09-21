import GD.Module0477
import GD.Module0474










set_option autoImplicit false
set_option warningAsError true

namespace GD.N0190
noncomputable section

open _root_.GD.N0181 _root_.GD.N0167
open _root_.GD.N0171 _root_.GD.N0204

theorem d007407 {N : ℕ} (hN : 16 ≤ N) :
    (3 : ℝ) / (N : ℝ) ^ 3 < 1 := by
  have hn : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) hn 3
  apply (div_lt_one (pow_pos hn0 3)).2
  norm_num at hpow
  linarith

theorem d007408 {N : ℕ} (hN : 16 ≤ N) :
    _root_.GD.N0181.d007273 N ≤ 3 / (N : ℝ) ^ 3 ∧ (3 : ℝ) / (N : ℝ) ^ 3 < 1 :=
  ⟨_root_.GD.N0181.d007297 hN, _root_.GD.N0190.d007407 hN⟩


theorem d007409 {N : ℕ} (hN : 16 ≤ N) :
    2 / (N : ℝ) ^ 2 + (Real.pi / 4) * _root_.GD.N0181.d007273 N ≤
      2 / (N : ℝ) ^ 2 + 3 / (N : ℝ) ^ 3 := by
  have hpi : Real.pi / 4 ≤ 1 := by linarith [Real.pi_lt_four]
  have hm := mul_le_mul_of_nonneg_right hpi (_root_.GD.N0181.d007296 N)
  have ht := _root_.GD.N0181.d007297 hN
  linarith only [hm, ht]


theorem d007410 {N : ℕ} (hN : 16 ≤ N) :
    2 * ((N : ℝ) ^ 2 - 1 / (1 - 1 / (N : ℝ) ^ 2)) ≤ 2 * (N : ℝ) ^ 2 := by
  have heta := _root_.GD.N0181.d007292 hN
  have hden : 0 ≤ 1 - _root_.GD.N0181.d007270 N := by linarith
  have hi := one_div_nonneg.mpr hden
  change 0 ≤ (1 : ℝ) / (1 - 1 / (N : ℝ) ^ 2) at hi
  linarith only [hi]


theorem d007411 {N : ℕ} (hN : 16 ≤ N) :
    (0 ≤ Real.pi / 4 - _root_.GD.N0181.d007274 N ∧
      Real.pi / 4 - _root_.GD.N0181.d007274 N ≤ 2 / (N : ℝ) ^ 2 + (Real.pi / 4) * _root_.GD.N0181.d007273 N ∧
      2 / (N : ℝ) ^ 2 + (Real.pi / 4) * _root_.GD.N0181.d007273 N ≤
        2 / (N : ℝ) ^ 2 + 3 / (N : ℝ) ^ 3) ∧
    (0 < _root_.GD.N0181.d007275 N ∧
      _root_.GD.N0181.d007275 N ≤ 2 * ((N : ℝ) ^ 2 - 1 / (1 - 1 / (N : ℝ) ^ 2)) ∧
      2 * ((N : ℝ) ^ 2 - 1 / (1 - 1 / (N : ℝ) ^ 2)) ≤ 2 * (N : ℝ) ^ 2) := by
  have hJ := _root_.GD.N0181.d007299 hN
  have hM := _root_.GD.N0181.d007302 hN
  refine ⟨⟨hJ.1, hJ.2, _root_.GD.N0190.d007409 hN⟩, ⟨hM.1, ?_, _root_.GD.N0190.d007410 hN⟩⟩
  simpa only [_root_.GD.N0181.d007270] using hM.2.1

theorem d007412 {N : ℕ} (hN : 16 ≤ N) :
    (4 : ℝ) / ((N : ℝ) - 1) ≤ 5 / (N : ℝ) := by
  have hn : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hm : 0 < (N : ℝ) - 1 := by linarith
  apply (div_le_div_iff₀ hm hn0).2
  linarith

theorem d007413 {N : ℕ} (hN : 16 ≤ N) :
    0 ≤ _root_.GD.N0171.d007332 N ∧ _root_.GD.N0171.d007332 N ≤ 4 / ((N : ℝ) - 1) ∧
      (4 : ℝ) / ((N : ℝ) - 1) ≤ 5 / (N : ℝ) :=
  ⟨_root_.GD.N0171.d007340 (by omega), _root_.GD.N0171.d007341 (by omega), _root_.GD.N0190.d007412 hN⟩


theorem d007414 {N : ℕ} (hN : 16 ≤ N) :
    _root_.GD.N0167.d007307 N ≤ 6 * Real.log (N : ℝ) / ((N : ℝ) * ((N : ℝ) - 1)) ∧
      6 * Real.log (N : ℝ) / ((N : ℝ) * ((N : ℝ) - 1)) ≤ 6 / (N : ℝ) ∧
      (6 : ℝ) / (N : ℝ) < 1 :=
  ⟨_root_.GD.N0167.d007324 (by omega), _root_.GD.N0167.d007325 (by omega), _root_.GD.N0167.d007327 hN⟩


theorem d007415 {N : ℕ} (hN : 16 ≤ N) :
    0 < _root_.GD.N0204.d007393 N ∧ _root_.GD.N0204.d007393 N ≤ 1 ∧ 0 < _root_.GD.N0204.d007394 N ∧ _root_.GD.N0204.d007394 N ≤ 1 ∧ 0 < _root_.GD.N0171.d007331 N ∧ _root_.GD.N0171.d007331 N ≤ 1 ∧
      1 - _root_.GD.N0204.d007394 N ≤ 7 / (N : ℝ) ^ 2 + 6 / (N : ℝ) ∧
      1 - _root_.GD.N0171.d007331 N ≤ 2 / (N : ℝ) + 7 / (2 * (N : ℝ) ^ 4) ∧
      0 ≤ _root_.GD.N0181.d007269 N * _root_.GD.N0181.d007275 N ∧ _root_.GD.N0181.d007269 N * _root_.GD.N0181.d007275 N ≤ 2 / (N : ℝ) ^ 2 ∧
      0 ≤ _root_.GD.N0171.d007332 N ∧ _root_.GD.N0171.d007332 N ≤ 4 / ((N : ℝ) - 1) ∧
      (4 : ℝ) / ((N : ℝ) - 1) ≤ 5 / (N : ℝ) := by
  have hN2 : 2 ≤ N := by omega
  have hmass := _root_.GD.N0181.d007303 hN
  have hmesh := _root_.GD.N0190.d007413 hN
  refine ⟨_root_.GD.N0204.d007399 hN2, _root_.GD.N0204.d007400 hN2, _root_.GD.N0204.d007402 hN, _root_.GD.N0204.d007404 hN2,
    _root_.GD.N0171.d007335 hN2, _root_.GD.N0171.d007336 hN2, (_root_.GD.N0204.d007406 hN).2, (_root_.GD.N0171.d007338 hN).2,
    hmass.1, ?_, hmesh.1, hmesh.2.1, hmesh.2.2⟩
  simpa only [div_pow, one_pow, mul_one_div] using hmass.2

end
end GD.N0190

#print axioms _root_.GD.N0190.d007407
#print axioms _root_.GD.N0190.d007408
#print axioms _root_.GD.N0190.d007409
#print axioms _root_.GD.N0190.d007410
#print axioms _root_.GD.N0190.d007411
#print axioms _root_.GD.N0190.d007412
#print axioms _root_.GD.N0190.d007413
#print axioms _root_.GD.N0190.d007414
#print axioms _root_.GD.N0190.d007415
