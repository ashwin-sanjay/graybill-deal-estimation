import GD.Module0473








set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace GD.N0204
noncomputable section
open _root_.GD.N0181 _root_.GD.N0167

def d007392 (N : ℕ) : ℝ := 2 * _root_.GD.N0181.d007269 N / ((1 - _root_.GD.N0181.d007269 N) * (_root_.GD.N0181.d007271 N + 2 * _root_.GD.N0181.d007270 N))
def d007393 (N : ℕ) : ℝ := (1 + _root_.GD.N0204.d007392 N) ^ (-(7 : ℝ) / 2)
def d007394 (N : ℕ) : ℝ := _root_.GD.N0204.d007393 N * (1 - _root_.GD.N0167.d007307 N)


theorem d007395 {x : ℝ} (hx : 0 ≤ x) :
    1 - (1 + x) ^ (-(7 : ℝ) / 2) ≤ (7 / 2 : ℝ) * x := by
  have hp : 0 < 1 + x := by linarith
  have hlog := Real.log_le_sub_one_of_pos hp
  have hexp := Real.add_one_le_exp (Real.log (1 + x) * (-(7 : ℝ) / 2))
  rw [Real.rpow_def_of_pos hp]
  linarith

theorem d007396 {N : ℕ} (hN : 2 ≤ N) : 0 < _root_.GD.N0204.d007392 N := by
  have hd : 0 < 1 - _root_.GD.N0181.d007269 N := by linarith [_root_.GD.N0181.d007282 hN]
  have ha := _root_.GD.N0181.d007293 hN
  have he := _root_.GD.N0181.d007291 hN
  exact div_pos (mul_pos (by norm_num) (_root_.GD.N0181.d007278 hN))
    (mul_pos hd (by linarith))


theorem d007397 {N : ℕ} (hN : 2 ≤ N) :
    _root_.GD.N0181.d007270 N ≤ (1 - _root_.GD.N0181.d007269 N) * (_root_.GD.N0181.d007271 N + 2 * _root_.GD.N0181.d007270 N) := by
  have hd : (1 / 2 : ℝ) ≤ 1 - _root_.GD.N0181.d007269 N := by linarith [_root_.GD.N0181.d007282 hN]
  have ha := _root_.GD.N0181.d007293 hN
  have he := _root_.GD.N0181.d007291 hN
  calc
    _root_.GD.N0181.d007270 N = (1 / 2 : ℝ) * (2 * _root_.GD.N0181.d007270 N) := by ring
    _ ≤ (1 - _root_.GD.N0181.d007269 N) * (_root_.GD.N0181.d007271 N + 2 * _root_.GD.N0181.d007270 N) :=
      mul_le_mul hd (by linarith) (by positivity) (by linarith)


theorem d007398 {N : ℕ} (hN : 16 ≤ N) :
    _root_.GD.N0204.d007392 N ≤ 2 / (N : ℝ) ^ 2 := by
  have hn2 : 2 ≤ N := by omega
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have he := _root_.GD.N0181.d007291 hn2
  have hden := _root_.GD.N0204.d007397 hn2
  have hden0 : 0 < (1 - _root_.GD.N0181.d007269 N) * (_root_.GD.N0181.d007271 N + 2 * _root_.GD.N0181.d007270 N) := he.trans_le hden
  have hd : _root_.GD.N0181.d007269 N ≤ _root_.GD.N0181.d007271 N := _root_.GD.N0181.d007290 hN
  have ha := _root_.GD.N0181.d007293 hn2
  calc
    _root_.GD.N0204.d007392 N ≤ 2 * _root_.GD.N0181.d007271 N / ((1 - _root_.GD.N0181.d007269 N) * (_root_.GD.N0181.d007271 N + 2 * _root_.GD.N0181.d007270 N)) :=
      div_le_div_of_nonneg_right (by linarith) hden0.le
    _ ≤ 2 * _root_.GD.N0181.d007271 N / _root_.GD.N0181.d007270 N :=
      div_le_div_of_nonneg_left (by positivity) he hden
    _ = 2 / (N : ℝ) ^ 2 := by
      unfold _root_.GD.N0181.d007271 _root_.GD.N0181.d007270
      field_simp [hn.ne'] <;> ring

theorem d007399 {N : ℕ} (hN : 2 ≤ N) : 0 < _root_.GD.N0204.d007393 N :=
  Real.rpow_pos_of_pos (by linarith [_root_.GD.N0204.d007396 hN]) _

theorem d007400 {N : ℕ} (hN : 2 ≤ N) : _root_.GD.N0204.d007393 N ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos
    (by linarith [_root_.GD.N0204.d007396 hN]) (by norm_num)


theorem d007401 {N : ℕ} (hN : 16 ≤ N) :
    0 ≤ 1 - _root_.GD.N0204.d007393 N ∧ 1 - _root_.GD.N0204.d007393 N ≤ 7 / (N : ℝ) ^ 2 := by
  have hN2 : 2 ≤ N := by omega
  have hpow := _root_.GD.N0204.d007395 (_root_.GD.N0204.d007396 hN2).le
  have hx := mul_le_mul_of_nonneg_left (_root_.GD.N0204.d007398 hN)
    (by norm_num : (0 : ℝ) ≤ 7 / 2)
  refine ⟨by linarith [_root_.GD.N0204.d007400 hN2], ?_⟩
  change 1 - _root_.GD.N0204.d007393 N ≤ (7 / 2 : ℝ) * _root_.GD.N0204.d007392 N at hpow
  calc
    1 - _root_.GD.N0204.d007393 N ≤ (7 / 2 : ℝ) * _root_.GD.N0204.d007392 N := hpow
    _ ≤ (7 / 2 : ℝ) * (2 / (N : ℝ) ^ 2) := hx
    _ = 7 / (N : ℝ) ^ 2 := by ring

theorem d007402 {N : ℕ} (hN : 16 ≤ N) : 0 < _root_.GD.N0204.d007394 N :=
  mul_pos (_root_.GD.N0204.d007399 (by omega)) (sub_pos.mpr (_root_.GD.N0167.d007328 hN))

theorem d007403 {N : ℕ} (hN : 2 ≤ N) : _root_.GD.N0204.d007394 N ≤ _root_.GD.N0204.d007393 N := by
  have h := mul_le_mul_of_nonneg_left
    (show 1 - _root_.GD.N0167.d007307 N ≤ 1 by linarith [_root_.GD.N0167.d007323 hN]) (_root_.GD.N0204.d007399 hN).le
  simpa only [_root_.GD.N0204.d007394, mul_one] using h

theorem d007404 {N : ℕ} (hN : 2 ≤ N) : _root_.GD.N0204.d007394 N ≤ 1 :=
  (_root_.GD.N0204.d007403 hN).trans (_root_.GD.N0204.d007400 hN)


theorem d007405 {N : ℕ} (hN : 16 ≤ N) :
    0 ≤ 1 - _root_.GD.N0204.d007394 N ∧ 1 - _root_.GD.N0204.d007394 N ≤ 7 / (N : ℝ) ^ 2 + _root_.GD.N0167.d007307 N := by
  have hN2 : 2 ≤ N := by omega
  have hmul := mul_le_mul_of_nonneg_right (_root_.GD.N0204.d007400 hN2) (_root_.GD.N0167.d007323 hN2)
  have hdef := (_root_.GD.N0204.d007401 hN).2
  refine ⟨by linarith [_root_.GD.N0204.d007404 hN2], ?_⟩
  calc
    1 - _root_.GD.N0204.d007394 N = (1 - _root_.GD.N0204.d007393 N) + _root_.GD.N0204.d007393 N * _root_.GD.N0167.d007307 N := by unfold _root_.GD.N0204.d007394; ring
    _ ≤ 7 / (N : ℝ) ^ 2 + _root_.GD.N0167.d007307 N := by nlinarith


theorem d007406 {N : ℕ} (hN : 16 ≤ N) :
    0 ≤ 1 - _root_.GD.N0204.d007394 N ∧ 1 - _root_.GD.N0204.d007394 N ≤ 7 / (N : ℝ) ^ 2 + 6 / (N : ℝ) := by
  have h := _root_.GD.N0204.d007405 hN
  refine ⟨h.1, h.2.trans ?_⟩
  have hl := _root_.GD.N0167.d007326 (by omega : 2 ≤ N)
  linarith only [hl]

end
end GD.N0204

#print axioms _root_.GD.N0204.d007395
#print axioms _root_.GD.N0204.d007398
#print axioms _root_.GD.N0204.d007399
#print axioms _root_.GD.N0204.d007400
#print axioms _root_.GD.N0204.d007401
#print axioms _root_.GD.N0204.d007402
#print axioms _root_.GD.N0204.d007404
#print axioms _root_.GD.N0204.d007405
#print axioms _root_.GD.N0204.d007406
