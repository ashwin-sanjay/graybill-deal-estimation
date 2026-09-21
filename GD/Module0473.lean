import GD.Module0472








set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace GD.N0167
noncomputable section
open _root_.GD.N0181

def d007304 (N : ℕ) : ℝ := -Real.log (_root_.GD.N0181.d007268 N)
def d007305 (N : ℕ) : ℝ := (N : ℝ) ^ 2 * _root_.GD.N0167.d007304 N
def d007306 (N : ℕ) : ℝ := ((N ^ 3 - N ^ 2 : ℕ) : ℝ) * _root_.GD.N0167.d007304 N
def d007307 (N : ℕ) : ℝ := Real.log (_root_.GD.N0181.d007272 N / _root_.GD.N0181.d007271 N) / _root_.GD.N0167.d007306 N


theorem d007308 {N : ℕ} (hN : 2 ≤ N) :
    _root_.GD.N0167.d007306 N = (N : ℝ) ^ 2 * ((N : ℝ) - 1) * _root_.GD.N0167.d007304 N := by
  have hpow : N ^ 2 ≤ N ^ 3 :=
    pow_le_pow_right₀ (by omega : 1 ≤ N) (by norm_num : 2 ≤ 3)
  unfold _root_.GD.N0167.d007306
  simp only [Nat.cast_sub hpow, Nat.cast_pow]
  ring

theorem d007309 {N : ℕ} (hN : 2 ≤ N) :
    _root_.GD.N0167.d007305 N + _root_.GD.N0167.d007306 N = (N : ℝ) ^ 3 * _root_.GD.N0167.d007304 N := by
  rw [_root_.GD.N0167.d007305, _root_.GD.N0167.d007308 hN]
  ring

theorem d007310 {N : ℕ} (hN : 2 ≤ N) : _root_.GD.N0181.d007268 N = Real.exp (-_root_.GD.N0167.d007304 N) := by
  unfold _root_.GD.N0167.d007304
  rw [neg_neg, Real.exp_log (_root_.GD.N0181.d007276 hN)]

theorem d007311 {N : ℕ} (hN : 2 ≤ N) : _root_.GD.N0181.d007269 N = Real.exp (-_root_.GD.N0167.d007305 N) := by
  calc
    _root_.GD.N0181.d007269 N = Real.exp (Real.log (_root_.GD.N0181.d007269 N)) := (Real.exp_log (_root_.GD.N0181.d007278 hN)).symm
    _ = Real.exp (-_root_.GD.N0167.d007305 N) := by
      congr 1
      rw [_root_.GD.N0181.d007269, Real.log_pow]
      unfold _root_.GD.N0167.d007305 _root_.GD.N0167.d007304
      simp only [Nat.cast_pow, mul_neg, neg_neg]


theorem d007312 {N : ℕ} (hN : 2 ≤ N) : 1 / (N : ℝ) ≤ _root_.GD.N0167.d007304 N := by
  have hl := Real.log_le_sub_one_of_pos (_root_.GD.N0181.d007276 hN)
  unfold _root_.GD.N0167.d007304
  unfold _root_.GD.N0181.d007268 at hl ⊢
  linarith

theorem d007313 {N : ℕ} (hN : 2 ≤ N) : 0 < _root_.GD.N0167.d007304 N := by
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  exact (one_div_pos.mpr hn).trans_le (_root_.GD.N0167.d007312 hN)

theorem d007314 {N : ℕ} (hN : 2 ≤ N) : (N : ℝ) ≤ _root_.GD.N0167.d007305 N := by
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  calc
    (N : ℝ) = (N : ℝ) ^ 2 * (1 / (N : ℝ)) := by
      field_simp [hn.ne'] <;> ring
    _ ≤ (N : ℝ) ^ 2 * _root_.GD.N0167.d007304 N := mul_le_mul_of_nonneg_left (_root_.GD.N0167.d007312 hN) (sq_nonneg _)
    _ = _root_.GD.N0167.d007305 N := rfl

theorem d007315 {N : ℕ} (hN : 2 ≤ N) : Real.log 2 < (N : ℝ) := by
  have hn : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem d007316 {N : ℕ} (hN : 2 ≤ N) : Real.log 2 < _root_.GD.N0167.d007305 N :=
  (_root_.GD.N0167.d007315 hN).trans_le (_root_.GD.N0167.d007314 hN)

theorem d007317 {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ) * ((N : ℝ) - 1) ≤ _root_.GD.N0167.d007306 N := by
  have hn : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hm : 0 ≤ (N : ℝ) - 1 := by linarith
  calc
    (N : ℝ) * ((N : ℝ) - 1) =
        (N : ℝ) ^ 2 * ((N : ℝ) - 1) * (1 / (N : ℝ)) := by
      field_simp [hn0.ne'] <;> ring
    _ ≤ (N : ℝ) ^ 2 * ((N : ℝ) - 1) * _root_.GD.N0167.d007304 N :=
      mul_le_mul_of_nonneg_left (_root_.GD.N0167.d007312 hN) (mul_nonneg (sq_nonneg _) hm)
    _ = _root_.GD.N0167.d007306 N := (_root_.GD.N0167.d007308 hN).symm

theorem d007318 {N : ℕ} (hN : 2 ≤ N) : 0 < _root_.GD.N0167.d007306 N := by
  have hn : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact (mul_pos (by linarith : (0 : ℝ) < (N : ℝ))
    (by linarith : 0 < (N : ℝ) - 1)).trans_le (_root_.GD.N0167.d007317 hN)


theorem d007319 {N : ℕ} (hN : 2 ≤ N) : _root_.GD.N0181.d007272 N / _root_.GD.N0181.d007271 N = (N : ℝ) ^ 6 := by
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  unfold _root_.GD.N0181.d007272 _root_.GD.N0181.d007271
  field_simp [hn.ne'] <;> ring

theorem d007320 {N : ℕ} (hN : 2 ≤ N) :
    Real.log (_root_.GD.N0181.d007272 N / _root_.GD.N0181.d007271 N) = 6 * Real.log (N : ℝ) := by
  rw [_root_.GD.N0167.d007319 hN, Real.log_pow]
  norm_num

theorem d007321 {N : ℕ} (hN : 2 ≤ N) : 0 < Real.log (_root_.GD.N0181.d007272 N / _root_.GD.N0181.d007271 N) := by
  have hn : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  rw [_root_.GD.N0167.d007320 hN]
  positivity

theorem d007322 {N : ℕ} (hN : 2 ≤ N) : 0 < _root_.GD.N0167.d007307 N :=
  div_pos (_root_.GD.N0167.d007321 hN) (_root_.GD.N0167.d007318 hN)

theorem d007323 {N : ℕ} (hN : 2 ≤ N) : 0 ≤ _root_.GD.N0167.d007307 N :=
  (_root_.GD.N0167.d007322 hN).le


theorem d007324 {N : ℕ} (hN : 2 ≤ N) :
    _root_.GD.N0167.d007307 N ≤ 6 * Real.log (N : ℝ) / ((N : ℝ) * ((N : ℝ) - 1)) := by
  have hn : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hm : 0 < (N : ℝ) - 1 := by linarith
  have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  unfold _root_.GD.N0167.d007307
  rw [_root_.GD.N0167.d007320 hN]
  exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hl)
    (mul_pos hn0 hm) (_root_.GD.N0167.d007317 hN)

theorem d007325 {N : ℕ} (hN : 2 ≤ N) :
    6 * Real.log (N : ℝ) / ((N : ℝ) * ((N : ℝ) - 1)) ≤ 6 / (N : ℝ) := by
  have hn : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hm : 0 < (N : ℝ) - 1 := by linarith
  have hl := Real.log_le_sub_one_of_pos hn0
  calc
    6 * Real.log (N : ℝ) / ((N : ℝ) * ((N : ℝ) - 1)) ≤
        (6 * ((N : ℝ) - 1)) / ((N : ℝ) * ((N : ℝ) - 1)) :=
      div_le_div_of_nonneg_right (by linarith) (mul_nonneg hn0.le hm.le)
    _ = 6 / (N : ℝ) := by field_simp [hn0.ne', hm.ne'] <;> ring

theorem d007326 {N : ℕ} (hN : 2 ≤ N) : _root_.GD.N0167.d007307 N ≤ 6 / (N : ℝ) :=
  (_root_.GD.N0167.d007324 hN).trans (_root_.GD.N0167.d007325 hN)

theorem d007327 {N : ℕ} (hN : 16 ≤ N) : (6 : ℝ) / (N : ℝ) < 1 := by
  have hn : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact (div_lt_one (by linarith : (0 : ℝ) < (N : ℝ))).2 (by linarith)

theorem d007328 {N : ℕ} (hN : 16 ≤ N) : _root_.GD.N0167.d007307 N < 1 :=
  (_root_.GD.N0167.d007326 (by omega : 2 ≤ N)).trans_lt (_root_.GD.N0167.d007327 hN)


theorem d007329 {N : ℕ} (hN : 16 ≤ N) : Real.log (_root_.GD.N0181.d007272 N / _root_.GD.N0181.d007271 N) < _root_.GD.N0167.d007306 N :=
  (div_lt_one (_root_.GD.N0167.d007318 (by omega : 2 ≤ N))).mp (_root_.GD.N0167.d007328 hN)

theorem d007330 {N : ℕ} (hN : 16 ≤ N) :
    0 < _root_.GD.N0167.d007306 N - Real.log (_root_.GD.N0181.d007272 N / _root_.GD.N0181.d007271 N) := sub_pos.mpr (_root_.GD.N0167.d007329 hN)

end
end GD.N0167

#print axioms _root_.GD.N0167.d007312
#print axioms _root_.GD.N0167.d007314
#print axioms _root_.GD.N0167.d007316
#print axioms _root_.GD.N0167.d007317
#print axioms _root_.GD.N0167.d007311
#print axioms _root_.GD.N0167.d007320
#print axioms _root_.GD.N0167.d007324
#print axioms _root_.GD.N0167.d007328
#print axioms _root_.GD.N0167.d007330
