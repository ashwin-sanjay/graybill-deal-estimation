import GD.Module0471









set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace GD.N0181
noncomputable section

def d007268 (N : ℕ) : ℝ := 1 - 1 / (N : ℝ)
def d007269 (N : ℕ) : ℝ := (_root_.GD.N0181.d007268 N) ^ (N ^ 2)
def d007270 (N : ℕ) : ℝ := 1 / (N : ℝ) ^ 2
def d007271 (N : ℕ) : ℝ := 1 / (N : ℝ) ^ 4
def d007272 (N : ℕ) : ℝ := (N : ℝ) ^ 2
def d007273 (N : ℕ) : ℝ := 1 / (N : ℝ) ^ 3 + 8 / (N : ℝ) ^ 4

def d007274 (N : ℕ) : ℝ := _root_.GD.N0203.d007249 (_root_.GD.N0181.d007270 N) (_root_.GD.N0181.d007271 N) (_root_.GD.N0181.d007272 N)
def d007275 (N : ℕ) : ℝ := _root_.GD.N0203.d007250 (_root_.GD.N0181.d007270 N) (_root_.GD.N0181.d007271 N) (_root_.GD.N0181.d007272 N)

theorem d007276 {N : ℕ} (hN : 2 ≤ N) : 0 < _root_.GD.N0181.d007268 N := by
  have hn : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hi : (1 : ℝ) / (N : ℝ) < 1 := (div_lt_one hn0).2 (by linarith)
  unfold _root_.GD.N0181.d007268
  linarith

theorem d007277 {N : ℕ} (hN : 2 ≤ N) : _root_.GD.N0181.d007268 N < 1 := by
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  unfold _root_.GD.N0181.d007268
  have hi := one_div_pos.mpr hn
  linarith

theorem d007278 {N : ℕ} (hN : 2 ≤ N) : 0 < _root_.GD.N0181.d007269 N :=
  pow_pos (_root_.GD.N0181.d007276 hN) _


theorem d007279 {N : ℕ} (hN : 2 ≤ N) : (_root_.GD.N0181.d007268 N) ^ N < 1 / 2 := by
  have hn : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hm : 0 < (N : ℝ) - 1 := by linarith
  have hi : 0 < 1 / ((N : ℝ) - 1) := one_div_pos.mpr hm
  have hb := one_add_mul_le_pow
    (a := (1 : ℝ) / ((N : ℝ) - 1)) (show -2 ≤ 1 / ((N : ℝ) - 1) by linarith) N
  have hquot : 1 < (N : ℝ) / ((N : ℝ) - 1) :=
    (lt_div_iff₀ hm).2 (by linarith)
  have htwo : (2 : ℝ) < (1 + 1 / ((N : ℝ) - 1)) ^ N := by
    rw [mul_one_div] at hb
    linarith
  have hid : (1 + 1 / ((N : ℝ) - 1)) * _root_.GD.N0181.d007268 N = 1 := by
    unfold _root_.GD.N0181.d007268
    field_simp [hn0.ne', hm.ne'] <;> ring
  have hp : (1 + 1 / ((N : ℝ) - 1)) ^ N * (_root_.GD.N0181.d007268 N) ^ N = 1 := by
    rw [← mul_pow, hid, one_pow]
  have hprod := mul_lt_mul_of_pos_right htwo (pow_pos (_root_.GD.N0181.d007276 hN) N)
  rw [hp] at hprod
  linarith


theorem d007280 {N : ℕ} (hN : 2 ≤ N) :
    (2 : ℝ) < 1 / (_root_.GD.N0181.d007268 N) ^ N := by
  apply (lt_div_iff₀ (pow_pos (_root_.GD.N0181.d007276 hN) N)).2
  linarith [_root_.GD.N0181.d007279 hN]


theorem d007281 {N : ℕ} (hN : 2 ≤ N) : _root_.GD.N0181.d007269 N < 1 / (2 : ℝ) ^ N := by
  have hp := pow_lt_pow_left₀ (_root_.GD.N0181.d007279 hN)
    (pow_nonneg (_root_.GD.N0181.d007276 hN).le N) (show N ≠ 0 by omega)
  calc
    _root_.GD.N0181.d007269 N = ((_root_.GD.N0181.d007268 N) ^ N) ^ N := by simp only [_root_.GD.N0181.d007269, pow_two, pow_mul]
    _ < (1 / 2 : ℝ) ^ N := hp
    _ = 1 / (2 : ℝ) ^ N := by rw [div_pow, one_pow]

theorem d007282 {N : ℕ} (hN : 2 ≤ N) : _root_.GD.N0181.d007269 N < 1 / 2 := by
  have hpow := one_div_pow_le_one_div_pow_of_le (a := (2 : ℝ))
    (by norm_num) (show 1 ≤ N by omega)
  exact (_root_.GD.N0181.d007281 hN).trans_le (by simpa only [pow_one] using hpow)


theorem d007283 {N : ℕ} (hN : 2 ≤ N) :
    1 / (_root_.GD.N0181.d007268 N) ^ N = (1 + 1 / ((N : ℝ) - 1)) ^ N := by
  have hn : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hm0 : (N : ℝ) - 1 ≠ 0 := by linarith
  have hi : 1 / _root_.GD.N0181.d007268 N = 1 + 1 / ((N : ℝ) - 1) := by
    unfold _root_.GD.N0181.d007268
    field_simp [hn0, hm0] <;> ring
  calc
    1 / (_root_.GD.N0181.d007268 N) ^ N = (1 / _root_.GD.N0181.d007268 N) ^ N := by rw [div_pow, one_pow]
    _ = (1 + 1 / ((N : ℝ) - 1)) ^ N := by rw [hi]

theorem d007284 : (2 : ℝ) ^ (16 : ℕ) = (16 : ℝ) ^ 4 := by
  norm_num

theorem d007285 : (17 / 16 : ℝ) ^ 4 < 2 := by
  norm_num


theorem d007286 {N : ℕ} (hN : 16 ≤ N) :
    (((N : ℝ) + 1) / (N : ℝ)) ^ 4 ≤ (17 / 16 : ℝ) ^ 4 := by
  have hn : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hr : ((N : ℝ) + 1) / (N : ℝ) ≤ (17 / 16 : ℝ) :=
    (div_le_iff₀ hn0).2 (by linarith)
  exact pow_le_pow_left₀ (div_nonneg (by positivity) hn0.le) hr 4


theorem d007287 {N : ℕ} (hN : 16 ≤ N) :
    1 / (N : ℝ) ^ 4 < 1 / 2 := by
  have hn : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) hn 4
  apply (div_lt_iff₀ (pow_pos hn0 4)).2
  norm_num at hp
  nlinarith


theorem d007288 {N : ℕ} (hN : 16 ≤ N) : (N : ℝ) ^ 4 ≤ (2 : ℝ) ^ N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hnR : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hstep : (n : ℝ) + 1 ≤ (17 / 16 : ℝ) * (n : ℝ) := by linarith
    have hpow := pow_le_pow_left₀ (show 0 ≤ (n : ℝ) + 1 by positivity) hstep 4
    rw [mul_pow] at hpow
    have hratio : (17 / 16 : ℝ) ^ 4 ≤ 2 := _root_.GD.N0181.d007285.le
    have hmul := mul_le_mul_of_nonneg_right hratio (pow_nonneg (Nat.cast_nonneg n) 4)
    have hnext : ((n : ℝ) + 1) ^ 4 ≤ 2 * (n : ℝ) ^ 4 := hpow.trans hmul
    calc
      ((n + 1 : ℕ) : ℝ) ^ 4 = ((n : ℝ) + 1) ^ 4 := by norm_cast
      _ ≤ 2 * (n : ℝ) ^ 4 := hnext
      _ ≤ 2 * (2 : ℝ) ^ n := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

theorem d007289 {N : ℕ} (hN : 16 ≤ N) :
    1 / (2 : ℝ) ^ N ≤ 1 / (N : ℝ) ^ 4 := by
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  exact one_div_le_one_div_of_le (pow_pos hn 4) (_root_.GD.N0181.d007288 hN)

theorem d007290 {N : ℕ} (hN : 16 ≤ N) : _root_.GD.N0181.d007269 N ≤ 1 / (N : ℝ) ^ 4 :=
  (_root_.GD.N0181.d007281 (by omega : 2 ≤ N)).le.trans (_root_.GD.N0181.d007289 hN)

theorem d007291 {N : ℕ} (hN : 2 ≤ N) : 0 < _root_.GD.N0181.d007270 N := by
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  unfold _root_.GD.N0181.d007270
  positivity

theorem d007292 {N : ℕ} (hN : 16 ≤ N) : _root_.GD.N0181.d007270 N < 1 / 2 := by
  have hn : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) hn 2
  unfold _root_.GD.N0181.d007270
  apply (div_lt_iff₀ (pow_pos hn0 2)).2
  norm_num at hpow
  nlinarith

theorem d007293 {N : ℕ} (hN : 2 ≤ N) : 0 < _root_.GD.N0181.d007271 N := by
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  unfold _root_.GD.N0181.d007271
  positivity

theorem d007294 {N : ℕ} (hN : 2 ≤ N) : _root_.GD.N0181.d007271 N ≤ _root_.GD.N0181.d007272 N := by
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  calc
    _root_.GD.N0181.d007271 N ≤ 1 := (div_le_one (pow_pos hn0 4)).2 (one_le_pow₀ hn)
    _ ≤ _root_.GD.N0181.d007272 N := one_le_pow₀ hn


theorem d007295 {N : ℕ} (hN : 2 ≤ N) :
    _root_.GD.N0203.d007248 (_root_.GD.N0181.d007270 N) (_root_.GD.N0181.d007271 N) (_root_.GD.N0181.d007272 N) = _root_.GD.N0181.d007273 N := by
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hratio : _root_.GD.N0181.d007271 N / _root_.GD.N0181.d007270 N = (1 / (N : ℝ)) ^ 2 := by
    unfold _root_.GD.N0181.d007271 _root_.GD.N0181.d007270
    field_simp [hn.ne'] <;> ring
  have hs : Real.sqrt (_root_.GD.N0181.d007271 N / _root_.GD.N0181.d007270 N) = 1 / (N : ℝ) := by
    rw [hratio, Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hn)]
  unfold _root_.GD.N0203.d007248
  rw [hs]
  unfold _root_.GD.N0181.d007271 _root_.GD.N0181.d007270 _root_.GD.N0181.d007272 _root_.GD.N0181.d007273
  field_simp [hn.ne'] <;> ring

theorem d007296 (N : ℕ) : 0 ≤ _root_.GD.N0181.d007273 N := by
  unfold _root_.GD.N0181.d007273
  positivity

theorem d007297 {N : ℕ} (hN : 16 ≤ N) :
    _root_.GD.N0181.d007273 N ≤ 3 / (N : ℝ) ^ 3 := by
  have hn : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have h8 : (8 : ℝ) / (N : ℝ) ≤ 2 := by
    apply (div_le_iff₀ hn0).2
    linarith
  have hm := mul_le_mul_of_nonneg_right h8
    (show 0 ≤ (1 : ℝ) / (N : ℝ) ^ 3 by positivity)
  have heq : (8 / (N : ℝ)) * (1 / (N : ℝ) ^ 3) = 8 / (N : ℝ) ^ 4 := by
    field_simp [hn0.ne'] <;> ring
  rw [heq] at hm
  calc
    _root_.GD.N0181.d007273 N = 1 / (N : ℝ) ^ 3 + 8 / (N : ℝ) ^ 4 := rfl
    _ ≤ 1 / (N : ℝ) ^ 3 + 2 * (1 / (N : ℝ) ^ 3) := by linarith only [hm]
    _ = 3 / (N : ℝ) ^ 3 := by ring

theorem d007298 {N : ℕ} (hN : 16 ≤ N) : _root_.GD.N0181.d007273 N < 1 := by
  have hn : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) hn 3
  have hfrac : (3 : ℝ) / (N : ℝ) ^ 3 < 1 := by
    apply (div_lt_one (pow_pos hn0 3)).2
    norm_num at hpow
    linarith
  exact (_root_.GD.N0181.d007297 hN).trans_lt hfrac


theorem d007299 {N : ℕ} (hN : 16 ≤ N) :
    0 ≤ Real.pi / 4 - _root_.GD.N0181.d007274 N ∧
      Real.pi / 4 - _root_.GD.N0181.d007274 N ≤ 2 / (N : ℝ) ^ 2 + (Real.pi / 4) * _root_.GD.N0181.d007273 N := by
  have he := _root_.GD.N0181.d007291 (by omega : 2 ≤ N)
  have ha := _root_.GD.N0181.d007293 (by omega : 2 ≤ N)
  have hab := _root_.GD.N0181.d007294 (by omega : 2 ≤ N)
  have ht : _root_.GD.N0203.d007248 (_root_.GD.N0181.d007270 N) (_root_.GD.N0181.d007271 N) (_root_.GD.N0181.d007272 N) < 1 := by
    rw [_root_.GD.N0181.d007295 (by omega : 2 ≤ N)]
    exact _root_.GD.N0181.d007298 hN
  have h := _root_.GD.N0203.d007267 he (_root_.GD.N0181.d007292 hN).le ha hab ht
  rw [_root_.GD.N0181.d007295 (by omega : 2 ≤ N)] at h
  simpa only [_root_.GD.N0181.d007274, _root_.GD.N0181.d007270, mul_one_div] using h


theorem d007300 {N : ℕ} (hN : 16 ≤ N) :
    0 ≤ Real.pi / 4 - _root_.GD.N0181.d007274 N ∧
      Real.pi / 4 - _root_.GD.N0181.d007274 N ≤ 2 * (1 / (N : ℝ)) ^ 2 + 3 * (1 / (N : ℝ)) ^ 3 := by
  have ht : _root_.GD.N0203.d007248 (_root_.GD.N0181.d007270 N) (_root_.GD.N0181.d007271 N) (_root_.GD.N0181.d007272 N) < 1 := by
    rw [_root_.GD.N0181.d007295 (by omega : 2 ≤ N)]
    exact _root_.GD.N0181.d007298 hN
  have h := _root_.GD.N0203.d007261 (_root_.GD.N0181.d007291 (by omega : 2 ≤ N))
    (_root_.GD.N0181.d007292 hN).le (_root_.GD.N0181.d007293 (by omega : 2 ≤ N)) (_root_.GD.N0181.d007294 (by omega : 2 ≤ N)) ht
  rw [_root_.GD.N0181.d007295 (by omega : 2 ≤ N)] at h
  have hbudget := _root_.GD.N0181.d007297 hN
  change 0 ≤ Real.pi / 4 - _root_.GD.N0181.d007274 N ∧ Real.pi / 4 - _root_.GD.N0181.d007274 N ≤ 2 * _root_.GD.N0181.d007270 N + _root_.GD.N0181.d007273 N at h
  refine ⟨h.1, ?_⟩
  simp only [div_pow, one_pow]
  unfold _root_.GD.N0181.d007270 at h
  calc
    Real.pi / 4 - _root_.GD.N0181.d007274 N ≤ 2 * (1 / (N : ℝ) ^ 2) + _root_.GD.N0181.d007273 N := h.2
    _ ≤ 2 * (1 / (N : ℝ) ^ 2) + 3 / (N : ℝ) ^ 3 := by linarith only [hbudget]
    _ = 2 * (1 / (N : ℝ) ^ 2) + 3 * (1 / (N : ℝ) ^ 3) := by ring

theorem d007301 {N : ℕ} (hN : 16 ≤ N) : _root_.GD.N0181.d007274 N ≤ Real.pi / 4 := by
  linarith [(_root_.GD.N0181.d007300 hN).1]


theorem d007302 {N : ℕ} (hN : 16 ≤ N) :
    0 < _root_.GD.N0181.d007275 N ∧
      _root_.GD.N0181.d007275 N ≤ 2 * ((N : ℝ) ^ 2 - 1 / (1 - _root_.GD.N0181.d007270 N)) ∧
      _root_.GD.N0181.d007275 N ≤ 2 * (N : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have ht : _root_.GD.N0203.d007248 (_root_.GD.N0181.d007270 N) (_root_.GD.N0181.d007271 N) (_root_.GD.N0181.d007272 N) < 1 := by
    rw [_root_.GD.N0181.d007295 (by omega : 2 ≤ N)]
    exact _root_.GD.N0181.d007298 hN
  have hm := _root_.GD.N0203.d007265 (_root_.GD.N0181.d007291 (by omega : 2 ≤ N))
    (_root_.GD.N0181.d007292 hN) (_root_.GD.N0181.d007293 (by omega : 2 ≤ N)) (_root_.GD.N0181.d007294 (by omega : 2 ≤ N)) ht
  have hm' := _root_.GD.N0203.d007266 (_root_.GD.N0181.d007291 (by omega : 2 ≤ N))
    (_root_.GD.N0181.d007292 hN) (_root_.GD.N0181.d007293 (by omega : 2 ≤ N)) (_root_.GD.N0181.d007294 (by omega : 2 ≤ N)) ht
  have hinv : 1 / _root_.GD.N0181.d007270 N = (N : ℝ) ^ 2 := by
    unfold _root_.GD.N0181.d007270
    field_simp [hn.ne']
  change 0 < _root_.GD.N0181.d007275 N ∧ _root_.GD.N0181.d007275 N ≤ 2 * (1 / _root_.GD.N0181.d007270 N - 1 / (1 - _root_.GD.N0181.d007270 N)) at hm
  rw [hinv] at hm
  refine ⟨hm.1, hm.2, ?_⟩
  change _root_.GD.N0181.d007275 N ≤ 2 / _root_.GD.N0181.d007270 N at hm'
  calc
    _root_.GD.N0181.d007275 N ≤ 2 / _root_.GD.N0181.d007270 N := hm'
    _ = 2 * (N : ℝ) ^ 2 := by rw [← mul_one_div, hinv]


theorem d007303 {N : ℕ} (hN : 16 ≤ N) :
    0 ≤ _root_.GD.N0181.d007269 N * _root_.GD.N0181.d007275 N ∧ _root_.GD.N0181.d007269 N * _root_.GD.N0181.d007275 N ≤ 2 * (1 / (N : ℝ)) ^ 2 := by
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hm := _root_.GD.N0181.d007302 hN
  refine ⟨mul_nonneg (_root_.GD.N0181.d007278 (by omega : 2 ≤ N)).le hm.1.le, ?_⟩
  calc
    _root_.GD.N0181.d007269 N * _root_.GD.N0181.d007275 N ≤ (1 / (N : ℝ) ^ 4) * (2 * (N : ℝ) ^ 2) :=
      mul_le_mul (_root_.GD.N0181.d007290 hN) hm.2.2 hm.1.le (by positivity)
    _ = 2 * (1 / (N : ℝ)) ^ 2 := by field_simp [hn.ne'] <;> ring

end
end GD.N0181

#print axioms _root_.GD.N0181.d007279
#print axioms _root_.GD.N0181.d007281
#print axioms _root_.GD.N0181.d007290
#print axioms _root_.GD.N0181.d007299
#print axioms _root_.GD.N0181.d007300
#print axioms _root_.GD.N0181.d007302
#print axioms _root_.GD.N0181.d007303

#print axioms _root_.GD.N0181.d007283
#print axioms _root_.GD.N0181.d007284
#print axioms _root_.GD.N0181.d007285
#print axioms _root_.GD.N0181.d007286
#print axioms _root_.GD.N0181.d007287
