import GD.Module1402








set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace GD.N0196
noncomputable section

open _root_.GD.N0160 _root_.GD.N0191
open _root_.GD.N0181 _root_.GD.N0167
open _root_.GD.N0204 _root_.GD.N0171

def d022599 : ℝ := Real.pi / 4


def d022600 (N : ℕ) : ℝ := _root_.GD.N0196.d022599 - _root_.GD.N0160.d022516 N


def d022601 (N : ℕ) : ℝ :=
  2 * _root_.GD.N0196.d022599 / (N : ℝ) +
    2 / (((N : ℝ) - 1) * (1 - 1 / (N : ℝ) ^ 4)) +
    6 * _root_.GD.N0196.d022599 * Real.log (N : ℝ) / ((N : ℝ) * ((N : ℝ) - 1)) +
    4 / (N : ℝ) ^ 2 +
    7 * _root_.GD.N0196.d022599 / (2 * (N : ℝ) ^ 2 * (1 - 1 / (N : ℝ) ^ 4)) +
    _root_.GD.N0196.d022599 / (N : ℝ) ^ 3 + 23 * _root_.GD.N0196.d022599 / (2 * (N : ℝ) ^ 4)

theorem d022602 {N : ℕ} (hN : 16 ≤ N) :
    0 < 1 - 1 / (N : ℝ) ^ 4 := by
  linarith [_root_.GD.N0181.d007287 hN]


theorem d022603 {N : ℕ} (hN : 16 ≤ N) :
    _root_.GD.N0204.d007392 N ≤ 1 / ((N : ℝ) ^ 2 * (1 - 1 / (N : ℝ) ^ 4)) := by
  have hN2 : 2 ≤ N := by omega
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have ha : 0 < 1 - _root_.GD.N0181.d007271 N := _root_.GD.N0196.d022602 hN
  have hapos := _root_.GD.N0181.d007293 hN2
  have he := _root_.GD.N0181.d007291 hN2
  have hd := _root_.GD.N0171.d007334 hN2
  have had := _root_.GD.N0181.d007290 hN
  change _root_.GD.N0181.d007269 N ≤ _root_.GD.N0181.d007271 N at had
  have hden : (1 - _root_.GD.N0181.d007271 N) * (2 * _root_.GD.N0181.d007270 N) ≤
      (1 - _root_.GD.N0181.d007269 N) * (_root_.GD.N0181.d007271 N + 2 * _root_.GD.N0181.d007270 N) :=
    mul_le_mul (by linarith only [had])
      (by linarith [_root_.GD.N0181.d007293 hN2]) (by positivity) hd.le
  have hden0 : 0 < (1 - _root_.GD.N0181.d007271 N) * (2 * _root_.GD.N0181.d007270 N) := by positivity
  have hactual : 0 < (1 - _root_.GD.N0181.d007269 N) * (_root_.GD.N0181.d007271 N + 2 * _root_.GD.N0181.d007270 N) := hden0.trans_le hden
  calc
    _root_.GD.N0204.d007392 N ≤ 2 * _root_.GD.N0181.d007271 N / ((1 - _root_.GD.N0181.d007269 N) * (_root_.GD.N0181.d007271 N + 2 * _root_.GD.N0181.d007270 N)) :=
      div_le_div_of_nonneg_right (by linarith only [had]) hactual.le
    _ ≤ 2 * _root_.GD.N0181.d007271 N / ((1 - _root_.GD.N0181.d007271 N) * (2 * _root_.GD.N0181.d007270 N)) :=
      div_le_div_of_nonneg_left (by positivity) hden0 hden
    _ = 1 / ((N : ℝ) ^ 2 * (1 - 1 / (N : ℝ) ^ 4)) := by
      unfold _root_.GD.N0181.d007271 _root_.GD.N0181.d007270
      field_simp [hn.ne', (_root_.GD.N0196.d022602 hN).ne'] <;> ring

theorem d022604 {N : ℕ} (hN : 16 ≤ N) :
    1 - _root_.GD.N0204.d007393 N ≤ 7 / (2 * (N : ℝ) ^ 2 * (1 - 1 / (N : ℝ) ^ 4)) := by
  have hbern := _root_.GD.N0204.d007395 (_root_.GD.N0204.d007396 (by omega : 2 ≤ N)).le
  have hbound := mul_le_mul_of_nonneg_left (_root_.GD.N0196.d022603 hN)
    (by norm_num : (0 : ℝ) ≤ 7 / 2)
  change 1 - _root_.GD.N0204.d007393 N ≤ (7 / 2 : ℝ) * _root_.GD.N0204.d007392 N at hbern
  calc
    1 - _root_.GD.N0204.d007393 N ≤ (7 / 2 : ℝ) * _root_.GD.N0204.d007392 N := hbern
    _ ≤ (7 / 2 : ℝ) * (1 / ((N : ℝ) ^ 2 * (1 - 1 / (N : ℝ) ^ 4))) := hbound
    _ = 7 / (2 * (N : ℝ) ^ 2 * (1 - 1 / (N : ℝ) ^ 4)) := by
      rw [mul_one_div, div_div, mul_assoc]


theorem d022605 {N : ℕ} (hN : 16 ≤ N) :
    _root_.GD.N0171.d007332 N ≤ 2 / (((N : ℝ) - 1) * (1 - 1 / (N : ℝ) ^ 4)) := by
  have hN2 : 2 ≤ N := by omega
  have hn : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hm : 0 < (N : ℝ) - 1 := by linarith
  have ha := _root_.GD.N0196.d022602 hN
  have hd := _root_.GD.N0171.d007334 hN2
  have hcompare : 1 - 1 / (N : ℝ) ^ 4 ≤ 1 - _root_.GD.N0181.d007269 N := by
    linarith only [_root_.GD.N0181.d007290 hN]
  have hnum : 2 * _root_.GD.N0171.d007331 N * (1 / ((N : ℝ) - 1)) ≤
      2 * (1 / ((N : ℝ) - 1)) := by
    have h := mul_le_mul_of_nonneg_right (_root_.GD.N0171.d007336 hN2)
      (show 0 ≤ 2 * (1 / ((N : ℝ) - 1)) by positivity)
    nlinarith only [h]
  unfold _root_.GD.N0171.d007332
  rw [_root_.GD.N0171.d007339 hN2]
  calc
    2 * _root_.GD.N0171.d007331 N * (1 / ((N : ℝ) - 1)) / (1 - _root_.GD.N0181.d007269 N) ≤
        (2 * (1 / ((N : ℝ) - 1))) / (1 - _root_.GD.N0181.d007269 N) :=
      div_le_div_of_nonneg_right hnum hd.le
    _ ≤ (2 * (1 / ((N : ℝ) - 1))) / (1 - 1 / (N : ℝ) ^ 4) :=
      div_le_div_of_nonneg_left (by positivity) ha hcompare
    _ = 2 / (((N : ℝ) - 1) * (1 - 1 / (N : ℝ) ^ 4)) := by
      rw [mul_one_div, div_div]


theorem d022606 {N : ℕ} (hN : 16 ≤ N) :
    _root_.GD.N0196.d022599 - _root_.GD.N0181.d007274 N ≤ 2 / (N : ℝ) ^ 2 + _root_.GD.N0196.d022599 / (N : ℝ) ^ 3 + 8 * _root_.GD.N0196.d022599 / (N : ℝ) ^ 4 := by
  calc
    _root_.GD.N0196.d022599 - _root_.GD.N0181.d007274 N ≤ 2 / (N : ℝ) ^ 2 + _root_.GD.N0196.d022599 * _root_.GD.N0181.d007273 N := (_root_.GD.N0181.d007299 hN).2
    _ = 2 / (N : ℝ) ^ 2 + _root_.GD.N0196.d022599 / (N : ℝ) ^ 3 + 8 * _root_.GD.N0196.d022599 / (N : ℝ) ^ 4 := by
      unfold _root_.GD.N0181.d007273
      ring


theorem d022607 {N : ℕ} (hN : 16 ≤ N) :
    1 - _root_.GD.N0204.d007393 N ≤ 7 / (2 * (N : ℝ) ^ 2 * (1 - 1 / (N : ℝ) ^ 4)) ∧
    _root_.GD.N0171.d007332 N ≤ 2 / (((N : ℝ) - 1) * (1 - 1 / (N : ℝ) ^ 4)) ∧
    _root_.GD.N0167.d007307 N ≤ 6 * Real.log (N : ℝ) / ((N : ℝ) * ((N : ℝ) - 1)) ∧
    _root_.GD.N0196.d022599 - _root_.GD.N0181.d007274 N ≤ 2 / (N : ℝ) ^ 2 + _root_.GD.N0196.d022599 / (N : ℝ) ^ 3 + 8 * _root_.GD.N0196.d022599 / (N : ℝ) ^ 4 :=
  ⟨_root_.GD.N0196.d022604 hN, _root_.GD.N0196.d022605 hN,
    _root_.GD.N0167.d007324 (by omega), _root_.GD.N0196.d022606 hN⟩

theorem d022608 {N : ℕ} (hN : 16 ≤ N) :
    1 - _root_.GD.N0204.d007394 N ≤ 7 / (2 * (N : ℝ) ^ 2 * (1 - 1 / (N : ℝ) ^ 4)) +
      6 * Real.log (N : ℝ) / ((N : ℝ) * ((N : ℝ) - 1)) := by
  have hN2 : 2 ≤ N := by omega
  have hm := mul_le_mul_of_nonneg_right (_root_.GD.N0204.d007400 hN2) (_root_.GD.N0167.d007323 hN2)
  have hr := _root_.GD.N0196.d022604 hN
  have hl := _root_.GD.N0167.d007324 hN2
  unfold _root_.GD.N0204.d007394
  nlinarith only [hm, hr, hl]


theorem d022609 {N : ℕ} (hN : 16 ≤ N) :
    _root_.GD.N0196.d022600 N ≤ _root_.GD.N0196.d022601 N := by
  have hz : 0 ≤ _root_.GD.N0196.d022599 := by unfold _root_.GD.N0196.d022599; positivity
  have hsum := (_root_.GD.N0191.d022549 hN).2.2
  have hJ := _root_.GD.N0196.d022606 hN
  have hw := mul_le_mul_of_nonneg_right (_root_.GD.N0196.d022608 hN) hz
  have hc := mul_le_mul_of_nonneg_right (_root_.GD.N0171.d007338 hN).2 hz
  have hmass : _root_.GD.N0181.d007269 N * _root_.GD.N0181.d007275 N ≤ 2 / (N : ℝ) ^ 2 := by
    simpa only [div_pow, one_pow, mul_one_div] using (_root_.GD.N0181.d007303 hN).2
  have hE := _root_.GD.N0196.d022605 hN
  change _root_.GD.N0196.d022600 N ≤ (_root_.GD.N0196.d022599 - _root_.GD.N0181.d007274 N) + (1 - _root_.GD.N0204.d007394 N) * _root_.GD.N0196.d022599 + _root_.GD.N0181.d007269 N * _root_.GD.N0181.d007275 N +
    (1 - _root_.GD.N0171.d007331 N) * _root_.GD.N0196.d022599 + _root_.GD.N0171.d007332 N at hsum
  have hraw : _root_.GD.N0196.d022600 N ≤
      (2 / (N : ℝ) ^ 2 + _root_.GD.N0196.d022599 / (N : ℝ) ^ 3 + 8 * _root_.GD.N0196.d022599 / (N : ℝ) ^ 4) +
      (7 / (2 * (N : ℝ) ^ 2 * (1 - 1 / (N : ℝ) ^ 4)) +
        6 * Real.log (N : ℝ) / ((N : ℝ) * ((N : ℝ) - 1))) * _root_.GD.N0196.d022599 +
      2 / (N : ℝ) ^ 2 + (2 / (N : ℝ) + 7 / (2 * (N : ℝ) ^ 4)) * _root_.GD.N0196.d022599 +
      2 / (((N : ℝ) - 1) * (1 - 1 / (N : ℝ) ^ 4)) := by
    linarith only [hsum, hJ, hw, hmass, hc, hE]
  calc
    _root_.GD.N0196.d022600 N ≤ _ := hraw
    _ = _root_.GD.N0196.d022601 N := by unfold _root_.GD.N0196.d022601; ring

theorem d022610 {N : ℕ} (hN : 16 ≤ N) :
    0 < _root_.GD.N0196.d022600 N ∧ _root_.GD.N0196.d022600 N ≤ _root_.GD.N0196.d022601 N :=
  ⟨(_root_.GD.N0160.d022522 hN).1, _root_.GD.N0196.d022609 hN⟩

end
end GD.N0196

#print axioms _root_.GD.N0196.d022602
#print axioms _root_.GD.N0196.d022603
#print axioms _root_.GD.N0196.d022604
#print axioms _root_.GD.N0196.d022605
#print axioms _root_.GD.N0196.d022606
#print axioms _root_.GD.N0196.d022607
#print axioms _root_.GD.N0196.d022608
#print axioms _root_.GD.N0196.d022609
#print axioms _root_.GD.N0196.d022610
