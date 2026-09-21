import GD.Module1399













set_option autoImplicit false
set_option warningAsError true

namespace GD.N0191
noncomputable section

open _root_.GD.N0160 _root_.GD.N0172
open _root_.GD.N0181 _root_.GD.N0167
open _root_.GD.N0204 _root_.GD.N0171


theorem d022549 {N : ℕ} (hN : 16 ≤ N) :
    _root_.GD.N0181.d007274 N - (1 - _root_.GD.N0204.d007394 N) * (Real.pi / 4) - _root_.GD.N0181.d007269 N * _root_.GD.N0181.d007275 N ≤
      _root_.GD.N0172.d022468 (_root_.GD.N0167.d007305 N) (_root_.GD.N0167.d007306 N) ∧
    _root_.GD.N0172.d022468 (_root_.GD.N0167.d007305 N) (_root_.GD.N0167.d007306 N) - (1 - _root_.GD.N0171.d007331 N) * (Real.pi / 4) - _root_.GD.N0171.d007332 N ≤
      _root_.GD.N0160.d022516 N ∧
    Real.pi / 4 - _root_.GD.N0160.d022516 N ≤
      (Real.pi / 4 - _root_.GD.N0181.d007274 N) + (1 - _root_.GD.N0204.d007394 N) * (Real.pi / 4) + _root_.GD.N0181.d007269 N * _root_.GD.N0181.d007275 N +
        (1 - _root_.GD.N0171.d007331 N) * (Real.pi / 4) + _root_.GD.N0171.d007332 N := by
  let s := _root_.GD.N0160.d022520 hN
  have hwJ := mul_le_mul_of_nonneg_left s.J_le
    (sub_nonneg.mpr s.w_le_one)
  have hwD := mul_le_mul_of_nonneg_right s.w_le_one s.D_nonneg
  have hcC := mul_le_mul_of_nonneg_left s.C_le
    (sub_nonneg.mpr s.c_le_one)
  have hC : s.J - (1 - s.w) * (Real.pi / 4) - s.D ≤ s.C := by
    nlinarith only [hwJ, hwD, s.continuum_lower]
  have hB : s.C - (1 - s.c) * (Real.pi / 4) - s.E ≤ _root_.GD.N0160.d022516 N := by
    nlinarith only [hcC, s.discrete_lower]
  have hsum : Real.pi / 4 - _root_.GD.N0160.d022516 N ≤
      (Real.pi / 4 - s.J) + (1 - s.w) * (Real.pi / 4) + s.D +
        (1 - s.c) * (Real.pi / 4) + s.E := by
    linarith only [hC, hB]
  exact ⟨hC, hB, hsum⟩


theorem d022550 :
    (11 : ℝ) / 16 + 3 / 256 + 7 / 8192 = 5735 / 8192 := by
  norm_num


theorem d022551 {x : ℝ} (hx : 0 ≤ x)
    (hupper : x ≤ 1 / 16) :
    13 * x + 11 * x ^ 2 + 3 * x ^ 3 + (7 / 2 : ℝ) * x ^ 4 ≤
      x * (13 + 5735 / 8192) := by
  have hgap : 0 ≤ (1 / 16 : ℝ) - x := sub_nonneg.mpr hupper
  have h₂step := mul_nonneg hx hgap
  have h₂ : x ^ 2 ≤ x / 16 := by nlinarith only [h₂step]
  have h₃step := mul_nonneg (sq_nonneg x) hgap
  have h₃ : x ^ 3 ≤ x / 256 := by nlinarith only [h₃step, h₂]
  have h₄step := mul_nonneg (pow_nonneg hx 3) hgap
  have h₄ : x ^ 4 ≤ x / 4096 := by nlinarith only [h₄step, h₃]
  nlinarith only [h₂, h₃, h₄]


theorem d022552 {N : ℕ} (hN : 16 ≤ N) :
    Real.pi / 4 - _root_.GD.N0160.d022516 N ≤
      13 / (N : ℝ) + 11 / (N : ℝ) ^ 2 + 3 / (N : ℝ) ^ 3 +
        7 / (2 * (N : ℝ) ^ 4) ∧
    13 / (N : ℝ) + 11 / (N : ℝ) ^ 2 + 3 / (N : ℝ) ^ 3 +
        7 / (2 * (N : ℝ) ^ 4) ≤
      (1 / (N : ℝ)) * (13 + 5735 / 8192) ∧
    (1 / (N : ℝ)) * (13 + 5735 / 8192) < 14 / (N : ℝ) := by
  have hn : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hx : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have hupper : (1 : ℝ) / (N : ℝ) ≤ 1 / 16 := by
    apply (div_le_div_iff₀ hnpos (by norm_num : (0 : ℝ) < 16)).2
    linarith only [hn]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [div_pow, one_pow, mul_one_div, div_mul_eq_div_div] using
      _root_.GD.N0160.d022521 hN
  · simpa only [div_pow, one_pow, mul_one_div, div_mul_eq_div_div] using
      _root_.GD.N0191.d022551 hx.le hupper
  · calc
      (1 / (N : ℝ)) * (13 + 5735 / 8192) < (1 / (N : ℝ)) * 14 :=
        mul_lt_mul_of_pos_left (by norm_num : (13 : ℝ) + 5735 / 8192 < 14) hx
      _ = 14 / (N : ℝ) := by ring


theorem d022553 {n : ℕ} (hn : 0 < n) :
    0 < Real.pi / 4 - _root_.GD.N0160.d022516 (16 * n) ∧
    Real.pi / 4 - _root_.GD.N0160.d022516 (16 * n) < 7 / (8 * (n : ℝ)) ∧
    (7 : ℝ) / (8 * (n : ℝ)) < 1 / (n : ℝ) := by
  have hN : 16 ≤ 16 * n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hrate := _root_.GD.N0160.d022522 hN
  have heq : (14 : ℝ) / ((16 * n : ℕ) : ℝ) = 7 / (8 * (n : ℝ)) := by
    push_cast
    field_simp [hnpos.ne'] <;> ring
  rw [heq] at hrate
  refine ⟨hrate.1, hrate.2, ?_⟩
  apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 8 * (n : ℝ)) hnpos).2
  nlinarith only [hnpos]

end
end GD.N0191

#print axioms _root_.GD.N0191.d022549
#print axioms _root_.GD.N0191.d022550
#print axioms _root_.GD.N0191.d022551
#print axioms _root_.GD.N0191.d022552
#print axioms _root_.GD.N0191.d022553
