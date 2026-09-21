import GD.Module1021








set_option warningAsError true
set_option autoImplicit false

open Set

namespace GD.N0232.N0720.N1224

noncomputable section

open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1237 _root_.GD.N0232.N0720.N1240

theorem d016250
    (q : ℝ) (hq : 2 ≤ q) (t : _root_.GD.N0232.N0720.N1441.d013676)
    (htlo : 1 / (2 * q ^ 2) ≤ (t : ℝ) * (1 - (t : ℝ)))
    (hthi : (t : ℝ) * (1 - (t : ℝ)) ≤ 1 / q ^ 2)
    (z : _root_.GD.N0232.N0720.N1436.d013217)
    (hu : z.1 ∈ Icc (1 / 4 : ℝ) (3 / 4))
    (hv : z.2 ∈ Icc (q ^ 2) (2 * q ^ 2)) :
    1 / (1024 * q ^ 3) ≤ _root_.GD.N0232.N0720.N1237.d016241 t z := by
  have hqpos : 0 < q := by linarith
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hq2pos : 0 < q ^ 2 := sq_pos_of_pos hqpos
  have hu0 : 0 < z.1 := by linarith [hu.1]
  have hu1 : z.1 < 1 := by linarith [hu.2]
  have hv0 : 0 < z.2 := hq2pos.trans_le hv.1
  have ht0 := t.property.1
  have ht1 := t.property.2
  have hp0 : 0 < (t : ℝ) * (1 - (t : ℝ)) :=
    mul_pos ht0 (sub_pos.mpr ht1)
  have hz : z ∈ _root_.GD.N0232.N0720.N1436.d013218 := ⟨⟨hu0, hu1⟩, hv0⟩
  have huPow : 1 ≤ z.1 ^ (-(1 / 2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1.le (by norm_num)
  have huPow' : 1 ≤ (1 - z.1) ^ (-(1 / 2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (sub_pos.mpr hu1)
      (by linarith) (by norm_num)
  have hvPow : q ≤ z.2 ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    calc
      q = Real.sqrt (q ^ 2) := (Real.sqrt_sq hqpos.le).symm
      _ ≤ Real.sqrt z.2 := Real.sqrt_le_sqrt hv.1
  have hconstant : (1 / 4 : ℝ) ≤ 3 / (2 * Real.pi) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) Real.pi_pos)).2
    linarith [Real.pi_lt_four]
  have hobs : q / 4 ≤ _root_.GD.N0232.N0720.N1237.d016246 z := by
    have hpair : (1 : ℝ) ≤
        z.1 ^ (-(1 / 2 : ℝ)) * (1 - z.1) ^ (-(1 / 2 : ℝ)) := by
      simpa using mul_le_mul huPow huPow' (by norm_num : (0 : ℝ) ≤ 1)
        (zero_le_one.trans huPow)
    have htriple : q ≤ z.1 ^ (-(1 / 2 : ℝ)) *
        (1 - z.1) ^ (-(1 / 2 : ℝ)) * z.2 ^ (1 / 2 : ℝ) := by
      simpa using mul_le_mul hpair hvPow hqpos.le (zero_le_one.trans hpair)
    have hh := mul_le_mul hconstant htriple hqpos.le
      (show (0 : ℝ) ≤ 3 / (2 * Real.pi) by positivity)
    simpa only [_root_.GD.N0232.N0720.N1237.d016246, one_div, div_eq_mul_inv, one_mul,
      mul_comm (4 : ℝ)⁻¹ q]
      using hh
  have hobs0 : 0 ≤ _root_.GD.N0232.N0720.N1237.d016246 z := le_trans (by positivity) hobs
  have hscale : 1 / (4 * q ^ 4) ≤ ((t : ℝ) * (1 - (t : ℝ))) ^ 2 := by
    calc
      1 / (4 * q ^ 4) = (1 / (2 * q ^ 2)) ^ 2 := by field_simp; ring
      _ ≤ _ := (sq_le_sq₀ (by positivity) hp0.le).2 htlo
  have hpv : (t : ℝ) * (1 - (t : ℝ)) * z.2 ≤ 2 := by
    calc
      _ ≤ (1 / q ^ 2) * (2 * q ^ 2) :=
        mul_le_mul hthi hv.2 hv0.le (by positivity)
      _ = 2 := by field_simp
  have htu : (t : ℝ) * (1 - z.1) ≤ 1 := by
    have hh := mul_le_mul ht1.le (show 1 - z.1 ≤ 1 by linarith)
      (sub_pos.mpr hu1).le (by norm_num : (0 : ℝ) ≤ 1)
    simpa using hh
  have hut : (1 - (t : ℝ)) * z.1 ≤ 1 := by
    have hh := mul_le_mul (show 1 - (t : ℝ) ≤ 1 by linarith) hu1.le
      hu0.le (by norm_num : (0 : ℝ) ≤ 1)
    simpa using hh
  have hQpos : 0 < _root_.GD.N0232.N0720.N1240.d002099 t z.1 z.2 := by
    unfold _root_.GD.N0232.N0720.N1240.d002099
    positivity
  have hQle : _root_.GD.N0232.N0720.N1240.d002099 t z.1 z.2 ≤ 4 := by
    unfold _root_.GD.N0232.N0720.N1240.d002099
    linarith
  have hpower : (1 / 64 : ℝ) ≤ Real.rpow (_root_.GD.N0232.N0720.N1240.d002099 t z.1 z.2) (-5 / 2) := by
    calc
      (1 / 64 : ℝ) = (4 : ℝ) ^ (-3 : ℝ) := by norm_num
      _ ≤ (4 : ℝ) ^ (-5 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos hQpos hQle (by norm_num)
  rw [_root_.GD.N0232.N0720.N1237.d016247 t hz]
  calc
    1 / (1024 * q ^ 3) =
        (q / 4 * (1 / (4 * q ^ 4))) * (1 / 64) := by field_simp; ring
    _ ≤ _ := mul_le_mul
      (mul_le_mul hobs hscale (by positivity) hobs0)
      hpower (by norm_num) (mul_nonneg hobs0 (sq_nonneg _))


theorem d016251
    (q : ℝ) (hq : 2 ≤ q) (t : _root_.GD.N0232.N0720.N1441.d013676)
    (ht : (t : ℝ) = 1 / q ^ 2 ∨ (t : ℝ) = 1 - 1 / q ^ 2)
    (z : _root_.GD.N0232.N0720.N1436.d013217)
    (hu : z.1 ∈ Icc (1 / 4 : ℝ) (3 / 4))
    (hv : z.2 ∈ Icc (q ^ 2) (2 * q ^ 2)) :
    1 / (1024 * q ^ 3) ≤ _root_.GD.N0232.N0720.N1237.d016241 t z := by
  have hqpos : 0 < q := by linarith
  have hq2pos : 0 < q ^ 2 := sq_pos_of_pos hqpos
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  have hinv0 : 0 < (1 : ℝ) / q ^ 2 := by positivity
  have hinv : (1 : ℝ) / q ^ 2 ≤ 1 / 4 := by
    apply (div_le_iff₀ hq2pos).2
    nlinarith
  have hprod : (t : ℝ) * (1 - (t : ℝ)) =
      (1 / q ^ 2) * (1 - 1 / q ^ 2) := by
    rcases ht with ht | ht
    · rw [ht]
    · rw [ht]
      ring
  apply _root_.GD.N0232.N0720.N1224.d016250 q hq t _ _ z hu hv
  · rw [hprod]
    have heq : (1 : ℝ) / (2 * q ^ 2) = ((1 : ℝ) / q ^ 2) / 2 := by ring
    rw [heq]
    nlinarith [mul_nonneg hinv0.le (show 0 ≤ 1 / 2 - (1 : ℝ) / q ^ 2 by linarith)]
  · rw [hprod]
    nlinarith [sq_nonneg ((1 : ℝ) / q ^ 2)]

end
end GD.N0232.N0720.N1224

#print axioms _root_.GD.N0232.N0720.N1224.d016251
