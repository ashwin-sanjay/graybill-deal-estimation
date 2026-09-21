import GD.Module0206





open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0232.N0720.N1378

open _root_.GD.N0232.N0720.N1377

noncomputable section

theorem d002871 (n : ℕ) {A : ℝ} (hA : 0 < A) (b : ℝ) :
    Tendsto (_root_.GD.N0232.N0720.N1377.d002851 n A b) atTop (𝓝 0) := by
  have he : Tendsto (fun r : ℝ ↦ Real.exp (-(1 / 2 : ℝ) * r)) atTop (𝓝 0) := by
    simpa only [neg_mul, Function.comp_def, id_eq] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (show (0 : ℝ) < 1 / 2 by norm_num))
  have hbase : Tendsto
      (fun r : ℝ ↦ r ^ n * Real.exp (-(A / 4) * r ^ 2)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
        (show 0 < A / 4 by positivity) (n : ℝ)).trans_tendsto he
  have hmajor : Tendsto (_root_.GD.N0232.N0720.N1377.d002857 n A b) atTop (𝓝 0) := by
    change Tendsto (fun r ↦ Real.exp (b ^ 2 / A) *
      (r ^ n * Real.exp (-(A / 4) * r ^ 2))) atTop (𝓝 0)
    simpa only [mul_zero] using hbase.const_mul (Real.exp (b ^ 2 / A))
  apply squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact _root_.GD.N0232.N0720.N1377.d002854 n A b hr
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact le_trans (le_abs_self _) (by
      simpa only [Real.norm_eq_abs] using _root_.GD.N0232.N0720.N1377.d002859 n hA b hr)

theorem d002872 (n : ℕ) (A b r : ℝ) :
    HasDerivAt (_root_.GD.N0232.N0720.N1377.d002851 (n + 1) A b)
      (((n + 1 : ℕ) : ℝ) * _root_.GD.N0232.N0720.N1377.d002851 n A b r +
        b * _root_.GD.N0232.N0720.N1377.d002851 (n + 1) A b r - A * _root_.GD.N0232.N0720.N1377.d002851 (n + 2) A b r) r := by
  have he : HasDerivAt (fun s : ℝ ↦ -A / 2 * s ^ 2 + b * s) (-A * r + b) r := by
    convert! (((hasDerivAt_id r).pow 2).const_mul (-A / 2)).add
      ((hasDerivAt_id r).const_mul b) using 1 <;> norm_num <;> ring
  convert! ((hasDerivAt_id r).pow (n + 1)).mul he.exp using 1
  simp only [_root_.GD.N0232.N0720.N1377.d002851, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
    Pi.pow_apply, pow_succ, id_eq, mul_one]
  ring


theorem d002873 (n : ℕ) {A : ℝ} (hA : 0 < A) (b : ℝ) :
    A * _root_.GD.N0232.N0720.N1377.d002852 (n + 2) A b =
      ((n + 1 : ℕ) : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 n A b + b * _root_.GD.N0232.N0720.N1377.d002852 (n + 1) A b := by
  have hint : IntegrableOn (fun r ↦
      (((n + 1 : ℕ) : ℝ) * _root_.GD.N0232.N0720.N1377.d002851 n A b r +
        b * _root_.GD.N0232.N0720.N1377.d002851 (n + 1) A b r - A * _root_.GD.N0232.N0720.N1377.d002851 (n + 2) A b r)) (Ioi 0) :=
    (((_root_.GD.N0232.N0720.N1377.d002860 n hA b).const_mul _).add
      ((_root_.GD.N0232.N0720.N1377.d002860 (n + 1) hA b).const_mul _)).sub
      ((_root_.GD.N0232.N0720.N1377.d002860 (n + 2) hA b).const_mul _)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun r _ ↦ _root_.GD.N0232.N0720.N1378.d002872 n A b r) hint
    (_root_.GD.N0232.N0720.N1378.d002871 (n + 1) hA b)
  rw [integral_sub
    (f := fun r ↦ ((n + 1 : ℕ) : ℝ) * _root_.GD.N0232.N0720.N1377.d002851 n A b r +
      b * _root_.GD.N0232.N0720.N1377.d002851 (n + 1) A b r)
    (g := fun r ↦ A * _root_.GD.N0232.N0720.N1377.d002851 (n + 2) A b r)
    (((_root_.GD.N0232.N0720.N1377.d002860 n hA b).const_mul _).add
      ((_root_.GD.N0232.N0720.N1377.d002860 (n + 1) hA b).const_mul _))
    ((_root_.GD.N0232.N0720.N1377.d002860 (n + 2) hA b).const_mul _),
    integral_add (f := fun r ↦ ((n + 1 : ℕ) : ℝ) * _root_.GD.N0232.N0720.N1377.d002851 n A b r)
      (g := fun r ↦ b * _root_.GD.N0232.N0720.N1377.d002851 (n + 1) A b r)
      ((_root_.GD.N0232.N0720.N1377.d002860 n hA b).const_mul _)
      ((_root_.GD.N0232.N0720.N1377.d002860 (n + 1) hA b).const_mul _)] at h
  simp only [integral_const_mul] at h
  have hz : _root_.GD.N0232.N0720.N1377.d002851 (n + 1) A b 0 = 0 := by simp [_root_.GD.N0232.N0720.N1377.d002851]
  rw [hz, sub_zero] at h
  change ((n + 1 : ℕ) : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 n A b +
      b * _root_.GD.N0232.N0720.N1377.d002852 (n + 1) A b - A * _root_.GD.N0232.N0720.N1377.d002852 (n + 2) A b = 0 at h
  linarith

theorem d002874 (n : ℕ) {A : ℝ} (hA : 0 < A) (b : ℝ) :
    b * _root_.GD.N0232.N0720.N1377.d002852 (n + 1) A b ≤ A * _root_.GD.N0232.N0720.N1377.d002852 (n + 2) A b := by
  rw [_root_.GD.N0232.N0720.N1378.d002873 n hA b]
  have h := _root_.GD.N0232.N0720.N1377.d002861 n hA b
  linarith [mul_nonneg (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by positivity) h.le]


theorem d002875 (n : ℕ) {A b : ℝ}
    (hA : 0 < A) (hb : 0 ≤ b) :
    b ^ 2 * _root_.GD.N0232.N0720.N1377.d002852 (n + 1) A b ≤ A ^ 2 * _root_.GD.N0232.N0720.N1377.d002852 (n + 3) A b := by
  have h1 := mul_le_mul_of_nonneg_left (_root_.GD.N0232.N0720.N1378.d002874 n hA b) hb
  have h2 := mul_le_mul_of_nonneg_left (_root_.GD.N0232.N0720.N1378.d002874 (n + 1) hA b) hA.le
  have heq : n + 1 + 1 = n + 2 := by omega
  have heq' : n + 1 + 2 = n + 3 := by omega
  rw [heq, heq'] at h2
  nlinarith


theorem d002876 {A : ℝ} (hA : 0 < A) :
    _root_.GD.N0232.N0720.N1377.d002852 1 A 0 = A⁻¹ := by
  have hd (r : ℝ) : HasDerivAt (_root_.GD.N0232.N0720.N1377.d002851 0 A 0)
      (-A * _root_.GD.N0232.N0720.N1377.d002851 1 A 0 r) r := by
    have he := (((hasDerivAt_id r).pow 2).const_mul (-A / 2)).exp
    convert! he using 1
    · funext s
      simp [_root_.GD.N0232.N0720.N1377.d002851]
    · simp only [_root_.GD.N0232.N0720.N1377.d002851, Pi.pow_apply, pow_one, id_eq, Nat.reduceSub, Nat.cast_ofNat,
        mul_one, zero_mul, add_zero]
      ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun r _ ↦ hd r) ((_root_.GD.N0232.N0720.N1377.d002860 1 hA 0).const_mul (-A))
    (_root_.GD.N0232.N0720.N1378.d002871 0 hA 0)
  rw [integral_const_mul] at h
  have hz : _root_.GD.N0232.N0720.N1377.d002851 0 A 0 0 = 1 := by simp [_root_.GD.N0232.N0720.N1377.d002851]
  rw [hz, zero_sub] at h
  have hprod : A * _root_.GD.N0232.N0720.N1377.d002852 1 A 0 = 1 := by
    change -A * _root_.GD.N0232.N0720.N1377.d002852 1 A 0 = -1 at h
    linarith
  apply (mul_left_cancel₀ hA.ne')
  simpa only [mul_inv_cancel₀ hA.ne'] using hprod


theorem d002877 : _root_.GD.N0232.N0720.N1377.d002852 5 1 0 = 8 := by
  have h1 := _root_.GD.N0232.N0720.N1378.d002876 (show (0 : ℝ) < 1 by norm_num)
  have h3 := _root_.GD.N0232.N0720.N1378.d002873 1 (show (0 : ℝ) < 1 by norm_num) 0
  have h5 := _root_.GD.N0232.N0720.N1378.d002873 3 (show (0 : ℝ) < 1 by norm_num) 0
  norm_num at h1 h3 h5
  linarith

end

end GD.N0232.N0720.N1378
