import GD.Module1313
import GD.Module0385












set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter Topology

namespace GD.N0106.N0428.N0765.N1527
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1534 _root_.GD.N0106.N0428.N0765.N1529 _root_.GD.N0106.N0428.N0765.N1521 _root_.GD.N0106.N0428.N0765.N1539
open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1663 _root_.GD.N0106.N0428.N0765.N1672 _root_.GD.N0106.N0428.N0765.N1528


theorem d021470 {e : ℝ} (he : 0 < e) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b 0 0 = (_root_.GD.N0106.N0428.N0765.N1538.d021245 e a b : ℂ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021243 _root_.GD.N0106.N0428.N0765.N1538.d021245
  calc
    (∫ x in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b 0 0 x) =
        ∫ x in (0 : ℝ)..1, (_root_.GD.N0106.N0428.N0765.N1538.d021235 e a b x : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le zero_le_one] at hx
      exact _root_.GD.N0106.N0428.N0765.N1538.d021239 he a b hx
    _ = ((∫ x in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1538.d021235 e a b x : ℝ) : ℂ) := by
      simp only [intervalIntegral.integral_of_le zero_le_one]
      exact integral_ofReal


theorem d021471 {e : ℝ} (he : 0 < e) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1538.d021244 e a b 0 0 = (_root_.GD.N0106.N0428.N0765.N1538.d021246 e a b : ℂ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021244 _root_.GD.N0106.N0428.N0765.N1538.d021246
  calc
    (∫ x in (0 : ℝ)..1, (x : ℂ) * _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b 0 0 x) =
        ∫ x in (0 : ℝ)..1, ((x * _root_.GD.N0106.N0428.N0765.N1538.d021235 e a b x : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le zero_le_one] at hx
      change (x : ℂ) * _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b 0 0 x = ((x * _root_.GD.N0106.N0428.N0765.N1538.d021235 e a b x : ℝ) : ℂ)
      rw [_root_.GD.N0106.N0428.N0765.N1538.d021239 he a b hx, Complex.ofReal_mul]
    _ = ((∫ x in (0 : ℝ)..1, x * _root_.GD.N0106.N0428.N0765.N1538.d021235 e a b x : ℝ) : ℂ) := by
      simp only [intervalIntegral.integral_of_le zero_le_one]
      exact integral_ofReal


theorem d021472 {e : ℝ} (he : 0 < e) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1538.d021247 e a b 0 0 =
      ((e⁻¹ * _root_.GD.N0106.N0428.N0765.N1529.d020799 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) : ℝ) : ℂ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021247
  rw [_root_.GD.N0106.N0428.N0765.N1527.d021471 he a b, _root_.GD.N0106.N0428.N0765.N1527.d021470 he a b,
    ← Complex.ofReal_div, ← Complex.ofReal_mul, _root_.GD.N0106.N0428.N0765.N1538.d021258 he a b]


theorem d021473 (a b : ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 0 ∧ 0 < _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 ∧
      0 < _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2 := by
  obtain ⟨h0, h1, h2⟩ := _root_.GD.N0106.N0428.N0765.N1538.d021252 a b
  rw [h0, h1, h2]
  exact ⟨(Real.sigmoid_pos a).le,
    mul_pos (sub_pos.mpr (Real.sigmoid_lt_one a)) (Real.sigmoid_pos b),
    mul_pos (sub_pos.mpr (Real.sigmoid_lt_one a))
      (sub_pos.mpr (Real.sigmoid_lt_one b))⟩


theorem d021474 (a b : ℝ) :
    Tendsto (fun e => _root_.GD.N0106.N0428.N0765.N1538.d021247 e a b 0 0) (𝓝[>] 0)
      (𝓝 ((((11 / 8 : ℝ) * _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 /
        (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 0 + _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2)) : ℝ) : ℂ)) := by
  obtain ⟨hu, hv, hw⟩ := _root_.GD.N0106.N0428.N0765.N1527.d021473 a b
  have hreal : Tendsto (fun e : ℝ => e⁻¹ * _root_.GD.N0106.N0428.N0765.N1529.d020799 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)))
      (𝓝[>] 0) (𝓝 ((11 / 8 : ℝ) * _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 /
        (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 0 + _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2))) := by
    simpa only [Function.comp_def, _root_.GD.N0106.N0428.N0765.N1529.d020799] using
      (_root_.GD.N0106.N0428.N0765.N1673.d005866 hu hv hw).comp tendsto_inv_nhdsGT_zero
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  refine hcomplex.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with e he
  exact (_root_.GD.N0106.N0428.N0765.N1527.d021472 he a b).symm


theorem d021475 (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1672.d021424 0 a b 0 0 / _root_.GD.N0106.N0428.N0765.N1672.d021423 0 a b 0 0 =
      ((((11 / 8 : ℝ) * _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 /
        (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 0 + _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2)) : ℝ) : ℂ) := by
  have hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 0 0 < Real.pi := by
    simpa [_root_.GD.N0106.N0428.N0765.N1538.d021192] using Real.pi_pos
  exact tendsto_nhds_unique (_root_.GD.N0106.N0428.N0765.N1528.d021468 a b 0 0 hw)
    (_root_.GD.N0106.N0428.N0765.N1527.d021474 a b)


theorem d021476 (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1672.d021424 0 a b 0 0 / _root_.GD.N0106.N0428.N0765.N1672.d021423 0 a b 0 0 =
      ((((11 / 8 : ℝ) * _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 /
        (1 - _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1)) : ℝ) : ℂ) := by
  have hsum : _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 0 + _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2 =
      1 - _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 := by
    obtain ⟨h0, h1, h2⟩ := _root_.GD.N0106.N0428.N0765.N1538.d021252 a b
    rw [h0, h1, h2]
    ring
  rw [_root_.GD.N0106.N0428.N0765.N1527.d021475, hsum]

end
end GD.N0106.N0428.N0765.N1527

#print axioms _root_.GD.N0106.N0428.N0765.N1527.d021472
#print axioms _root_.GD.N0106.N0428.N0765.N1527.d021474
#print axioms _root_.GD.N0106.N0428.N0765.N1527.d021475
#print axioms _root_.GD.N0106.N0428.N0765.N1527.d021476
