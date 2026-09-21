import GD.Module1312











set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory Set Filter Topology

namespace GD.N0106.N0428.N0765.N1528
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1663 _root_.GD.N0106.N0428.N0765.N1672 _root_.GD.N0106.N0428.N0765.N1526

theorem d021458 (e a b x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b 0 0 x = (_root_.GD.N0106.N0428.N0765.N1526.d021435 e a b x : ℂ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1526.d021439]
  simp only [zero_add, _root_.GD.N0106.N0428.N0765.N1538.d021187, _root_.GD.N0106.N0428.N0765.N1526.d021435, Complex.ofReal_add]

theorem d021459 (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ContinuousOn (_root_.GD.N0106.N0428.N0765.N1672.d021422 0 a b α β) (Ioo (0 : ℝ) 1) := by
  have hb : Continuous (_root_.GD.N0106.N0428.N0765.N1663.d021418 0 a b α β) := by unfold _root_.GD.N0106.N0428.N0765.N1663.d021418; fun_prop
  have hr := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 9 / 2)).comp
    (show Continuous (fun x : ℝ => x * (1 - x)) by fun_prop)
  have hweight : Continuous (fun x : ℝ =>
      (((x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 0 x ^ 10 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hr.mul (by unfold _root_.GD.N0106.N0428.N0765.N1663.d021403; fun_prop))
  exact hweight.continuousOn.mul (hb.continuousOn.cpow_const fun x hx =>
    _root_.GD.N0106.N0428.N0765.N1526.d021446 le_rfl (Ioo_subset_Icc_self hx)
      (by simpa [_root_.GD.N0106.N0428.N0765.N1663.d021403] using sub_pos.mpr hx.2) a b α β hw)

theorem d021460 (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    IntervalIntegrable (_root_.GD.N0106.N0428.N0765.N1672.d021422 0 a b α β) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  refine Integrable.mono' (integrableOn_const (C := _root_.GD.N0106.N0428.N0765.N1526.d021443 b α β) (by simp [Real.volume_Ioo]))
    ((_root_.GD.N0106.N0428.N0765.N1528.d021459 a b α β hw).aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact _root_.GD.N0106.N0428.N0765.N1526.d021449 le_rfl hx a b α β (_root_.GD.N0106.N0428.N0765.N1538.d021233 hw)

theorem d021461 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (a b : ℝ) :
    0 < (_root_.GD.N0106.N0428.N0765.N1672.d021422 0 a b 0 0 x).re := by
  have hD : 0 < _root_.GD.N0106.N0428.N0765.N1663.d021403 0 x := by simpa [_root_.GD.N0106.N0428.N0765.N1663.d021403] using sub_pos.mpr hx.2
  have hm : 0 < _root_.GD.N0106.N0428.N0765.N1526.d021435 0 a b x :=
    lt_of_lt_of_le (mul_pos (lt_min (Real.exp_pos b) zero_lt_one) hD)
      (_root_.GD.N0106.N0428.N0765.N1526.d021440 le_rfl (Ioo_subset_Icc_self hx) a b)
  have hw : 0 < (x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 0 x ^ 10 :=
    mul_pos (Real.rpow_pos_of_pos (mul_pos hx.1 (sub_pos.mpr hx.2)) _) (pow_pos hD _)
  have hcp : (_root_.GD.N0106.N0428.N0765.N1526.d021435 0 a b x : ℂ) ^ (-((21 : ℂ) / 2)) =
      ((_root_.GD.N0106.N0428.N0765.N1526.d021435 0 a b x ^ (-((21 : ℝ) / 2)) : ℝ) : ℂ) := by
    convert (Complex.ofReal_cpow hm.le (-((21 : ℝ) / 2))).symm using 1 <;> push_cast <;> rfl
  unfold _root_.GD.N0106.N0428.N0765.N1672.d021422
  rw [_root_.GD.N0106.N0428.N0765.N1528.d021458, hcp, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_pos hw (Real.rpow_pos_of_pos hm _)


theorem d021462 (a b : ℝ) : 0 < (_root_.GD.N0106.N0428.N0765.N1672.d021423 0 a b 0 0).re := by
  have hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 0 0 < Real.pi := by simpa [_root_.GD.N0106.N0428.N0765.N1538.d021192] using Real.pi_pos
  have hi := _root_.GD.N0106.N0428.N0765.N1528.d021460 a b 0 0 hw
  have hire : IntervalIntegrable (fun x => (_root_.GD.N0106.N0428.N0765.N1672.d021422 0 a b 0 0 x).re) volume 0 1 :=
    ⟨hi.1.re, hi.2.re⟩
  have hp := intervalIntegral.intervalIntegral_pos_of_pos_on hire
    (fun x hx => _root_.GD.N0106.N0428.N0765.N1528.d021461 hx a b) zero_lt_one
  have heq : (∫ x in (0 : ℝ)..1, (_root_.GD.N0106.N0428.N0765.N1672.d021422 0 a b 0 0 x).re) =
      (_root_.GD.N0106.N0428.N0765.N1672.d021423 0 a b 0 0).re := by
    unfold _root_.GD.N0106.N0428.N0765.N1672.d021423
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact integral_re hi.1
  rwa [heq] at hp

theorem d021463 {e : ℝ} (he : 0 < e) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1538.d021245 e a b = (_root_.GD.N0106.N0428.N0765.N1538.d021243 e a b 0 0).re := by
  have heq : _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b 0 0 = (_root_.GD.N0106.N0428.N0765.N1538.d021245 e a b : ℂ) := by
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
  rw [heq, Complex.ofReal_re]


theorem d021464 {e : ℝ} (he : 0 < e) (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    _root_.GD.N0106.N0428.N0765.N1538.d021231 α β * (_root_.GD.N0106.N0428.N0765.N1672.d021423 e a b 0 0).re ≤ ‖_root_.GD.N0106.N0428.N0765.N1672.d021423 e a b α β‖ := by
  have hc : 0 < (e⁻¹) ^ 5 := pow_pos (inv_pos.mpr he) _
  have hh := _root_.GD.N0106.N0428.N0765.N1538.d021250 he a b α β hw
  rw [_root_.GD.N0106.N0428.N0765.N1528.d021463 he a b,
    _root_.GD.N0106.N0428.N0765.N1672.d021427 he a b 0 0 (by simpa [_root_.GD.N0106.N0428.N0765.N1538.d021192] using Real.pi_pos),
    _root_.GD.N0106.N0428.N0765.N1672.d021427 he a b α β (_root_.GD.N0106.N0428.N0765.N1538.d021233 hw)] at hh
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, norm_mul, Complex.norm_of_nonneg hc.le] at hh
  apply (mul_le_mul_iff_right₀ hc).mp
  nlinarith only [hh]


theorem d021465 (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    _root_.GD.N0106.N0428.N0765.N1538.d021231 α β * (_root_.GD.N0106.N0428.N0765.N1672.d021423 0 a b 0 0).re ≤ ‖_root_.GD.N0106.N0428.N0765.N1672.d021423 0 a b α β‖ := by
  have hw0 : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 0 0 < Real.pi := by simpa [_root_.GD.N0106.N0428.N0765.N1538.d021192] using Real.pi_pos
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp
    (_root_.GD.N0106.N0428.N0765.N1526.d021456 a b 0 0 hw0)
  have hleft := hreal.const_mul (_root_.GD.N0106.N0428.N0765.N1538.d021231 α β)
  have hright := (_root_.GD.N0106.N0428.N0765.N1526.d021456 a b α β hw).norm
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with e he
  exact _root_.GD.N0106.N0428.N0765.N1528.d021464 he a b α β hw

theorem d021466 (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    _root_.GD.N0106.N0428.N0765.N1672.d021423 0 a b α β ≠ 0 := by
  apply norm_pos_iff.mp
  exact (mul_pos (_root_.GD.N0106.N0428.N0765.N1538.d021232 hw) (_root_.GD.N0106.N0428.N0765.N1528.d021462 a b)).trans_le
    (_root_.GD.N0106.N0428.N0765.N1528.d021465 a b α β hw)


theorem d021467 (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    Tendsto (fun e => _root_.GD.N0106.N0428.N0765.N1672.d021424 e a b α β / _root_.GD.N0106.N0428.N0765.N1672.d021423 e a b α β)
      (𝓝[>] 0) (𝓝 (_root_.GD.N0106.N0428.N0765.N1672.d021424 0 a b α β / _root_.GD.N0106.N0428.N0765.N1672.d021423 0 a b α β)) :=
  (_root_.GD.N0106.N0428.N0765.N1526.d021457 a b α β hw).div (_root_.GD.N0106.N0428.N0765.N1526.d021456 a b α β hw)
    (_root_.GD.N0106.N0428.N0765.N1528.d021466 a b α β hw)


theorem d021468 (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    Tendsto (fun e => _root_.GD.N0106.N0428.N0765.N1538.d021247 e a b α β) (𝓝[>] 0)
      (𝓝 (_root_.GD.N0106.N0428.N0765.N1672.d021424 0 a b α β / _root_.GD.N0106.N0428.N0765.N1672.d021423 0 a b α β)) := by
  refine (_root_.GD.N0106.N0428.N0765.N1528.d021467 a b α β hw).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with e he
  exact (_root_.GD.N0106.N0428.N0765.N1672.d021429 he a b α β (_root_.GD.N0106.N0428.N0765.N1538.d021233 hw)).symm


theorem d021469 (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1672.d021424 0 a b α β / _root_.GD.N0106.N0428.N0765.N1672.d021423 0 a b α β‖ ≤
      (3 / 2 : ℝ) * Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ^ (-((21 : ℝ) / 2)) *
        (_root_.GD.N0106.N0428.N0765.N1538.d021231 α β)⁻¹ * Real.exp b := by
  apply le_of_tendsto (_root_.GD.N0106.N0428.N0765.N1528.d021467 a b α β hw).norm
  filter_upwards [self_mem_nhdsWithin] with e he
  exact _root_.GD.N0106.N0428.N0765.N1672.d021430 he a b α β hw

end
end GD.N0106.N0428.N0765.N1528

#print axioms _root_.GD.N0106.N0428.N0765.N1528.d021462
#print axioms _root_.GD.N0106.N0428.N0765.N1528.d021466
#print axioms _root_.GD.N0106.N0428.N0765.N1528.d021467
#print axioms _root_.GD.N0106.N0428.N0765.N1528.d021468
#print axioms _root_.GD.N0106.N0428.N0765.N1528.d021469
