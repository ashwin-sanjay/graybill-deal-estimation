import GD.Module1308
import GD.Module1313
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod









set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory Set Filter Topology
namespace GD.N0106.N0428.N0765.N1675
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1663 _root_.GD.N0106.N0428.N0765.N1672 _root_.GD.N0106.N0428.N0765.N1528
open _root_.GD.N0106.N0428.N0765.N1584 _root_.GD.N0106.N0428.N0765.N1521

def d021510 (e α β : ℝ) (p : ℝ × ℝ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1672.d021424 e p.1 p.2 α β / _root_.GD.N0106.N0428.N0765.N1672.d021423 e p.1 p.2 α β

def d021511 (α β : ℝ) : ℝ :=
  (3 / 2 : ℝ) * Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ^ (-((21 : ℝ) / 2)) * (_root_.GD.N0106.N0428.N0765.N1538.d021231 α β)⁻¹

theorem d021512 {α β : ℝ} (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    0 < _root_.GD.N0106.N0428.N0765.N1675.d021511 α β := by
  exact mul_pos (mul_pos (by norm_num)
    (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1538.d021219 (_root_.GD.N0106.N0428.N0765.N1538.d021233 hw)) _))
      (inv_pos.mpr (_root_.GD.N0106.N0428.N0765.N1538.d021232 hw))

theorem d021513 {e : ℝ} (he : 0 ≤ e) (α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (p : ℝ × ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1675.d021510 e α β p‖ ≤ _root_.GD.N0106.N0428.N0765.N1675.d021511 α β * Real.exp p.2 := by
  rcases he.eq_or_lt with he | he
  · subst e
    exact _root_.GD.N0106.N0428.N0765.N1528.d021469 p.1 p.2 α β hw
  · exact _root_.GD.N0106.N0428.N0765.N1672.d021430 he p.1 p.2 α β hw


theorem d021514 (z : ℂ) : Measurable (fun x : ℂ => x ^ z) := by
  simp only [Complex.cpow_def]
  exact Measurable.ite (measurableSet_singleton (0 : ℂ)) measurable_const
    (Complex.measurable_exp.comp (Complex.measurable_log.mul_const z))

theorem d021515 (e α β : ℝ) :
    Measurable (fun y : (ℝ × ℝ) × ℝ => _root_.GD.N0106.N0428.N0765.N1672.d021422 e y.1.1 y.1.2 α β y.2) := by
  have hb : Measurable (fun y : (ℝ × ℝ) × ℝ => _root_.GD.N0106.N0428.N0765.N1663.d021418 e y.1.1 y.1.2 α β y.2) := by
    unfold _root_.GD.N0106.N0428.N0765.N1663.d021418
    fun_prop
  have hp := (_root_.GD.N0106.N0428.N0765.N1675.d021514 (-((21 : ℂ) / 2))).comp hb
  have hm : Measurable (fun y : (ℝ × ℝ) × ℝ =>
      (y.2 * (1 - y.2)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e y.2 ^ 10) := by
    unfold _root_.GD.N0106.N0428.N0765.N1663.d021403
    fun_prop
  exact (Complex.measurable_ofReal.comp hm).mul hp

theorem d021516 (e α β : ℝ) :
    Measurable (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1672.d021423 e p.1 p.2 α β) := by
  have h := (_root_.GD.N0106.N0428.N0765.N1675.d021515 e α β).stronglyMeasurable.integral_prod_right
    (ν := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun p : ℝ × ℝ => fun x : ℝ => _root_.GD.N0106.N0428.N0765.N1672.d021422 e p.1 p.2 α β x)
  simpa only [_root_.GD.N0106.N0428.N0765.N1672.d021423, intervalIntegral.integral_of_le zero_le_one] using h.measurable

theorem d021517 (e α β : ℝ) :
    Measurable (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1672.d021424 e p.1 p.2 α β) := by
  have hm : Measurable (fun y : (ℝ × ℝ) × ℝ =>
      ((y.2 / _root_.GD.N0106.N0428.N0765.N1663.d021403 e y.2 : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1672.d021422 e y.1.1 y.1.2 α β y.2) := by
    have hf : Measurable (fun y : (ℝ × ℝ) × ℝ => ((y.2 / _root_.GD.N0106.N0428.N0765.N1663.d021403 e y.2 : ℝ) : ℂ)) := by
      unfold _root_.GD.N0106.N0428.N0765.N1663.d021403
      fun_prop
    exact hf.mul (_root_.GD.N0106.N0428.N0765.N1675.d021515 e α β)
  have h := hm.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun p : ℝ × ℝ => fun x : ℝ =>
      ((x / _root_.GD.N0106.N0428.N0765.N1663.d021403 e x : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1672.d021422 e p.1 p.2 α β x)
  simpa only [_root_.GD.N0106.N0428.N0765.N1672.d021424, intervalIntegral.integral_of_le zero_le_one] using h.measurable

@[fun_prop] theorem d021518 (e α β : ℝ) : Measurable (_root_.GD.N0106.N0428.N0765.N1675.d021510 e α β) :=
  (_root_.GD.N0106.N0428.N0765.N1675.d021517 e α β).div (_root_.GD.N0106.N0428.N0765.N1675.d021516 e α β)


theorem d021519 {e α β : ℝ} (he : 0 ≤ e)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0765.N1521.d020868 p * ‖_root_.GD.N0106.N0428.N0765.N1675.d021510 e α β p‖) := by
  refine Integrable.mono' (_root_.GD.N0106.N0428.N0765.N1584.d021372.const_mul (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β))
    ((_root_.GD.N0106.N0428.N0765.N1584.d021369.mul (_root_.GD.N0106.N0428.N0765.N1675.d021518 e α β).norm).aestronglyMeasurable) ?_
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (_root_.GD.N0106.N0428.N0765.N1584.d021368 p) (norm_nonneg _))]
  calc _root_.GD.N0106.N0428.N0765.N1521.d020868 p * ‖_root_.GD.N0106.N0428.N0765.N1675.d021510 e α β p‖ ≤
      _root_.GD.N0106.N0428.N0765.N1521.d020868 p * (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β * Real.exp p.2) :=
        mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1675.d021513 he α β hw p) (_root_.GD.N0106.N0428.N0765.N1584.d021368 p)
    _ = _root_.GD.N0106.N0428.N0765.N1675.d021511 α β * (_root_.GD.N0106.N0428.N0765.N1521.d020868 p * Real.exp p.2) := by ring

theorem d021520 {e α β : ℝ} (he : 0 ≤ e)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    (∫ p, _root_.GD.N0106.N0428.N0765.N1521.d020868 p * ‖_root_.GD.N0106.N0428.N0765.N1675.d021510 e α β p‖) ≤ (5 / 4) * _root_.GD.N0106.N0428.N0765.N1675.d021511 α β := by
  have h := integral_mono_ae (_root_.GD.N0106.N0428.N0765.N1675.d021519 he hw)
    (_root_.GD.N0106.N0428.N0765.N1584.d021372.const_mul (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β))
    (Filter.Eventually.of_forall (fun p => show
      _root_.GD.N0106.N0428.N0765.N1521.d020868 p * ‖_root_.GD.N0106.N0428.N0765.N1675.d021510 e α β p‖ ≤
        _root_.GD.N0106.N0428.N0765.N1675.d021511 α β * (_root_.GD.N0106.N0428.N0765.N1521.d020868 p * Real.exp p.2) from by
          nlinarith [mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1675.d021513 he α β hw p)
            (_root_.GD.N0106.N0428.N0765.N1584.d021368 p)]))
  change (∫ p, _root_.GD.N0106.N0428.N0765.N1521.d020868 p * ‖_root_.GD.N0106.N0428.N0765.N1675.d021510 e α β p‖) ≤
    ∫ p, _root_.GD.N0106.N0428.N0765.N1675.d021511 α β * (_root_.GD.N0106.N0428.N0765.N1521.d020868 p * Real.exp p.2) at h
  rw [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1584.d021374] at h
  simpa only [mul_comm] using h


theorem d021521 {e α β : ℝ} (he : 0 ≤ e)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0765.N1521.d020868 p * ‖_root_.GD.N0106.N0428.N0765.N1675.d021510 e α β p‖ ^ 2) := by
  refine Integrable.mono' (_root_.GD.N0106.N0428.N0765.N1584.d021373.const_mul ((_root_.GD.N0106.N0428.N0765.N1675.d021511 α β)^2))
    ((_root_.GD.N0106.N0428.N0765.N1584.d021369.mul ((_root_.GD.N0106.N0428.N0765.N1675.d021518 e α β).norm.pow_const 2)).aestronglyMeasurable) ?_
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (_root_.GD.N0106.N0428.N0765.N1584.d021368 p) (sq_nonneg _))]
  have hs := pow_le_pow_left₀ (norm_nonneg _) (_root_.GD.N0106.N0428.N0765.N1675.d021513 he α β hw p) 2
  calc _root_.GD.N0106.N0428.N0765.N1521.d020868 p * ‖_root_.GD.N0106.N0428.N0765.N1675.d021510 e α β p‖ ^ 2 ≤
      _root_.GD.N0106.N0428.N0765.N1521.d020868 p * (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β * Real.exp p.2)^2 :=
        mul_le_mul_of_nonneg_left hs (_root_.GD.N0106.N0428.N0765.N1584.d021368 p)
    _ = (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β)^2 * (_root_.GD.N0106.N0428.N0765.N1521.d020868 p * (Real.exp p.2)^2) := by ring

theorem d021522 {e α β : ℝ} (he : 0 ≤ e)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    (∫ p, _root_.GD.N0106.N0428.N0765.N1521.d020868 p * ‖_root_.GD.N0106.N0428.N0765.N1675.d021510 e α β p‖ ^ 2) ≤
      (5 / 2) * (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β)^2 := by
  have h := integral_mono_ae (_root_.GD.N0106.N0428.N0765.N1675.d021521 he hw)
    (_root_.GD.N0106.N0428.N0765.N1584.d021373.const_mul ((_root_.GD.N0106.N0428.N0765.N1675.d021511 α β)^2))
    (Filter.Eventually.of_forall (fun p => show
      _root_.GD.N0106.N0428.N0765.N1521.d020868 p * ‖_root_.GD.N0106.N0428.N0765.N1675.d021510 e α β p‖ ^ 2 ≤
        (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β)^2 * (_root_.GD.N0106.N0428.N0765.N1521.d020868 p * (Real.exp p.2)^2) from by
          have hs := pow_le_pow_left₀ (norm_nonneg _) (_root_.GD.N0106.N0428.N0765.N1675.d021513 he α β hw p) 2
          nlinarith [mul_le_mul_of_nonneg_left hs (_root_.GD.N0106.N0428.N0765.N1584.d021368 p)]))
  change (∫ p, _root_.GD.N0106.N0428.N0765.N1521.d020868 p * ‖_root_.GD.N0106.N0428.N0765.N1675.d021510 e α β p‖ ^ 2) ≤
    ∫ p, (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β)^2 * (_root_.GD.N0106.N0428.N0765.N1521.d020868 p * (Real.exp p.2)^2) at h
  rw [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1584.d021375] at h
  simpa only [mul_comm] using h



theorem d021523 (α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    Tendsto (fun e : ℝ => ∫ p, _root_.GD.N0106.N0428.N0765.N1521.d020868 p *
      ‖_root_.GD.N0106.N0428.N0765.N1675.d021510 e α β p - _root_.GD.N0106.N0428.N0765.N1675.d021510 0 α β p‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
    (fun p : ℝ × ℝ => (4 * (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β)^2) *
      (_root_.GD.N0106.N0428.N0765.N1521.d020868 p * (Real.exp p.2)^2))
    (F := fun e p => _root_.GD.N0106.N0428.N0765.N1521.d020868 p * ‖_root_.GD.N0106.N0428.N0765.N1675.d021510 e α β p - _root_.GD.N0106.N0428.N0765.N1675.d021510 0 α β p‖ ^ 2)
    (f := fun _ => (0 : ℝ)) ?_ ?_
    (_root_.GD.N0106.N0428.N0765.N1584.d021373.const_mul (4 * (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β)^2)) ?_
  · simpa only [integral_zero] using h
  · exact Filter.Eventually.of_forall fun e =>
      (_root_.GD.N0106.N0428.N0765.N1584.d021369.mul (((_root_.GD.N0106.N0428.N0765.N1675.d021518 e α β).sub
        (_root_.GD.N0106.N0428.N0765.N1675.d021518 0 α β)).norm.pow_const 2)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with e he
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (_root_.GD.N0106.N0428.N0765.N1584.d021368 p) (sq_nonneg _))]
    have h1 := _root_.GD.N0106.N0428.N0765.N1675.d021513 (le_of_lt he) α β hw p
    have h0 := _root_.GD.N0106.N0428.N0765.N1675.d021513 (e := 0) le_rfl α β hw p
    have hn := norm_sub_le (_root_.GD.N0106.N0428.N0765.N1675.d021510 e α β p) (_root_.GD.N0106.N0428.N0765.N1675.d021510 0 α β p)
    have hd : ‖_root_.GD.N0106.N0428.N0765.N1675.d021510 e α β p - _root_.GD.N0106.N0428.N0765.N1675.d021510 0 α β p‖ ≤
        2 * (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β * Real.exp p.2) := by linarith
    have hs := pow_le_pow_left₀ (norm_nonneg _) hd 2
    nlinarith [mul_le_mul_of_nonneg_left hs (_root_.GD.N0106.N0428.N0765.N1584.d021368 p)]
  · filter_upwards with p
    have hl := (_root_.GD.N0106.N0428.N0765.N1528.d021467 p.1 p.2 α β hw).sub_const
      (_root_.GD.N0106.N0428.N0765.N1675.d021510 0 α β p)
    have hs := (hl.norm.pow 2).const_mul (_root_.GD.N0106.N0428.N0765.N1521.d020868 p)
    simpa only [_root_.GD.N0106.N0428.N0765.N1675.d021510, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero] using hs

end
end GD.N0106.N0428.N0765.N1675

#print axioms _root_.GD.N0106.N0428.N0765.N1675.d021518
#print axioms _root_.GD.N0106.N0428.N0765.N1675.d021520
#print axioms _root_.GD.N0106.N0428.N0765.N1675.d021522
#print axioms _root_.GD.N0106.N0428.N0765.N1675.d021523
