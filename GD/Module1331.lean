import GD.Module1019
import GD.Module0274
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0101.N0368
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1242 _root_.GD.N0232.N0720.N1234
open _root_.GD.N0232.N0720.N1436

theorem d021673 {u t : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (u - t) ^ 2 / _root_.GD.N0232.N0720.N1242.d002130 t u ≤ u + t := by
  apply (div_le_iff₀ (_root_.GD.N0232.N0720.N1242.d002132 ht hu)).mpr
  have hnon := mul_nonneg (mul_nonneg hu.1.le ht.1.le)
    (show 0 ≤ 2 - u - t by linarith [hu.2, ht.2])
  unfold _root_.GD.N0232.N0720.N1242.d002130
  nlinarith

theorem d021674 : Integrable (fun u : ℝ => u) _root_.GD.N0232.N0720.N1242.d002139 := by
  letI := _root_.GD.N0232.N0720.N1242.d002140
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [_root_.GD.N0232.N0720.N1242.d002141] with u hu
  rw [Real.norm_eq_abs, abs_of_pos hu.1]
  exact hu.2.le

theorem d021675 : (∫ u : ℝ, u ∂_root_.GD.N0232.N0720.N1242.d002139) = 1 / 2 := by
  calc
    _ = beta ((1 / 2 : ℝ) + 1) (1 / 2) / beta (1 / 2) (1 / 2) := by
      simpa only [_root_.GD.N0232.N0720.N1242.d002139, pow_one, pow_zero, mul_one, Nat.cast_one,
        Nat.cast_zero, add_zero] using
        _root_.GD.N0235.d004044
          (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) 1 0
    _ = _ := by
      rw [_root_.GD.N0235.d004038
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)]
      rw [mul_div_cancel_right₀ _ (ne_of_gt (beta_pos
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)))]
      norm_num

theorem d021676 {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ u, ENNReal.ofReal (u + t) ∂_root_.GD.N0232.N0720.N1242.d002139) = ENNReal.ofReal (1 / 2 + t) := by
  letI := _root_.GD.N0232.N0720.N1242.d002140
  have hi : Integrable (fun u : ℝ => u + t) _root_.GD.N0232.N0720.N1242.d002139 :=
    _root_.GD.N0101.N0368.d021674.add (integrable_const t)
  rw [← ofReal_integral_eq_lintegral_ofReal
    hi
    (_root_.GD.N0232.N0720.N1242.d002141.mono fun u hu => add_nonneg hu.1.le ht),
    integral_add _root_.GD.N0101.N0368.d021674 (integrable_const t), _root_.GD.N0101.N0368.d021675]
  simp


theorem d021677 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1242.d002144 t id ≤ ENNReal.ofReal (Real.sqrt t * (1 / 2 + t)) := by
  rw [_root_.GD.N0232.N0720.N1242.d002145 t ht id measurable_id]
  have hbound : (∫⁻ u, _root_.GD.N0232.N0720.N1242.d002131 t u u ∂_root_.GD.N0232.N0720.N1242.d002139) ≤ ENNReal.ofReal (1 / 2 + t) := by
    rw [← _root_.GD.N0101.N0368.d021676 ht.1.le]
    apply lintegral_mono_ae
    filter_upwards [_root_.GD.N0232.N0720.N1242.d002141] with u hu
    exact ENNReal.ofReal_le_ofReal (_root_.GD.N0101.N0368.d021673 hu ht)
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt (t * (1 - t))) * ENNReal.ofReal (1 / 2 + t) := by
      gcongr
      exact hbound
    _ = ENNReal.ofReal (Real.sqrt (t * (1 - t)) * (1 / 2 + t)) :=
      (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])) (by linarith [ht.1]))


theorem d021678 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ z, ENNReal.ofReal ((z.1 - t) ^ 2) ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t) ≤
      ENNReal.ofReal (Real.sqrt t * (1 / 2 + t)) := by
  rw [_root_.GD.N0232.N0720.N1234.d016228 ht
    (fun u => ENNReal.ofReal ((u - t) ^ 2)) (by fun_prop)]
  exact _root_.GD.N0101.N0368.d021677 ht

def d021679 (t : ℝ) : ℝ := (_root_.GD.N0232.N0720.N1242.d002144 t id).toReal

theorem d021680 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0101.N0368.d021679 t =
      (∫⁻ z, ENNReal.ofReal ((z.1 - t) ^ 2) ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t).toReal := by
  rw [_root_.GD.N0232.N0720.N1234.d016228 ht
    (fun u => ENNReal.ofReal ((u - t) ^ 2)) (by fun_prop)]
  rfl

theorem d021681 : Measurable _root_.GD.N0101.N0368.d021679 := by
  letI := _root_.GD.N0232.N0720.N1242.d002140
  have heq : (fun t => _root_.GD.N0232.N0720.N1242.d002144 t id) = fun t => ∫⁻ u,
      ENNReal.ofReal (Real.sqrt (t * (1 - t)) / _root_.GD.N0232.N0720.N1242.d002130 t u) *
        ENNReal.ofReal ((u - t) ^ 2) ∂_root_.GD.N0232.N0720.N1242.d002139 := by
    funext t
    unfold _root_.GD.N0232.N0720.N1242.d002144 _root_.GD.N0232.N0720.N1242.d002143
    exact lintegral_withDensity_eq_lintegral_mul _
      (by unfold _root_.GD.N0232.N0720.N1242.d002130; fun_prop) (by fun_prop)
  have hm : Measurable (fun t => _root_.GD.N0232.N0720.N1242.d002144 t id) := by
    rw [heq]
    exact (show Measurable (fun z : ℝ × ℝ =>
      ENNReal.ofReal (Real.sqrt (z.1 * (1 - z.1)) / _root_.GD.N0232.N0720.N1242.d002130 z.1 z.2) *
        ENNReal.ofReal ((z.2 - z.1) ^ 2)) by unfold _root_.GD.N0232.N0720.N1242.d002130; fun_prop).lintegral_prod_right
  exact hm.ennreal_toReal

theorem d021682 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0101.N0368.d021679 t ≤ Real.sqrt t * (1 / 2 + t) :=
  ENNReal.toReal_le_of_le_ofReal (mul_nonneg (Real.sqrt_nonneg _) (by linarith [ht.1]))
    (_root_.GD.N0101.N0368.d021677 ht)

def d021683 (t : ℝ) : ℝ := _root_.GD.N0101.N0368.d021679 t * t ^ (-(3 / 2 : ℝ))

theorem d021684 : Measurable _root_.GD.N0101.N0368.d021683 :=
  _root_.GD.N0101.N0368.d021681.mul (measurable_id.pow_const _)

theorem d021685 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0101.N0368.d021683 t ≤ (1 / 2 : ℝ) / t + 1 := by
  have hpow : t ^ (1 / 2 : ℝ) * t ^ (-(3 / 2 : ℝ)) = t⁻¹ := by
    rw [← Real.rpow_add ht.1]
    norm_num [Real.rpow_neg_one]
  calc
    _ ≤ (Real.sqrt t * (1 / 2 + t)) * t ^ (-(3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (_root_.GD.N0101.N0368.d021682 ht) (Real.rpow_nonneg ht.1.le _)
    _ = (1 / 2 + t) * t⁻¹ := by
      rw [Real.sqrt_eq_rpow]
      calc
        _ = (1 / 2 + t) * (t ^ (1 / 2 : ℝ) * t ^ (-(3 / 2 : ℝ))) := by ring
        _ = _ := by rw [hpow]
    _ = _ := by field_simp [ht.1.ne']

theorem d021686 {a ε : ℝ}
    (ha : 0 < a) (he : ε < 1) : IntegrableOn _root_.GD.N0101.N0368.d021683 (Ioo a ε) := by
  have hc : ContinuousOn (fun t : ℝ => (1 / 2 : ℝ) / t + 1) (Icc a ε) :=
    (continuousOn_const.div continuousOn_id
      (fun t ht => (ha.trans_le ht.1).ne')).add continuousOn_const
  apply (hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mono'
    _root_.GD.N0101.N0368.d021684.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hn : 0 ≤ _root_.GD.N0101.N0368.d021683 t :=
    mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (ha.trans ht.1).le _)
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact _root_.GD.N0101.N0368.d021685 ⟨ha.trans ht.1, ht.2.trans he⟩


theorem d021687 {a ε : ℝ}
    (ha : 0 < a) (hae : a ≤ ε) (he : ε < 1) :
    (∫ t in Ioo a ε, _root_.GD.N0101.N0368.d021683 t) ≤
      (1 / 2 : ℝ) * Real.log (ε / a) + (ε - a) := by
  have hc : ContinuousOn (fun t : ℝ => (1 / 2 : ℝ) / t + 1) (Icc a ε) :=
    (continuousOn_const.div continuousOn_id
      (fun t ht => (ha.trans_le ht.1).ne')).add continuousOn_const
  calc
    _ ≤ ∫ t in Ioo a ε, (1 / 2 : ℝ) / t + 1 := by
      apply integral_mono_ae (_root_.GD.N0101.N0368.d021686 ha he)
        (hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact _root_.GD.N0101.N0368.d021685 ⟨ha.trans ht.1, ht.2.trans he⟩
    _ = _ := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hae]
      have hci : ContinuousOn (fun t : ℝ => t⁻¹) (Icc a ε) :=
        continuousOn_id.inv₀ (fun t ht => (ha.trans_le ht.1).ne')
      change (∫ t in a..ε, (1 / 2 : ℝ) * t⁻¹ + 1) = _
      rw [intervalIntegral.integral_add
        ((hci.intervalIntegrable_of_Icc hae).const_mul (1 / 2 : ℝ))
        intervalIntegrable_const, intervalIntegral.integral_const_mul,
        integral_inv_of_pos ha (ha.trans_le hae)]
      simp

end
end GD.N0101.N0368

#print axioms _root_.GD.N0101.N0368.d021673
#print axioms _root_.GD.N0101.N0368.d021675
#print axioms _root_.GD.N0101.N0368.d021678
#print axioms _root_.GD.N0101.N0368.d021681
#print axioms _root_.GD.N0101.N0368.d021686
#print axioms _root_.GD.N0101.N0368.d021687
