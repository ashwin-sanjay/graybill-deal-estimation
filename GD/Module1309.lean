import GD.Module0389
import GD.Module1306
import GD.Module1307
import Mathlib.Topology.Order.LeftRight












set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory Set Filter Topology

namespace GD.N0106.N0428.N0765.N1612
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1534

def d021377 (m eta u v w l : ℝ) : ℝ :=
  (l * (1 - l)) ^ ((9 : ℝ) / 2) *
    (max (_root_.GD.N0106.N0428.N0765.N1534.d005328 eta u v w l) m) ^ (-((21 : ℝ) / 2))

def d021378 (m eta u v w : ℝ) : ℝ :=
  (∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1612.d021377 m eta u v w l) /
    ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1612.d021377 m eta u v w l

theorem d021379 {m : ℝ} (hm : 0 < m) (u v w : ℝ) :
    Continuous fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1612.d021377 m p.1 u v w p.2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1612.d021377
  refine Continuous.mul ?_ ?_
  · exact (Real.continuous_rpow_const (by norm_num)).comp (by fun_prop)
  · apply Continuous.rpow_const
      ((by unfold _root_.GD.N0106.N0428.N0765.N1534.d005328; fun_prop :
        Continuous fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1534.d005328 p.1 u v w p.2).max continuous_const)
    intro p
    exact Or.inl (lt_of_lt_of_le hm (le_max_right _ _)).ne'

theorem d021380 {m : ℝ} (hm : 0 < m) (eta u v w : ℝ) :
    0 < ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1612.d021377 m eta u v w l := by
  have hc : Continuous (_root_.GD.N0106.N0428.N0765.N1612.d021377 m eta u v w) :=
    (_root_.GD.N0106.N0428.N0765.N1612.d021379 hm u v w).comp (continuous_const.prodMk continuous_id)
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact hc.continuousOn.intervalIntegrable_of_Icc zero_le_one
  · intro l hl
    exact mul_pos (Real.rpow_pos_of_pos (mul_pos hl.1 (sub_pos.mpr hl.2)) _)
      (Real.rpow_pos_of_pos (lt_of_lt_of_le hm (le_max_right _ _)) _)
  · exact zero_lt_one

theorem d021381 {m : ℝ} (hm : 0 < m) (u v w : ℝ) :
    Continuous fun eta => _root_.GD.N0106.N0428.N0765.N1612.d021378 m eta u v w := by
  have hD : Continuous fun eta => ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1612.d021377 m eta u v w l := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (_root_.GD.N0106.N0428.N0765.N1612.d021379 hm u v w) 0 1
  have hN : Continuous fun eta => ∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1612.d021377 m eta u v w l := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (continuous_snd.mul (_root_.GD.N0106.N0428.N0765.N1612.d021379 hm u v w)) 0 1
  exact hN.div hD (fun eta => (_root_.GD.N0106.N0428.N0765.N1612.d021380 hm eta u v w).ne')

theorem d021382 {eta0 eta u v w : ℝ} (heta0 : 0 < eta0)
    (heta : eta0 / 2 ≤ eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    _root_.GD.N0106.N0428.N0765.N1534.d005330 eta u v w = _root_.GD.N0106.N0428.N0765.N1612.d021378 (min v (eta0 / 2 * w)) eta u v w := by
  have heta' : 0 < eta := lt_of_lt_of_le (half_pos heta0) heta
  have hbound : ∀ l ∈ Icc (0 : ℝ) 1,
      min v (eta0 / 2 * w) ≤ _root_.GD.N0106.N0428.N0765.N1534.d005328 eta u v w l := by
    intro l hl
    have hleft := min_le_left v (eta0 / 2 * w)
    have hright : min v (eta0 / 2 * w) ≤ eta * w :=
      (min_le_right _ _).trans (mul_le_mul_of_nonneg_right heta hw.le)
    have h1 := mul_le_mul_of_nonneg_right hleft (sub_nonneg.mpr hl.2)
    have h2 := mul_le_mul_of_nonneg_right hright hl.1
    have h3 : 0 ≤ (1 + eta) * u * l * (1 - l) := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith : 0 ≤ 1 + eta) hu) hl.1)
        (sub_nonneg.mpr hl.2)
    unfold _root_.GD.N0106.N0428.N0765.N1534.d005328
    nlinarith
  have hk : ∀ l ∈ Icc (0 : ℝ) 1,
      _root_.GD.N0106.N0428.N0765.N1534.d005329 eta u v w l = _root_.GD.N0106.N0428.N0765.N1612.d021377 (min v (eta0 / 2 * w)) eta u v w l := by
    intro l hl
    simp only [_root_.GD.N0106.N0428.N0765.N1534.d005329, _root_.GD.N0106.N0428.N0765.N1612.d021377, max_eq_left (hbound l hl)]
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005330 _root_.GD.N0106.N0428.N0765.N1612.d021378
  congr 1 <;> apply intervalIntegral.integral_congr <;> intro l hl
  · rw [uIcc_of_le zero_le_one] at hl
    simpa only using congrArg (fun y : ℝ => l * y) (hk l hl)
  · rw [uIcc_of_le zero_le_one] at hl
    exact hk l hl

theorem d021383 {eta u v w : ℝ} (heta : 0 < eta)
    (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    ContinuousAt (fun t => _root_.GD.N0106.N0428.N0765.N1534.d005330 t u v w) eta := by
  have hm : 0 < min v (eta / 2 * w) := lt_min hv (mul_pos (half_pos heta) hw)
  apply (_root_.GD.N0106.N0428.N0765.N1612.d021381 hm u v w).continuousAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (by linarith : eta / 2 < eta)] with t ht
  exact _root_.GD.N0106.N0428.N0765.N1612.d021382 heta ht.le hu hv hw

theorem d021384 {e : ℝ} (he : 0 < e) {p : ℝ × ℝ}
    (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420) :
    ContinuousAt (fun t => _root_.GD.N0106.N0428.N0765.N1664.d005965 t p.1 p.2) e := by
  obtain ⟨hu, hu1, hv, hv1⟩ := hp
  have hw : 0 ≤ 1 - p.1 - p.2 := by linarith
  rcases eq_or_lt_of_le hw with hw | hw
  · have hz : (fun t => _root_.GD.N0106.N0428.N0765.N1664.d005965 t p.1 p.2) = fun _ => (0 : ℝ) := by
      funext t
      unfold _root_.GD.N0106.N0428.N0765.N1664.d005965
      rw [← hw, _root_.GD.N0106.N0428.N0765.N1543.d005388, zero_mul]
    rw [hz]
    exact continuousAt_const
  · have hH : ContinuousAt (fun t => _root_.GD.N0106.N0428.N0765.N1664.d005963 t p.1 p.2) e := by
      have hc := (_root_.GD.N0106.N0428.N0765.N1612.d021383 (inv_pos.mpr he) hu.le hv hw).comp
        (continuousAt_id.inv₀ he.ne')
      apply hc.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds he] with t ht
      exact _root_.GD.N0106.N0428.N0765.N1664.d005964 ht hu.le
    have hq : ContinuousAt (fun t => p.2 / (t * p.2 + (1 - p.1 - p.2))) e := by
      apply ContinuousAt.div continuousAt_const (by fun_prop)
      exact (by positivity : 0 < e * p.2 + (1 - p.1 - p.2)).ne'
    have ho : ContinuousAt _root_.GD.N0106.N0428.N0765.N1543.d005392 e := by
      unfold _root_.GD.N0106.N0428.N0765.N1543.d005392
      exact continuousAt_const.div (by fun_prop) (by linarith)
    exact continuousAt_const.mul (((hq.sub ho).pow 2).sub
      ((((continuousAt_id.inv₀ he.ne').mul hH).sub ho).pow 2))

theorem d021385 {e : ℝ} (he : 0 < e) :
    ContinuousAt (fun t => ∫ p, _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator
      (Function.uncurry (_root_.GD.N0106.N0428.N0765.N1664.d005965 t)) p) e := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun p => _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry _root_.GD.N0106.N0428.N0765.N1664.d005967) p)
  · exact Eventually.of_forall fun t =>
      ((_root_.GD.N0106.N0428.N0765.N1664.d005969 t).indicator _root_.GD.N0106.N0428.N0765.N1542.d005421).aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds he] with t ht
    refine Eventually.of_forall fun p => ?_
    by_cases hp : p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420
    · rw [indicator_of_mem hp, indicator_of_mem hp, Real.norm_eq_abs]
      exact _root_.GD.N0106.N0428.N0765.N1664.d005975 ht hp
    · rw [indicator_of_notMem hp, indicator_of_notMem hp, norm_zero]
  · rw [integrable_indicator_iff _root_.GD.N0106.N0428.N0765.N1542.d005421]
    refine Integrable.mono' (integrableOn_const (C := 6)
      (hs := _root_.GD.N0106.N0428.N0765.N1542.d005423)) _root_.GD.N0106.N0428.N0765.N1664.d005971.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem _root_.GD.N0106.N0428.N0765.N1542.d005421] with p hp
    change ‖_root_.GD.N0106.N0428.N0765.N1664.d005967 p.1 p.2‖ ≤ 6
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0106.N0428.N0765.N1664.d005972 hp.1.le)]
    exact _root_.GD.N0106.N0428.N0765.N1664.d005973 hp
  · refine Eventually.of_forall fun p => ?_
    by_cases hp : p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420
    · simp only [indicator_of_mem hp]
      exact (_root_.GD.N0106.N0428.N0765.N1612.d021384 he hp).tendsto
    · simp only [indicator_of_notMem hp]
      exact tendsto_const_nhds

theorem d021386 {e : ℝ} (he : 0 < e) :
    ContinuousAt _root_.GD.N0106.N0428.N0765.N1543.d005396 e := by
  have hV : ContinuousAt (fun t : ℝ => _root_.GD.N0106.N0428.N0765.N1534.d005331 t) e := by unfold _root_.GD.N0106.N0428.N0765.N1534.d005331; fun_prop
  have hc := hV.mul ((_root_.GD.N0106.N0428.N0765.N1612.d021385 he).div_const _root_.GD.N0106.N0428.N0765.N1543.d005384)
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds he] with t ht
  exact _root_.GD.N0106.N0428.N0765.N1664.d005986 ht

theorem d021387 :
    ∀ᵐ p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798, 0 ≤ p 0 ∧ 0 < p 1 ∧ 0 < p 2 := by
  rw [← _root_.GD.N0106.N0428.N0765.N1521.d020844]
  apply (ae_map_iff _root_.GD.N0235.d004248.aemeasurable ?_).2
  · filter_upwards [_root_.GD.N0106.N0428.N0765.N1521.d020846] with p hp
    change 0 ≤ p.1 ∧ 0 < (1 - p.1) * p.2 ∧ 0 < (1 - p.1) * (1 - p.2)
    exact ⟨hp.1.1.le, mul_pos (sub_pos.mpr hp.1.2) hp.2.1,
      mul_pos (sub_pos.mpr hp.1.2) (sub_pos.mpr hp.2.2)⟩
  · exact (measurableSet_le measurable_const (measurable_pi_apply 0)).inter
      ((measurableSet_lt measurable_const (measurable_pi_apply 1)).inter
        (measurableSet_lt measurable_const (measurable_pi_apply 2)))


theorem d021388 {e : ℝ} (he : 0 < e) :
    ∀ᵐ p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798,
      (e⁻¹ * _root_.GD.N0106.N0428.N0765.N1529.d020799 e⁻¹ p) ^ 2 ≤
        (9 / 4 : ℝ) * (p 1 / p 2) ^ 2 := by
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1612.d021387] with p hp
  have he' := inv_pos.mpr he
  have hH0 : 0 ≤ e⁻¹ * _root_.GD.N0106.N0428.N0765.N1529.d020799 e⁻¹ p :=
    mul_nonneg he'.le (_root_.GD.N0106.N0428.N0765.N1534.d005345 he' hp.1 hp.2.1 hp.2.2).1.le
  have h := _root_.GD.N0106.N0428.N0765.N1681.d005962 he' hp.1 hp.2.1 hp.2.2
  rw [inv_inv] at h
  have hfrac : p 1 / (e * p 1 + p 2) ≤ p 1 / p 2 :=
    div_le_div_of_nonneg_left hp.2.1.le hp.2.2
      (by nlinarith [mul_nonneg he.le hp.2.1.le])
  have hH : e⁻¹ * _root_.GD.N0106.N0428.N0765.N1529.d020799 e⁻¹ p ≤ (3 / 2 : ℝ) * (p 1 / p 2) :=
    h.trans (mul_le_mul_of_nonneg_left hfrac (by norm_num))
  calc
    (e⁻¹ * _root_.GD.N0106.N0428.N0765.N1529.d020799 e⁻¹ p) ^ 2 ≤ ((3 / 2 : ℝ) * (p 1 / p 2)) ^ 2 :=
      pow_le_pow_left₀ hH0 hH 2
    _ = (9 / 4 : ℝ) * (p 1 / p 2) ^ 2 := by ring

theorem d021389 {e : ℝ} (he : 0 < e) :
    Integrable (fun p => (e⁻¹ * _root_.GD.N0106.N0428.N0765.N1529.d020799 e⁻¹ p) ^ 2)
      _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  refine Integrable.mono' (_root_.GD.N0106.N0428.N0765.N1661.d021361.const_mul (9 / 4 : ℝ))
    (((_root_.GD.N0106.N0428.N0765.N1529.d020809 e⁻¹).const_mul e⁻¹).pow_const 2).aestronglyMeasurable ?_
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1612.d021388 he] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hp

theorem d021390 {e : ℝ} (he : 0 < e) :
    (∫ p, (e⁻¹ * _root_.GD.N0106.N0428.N0765.N1529.d020799 e⁻¹ p) ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1529.d020798)
      ≤ (45 / 8 : ℝ) := by
  have h := integral_mono_ae (_root_.GD.N0106.N0428.N0765.N1612.d021389 he)
    (_root_.GD.N0106.N0428.N0765.N1661.d021361.const_mul (9 / 4 : ℝ))
    (_root_.GD.N0106.N0428.N0765.N1612.d021388 he)
  rw [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1661.d021363] at h
  norm_num at h ⊢
  exact h


def d021391 (location eta : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta (_root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 11)) -
    _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1611.d012593

def d021392 (location e : ℝ) : ℝ := e⁻¹ * _root_.GD.N0106.N0428.N0765.N1612.d021391 location e⁻¹

theorem d021393 (location eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1612.d021391 location eta = _root_.GD.N0106.N0428.N0765.N1543.d005395 eta := by
  rw [_root_.GD.N0106.N0428.N0765.N1612.d021391, _root_.GD.N0106.N0428.N0765.N1529.d020838 location eta heta,
    ← _root_.GD.N0106.N0428.N0765.N1632.d021350 eta heta]

theorem d021394 (location e : ℝ) (he : 0 < e) :
    _root_.GD.N0106.N0428.N0765.N1612.d021392 location e = _root_.GD.N0106.N0428.N0765.N1543.d005396 e := by
  rw [_root_.GD.N0106.N0428.N0765.N1612.d021392, _root_.GD.N0106.N0428.N0765.N1612.d021393 location e⁻¹ (inv_pos.mpr he)]
  rfl

theorem d021395 (location : ℝ) :
    Tendsto (_root_.GD.N0106.N0428.N0765.N1612.d021392 location) (𝓝[>] 0) (𝓝 (5 / 264)) := by
  apply _root_.GD.N0106.N0428.N0765.N1664.d005987.congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  exact (_root_.GD.N0106.N0428.N0765.N1612.d021394 location e he).symm


def d021396 (location e : ℝ) : ℝ := if e = 0 then 5 / 264 else _root_.GD.N0106.N0428.N0765.N1612.d021392 location e

theorem d021397 (location : ℝ) : _root_.GD.N0106.N0428.N0765.N1612.d021396 location 0 = 5 / 264 := by
  simp [_root_.GD.N0106.N0428.N0765.N1612.d021396]

theorem d021398 (location e : ℝ) (he : 0 < e) :
    _root_.GD.N0106.N0428.N0765.N1612.d021396 location e = e⁻¹ * _root_.GD.N0106.N0428.N0765.N1612.d021391 location e⁻¹ := by
  simp [_root_.GD.N0106.N0428.N0765.N1612.d021396, he.ne', _root_.GD.N0106.N0428.N0765.N1612.d021392]

theorem d021399 (location : ℝ) :
    ContinuousWithinAt (_root_.GD.N0106.N0428.N0765.N1612.d021396 location) (Ici 0) 0 := by
  apply continuousWithinAt_Ioi_iff_Ici.mp
  change Tendsto (_root_.GD.N0106.N0428.N0765.N1612.d021396 location) (𝓝[>] 0) (𝓝 (_root_.GD.N0106.N0428.N0765.N1612.d021396 location 0))
  rw [_root_.GD.N0106.N0428.N0765.N1612.d021397]
  apply (_root_.GD.N0106.N0428.N0765.N1612.d021395 location).congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  have he' : 0 < e := he
  simp only [_root_.GD.N0106.N0428.N0765.N1612.d021396, if_neg he'.ne']

theorem d021400 (location : ℝ) {e : ℝ} (he : 0 < e) :
    ContinuousAt (_root_.GD.N0106.N0428.N0765.N1612.d021396 location) e := by
  apply (_root_.GD.N0106.N0428.N0765.N1612.d021386 he).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds he] with t ht
  have ht' : 0 < t := ht
  simp only [_root_.GD.N0106.N0428.N0765.N1612.d021396, if_neg ht'.ne']
  exact _root_.GD.N0106.N0428.N0765.N1612.d021394 location t ht'


theorem d021401 (location : ℝ) :
    ContinuousOn (_root_.GD.N0106.N0428.N0765.N1612.d021396 location) (Ici 0) := by
  intro e he
  have he' : 0 ≤ e := he
  rcases eq_or_lt_of_le he' with he | he
  · subst e
    exact _root_.GD.N0106.N0428.N0765.N1612.d021399 location
  · exact (_root_.GD.N0106.N0428.N0765.N1612.d021400 location he).continuousWithinAt


theorem d021402 {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hsum : u + v + w = 1) :
    Tendsto (fun eta => eta * _root_.GD.N0106.N0428.N0765.N1534.d005330 eta u v w) atTop
      (𝓝 ((11 / 8 : ℝ) * v / (1 - v))) := by
  have h := _root_.GD.N0106.N0428.N0765.N1673.d005866 hu hv hw
  rw [show u + w = 1 - v by linarith] at h
  exact h

end
end GD.N0106.N0428.N0765.N1612

#print axioms _root_.GD.N0106.N0428.N0765.N1612.d021383
#print axioms _root_.GD.N0106.N0428.N0765.N1612.d021385
#print axioms _root_.GD.N0106.N0428.N0765.N1612.d021389
#print axioms _root_.GD.N0106.N0428.N0765.N1612.d021390
#print axioms _root_.GD.N0106.N0428.N0765.N1612.d021393
#print axioms _root_.GD.N0106.N0428.N0765.N1612.d021395
#print axioms _root_.GD.N0106.N0428.N0765.N1612.d021401
#print axioms _root_.GD.N0106.N0428.N0765.N1612.d021402
