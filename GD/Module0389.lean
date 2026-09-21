import GD.Module0385
import GD.Module0362
import GD.Module0388
import Mathlib.Tactic






















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology

namespace GD.N0106.N0428.N0765.N1664
open _root_.GD.N0106.N0428.N0765.N1534 _root_.GD.N0106.N0428.N0765.N1543 _root_.GD.N0106.N0428.N0765.N1542 _root_.GD.N0106.N0428.N0765.N1673 _root_.GD.N0106.N0428.N0765.N1681
noncomputable section





def d005963 (e u v : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1534.d005299 v (e⁻¹ * (1 - u - v)) (Real.sqrt ((1 + e⁻¹) * u / 11))

theorem d005964 {e u v : ℝ} (he : 0 < e) (hu : 0 ≤ u) :
    _root_.GD.N0106.N0428.N0765.N1664.d005963 e u v = _root_.GD.N0106.N0428.N0765.N1534.d005330 e⁻¹ u v (1 - u - v) := by
  unfold _root_.GD.N0106.N0428.N0765.N1664.d005963
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005344 (inv_pos.mpr he) hu]


def d005965 (e u v : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) *
    ((v / (e * v + (1 - u - v)) - _root_.GD.N0106.N0428.N0765.N1543.d005392 e) ^ 2 - (e⁻¹ * _root_.GD.N0106.N0428.N0765.N1664.d005963 e u v - _root_.GD.N0106.N0428.N0765.N1543.d005392 e) ^ 2)


def d005966 (u v : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) *
    ((v / (1 - u - v) - 1) ^ 2 - (11 / 8 * v / (u + (1 - u - v)) - 1) ^ 2)


def d005967 (u v : ℝ) : ℝ :=
  Real.sqrt u * (13 / 4 * (v ^ 6 * (1 - u - v) ^ 2) + 2 * (v ^ 4 * (1 - u - v) ^ 4))

theorem d005968 (e : ℝ) : Measurable fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1664.d005963 e p.1 p.2 := by
  have hmap : Measurable fun p : ℝ × ℝ =>
      (p.2, (e⁻¹ * (1 - p.1 - p.2), Real.sqrt ((1 + e⁻¹) * p.1 / 11))) := by
    refine measurable_snd.prodMk (Measurable.prodMk ?_ ?_)
    · exact measurable_const.mul ((measurable_const.sub measurable_fst).sub measurable_snd)
    · exact Real.continuous_sqrt.measurable.comp
        ((measurable_const.mul measurable_fst).div_const 11)
  have h := _root_.GD.N0106.N0428.N0765.N1534.d005350.comp hmap
  simpa [Function.comp_def, _root_.GD.N0106.N0428.N0765.N1664.d005963] using h

theorem d005969 (e : ℝ) : Measurable (Function.uncurry (_root_.GD.N0106.N0428.N0765.N1664.d005965 e)) := by
  have h1 : Measurable fun p : ℝ × ℝ => p.2 / (e * p.2 + (1 - p.1 - p.2)) :=
    measurable_snd.div ((measurable_const.mul measurable_snd).add
      ((measurable_const.sub measurable_fst).sub measurable_snd))
  have h2 : Measurable fun p : ℝ × ℝ => e⁻¹ * _root_.GD.N0106.N0428.N0765.N1664.d005963 e p.1 p.2 := measurable_const.mul (_root_.GD.N0106.N0428.N0765.N1664.d005968 e)
  exact _root_.GD.N0106.N0428.N0765.N1542.d005435.mul (((h1.sub measurable_const).pow_const 2).sub
    ((h2.sub measurable_const).pow_const 2))

theorem d005970 : Measurable (Function.uncurry _root_.GD.N0106.N0428.N0765.N1664.d005966) := by
  have h1 : Measurable fun p : ℝ × ℝ => p.2 / (1 - p.1 - p.2) :=
    measurable_snd.div ((measurable_const.sub measurable_fst).sub measurable_snd)
  have h2 : Measurable fun p : ℝ × ℝ => 11 / 8 * p.2 / (p.1 + (1 - p.1 - p.2)) :=
    (measurable_const.mul measurable_snd).div
      (measurable_fst.add ((measurable_const.sub measurable_fst).sub measurable_snd))
  exact _root_.GD.N0106.N0428.N0765.N1542.d005435.mul (((h1.sub measurable_const).pow_const 2).sub
    ((h2.sub measurable_const).pow_const 2))

theorem d005971 : Measurable (Function.uncurry _root_.GD.N0106.N0428.N0765.N1664.d005967) := by
  unfold _root_.GD.N0106.N0428.N0765.N1664.d005967
  refine (Real.continuous_sqrt.measurable.comp measurable_fst).mul ?_
  exact (measurable_const.mul ((measurable_snd.pow_const 6).mul
      (((measurable_const.sub measurable_fst).sub measurable_snd).pow_const 2))).add
    (measurable_const.mul ((measurable_snd.pow_const 4).mul
      (((measurable_const.sub measurable_fst).sub measurable_snd).pow_const 4)))



theorem d005972 {u v : ℝ} (hu : 0 ≤ u) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1664.d005967 u v := by
  unfold _root_.GD.N0106.N0428.N0765.N1664.d005967
  have := Real.sqrt_nonneg u
  positivity

theorem d005973 {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420) : _root_.GD.N0106.N0428.N0765.N1664.d005967 p.1 p.2 ≤ 6 := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  unfold _root_.GD.N0106.N0428.N0765.N1664.d005967
  have hw0 : 0 ≤ 1 - p.1 - p.2 := by linarith
  have hw1 : 1 - p.1 - p.2 ≤ 1 := by linarith
  have hs : Real.sqrt p.1 ≤ 1 := Real.sqrt_le_one.mpr h2
  have hv1 : p.2 ≤ 1 := by linarith
  have a1 : p.2 ^ 6 * (1 - p.1 - p.2) ^ 2 ≤ 1 := by
    have := pow_le_one₀ h3.le hv1 (n := 6)
    have := pow_le_one₀ hw0 hw1 (n := 2)
    nlinarith [pow_nonneg h3.le 6, pow_nonneg hw0 2]
  have a2 : p.2 ^ 4 * (1 - p.1 - p.2) ^ 4 ≤ 1 := by
    have := pow_le_one₀ h3.le hv1 (n := 4)
    have := pow_le_one₀ hw0 hw1 (n := 4)
    nlinarith [pow_nonneg h3.le 4, pow_nonneg hw0 4]
  have hb : 13 / 4 * (p.2 ^ 6 * (1 - p.1 - p.2) ^ 2) + 2 * (p.2 ^ 4 * (1 - p.1 - p.2) ^ 4) ≤ 6 := by
    nlinarith
  have hb0 : 0 ≤ 13 / 4 * (p.2 ^ 6 * (1 - p.1 - p.2) ^ 2) + 2 * (p.2 ^ 4 * (1 - p.1 - p.2) ^ 4) := by
    positivity
  calc Real.sqrt p.1 * (13 / 4 * (p.2 ^ 6 * (1 - p.1 - p.2) ^ 2) + 2 * (p.2 ^ 4 * (1 - p.1 - p.2) ^ 4))
      ≤ 1 * 6 := mul_le_mul hs hb hb0 zero_le_one
    _ = 6 := by ring

theorem d005974 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a - b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
  nlinarith [mul_nonneg ha hb]


theorem d005975 {e : ℝ} (he : 0 < e) {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420) :
    |_root_.GD.N0106.N0428.N0765.N1664.d005965 e p.1 p.2| ≤ _root_.GD.N0106.N0428.N0765.N1664.d005967 p.1 p.2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  set u := p.1
  set v := p.2
  have hw0 : 0 ≤ 1 - u - v := by linarith
  rcases eq_or_lt_of_le hw0 with hw | hw
  ·
    unfold _root_.GD.N0106.N0428.N0765.N1664.d005965 _root_.GD.N0106.N0428.N0765.N1664.d005967
    rw [← hw, _root_.GD.N0106.N0428.N0765.N1543.d005388]
    simp
  · have hor0 : 0 ≤ _root_.GD.N0106.N0428.N0765.N1543.d005392 e := by unfold _root_.GD.N0106.N0428.N0765.N1543.d005392; positivity
    have hor1 : _root_.GD.N0106.N0428.N0765.N1543.d005392 e ≤ 1 := by
      unfold _root_.GD.N0106.N0428.N0765.N1543.d005392
      rw [div_le_one (by linarith)]
      linarith
    have hden : 0 < e * v + (1 - u - v) := by positivity
    have hq0 : 0 ≤ v / (e * v + (1 - u - v)) := div_nonneg h3.le hden.le
    have hq1 : v / (e * v + (1 - u - v)) ≤ v / (1 - u - v) :=
      div_le_div_of_nonneg_left h3.le hw (by nlinarith)
    have hH0 : 0 ≤ e⁻¹ * _root_.GD.N0106.N0428.N0765.N1664.d005963 e u v := by
      rw [_root_.GD.N0106.N0428.N0765.N1664.d005964 he h1.le]
      exact mul_nonneg (inv_nonneg.mpr he.le)
        (_root_.GD.N0106.N0428.N0765.N1534.d005345 (inv_pos.mpr he) h1.le h3 hw).1.le
    have hH1 : e⁻¹ * _root_.GD.N0106.N0428.N0765.N1664.d005963 e u v ≤ 3 / 2 * (v / (1 - u - v)) := by
      rw [_root_.GD.N0106.N0428.N0765.N1664.d005964 he h1.le]
      have h := _root_.GD.N0106.N0428.N0765.N1681.d005962 (inv_pos.mpr he) h1.le h3 hw
      rw [inv_inv] at h
      refine h.trans (mul_le_mul_of_nonneg_left hq1 (by norm_num))
    have hx0 : 0 ≤ v / (1 - u - v) := div_nonneg h3.le hw.le
    have hg : |(v / (e * v + (1 - u - v)) - _root_.GD.N0106.N0428.N0765.N1543.d005392 e) ^ 2 - (e⁻¹ * _root_.GD.N0106.N0428.N0765.N1664.d005963 e u v - _root_.GD.N0106.N0428.N0765.N1543.d005392 e) ^ 2| ≤
        13 / 4 * (v / (1 - u - v)) ^ 2 + 2 := by
      have e1 := _root_.GD.N0106.N0428.N0765.N1664.d005974 hq0 hor0
      have e2 := _root_.GD.N0106.N0428.N0765.N1664.d005974 hH0 hor0
      have e3 : (v / (e * v + (1 - u - v))) ^ 2 ≤ (v / (1 - u - v)) ^ 2 := by
        exact pow_le_pow_left₀ hq0 hq1 2
      have e4 : (e⁻¹ * _root_.GD.N0106.N0428.N0765.N1664.d005963 e u v) ^ 2 ≤ (3 / 2 * (v / (1 - u - v))) ^ 2 := by
        exact pow_le_pow_left₀ hH0 hH1 2
      have e5 : _root_.GD.N0106.N0428.N0765.N1543.d005392 e ^ 2 ≤ 1 := pow_le_one₀ hor0 hor1
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (v / (e * v + (1 - u - v)) - _root_.GD.N0106.N0428.N0765.N1543.d005392 e),
        sq_nonneg (e⁻¹ * _root_.GD.N0106.N0428.N0765.N1664.d005963 e u v - _root_.GD.N0106.N0428.N0765.N1543.d005392 e)]
    have hd0 : 0 ≤ _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) := by
      unfold _root_.GD.N0106.N0428.N0765.N1543.d005383
      have := Real.sqrt_nonneg u
      positivity
    unfold _root_.GD.N0106.N0428.N0765.N1664.d005965
    rw [abs_mul, abs_of_nonneg hd0]
    calc _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) *
          |(v / (e * v + (1 - u - v)) - _root_.GD.N0106.N0428.N0765.N1543.d005392 e) ^ 2 - (e⁻¹ * _root_.GD.N0106.N0428.N0765.N1664.d005963 e u v - _root_.GD.N0106.N0428.N0765.N1543.d005392 e) ^ 2|
        ≤ _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * (13 / 4 * (v / (1 - u - v)) ^ 2 + 2) :=
          mul_le_mul_of_nonneg_left hg hd0
      _ = _root_.GD.N0106.N0428.N0765.N1664.d005967 u v := by
          unfold _root_.GD.N0106.N0428.N0765.N1543.d005383 _root_.GD.N0106.N0428.N0765.N1664.d005967
          field_simp



theorem d005976 {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420) :
    Tendsto (fun e => _root_.GD.N0106.N0428.N0765.N1664.d005965 e p.1 p.2) (𝓝[>] 0) (𝓝 (_root_.GD.N0106.N0428.N0765.N1664.d005966 p.1 p.2)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  set u := p.1
  set v := p.2
  have hw0 : 0 ≤ 1 - u - v := by linarith
  rcases eq_or_lt_of_le hw0 with hw | hw
  · have hz : ∀ e, _root_.GD.N0106.N0428.N0765.N1664.d005965 e u v = 0 := by
      intro e; unfold _root_.GD.N0106.N0428.N0765.N1664.d005965; rw [← hw, _root_.GD.N0106.N0428.N0765.N1543.d005388, zero_mul]
    have hz0 : _root_.GD.N0106.N0428.N0765.N1664.d005966 u v = 0 := by unfold _root_.GD.N0106.N0428.N0765.N1664.d005966; rw [← hw, _root_.GD.N0106.N0428.N0765.N1543.d005388, zero_mul]
    simp only [hz, hz0]
    exact tendsto_const_nhds
  · have hcont1 : ContinuousAt (fun e : ℝ => v / (e * v + (1 - u - v))) 0 := by
      apply ContinuousAt.div continuousAt_const (by fun_prop)
      simp only [zero_mul, zero_add]
      exact hw.ne'
    have hq : Tendsto (fun e : ℝ => v / (e * v + (1 - u - v))) (𝓝[>] 0)
        (𝓝 (v / (1 - u - v))) := by
      have := hcont1.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    have hor : Tendsto (fun e : ℝ => _root_.GD.N0106.N0428.N0765.N1543.d005392 e) (𝓝[>] 0) (𝓝 1) := by
      have hc : ContinuousAt (fun e : ℝ => 1 / (1 + e)) 0 := by
        apply ContinuousAt.div continuousAt_const (by fun_prop)
        norm_num
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      unfold _root_.GD.N0106.N0428.N0765.N1543.d005392
      simpa using this
    have hH : Tendsto (fun e : ℝ => e⁻¹ * _root_.GD.N0106.N0428.N0765.N1664.d005963 e u v) (𝓝[>] 0)
        (𝓝 (11 / 8 * v / (u + (1 - u - v)))) := by
      have h := (_root_.GD.N0106.N0428.N0765.N1673.d005866 h1.le h3 hw).comp tendsto_inv_nhdsGT_zero
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with e he
      simp only [Function.comp_def]
      rw [_root_.GD.N0106.N0428.N0765.N1664.d005964 he h1.le]
    have := (((hq.sub hor).pow 2).sub ((hH.sub hor).pow 2)).const_mul (_root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v))
    exact this



theorem d005977 (F : ℝ → ℝ → ℝ) (hF : Measurable (Function.uncurry F)) {C : ℝ}
    (hC : ∀ p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420, |Function.uncurry F p| ≤ C) :
    (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..(1 - u), F u v) =
      ∫ p, _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry F) p := by
  rw [_root_.GD.N0106.N0428.N0765.N1542.d005425]
  have hint : Integrable (_root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry F)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod, integrable_indicator_iff _root_.GD.N0106.N0428.N0765.N1542.d005421]
    refine Integrable.mono' (integrableOn_const (C := C) (hs := _root_.GD.N0106.N0428.N0765.N1542.d005423))
      hF.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem _root_.GD.N0106.N0428.N0765.N1542.d005421] with p hp
    rw [Real.norm_eq_abs]
    exact hC p hp
  exact (integral_prod _ hint).symm

theorem d005978 :
    Tendsto (fun e => ∫ p, _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry (_root_.GD.N0106.N0428.N0765.N1664.d005965 e)) p) (𝓝[>] 0)
      (𝓝 (∫ p, _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry _root_.GD.N0106.N0428.N0765.N1664.d005966) p)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun p => _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry _root_.GD.N0106.N0428.N0765.N1664.d005967) p) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun e =>
      ((_root_.GD.N0106.N0428.N0765.N1664.d005969 e).indicator _root_.GD.N0106.N0428.N0765.N1542.d005421).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with e he
    refine Eventually.of_forall fun p => ?_
    by_cases hp : p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420
    · rw [indicator_of_mem hp, indicator_of_mem hp, Real.norm_eq_abs]
      exact _root_.GD.N0106.N0428.N0765.N1664.d005975 he hp
    · rw [indicator_of_notMem hp, indicator_of_notMem hp, norm_zero]
  · rw [integrable_indicator_iff _root_.GD.N0106.N0428.N0765.N1542.d005421]
    refine Integrable.mono' (integrableOn_const (C := 6) (hs := _root_.GD.N0106.N0428.N0765.N1542.d005423))
      _root_.GD.N0106.N0428.N0765.N1664.d005971.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem _root_.GD.N0106.N0428.N0765.N1542.d005421] with p hp
    rw [Real.norm_eq_abs]
    show |_root_.GD.N0106.N0428.N0765.N1664.d005967 p.1 p.2| ≤ 6
    rw [abs_of_nonneg (_root_.GD.N0106.N0428.N0765.N1664.d005972 hp.1.le)]
    exact _root_.GD.N0106.N0428.N0765.N1664.d005973 hp
  · refine Eventually.of_forall fun p => ?_
    by_cases hp : p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420
    · simp only [indicator_of_mem hp]
      exact _root_.GD.N0106.N0428.N0765.N1664.d005976 hp
    · simp only [indicator_of_notMem hp]
      exact tendsto_const_nhds




def d005979 (u v : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * (v / (1 - u - v) - 1) ^ 2


def d005980 (u v : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * (11 / 8 * v / (u + (1 - u - v)) - 1) ^ 2

theorem d005981 : Measurable (Function.uncurry _root_.GD.N0106.N0428.N0765.N1664.d005979) :=
  _root_.GD.N0106.N0428.N0765.N1542.d005435.mul (((measurable_snd.div
    ((measurable_const.sub measurable_fst).sub measurable_snd)).sub measurable_const).pow_const 2)

theorem d005982 : Measurable (Function.uncurry _root_.GD.N0106.N0428.N0765.N1664.d005980) :=
  _root_.GD.N0106.N0428.N0765.N1542.d005435.mul ((((measurable_const.mul measurable_snd).div
    (measurable_fst.add ((measurable_const.sub measurable_fst).sub measurable_snd))).sub
      measurable_const).pow_const 2)

theorem d005983 {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420) : |Function.uncurry _root_.GD.N0106.N0428.N0765.N1664.d005979 p| ≤ 6 := by
  have hP := _root_.GD.N0106.N0428.N0765.N1664.d005975 one_pos hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  show |_root_.GD.N0106.N0428.N0765.N1543.d005383 p.1 p.2 (1 - p.1 - p.2) * (p.2 / (1 - p.1 - p.2) - 1) ^ 2| ≤ 6
  have hw0 : 0 ≤ 1 - p.1 - p.2 := by linarith
  rcases eq_or_lt_of_le hw0 with hw | hw
  · rw [← hw, _root_.GD.N0106.N0428.N0765.N1543.d005388]; simp
  · have hd0 : 0 ≤ _root_.GD.N0106.N0428.N0765.N1543.d005383 p.1 p.2 (1 - p.1 - p.2) := by
      unfold _root_.GD.N0106.N0428.N0765.N1543.d005383; have := Real.sqrt_nonneg p.1; positivity
    have hx0 : 0 ≤ p.2 / (1 - p.1 - p.2) := div_nonneg h3.le hw.le
    have hsq := _root_.GD.N0106.N0428.N0765.N1664.d005974 hx0 zero_le_one
    rw [abs_of_nonneg (mul_nonneg hd0 (sq_nonneg _))]
    calc _root_.GD.N0106.N0428.N0765.N1543.d005383 p.1 p.2 (1 - p.1 - p.2) * (p.2 / (1 - p.1 - p.2) - 1) ^ 2
        ≤ _root_.GD.N0106.N0428.N0765.N1543.d005383 p.1 p.2 (1 - p.1 - p.2) * (13 / 4 * (p.2 / (1 - p.1 - p.2)) ^ 2 + 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hd0
          nlinarith [sq_nonneg (p.2 / (1 - p.1 - p.2))]
      _ = _root_.GD.N0106.N0428.N0765.N1664.d005967 p.1 p.2 := by unfold _root_.GD.N0106.N0428.N0765.N1543.d005383 _root_.GD.N0106.N0428.N0765.N1664.d005967; field_simp
      _ ≤ 6 := _root_.GD.N0106.N0428.N0765.N1664.d005973 ⟨h1, h2, h3, h4⟩

theorem d005984 {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420) : |Function.uncurry _root_.GD.N0106.N0428.N0765.N1664.d005980 p| ≤ 6 := by
  show |_root_.GD.N0106.N0428.N0765.N1543.d005383 p.1 p.2 (1 - p.1 - p.2) * (11 / 8 * p.2 / (p.1 + (1 - p.1 - p.2)) - 1) ^ 2| ≤ 6
  rw [show p.1 + (1 - p.1 - p.2) = 1 - p.2 by ring]
  exact _root_.GD.N0106.N0428.N0765.N1542.d005443 hp

theorem d005985 : (∫ p, _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry _root_.GD.N0106.N0428.N0765.N1664.d005966) p) = _root_.GD.N0106.N0428.N0765.N1543.d005384 * (5 / 24) := by
  have hF0 : _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry _root_.GD.N0106.N0428.N0765.N1664.d005966) =
      _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry _root_.GD.N0106.N0428.N0765.N1664.d005979) - _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry _root_.GD.N0106.N0428.N0765.N1664.d005980) := by
    funext p
    simp only [Pi.sub_apply]
    by_cases hp : p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420
    · simp only [indicator_of_mem hp]
      show _root_.GD.N0106.N0428.N0765.N1664.d005966 p.1 p.2 = _root_.GD.N0106.N0428.N0765.N1664.d005979 p.1 p.2 - _root_.GD.N0106.N0428.N0765.N1664.d005980 p.1 p.2
      unfold _root_.GD.N0106.N0428.N0765.N1664.d005966 _root_.GD.N0106.N0428.N0765.N1664.d005979 _root_.GD.N0106.N0428.N0765.N1664.d005980
      ring
    · simp only [indicator_of_notMem hp, sub_zero]
  have hint : ∀ (G : ℝ → ℝ → ℝ), Measurable (Function.uncurry G) →
      (∀ p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420, |Function.uncurry G p| ≤ 6) → Integrable (_root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry G)) := by
    intro G hG hC
    rw [integrable_indicator_iff _root_.GD.N0106.N0428.N0765.N1542.d005421]
    refine Integrable.mono' (integrableOn_const (C := 6) (hs := _root_.GD.N0106.N0428.N0765.N1542.d005423))
      hG.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem _root_.GD.N0106.N0428.N0765.N1542.d005421] with p hp
    rw [Real.norm_eq_abs]
    exact hC p hp
  rw [hF0]
  simp only [Pi.sub_apply]
  rw [integral_sub (hint _root_.GD.N0106.N0428.N0765.N1664.d005979 _root_.GD.N0106.N0428.N0765.N1664.d005981 fun p hp => _root_.GD.N0106.N0428.N0765.N1664.d005983 hp) (hint _root_.GD.N0106.N0428.N0765.N1664.d005980 _root_.GD.N0106.N0428.N0765.N1664.d005982 fun p hp => _root_.GD.N0106.N0428.N0765.N1664.d005984 hp),
    ← _root_.GD.N0106.N0428.N0765.N1664.d005977 _root_.GD.N0106.N0428.N0765.N1664.d005979 _root_.GD.N0106.N0428.N0765.N1664.d005981 (fun p hp => _root_.GD.N0106.N0428.N0765.N1664.d005983 hp),
    ← _root_.GD.N0106.N0428.N0765.N1664.d005977 _root_.GD.N0106.N0428.N0765.N1664.d005980 _root_.GD.N0106.N0428.N0765.N1664.d005982 (fun p hp => _root_.GD.N0106.N0428.N0765.N1664.d005984 hp)]
  have e1 : (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..(1 - u), _root_.GD.N0106.N0428.N0765.N1664.d005979 u v) =
      _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun _ v w => (v / w - 1) ^ 2) * _root_.GD.N0106.N0428.N0765.N1543.d005384 := by
    unfold _root_.GD.N0106.N0428.N0765.N1543.d005385
    rw [div_mul_cancel₀ _ _root_.GD.N0106.N0428.N0765.N1542.d005440.ne']
    rfl
  have e2 : (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..(1 - u), _root_.GD.N0106.N0428.N0765.N1664.d005980 u v) =
      _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w => (11 / 8 * v / (u + w) - 1) ^ 2) * _root_.GD.N0106.N0428.N0765.N1543.d005384 := by
    unfold _root_.GD.N0106.N0428.N0765.N1543.d005385
    rw [div_mul_cancel₀ _ _root_.GD.N0106.N0428.N0765.N1542.d005440.ne']
    rfl
  rw [e1, e2, _root_.GD.N0106.N0428.N0765.N1542.d005442, _root_.GD.N0106.N0428.N0765.N1542.d005446]
  ring




theorem d005986 {e : ℝ} (he : 0 < e) :
    _root_.GD.N0106.N0428.N0765.N1543.d005396 e = _root_.GD.N0106.N0428.N0765.N1534.d005331 e * ((∫ p, _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry (_root_.GD.N0106.N0428.N0765.N1664.d005965 e)) p) / _root_.GD.N0106.N0428.N0765.N1543.d005384) := by
  rw [_root_.GD.N0106.N0428.N0765.N1543.d005402 he]
  congr 1
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005385
  congr 1
  rw [← _root_.GD.N0106.N0428.N0765.N1664.d005977 (_root_.GD.N0106.N0428.N0765.N1664.d005965 e) (_root_.GD.N0106.N0428.N0765.N1664.d005969 e) (fun p hp => (_root_.GD.N0106.N0428.N0765.N1664.d005975 he hp).trans (_root_.GD.N0106.N0428.N0765.N1664.d005973 hp))]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le zero_le_one] at hu
  refine intervalIntegral.integral_congr fun v _ => ?_
  beta_reduce
  unfold _root_.GD.N0106.N0428.N0765.N1664.d005965
  rw [_root_.GD.N0106.N0428.N0765.N1664.d005964 he hu.1]


theorem d005987 : Tendsto _root_.GD.N0106.N0428.N0765.N1543.d005396 (𝓝[>] 0) (𝓝 (5 / 264)) := by
  have hV : Tendsto (fun e : ℝ => _root_.GD.N0106.N0428.N0765.N1534.d005331 e) (𝓝[>] 0) (𝓝 (1 / 11)) := by
    have hc : Continuous fun e : ℝ => _root_.GD.N0106.N0428.N0765.N1534.d005331 e := by unfold _root_.GD.N0106.N0428.N0765.N1534.d005331; fun_prop
    have := (hc.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [_root_.GD.N0106.N0428.N0765.N1534.d005331] using this
  have h := hV.mul (_root_.GD.N0106.N0428.N0765.N1664.d005978.div_const _root_.GD.N0106.N0428.N0765.N1543.d005384)
  rw [_root_.GD.N0106.N0428.N0765.N1664.d005985, mul_div_cancel_left₀ _ _root_.GD.N0106.N0428.N0765.N1542.d005440.ne',
    show (1 / 11 : ℝ) * (5 / 24) = 5 / 264 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with e he
  exact (_root_.GD.N0106.N0428.N0765.N1664.d005986 he).symm

end

end GD.N0106.N0428.N0765.N1664
