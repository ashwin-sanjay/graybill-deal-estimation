import GD.Module0852
import Mathlib.MeasureTheory.Integral.DominatedConvergence














open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

namespace GD.N0232.N0720.N1309

open _root_.GD.N0232.N0720.N1310

noncomputable section

def d013069 (epsilon : ℝ) : ℝ := epsilon / (1 + epsilon)

def d013070 (alpha beta epsilon : ℝ) : ℝ :=
  ∫ u : ℝ, (_root_.GD.N0232.N0720.N1310.d013058 epsilon (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 epsilon) ^ 2
    ∂betaMeasure alpha beta

def d013071 (alpha beta epsilon : ℝ) : ℝ :=
  ∫ u : ℝ, (_root_.GD.N0232.N0720.N1310.d013059 (beta / alpha) epsilon (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 epsilon) ^ 2
    ∂betaMeasure alpha beta

theorem d013072 (alpha beta : ℝ) :
    ∀ᵐ u ∂betaMeasure alpha beta, u ∈ Ioo (0 : ℝ) 1 := by
  unfold betaMeasure betaPDF
  rw [ae_withDensity_iff ((measurable_betaPDFReal alpha beta).ennreal_ofReal)]
  filter_upwards with u
  intro hu
  by_contra hnot
  have hout : ¬ (0 < u ∧ u < 1) := hnot
  simp [betaPDFReal, hout] at hu

theorem d013073 {epsilon : ℝ} (he : 0 < epsilon) (g : ℝ) :
    (g - _root_.GD.N0232.N0720.N1309.d013069 epsilon) ^ 2 / epsilon =
      g ^ 2 / epsilon - 2 * (g / (1 + epsilon)) + epsilon / (1 + epsilon) ^ 2 := by
  have hd : 1 + epsilon ≠ 0 := ne_of_gt (by linarith)
  unfold _root_.GD.N0232.N0720.N1309.d013069
  field_simp [he.ne', hd]
  ring

theorem d013074 {epsilon : ℝ} (he : 0 ≤ epsilon) :
    _root_.GD.N0232.N0720.N1309.d013069 epsilon ^ 2 ≤ epsilon := by
  have hd : 0 < 1 + epsilon := by linarith
  have hsq : epsilon ≤ (1 + epsilon) ^ 2 := by nlinarith [sq_nonneg epsilon]
  unfold _root_.GD.N0232.N0720.N1309.d013069
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hd)).2
  nlinarith [mul_le_mul_of_nonneg_left hsq he]

theorem d013075 {epsilon g H : ℝ} (he : 0 < epsilon)
    (hsecond : g ^ 2 / epsilon ≤ H) :
    (g - _root_.GD.N0232.N0720.N1309.d013069 epsilon) ^ 2 / epsilon ≤ 2 * H + 2 := by
  have hs := (div_le_iff₀ he).1 hsecond
  have ht := _root_.GD.N0232.N0720.N1309.d013074 he.le
  apply (div_le_iff₀ he).2
  nlinarith [sq_nonneg (g + _root_.GD.N0232.N0720.N1309.d013069 epsilon)]

private theorem d013076 {epsilon g : ℕ → ℝ} {L : ℝ}
    (he : Tendsto epsilon atTop (𝓝 0)) (hepos : ∀ n, 0 < epsilon n)
    (hg : Tendsto g atTop (𝓝 0))
    (hsq : Tendsto (fun n ↦ g n ^ 2 / epsilon n) atTop (𝓝 L)) :
    Tendsto (fun n ↦ (g n - _root_.GD.N0232.N0720.N1309.d013069 (epsilon n)) ^ 2 / epsilon n)
      atTop (𝓝 L) := by
  have hd : Tendsto (fun n ↦ 1 + epsilon n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add he
  have hcross : Tendsto (fun n ↦ 2 * (g n / (1 + epsilon n))) atTop (𝓝 0) := by
    simpa using (hg.div hd (by norm_num)).const_mul 2
  have ht : Tendsto (fun n ↦ epsilon n / (1 + epsilon n) ^ 2) atTop (𝓝 0) := by
    simpa using! he.div (hd.pow 2) (by norm_num)
  have hsum : Tendsto
      (fun n ↦ g n ^ 2 / epsilon n - 2 * (g n / (1 + epsilon n)) +
        epsilon n / (1 + epsilon n) ^ 2) atTop (𝓝 L) := by
    simpa using (hsq.sub hcross).add ht
  exact Filter.Tendsto.congr'
    (Eventually.of_forall fun n ↦ (_root_.GD.N0232.N0720.N1309.d013073 (hepos n) (g n)).symm) hsum

theorem d013077 {epsilon : ℕ → ℝ}
    (he : Tendsto epsilon atTop (𝓝 0)) (hepos : ∀ n, 0 < epsilon n)
    {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun n ↦ (_root_.GD.N0232.N0720.N1310.d013058 (epsilon n) r - _root_.GD.N0232.N0720.N1309.d013069 (epsilon n)) ^ 2 / epsilon n)
      atTop (𝓝 r) := by
  have hp : Tendsto (fun n ↦ epsilon n * r) atTop (𝓝 0) := by
    simpa using he.mul_const r
  have hs : Tendsto (fun n ↦ Real.sqrt (epsilon n * r)) atTop (𝓝 0) := by
    simpa using! (Real.continuous_sqrt.tendsto 0).comp hp
  have hd : Tendsto (fun n ↦ 1 + Real.sqrt (epsilon n * r)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hs
  have hg : Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1310.d013058 (epsilon n) r) atTop (𝓝 0) := by
    simpa only [_root_.GD.N0232.N0720.N1310.d013058, zero_div] using! hs.div hd (by norm_num)
  have hnorm : Tendsto (fun n ↦ r / (1 + Real.sqrt (epsilon n * r)) ^ 2)
      atTop (𝓝 r) := by
    simpa using! (tendsto_const_nhds (x := r)).div (hd.pow 2) (by norm_num)
  have hsq : Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1310.d013058 (epsilon n) r ^ 2 / epsilon n) atTop (𝓝 r) :=
    Filter.Tendsto.congr'
      (Eventually.of_forall fun n ↦ (_root_.GD.N0232.N0720.N1310.d013060 (hepos n) hr).symm) hnorm
  exact _root_.GD.N0232.N0720.N1309.d013076 he hepos hg hsq

theorem d013078 {epsilon : ℕ → ℝ}
    (he : Tendsto epsilon atTop (𝓝 0)) (hepos : ∀ n, 0 < epsilon n)
    {k r : ℝ} (hk : 0 ≤ k) (hr : 0 ≤ r) :
    Tendsto (fun n ↦ (_root_.GD.N0232.N0720.N1310.d013059 k (epsilon n) r - _root_.GD.N0232.N0720.N1309.d013069 (epsilon n)) ^ 2 / epsilon n)
      atTop (𝓝 0) := by
  have hp : Tendsto (fun n ↦ k * epsilon n * r) atTop (𝓝 0) := by
    simpa using (he.const_mul k).mul_const r
  have hd : Tendsto (fun n ↦ 1 + k * epsilon n * r) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hp
  have hg : Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1310.d013059 k (epsilon n) r) atTop (𝓝 0) := by
    simpa only [_root_.GD.N0232.N0720.N1310.d013059, zero_div] using! hp.div hd (by norm_num)
  have hn : Tendsto (fun n ↦ k ^ 2 * epsilon n * r ^ 2) atTop (𝓝 0) := by
    simpa using (he.const_mul (k ^ 2)).mul_const (r ^ 2)
  have hnorm : Tendsto (fun n ↦ k ^ 2 * epsilon n * r ^ 2 / (1 + k * epsilon n * r) ^ 2)
      atTop (𝓝 0) := by
    simpa using! hn.div (hd.pow 2) (by norm_num)
  have hsq : Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1310.d013059 k (epsilon n) r ^ 2 / epsilon n) atTop (𝓝 0) :=
    Filter.Tendsto.congr'
      (Eventually.of_forall fun n ↦ (_root_.GD.N0232.N0720.N1310.d013062 hk (hepos n) hr).symm) hnorm
  exact _root_.GD.N0232.N0720.N1309.d013076 he hepos hg hsq


theorem d013079 {alpha beta : ℝ} (ha : 0 < alpha) (hb : 1 < beta)
    {epsilon : ℕ → ℝ} (he : Tendsto epsilon atTop (𝓝 0)) (hepos : ∀ n, 0 < epsilon n) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1309.d013070 alpha beta (epsilon n) / epsilon n)
      atTop (𝓝 (alpha / (beta - 1))) := by
  letI : IsProbabilityMeasure (betaMeasure alpha beta) :=
    isProbabilityMeasureBeta ha (lt_trans zero_lt_one hb)
  have hlim : Tendsto (fun n ↦ ∫ u : ℝ,
      (_root_.GD.N0232.N0720.N1310.d013058 (epsilon n) (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 (epsilon n)) ^ 2 / epsilon n
        ∂betaMeasure alpha beta)
      atTop (𝓝 (∫ u : ℝ, u / (1 - u) ∂betaMeasure alpha beta)) := by
    apply tendsto_integral_of_dominated_convergence (fun u : ℝ ↦ 2 * (u / (1 - u)) + 2)
    · intro n
      have hm : Measurable (fun u : ℝ ↦
          (_root_.GD.N0232.N0720.N1310.d013058 (epsilon n) (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 (epsilon n)) ^ 2 / epsilon n) := by
        unfold _root_.GD.N0232.N0720.N1310.d013058 _root_.GD.N0232.N0720.N1309.d013069
        fun_prop
      exact hm.aestronglyMeasurable
    · exact ((_root_.GD.N0232.N0720.N1310.d013067 ha hb).const_mul 2).add (integrable_const 2)
    · intro n
      filter_upwards [_root_.GD.N0232.N0720.N1309.d013072 alpha beta] with u hu
      have hr : 0 ≤ u / (1 - u) := div_nonneg hu.1.le (sub_pos.mpr hu.2).le
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (hepos n).le)]
      exact _root_.GD.N0232.N0720.N1309.d013075 (hepos n) (_root_.GD.N0232.N0720.N1310.d013061 (hepos n) hr)
    · filter_upwards [_root_.GD.N0232.N0720.N1309.d013072 alpha beta] with u hu
      exact _root_.GD.N0232.N0720.N1309.d013077 he hepos
        (div_nonneg hu.1.le (sub_pos.mpr hu.2).le)
  simp_rw [integral_div] at hlim
  rw [_root_.GD.N0232.N0720.N1310.d013068 ha hb] at hlim
  exact hlim


theorem d013080 {alpha beta : ℝ} (ha : 0 < alpha) (hb : 1 < beta)
    {epsilon : ℕ → ℝ} (he : Tendsto epsilon atTop (𝓝 0)) (hepos : ∀ n, 0 < epsilon n) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1309.d013071 alpha beta (epsilon n) / epsilon n) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (betaMeasure alpha beta) :=
    isProbabilityMeasureBeta ha (lt_trans zero_lt_one hb)
  have hk : 0 ≤ beta / alpha := (div_pos (lt_trans zero_lt_one hb) ha).le
  have hlim : Tendsto (fun n ↦ ∫ u : ℝ,
      (_root_.GD.N0232.N0720.N1310.d013059 (beta / alpha) (epsilon n) (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 (epsilon n)) ^ 2 / epsilon n
        ∂betaMeasure alpha beta)
      atTop (𝓝 (∫ _u : ℝ, (0 : ℝ) ∂betaMeasure alpha beta)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun u : ℝ ↦ 2 * ((beta / alpha) * (u / (1 - u))) + 2)
    · intro n
      have hm : Measurable (fun u : ℝ ↦
          (_root_.GD.N0232.N0720.N1310.d013059 (beta / alpha) (epsilon n) (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 (epsilon n)) ^ 2 /
            epsilon n) := by
        unfold _root_.GD.N0232.N0720.N1310.d013059 _root_.GD.N0232.N0720.N1309.d013069
        fun_prop
      exact hm.aestronglyMeasurable
    · exact (((_root_.GD.N0232.N0720.N1310.d013067 ha hb).const_mul (beta / alpha)).const_mul 2).add
        (integrable_const 2)
    · intro n
      filter_upwards [_root_.GD.N0232.N0720.N1309.d013072 alpha beta] with u hu
      have hr : 0 ≤ u / (1 - u) := div_nonneg hu.1.le (sub_pos.mpr hu.2).le
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (hepos n).le)]
      exact _root_.GD.N0232.N0720.N1309.d013075 (hepos n) (_root_.GD.N0232.N0720.N1310.d013064 hk (hepos n) hr)
    · filter_upwards [_root_.GD.N0232.N0720.N1309.d013072 alpha beta] with u hu
      exact _root_.GD.N0232.N0720.N1309.d013078 he hepos hk
        (div_nonneg hu.1.le (sub_pos.mpr hu.2).le)
  simp_rw [integral_div] at hlim
  simpa only [_root_.GD.N0232.N0720.N1309.d013071, integral_zero] using! hlim

theorem d013081 {alpha beta : ℝ} (ha : 0 < alpha) (hb : 1 < beta)
    {epsilon : ℕ → ℝ} (he : Tendsto epsilon atTop (𝓝 0)) (hepos : ∀ n, 0 < epsilon n) :
    ∀ᶠ n in atTop, _root_.GD.N0232.N0720.N1309.d013071 alpha beta (epsilon n) < _root_.GD.N0232.N0720.N1309.d013070 alpha beta (epsilon n) := by
  have hgap := (_root_.GD.N0232.N0720.N1309.d013079 ha hb he hepos).sub
    (_root_.GD.N0232.N0720.N1309.d013080 ha hb he hepos)
  have hpos : 0 < alpha / (beta - 1) - 0 := by
    simpa using div_pos ha (sub_pos.mpr hb)
  filter_upwards [(tendsto_order.1 hgap).1 0 hpos] with n hn
  exact (div_lt_div_iff_of_pos_right (hepos n)).1 (sub_pos.mp hn)



theorem d013082 {alpha beta : ℝ} (ha : 0 < alpha) (hb : 1 < beta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ _root_.GD.N0232.N0720.N1309.d013071 alpha beta epsilon < _root_.GD.N0232.N0720.N1309.d013070 alpha beta epsilon := by
  let epsilon : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have he : Tendsto epsilon atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hepos (n : ℕ) : 0 < epsilon n := by unfold epsilon; positivity
  obtain ⟨n, hn⟩ := (_root_.GD.N0232.N0720.N1309.d013081 ha hb he hepos).exists
  exact ⟨epsilon n, hepos n, hn⟩

end
end GD.N0232.N0720.N1309

#print axioms _root_.GD.N0232.N0720.N1309.d013079
#print axioms _root_.GD.N0232.N0720.N1309.d013080
#print axioms _root_.GD.N0232.N0720.N1309.d013082
