import GD.Module0854

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

namespace GD.N0207.N0453
noncomputable section

open _root_.GD.N0232.N0720.N1310
open _root_.GD.N0232.N0720.N1309
open _root_.GD.N0232.N0720.N1313
open _root_.GD.N0232.N0720.N1091

theorem d023512 {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∃ e : ℝ, 0 < e ∧ C * e < _root_.GD.N0232.N0720.N1309.d013070 a 1 e := by
  let L : ℝ := (a + 1) * (|C| + 1) + a
  have hL : 0 < L := by dsimp [L]; positivity
  have haL : a < L := by
    dsimp [L]
    have : 0 < (a + 1) * (|C| + 1) := by positivity
    linarith
  let b : ℝ := 1 + a / L
  have hb : 1 < b := by dsimp [b]; linarith [div_pos ha hL]
  have hb2 : b ≤ 2 := by
    dsimp [b]
    have : a / L ≤ 1 := (div_le_one hL).2 haL.le
    linarith
  let e : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hepos (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have hlim := _root_.GD.N0232.N0720.N1309.d013079 ha hb he hepos
  have hvalue : a / (b - 1) = L := by
    dsimp [b]
    field_simp [ha.ne', hL.ne']
    ring
  rw [hvalue] at hlim
  have hCL : (a + 1) * C < L := by
    dsimp [L]
    have hC : C ≤ |C| := le_abs_self C
    nlinarith
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).1 ((a + 1) * C) hCL).exists
  have hbound := _root_.GD.N0232.N0720.N1313.d013092 ha hb.le hb2 (hepos n).le
  have hn' := (lt_div_iff₀ (hepos n)).1 hn
  refine ⟨e n, hepos n, ?_⟩
  nlinarith

theorem d023513 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hb1 : b ≤ 1) (u : ℝ) :
    betaPDFReal a 1 u ≤
      (a * ProbabilityTheory.beta a b) * betaPDFReal a b u := by
  by_cases hu : u ∈ Ioo (0 : ℝ) 1
  · have hpow : (1 : ℝ) ≤ (1 - u) ^ (b - 1) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge (sub_pos.mpr hu.2)
        (show 1 - u ≤ 1 by linarith [hu.1]) (show b - 1 ≤ 0 by linarith)
    have hp : 0 ≤ u ^ (a - 1) := Real.rpow_nonneg hu.1.le _
    rw [betaPDFReal, if_pos (show 0 < u ∧ u < 1 from hu), _root_.GD.N0232.N0720.N1313.d013083 ha,
      betaPDFReal, if_pos (show 0 < u ∧ u < 1 from hu)]
    simp only [sub_self, Real.rpow_zero, mul_one, one_div_div, div_one]
    have heq : (a * ProbabilityTheory.beta a b) *
        (1 / ProbabilityTheory.beta a b * u ^ (a - 1) * (1 - u) ^ (b - 1)) =
        a * u ^ (a - 1) * (1 - u) ^ (b - 1) := by
      field_simp [(beta_pos ha hb).ne']
    rw [heq]
    exact le_mul_of_one_le_right (mul_nonneg ha.le hp) hpow
  · simp only [betaPDFReal, if_neg (show ¬ (0 < u ∧ u < 1) from hu)]
    norm_num

theorem d023514 {a b e : ℝ} (ha : 0 < a) (hb : 0 < b)
    (he : 0 ≤ e) : Integrable (fun u ↦ betaPDFReal a b u *
      (_root_.GD.N0232.N0720.N1310.d013058 e (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 e) ^ 2) := by
  apply Integrable.mono' (_root_.GD.N0232.N0720.N1091.d012772 ha hb)
    (show Measurable (fun u ↦ betaPDFReal a b u *
      (_root_.GD.N0232.N0720.N1310.d013058 e (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 e) ^ 2) from by
      unfold _root_.GD.N0232.N0720.N1310.d013058 _root_.GD.N0232.N0720.N1309.d013069
      fun_prop).aestronglyMeasurable
  filter_upwards with u
  rw [norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (_root_.GD.N0235.d004040 ha hb u),
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hg := _root_.GD.N0232.N0720.N1313.d013088 e (u / (1 - u))
  have ht := _root_.GD.N0232.N0720.N1313.d013089 he
  have hsq : (_root_.GD.N0232.N0720.N1310.d013058 e (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 e) ^ 2 ≤ 1 := by
    apply (sq_le_one_iff_abs_le_one _).2
    exact abs_le.mpr ⟨by linarith [hg.1, ht.2], by linarith [hg.2, ht.1]⟩
  exact mul_le_of_le_one_right (_root_.GD.N0235.d004040 ha hb u) hsq

theorem d023515 {a b e : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hb1 : b ≤ 1) (he : 0 ≤ e) :
    _root_.GD.N0232.N0720.N1309.d013070 a 1 e ≤ (a * ProbabilityTheory.beta a b) * _root_.GD.N0232.N0720.N1309.d013070 a b e := by
  unfold _root_.GD.N0232.N0720.N1309.d013070
  rw [_root_.GD.N0235.d004041 ha zero_lt_one,
    _root_.GD.N0235.d004041 ha hb,
    ← integral_const_mul]
  apply integral_mono (_root_.GD.N0207.N0453.d023514 ha zero_lt_one he)
    ((_root_.GD.N0207.N0453.d023514 ha hb he).const_mul (a * ProbabilityTheory.beta a b))
  intro u
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (_root_.GD.N0207.N0453.d023513 ha hb hb1 u)
    (sq_nonneg (_root_.GD.N0232.N0720.N1310.d013058 e (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 e))

theorem d023516 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hb1 : b ≤ 1)
    (C : ℝ) : ∃ e : ℝ, 0 < e ∧ C * e < _root_.GD.N0232.N0720.N1309.d013070 a b e := by
  have hA : 0 < a * ProbabilityTheory.beta a b := mul_pos ha (beta_pos ha hb)
  obtain ⟨e, he, hroot⟩ := _root_.GD.N0207.N0453.d023512 ha ((a * ProbabilityTheory.beta a b) * C)
  have hbound := _root_.GD.N0207.N0453.d023515 ha hb hb1 he.le
  refine ⟨e, he, ?_⟩
  nlinarith

end
end GD.N0207.N0453

#print axioms _root_.GD.N0207.N0453.d023516
