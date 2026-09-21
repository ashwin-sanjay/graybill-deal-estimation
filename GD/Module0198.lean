import GD.Module0197
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic.Ring










open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace GD.N0232.N0720.N1296

open _root_.GD.N0232.N0720.N1297

noncomputable section

def d002713 (M a : ℝ) : ℝ := max (-M) (min M a)

theorem d002714 {M : ℝ} (hM : 0 ≤ M) (a : ℝ) : |_root_.GD.N0232.N0720.N1296.d002713 M a| ≤ M := by
  apply abs_le.2
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem d002715 {M a : ℝ} (ha : |a| ≤ M) : _root_.GD.N0232.N0720.N1296.d002713 M a = a := by
  rcases abs_le.1 ha with ⟨hl, hu⟩
  simp only [_root_.GD.N0232.N0720.N1296.d002713, min_eq_right hu, max_eq_right hl]

theorem d002716 {M : ℝ} (hM : 0 ≤ M) (a : ℝ) :
    |a - _root_.GD.N0232.N0720.N1296.d002713 M a| ≤ |a| := by
  by_cases hl : a < -M
  · have ha : a < 0 := by linarith
    have ham : a ≤ M := by linarith
    rw [_root_.GD.N0232.N0720.N1296.d002713, min_eq_right ham, max_eq_left hl.le,
      abs_of_nonpos (by linarith : a - -M ≤ 0), abs_of_neg ha]
    linarith
  · by_cases hu : M < a
    · have ha : 0 < a := by linarith
      rw [_root_.GD.N0232.N0720.N1296.d002713, min_eq_left hu.le, max_eq_right (by linarith : -M ≤ M),
        abs_of_nonneg (by linarith : 0 ≤ a - M), abs_of_pos ha]
      linarith
    · rw [_root_.GD.N0232.N0720.N1296.d002715 (abs_le.2 ⟨le_of_not_gt hl, le_of_not_gt hu⟩), sub_self, abs_zero]
      exact abs_nonneg a

def d002717 (f : _root_.GD.N0232.N0720.N1297.d002702 → ℝ) (hf : Continuous f)
    (M : ℝ) (hM : 0 ≤ M) : _root_.GD.N0232.N0720.N1297.d002702 →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun p ↦ _root_.GD.N0232.N0720.N1296.d002713 M (f p))
    (continuous_const.max (continuous_const.min hf)) M
    (fun p ↦ by simpa only [Real.norm_eq_abs] using _root_.GD.N0232.N0720.N1296.d002714 hM (f p))



theorem d002718
    {f : _root_.GD.N0232.N0720.N1297.d002702 → ℝ} (hf : Continuous f) {C α β : ℝ}
    (hC : 0 ≤ C) (hα : 0 ≤ α) (hαβ : α < β)
    (hbound : ∀ p, ‖f p‖ ≤ C * _root_.GD.N0232.N0720.N1297.d002703 α p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b : _root_.GD.N0232.N0720.N1297.d002702 →ᵇ ℝ, ∀ p,
      ‖f p - b p‖ ≤ ε * _root_.GD.N0232.N0720.N1297.d002703 β p := by
  have hdecay : Tendsto (fun T : ℝ ↦ C * Real.exp ((α - β) * T))
      atTop (𝓝 0) := by
    have ht : Tendsto (fun T : ℝ ↦ (α - β) * T) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (sub_neg.2 hαβ)).2 tendsto_id
    simpa only [mul_zero, Function.comp_def] using
      tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp ht)
  obtain ⟨T, hTsmall⟩ := (hdecay.eventually (Iio_mem_nhds hε)).exists
  let M : ℝ := C * Real.exp (α * T)
  have hM : 0 ≤ M := mul_nonneg hC (Real.exp_pos _).le
  refine ⟨_root_.GD.N0232.N0720.N1296.d002717 f hf M hM, ?_⟩
  intro p
  change ‖f p - _root_.GD.N0232.N0720.N1296.d002713 M (f p)‖ ≤ ε * _root_.GD.N0232.N0720.N1297.d002703 β p
  by_cases hp : p.1 ^ 2 ≤ T
  · have hfp : |f p| ≤ M := by
      apply (hbound p).trans
      dsimp [_root_.GD.N0232.N0720.N1297.d002703, M]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hp hα)) hC
    rw [_root_.GD.N0232.N0720.N1296.d002715 hfp, sub_self, norm_zero]
    exact mul_nonneg hε.le (_root_.GD.N0232.N0720.N1297.d002705 β p).le
  · have htail : C * Real.exp ((α - β) * p.1 ^ 2) ≤ ε := by
      apply le_trans _ hTsmall.le
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left (le_of_not_ge hp)
          (sub_nonpos.2 hαβ.le))) hC
    calc
      ‖f p - _root_.GD.N0232.N0720.N1296.d002713 M (f p)‖ ≤ ‖f p‖ := _root_.GD.N0232.N0720.N1296.d002716 hM (f p)
      _ ≤ C * _root_.GD.N0232.N0720.N1297.d002703 α p := hbound p
      _ = (C * Real.exp ((α - β) * p.1 ^ 2)) * _root_.GD.N0232.N0720.N1297.d002703 β p := by
        dsimp [_root_.GD.N0232.N0720.N1297.d002703]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ ε * _root_.GD.N0232.N0720.N1297.d002703 β p :=
        mul_le_mul_of_nonneg_right htail (_root_.GD.N0232.N0720.N1297.d002705 β p).le

theorem d002719 {μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1297.d002702}
    {f : _root_.GD.N0232.N0720.N1297.d002702 → ℝ} (hf : Continuous f) {C α β : ℝ}
    (hC : 0 ≤ C) (hαβ : α ≤ β)
    (hbound : ∀ p, ‖f p‖ ≤ C * _root_.GD.N0232.N0720.N1297.d002703 α p)
    (hi : Integrable (_root_.GD.N0232.N0720.N1297.d002703 β) (μ : Measure _root_.GD.N0232.N0720.N1297.d002702)) :
    Integrable f (μ : Measure _root_.GD.N0232.N0720.N1297.d002702) := by
  apply (hi.const_mul C).mono' hf.aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  apply (hbound p).trans
  apply mul_le_mul_of_nonneg_left _ hC
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hαβ (sq_nonneg p.1))

private theorem d002720
    {μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1297.d002702} {f : _root_.GD.N0232.N0720.N1297.d002702 → ℝ}
    (hfi : Integrable f (μ : Measure _root_.GD.N0232.N0720.N1297.d002702)) (b : _root_.GD.N0232.N0720.N1297.d002702 →ᵇ ℝ)
    {ε β B : ℝ} (hε : 0 ≤ ε)
    (hi : Integrable (_root_.GD.N0232.N0720.N1297.d002703 β) (μ : Measure _root_.GD.N0232.N0720.N1297.d002702))
    (hb : (∫ p, _root_.GD.N0232.N0720.N1297.d002703 β p ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702)) ≤ B)
    (herr : ∀ p, ‖f p - b p‖ ≤ ε * _root_.GD.N0232.N0720.N1297.d002703 β p) :
    dist (∫ p, f p ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702))
      (∫ p, b p ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702)) ≤ ε * B := by
  rw [dist_eq_norm, ← integral_sub hfi
    (BoundedContinuousFunction.integrable (μ : Measure _root_.GD.N0232.N0720.N1297.d002702) b)]
  calc
    ‖∫ p, f p - b p ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702)‖
      ≤ ∫ p, ε * _root_.GD.N0232.N0720.N1297.d002703 β p ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702) :=
        norm_integral_le_of_norm_le (hi.const_mul ε) (Eventually.of_forall herr)
    _ = ε * ∫ p, _root_.GD.N0232.N0720.N1297.d002703 β p ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702) :=
      integral_const_mul ε _
    _ ≤ ε * B := mul_le_mul_of_nonneg_left hb hε



theorem d002721
    {ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1297.d002702} {μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1297.d002702}
    (hlim : Tendsto ν atTop (𝓝 μ)) {β B : ℝ}
    (hmoment : _root_.GD.N0232.N0720.N1297.d002706 ν β B)
    {f : _root_.GD.N0232.N0720.N1297.d002702 → ℝ} (hf : Continuous f) {C α : ℝ}
    (hC : 0 ≤ C) (hβ : 0 < β) (hαβ : α < β)
    (hbound : ∀ p, ‖f p‖ ≤ C * _root_.GD.N0232.N0720.N1297.d002703 α p) :
    Tendsto (fun n ↦ ∫ p, f p ∂(ν n : Measure _root_.GD.N0232.N0720.N1297.d002702)) atTop
      (𝓝 (∫ p, f p ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702))) := by
  have hlimitMoment := _root_.GD.N0232.N0720.N1297.d002712 hlim hmoment
  have hB : 0 ≤ B := (integral_nonneg fun p ↦
    (_root_.GD.N0232.N0720.N1297.d002705 β p).le).trans (hmoment 0).2
  have hfi (n : ℕ) : Integrable f (ν n : Measure _root_.GD.N0232.N0720.N1297.d002702) :=
    _root_.GD.N0232.N0720.N1296.d002719 hf hC hαβ.le hbound (hmoment n).1
  have hfμ : Integrable f (μ : Measure _root_.GD.N0232.N0720.N1297.d002702) :=
    _root_.GD.N0232.N0720.N1296.d002719 hf hC hαβ.le hbound hlimitMoment.1
  have hbound' (p : _root_.GD.N0232.N0720.N1297.d002702) : ‖f p‖ ≤ C * _root_.GD.N0232.N0720.N1297.d002703 (max α 0) p := by
    apply (hbound p).trans
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left α 0) (sq_nonneg p.1))) hC
  apply Metric.tendsto_atTop.2
  intro δ hδ
  let ε : ℝ := δ / (3 * (B + 1))
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hεB : ε * B ≤ δ / 3 := by
    have he : ε * (B + 1) = δ / 3 := by
      dsimp [ε]
      field_simp [show B + 1 ≠ 0 by linarith]
    have hm := mul_le_mul_of_nonneg_left (show B ≤ B + 1 by linarith) hε.le
    rwa [he] at hm
  obtain ⟨b, hb⟩ := _root_.GD.N0232.N0720.N1296.d002718 hf hC (le_max_right α 0)
    (max_lt hαβ hβ) hbound' hε
  have hbLimit : Tendsto (fun n ↦ ∫ p, b p ∂(ν n : Measure _root_.GD.N0232.N0720.N1297.d002702)) atTop
      (𝓝 (∫ p, b p ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702))) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction b).tendsto μ |>.comp hlim
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hbLimit (δ / 3) (by linarith)
  refine ⟨N, ?_⟩
  intro n hn
  have hleft := _root_.GD.N0232.N0720.N1296.d002720 (hfi n) b hε.le (hmoment n).1 (hmoment n).2 hb
  have hright := _root_.GD.N0232.N0720.N1296.d002720 hfμ b hε.le hlimitMoment.1 hlimitMoment.2 hb
  have htri := dist_triangle
    (∫ p, f p ∂(ν n : Measure _root_.GD.N0232.N0720.N1297.d002702))
    (∫ p, b p ∂(ν n : Measure _root_.GD.N0232.N0720.N1297.d002702))
    (∫ p, f p ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702))
  have htri' := dist_triangle
    (∫ p, b p ∂(ν n : Measure _root_.GD.N0232.N0720.N1297.d002702))
    (∫ p, b p ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702))
    (∫ p, f p ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702))
  rw [dist_comm (∫ p, b p ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702))] at htri'
  have hmiddle := hN n hn
  linarith

end
end GD.N0232.N0720.N1296

#print axioms _root_.GD.N0232.N0720.N1296.d002718
#print axioms _root_.GD.N0232.N0720.N1296.d002721
