import GD.Module0502
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic.Ring










set_option linter.unusedSectionVars false

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace GD.N0212.N0469

open _root_.GD.N0212.N0468

noncomputable section

variable {K : Type*} [MetricSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

def d007655 (M a : ℝ) : ℝ := max (-M) (min M a)

theorem d007656 {M : ℝ} (hM : 0 ≤ M) (a : ℝ) : |_root_.GD.N0212.N0469.d007655 M a| ≤ M := by
  apply abs_le.2
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem d007657 {M a : ℝ} (ha : |a| ≤ M) : _root_.GD.N0212.N0469.d007655 M a = a := by
  rcases abs_le.1 ha with ⟨hl, hu⟩
  simp only [_root_.GD.N0212.N0469.d007655, min_eq_right hu, max_eq_right hl]

theorem d007658 {M : ℝ} (hM : 0 ≤ M) (a : ℝ) :
    |a - _root_.GD.N0212.N0469.d007655 M a| ≤ |a| := by
  by_cases hl : a < -M
  · have ha : a < 0 := by linarith
    have ham : a ≤ M := by linarith
    rw [_root_.GD.N0212.N0469.d007655, min_eq_right ham, max_eq_left hl.le,
      abs_of_nonpos (by linarith : a - -M ≤ 0), abs_of_neg ha]
    linarith
  · by_cases hu : M < a
    · have ha : 0 < a := by linarith
      rw [_root_.GD.N0212.N0469.d007655, min_eq_left hu.le, max_eq_right (by linarith : -M ≤ M),
        abs_of_nonneg (by linarith : 0 ≤ a - M), abs_of_pos ha]
      linarith
    · rw [_root_.GD.N0212.N0469.d007657 (abs_le.2 ⟨le_of_not_gt hl, le_of_not_gt hu⟩), sub_self, abs_zero]
      exact abs_nonneg a

def d007659 (f : (_root_.GD.N0212.N0468.d007644 K) → ℝ) (hf : Continuous f)
    (M : ℝ) (hM : 0 ≤ M) : (_root_.GD.N0212.N0468.d007644 K) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun p ↦ _root_.GD.N0212.N0469.d007655 M (f p))
    (continuous_const.max (continuous_const.min hf)) M
    (fun p ↦ by simpa only [Real.norm_eq_abs] using _root_.GD.N0212.N0469.d007656 hM (f p))



theorem d007660
    {f : (_root_.GD.N0212.N0468.d007644 K) → ℝ} (hf : Continuous f) {C α β : ℝ}
    (hC : 0 ≤ C) (hα : 0 ≤ α) (hαβ : α < β)
    (hbound : ∀ p, ‖f p‖ ≤ C * _root_.GD.N0212.N0468.d007645 α p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b : (_root_.GD.N0212.N0468.d007644 K) →ᵇ ℝ, ∀ p,
      ‖f p - b p‖ ≤ ε * _root_.GD.N0212.N0468.d007645 β p := by
  have hdecay : Tendsto (fun T : ℝ ↦ C * Real.exp ((α - β) * T))
      atTop (𝓝 0) := by
    have ht : Tendsto (fun T : ℝ ↦ (α - β) * T) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (sub_neg.2 hαβ)).2 tendsto_id
    simpa only [mul_zero, Function.comp_def] using
      tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp ht)
  obtain ⟨T, hTsmall⟩ := (hdecay.eventually (Iio_mem_nhds hε)).exists
  let M : ℝ := C * Real.exp (α * T)
  have hM : 0 ≤ M := mul_nonneg hC (Real.exp_pos _).le
  refine ⟨_root_.GD.N0212.N0469.d007659 f hf M hM, ?_⟩
  intro p
  change ‖f p - _root_.GD.N0212.N0469.d007655 M (f p)‖ ≤ ε * _root_.GD.N0212.N0468.d007645 β p
  by_cases hp : p.1 ^ 2 ≤ T
  · have hfp : |f p| ≤ M := by
      apply (hbound p).trans
      dsimp [_root_.GD.N0212.N0468.d007645, M]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hp hα)) hC
    rw [_root_.GD.N0212.N0469.d007657 hfp, sub_self, norm_zero]
    exact mul_nonneg hε.le (_root_.GD.N0212.N0468.d007647 β p).le
  · have htail : C * Real.exp ((α - β) * p.1 ^ 2) ≤ ε := by
      apply le_trans _ hTsmall.le
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left (le_of_not_ge hp)
          (sub_nonpos.2 hαβ.le))) hC
    calc
      ‖f p - _root_.GD.N0212.N0469.d007655 M (f p)‖ ≤ ‖f p‖ := _root_.GD.N0212.N0469.d007658 hM (f p)
      _ ≤ C * _root_.GD.N0212.N0468.d007645 α p := hbound p
      _ = (C * Real.exp ((α - β) * p.1 ^ 2)) * _root_.GD.N0212.N0468.d007645 β p := by
        dsimp [_root_.GD.N0212.N0468.d007645]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ ε * _root_.GD.N0212.N0468.d007645 β p :=
        mul_le_mul_of_nonneg_right htail (_root_.GD.N0212.N0468.d007647 β p).le

theorem d007661 {μ : ProbabilityMeasure (_root_.GD.N0212.N0468.d007644 K)}
    {f : (_root_.GD.N0212.N0468.d007644 K) → ℝ} (hf : Continuous f) {C α β : ℝ}
    (hC : 0 ≤ C) (hαβ : α ≤ β)
    (hbound : ∀ p, ‖f p‖ ≤ C * _root_.GD.N0212.N0468.d007645 α p)
    (hi : Integrable (_root_.GD.N0212.N0468.d007645 β) (μ : Measure (_root_.GD.N0212.N0468.d007644 K))) :
    Integrable f (μ : Measure (_root_.GD.N0212.N0468.d007644 K)) := by
  apply (hi.const_mul C).mono' hf.aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  apply (hbound p).trans
  apply mul_le_mul_of_nonneg_left _ hC
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hαβ (sq_nonneg p.1))

private theorem d007662
    {μ : ProbabilityMeasure (_root_.GD.N0212.N0468.d007644 K)} {f : (_root_.GD.N0212.N0468.d007644 K) → ℝ}
    (hfi : Integrable f (μ : Measure (_root_.GD.N0212.N0468.d007644 K))) (b : (_root_.GD.N0212.N0468.d007644 K) →ᵇ ℝ)
    {ε β B : ℝ} (hε : 0 ≤ ε)
    (hi : Integrable (_root_.GD.N0212.N0468.d007645 β) (μ : Measure (_root_.GD.N0212.N0468.d007644 K)))
    (hb : (∫ p, _root_.GD.N0212.N0468.d007645 β p ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K))) ≤ B)
    (herr : ∀ p, ‖f p - b p‖ ≤ ε * _root_.GD.N0212.N0468.d007645 β p) :
    dist (∫ p, f p ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K)))
      (∫ p, b p ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K))) ≤ ε * B := by
  rw [dist_eq_norm, ← integral_sub hfi
    (BoundedContinuousFunction.integrable (μ : Measure (_root_.GD.N0212.N0468.d007644 K)) b)]
  calc
    ‖∫ p, f p - b p ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K))‖
      ≤ ∫ p, ε * _root_.GD.N0212.N0468.d007645 β p ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K)) :=
        norm_integral_le_of_norm_le (hi.const_mul ε) (Eventually.of_forall herr)
    _ = ε * ∫ p, _root_.GD.N0212.N0468.d007645 β p ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K)) :=
      integral_const_mul ε _
    _ ≤ ε * B := mul_le_mul_of_nonneg_left hb hε



theorem d007663
    {ν : ℕ → ProbabilityMeasure (_root_.GD.N0212.N0468.d007644 K)} {μ : ProbabilityMeasure (_root_.GD.N0212.N0468.d007644 K)}
    (hlim : Tendsto ν atTop (𝓝 μ)) {β B : ℝ}
    (hmoment : _root_.GD.N0212.N0468.d007648 ν β B)
    {f : (_root_.GD.N0212.N0468.d007644 K) → ℝ} (hf : Continuous f) {C α : ℝ}
    (hC : 0 ≤ C) (hβ : 0 < β) (hαβ : α < β)
    (hbound : ∀ p, ‖f p‖ ≤ C * _root_.GD.N0212.N0468.d007645 α p) :
    Tendsto (fun n ↦ ∫ p, f p ∂(ν n : Measure (_root_.GD.N0212.N0468.d007644 K))) atTop
      (𝓝 (∫ p, f p ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K)))) := by
  have hlimitMoment := _root_.GD.N0212.N0468.d007654 hlim hmoment
  have hB : 0 ≤ B := (integral_nonneg fun p ↦
    (_root_.GD.N0212.N0468.d007647 β p).le).trans (hmoment 0).2
  have hfi (n : ℕ) : Integrable f (ν n : Measure (_root_.GD.N0212.N0468.d007644 K)) :=
    _root_.GD.N0212.N0469.d007661 hf hC hαβ.le hbound (hmoment n).1
  have hfμ : Integrable f (μ : Measure (_root_.GD.N0212.N0468.d007644 K)) :=
    _root_.GD.N0212.N0469.d007661 hf hC hαβ.le hbound hlimitMoment.1
  have hbound' (p : (_root_.GD.N0212.N0468.d007644 K)) : ‖f p‖ ≤ C * _root_.GD.N0212.N0468.d007645 (max α 0) p := by
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
  obtain ⟨b, hb⟩ := _root_.GD.N0212.N0469.d007660 hf hC (le_max_right α 0)
    (max_lt hαβ hβ) hbound' hε
  have hbLimit : Tendsto (fun n ↦ ∫ p, b p ∂(ν n : Measure (_root_.GD.N0212.N0468.d007644 K))) atTop
      (𝓝 (∫ p, b p ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K)))) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction b).tendsto μ |>.comp hlim
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hbLimit (δ / 3) (by linarith)
  refine ⟨N, ?_⟩
  intro n hn
  have hleft := _root_.GD.N0212.N0469.d007662 (hfi n) b hε.le (hmoment n).1 (hmoment n).2 hb
  have hright := _root_.GD.N0212.N0469.d007662 hfμ b hε.le hlimitMoment.1 hlimitMoment.2 hb
  have htri := dist_triangle
    (∫ p, f p ∂(ν n : Measure (_root_.GD.N0212.N0468.d007644 K)))
    (∫ p, b p ∂(ν n : Measure (_root_.GD.N0212.N0468.d007644 K)))
    (∫ p, f p ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K)))
  have htri' := dist_triangle
    (∫ p, b p ∂(ν n : Measure (_root_.GD.N0212.N0468.d007644 K)))
    (∫ p, b p ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K)))
    (∫ p, f p ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K)))
  rw [dist_comm (∫ p, b p ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K)))] at htri'
  have hmiddle := hN n hn
  linarith

end
end GD.N0212.N0469

#print axioms _root_.GD.N0212.N0469.d007660
#print axioms _root_.GD.N0212.N0469.d007663
