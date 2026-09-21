import GD.Module0364















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1522
noncomputable section

open MeasureTheory Filter Set Complex
open _root_.GD.N0106.N0428.N0765.N1550
open scoped Topology

private theorem d005491 {d y s : ℝ} (hd : 0 ≤ d)
    (hy : |y| ≤ d) (hs : s ∈ uIcc 0 y) : |s| ≤ d := by
  have hy' := abs_le.mp hy
  change min 0 y ≤ s ∧ s ≤ max 0 y at hs
  exact abs_le.mpr ⟨(le_min (by linarith) hy'.1).trans hs.1,
    hs.2.trans (max_le hd hy'.2)⟩



theorem d005492 {f : ℂ → ℂ} {d y : ℝ}
    (hd : 0 < d) (hy : |y| ≤ d)
    (hc : ContinuousOn f {z : ℂ | |z.im| ≤ d})
    (hf : DifferentiableOn ℂ f {z : ℂ | |z.im| < d}) (R : ℝ) :
    (∫ x : ℝ in -R..R, _root_.GD.N0106.N0428.N0765.N1550.d005474 f 0 x) -
      (∫ x : ℝ in -R..R, _root_.GD.N0106.N0428.N0765.N1550.d005474 f y x) +
      Complex.I * _root_.GD.N0106.N0428.N0765.N1550.d005475 f R y - Complex.I * _root_.GD.N0106.N0428.N0765.N1550.d005475 f (-R) y = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f (_root_.GD.N0106.N0428.N0765.N1550.d005473 (-R) 0) (_root_.GD.N0106.N0428.N0765.N1550.d005473 R y)
    (hc.mono (by
      intro z hz
      apply _root_.GD.N0106.N0428.N0765.N1522.d005491 hd.le hy
      simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477, Set.mem_preimage] using hz.2))
    (hf.mono (by
      intro z hz
      have hz' : min 0 y < z.im ∧ z.im < max 0 y := by
        simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477, Set.mem_preimage, Set.mem_Ioo] using hz.2
      have hy' := abs_le.mp hy
      have hlo : -d ≤ min 0 y := le_min (by linarith) hy'.1
      have hhi : max 0 y ≤ d := max_le hd.le hy'.2
      exact abs_lt.mpr ⟨hlo.trans_lt hz'.1, hz'.2.trans_le hhi⟩))
  simpa [_root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005475, _root_.GD.N0106.N0428.N0765.N1550.d005473, smul_eq_mul] using h



theorem d005493 {g : ℝ → ℝ → ℂ} {y : ℝ}
    (hdecay : ∀ ε : ℝ, 0 < ε → ∀ᶠ R : ℝ in atTop,
      ∀ s ∈ uIoc 0 y, ‖g R s‖ ≤ ε) :
    Tendsto (fun R : ℝ => ∫ s : ℝ in 0..y, g R s) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hden : 0 < |y| + 1 := by positivity
  have hsmall : 0 < ε / (|y| + 1) := div_pos hε hden
  filter_upwards [hdecay (ε / (|y| + 1)) hsmall] with R hR
  have hbound : ‖∫ s : ℝ in 0..y, g R s‖ ≤
      (ε / (|y| + 1)) * |y| := by
    simpa only [sub_zero] using
      intervalIntegral.norm_integral_le_of_norm_le_const hR
  have hmul : (ε / (|y| + 1)) * (|y| + 1) = ε :=
    div_mul_cancel₀ ε (ne_of_gt hden)
  have hlt : (ε / (|y| + 1)) * |y| < ε := by nlinarith
  simpa only [dist_zero_right] using hbound.trans_lt hlt




theorem d005494 {f : ℂ → ℂ} {d y : ℝ}
    (hd : 0 < d) (hy : |y| ≤ d)
    (hc : ContinuousOn f {z : ℂ | |z.im| ≤ d})
    (hf : DifferentiableOn ℂ f {z : ℂ | |z.im| < d})
    (h0 : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 f 0)) (hyint : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 f y))
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x s : ℝ,
      R ≤ |x| → |s| ≤ d → ‖f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ ≤ ε) :
    (∫ x : ℝ, _root_.GD.N0106.N0428.N0765.N1550.d005474 f 0 x) = ∫ x : ℝ, _root_.GD.N0106.N0428.N0765.N1550.d005474 f y x := by
  have hR : Tendsto (fun R : ℝ => _root_.GD.N0106.N0428.N0765.N1550.d005475 f R y) atTop (𝓝 0) := by
    apply _root_.GD.N0106.N0428.N0765.N1522.d005493
    intro ε hε
    obtain ⟨R0, hR0⟩ := hdecay ε hε
    filter_upwards [eventually_ge_atTop (max R0 0)] with R hR
    intro s hs
    have hs' : s ∈ uIcc 0 y := ⟨le_of_lt hs.1, hs.2⟩
    have hnonneg : 0 ≤ R := (le_max_right R0 0).trans hR
    apply hR0 R s
    · rw [abs_of_nonneg hnonneg]
      exact (le_max_left R0 0).trans hR
    · exact _root_.GD.N0106.N0428.N0765.N1522.d005491 hd.le hy hs'
  have hL : Tendsto (fun R : ℝ => _root_.GD.N0106.N0428.N0765.N1550.d005475 f (-R) y) atTop (𝓝 0) := by
    apply _root_.GD.N0106.N0428.N0765.N1522.d005493
    intro ε hε
    obtain ⟨R0, hR0⟩ := hdecay ε hε
    filter_upwards [eventually_ge_atTop (max R0 0)] with R hR
    intro s hs
    have hs' : s ∈ uIcc 0 y := ⟨le_of_lt hs.1, hs.2⟩
    have hnonneg : 0 ≤ R := (le_max_right R0 0).trans hR
    apply hR0 (-R) s
    · rw [abs_neg, abs_of_nonneg hnonneg]
      exact (le_max_left R0 0).trans hR
    · exact _root_.GD.N0106.N0428.N0765.N1522.d005491 hd.le hy hs'
  have hbase : Tendsto (fun R : ℝ => ∫ x : ℝ in -R..R, _root_.GD.N0106.N0428.N0765.N1550.d005474 f 0 x)
      atTop (𝓝 (∫ x : ℝ, _root_.GD.N0106.N0428.N0765.N1550.d005474 f 0 x)) :=
    intervalIntegral_tendsto_integral h0 tendsto_neg_atTop_atBot tendsto_id
  have hshift : Tendsto (fun R : ℝ => ∫ x : ℝ in -R..R, _root_.GD.N0106.N0428.N0765.N1550.d005474 f y x)
      atTop (𝓝 (∫ x : ℝ, _root_.GD.N0106.N0428.N0765.N1550.d005474 f y x)) :=
    intervalIntegral_tendsto_integral hyint tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hbase.sub hshift).add (hR.const_mul Complex.I)).sub
    (hL.const_mul Complex.I)
  have hzero : Tendsto (fun R : ℝ =>
      (∫ x : ℝ in -R..R, _root_.GD.N0106.N0428.N0765.N1550.d005474 f 0 x) -
        (∫ x : ℝ in -R..R, _root_.GD.N0106.N0428.N0765.N1550.d005474 f y x) +
        Complex.I * _root_.GD.N0106.N0428.N0765.N1550.d005475 f R y - Complex.I * _root_.GD.N0106.N0428.N0765.N1550.d005475 f (-R) y)
      atTop (𝓝 0) := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1522.d005492 hd hy hc hf] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
  have heq := tendsto_nhds_unique hlim hzero
  simpa only [mul_zero, add_zero, sub_zero, sub_eq_zero] using heq

end
end GD.N0106.N0428.N0765.N1522

#print axioms _root_.GD.N0106.N0428.N0765.N1522.d005492
#print axioms _root_.GD.N0106.N0428.N0765.N1522.d005493
#print axioms _root_.GD.N0106.N0428.N0765.N1522.d005494
