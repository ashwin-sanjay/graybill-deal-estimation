import GD.Module0015



















open Filter MeasureTheory Set

namespace GD
namespace N0230
namespace N0590

noncomputable section

variable {X : Type*} [MeasurableSpace X]

private theorem d000141
    {a b : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]
    ring




theorem d000142
    (mu : Measure X) (f : ℕ → X → ℝ) (g : X → ℝ)
    (hfmeas : ∀ n, Measurable (f n)) (hgmeas : Measurable g)
    (hfint : ∀ n, Integrable (f n) mu) (hgint : Integrable g mu)
    (hfnonneg : ∀ n x, 0 ≤ f n x) (hgnonneg : ∀ x, 0 ≤ g x)
    (hpoint : ∀ x, Tendsto (fun n ↦ f n x) atTop (nhds (g x)))
    (hmass : Tendsto (fun n ↦ ∫ x, f n x ∂mu) atTop
      (nhds (∫ x, g x ∂mu))) :
    Tendsto (fun n ↦ ∫ x, |f n x - g x| ∂mu) atTop (nhds 0) := by
  have hminInt : ∀ n, Integrable (fun x ↦ min (f n x) (g x)) mu := by
    intro n
    apply hgint.mono'
    · exact (hfmeas n).min hgmeas |>.aestronglyMeasurable
    · exact ae_of_all mu fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hfnonneg n x) (hgnonneg x))]
        exact min_le_right _ _
  have hmin : Tendsto
      (fun n ↦ ∫ x, min (f n x) (g x) ∂mu) atTop
      (nhds (∫ x, g x ∂mu)) := by
    apply tendsto_integral_of_dominated_convergence g
    · intro n
      exact ((hfmeas n).min hgmeas).aestronglyMeasurable
    · exact hgint
    · intro n
      exact ae_of_all mu fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hfnonneg n x) (hgnonneg x))]
        exact min_le_right _ _
    · exact ae_of_all mu fun x ↦ by
        simpa only [min_self] using
          (hpoint x).min
            (show Tendsto (fun _ : ℕ ↦ g x) atTop (nhds (g x)) from
              tendsto_const_nhds)
  have hformula : ∀ n,
      (∫ x, |f n x - g x| ∂mu) =
        (∫ x, f n x ∂mu) + (∫ x, g x ∂mu) -
          2 * (∫ x, min (f n x) (g x) ∂mu) := by
    intro n
    calc
      (∫ x, |f n x - g x| ∂mu) =
          ∫ x, (f n x + g x) -
            2 * min (f n x) (g x) ∂mu := by
        apply integral_congr_ae
        exact ae_of_all mu fun x ↦
          _root_.GD.N0230.N0590.d000141 (hfnonneg n x) (hgnonneg x)
      _ = (∫ x, f n x + g x ∂mu) -
          ∫ x, 2 * min (f n x) (g x) ∂mu := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          (integral_sub (hfint n |>.add hgint) ((hminInt n).const_mul 2))
      _ = (∫ x, f n x ∂mu) + (∫ x, g x ∂mu) -
          2 * (∫ x, min (f n x) (g x) ∂mu) := by
        rw [integral_add (hfint n) hgint, integral_const_mul]
  have htwo : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hconstIntegral : Tendsto
      (fun _ : ℕ ↦ ∫ x, g x ∂mu) atTop
      (nhds (∫ x, g x ∂mu)) := tendsto_const_nhds
  have hcombined := (hmass.add hconstIntegral).sub (htwo.mul hmin)
  rw [show (fun n ↦ ∫ x, |f n x - g x| ∂mu) =
      fun n ↦ (∫ x, f n x ∂mu) + (∫ x, g x ∂mu) -
        2 * (∫ x, min (f n x) (g x) ∂mu) by
    funext n
    exact hformula n]
  have hzero :
      (∫ x, g x ∂mu) + (∫ x, g x ∂mu) -
        2 * (∫ x, g x ∂mu) = 0 := by ring
  simpa only [hzero] using hcombined

private theorem d000143
    (mu : Measure X) (h : X → ℝ) (hhmeas : Measurable h)
    (hhnonneg : ∀ x, 0 ≤ h x) (s : Set X) (hs : MeasurableSet s) :
    (mu.withDensity (fun x ↦ ENNReal.ofReal (h x))).real s =
      ∫ x in s, h x ∂mu := by
  rw [← integral_indicator_one hs]
  rw [integral_withDensity_eq_integral_toReal_smul
    hhmeas.ennreal_ofReal
    (ae_of_all mu fun x ↦ ENNReal.ofReal_lt_top) (s.indicator 1)]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  exact ae_of_all mu fun x ↦ by
    by_cases hx : x ∈ s
    · simp [hx, ENNReal.toReal_ofReal (hhnonneg x)]
    · simp [hx]



theorem d000144
    (mu : Measure X) (f : ℕ → X → ℝ) (g : X → ℝ)
    (hfmeas : ∀ n, Measurable (f n)) (hgmeas : Measurable g)
    (hfint : ∀ n, Integrable (f n) mu) (hgint : Integrable g mu)
    (hfnonneg : ∀ n x, 0 ≤ f n x) (hgnonneg : ∀ x, 0 ≤ g x)
    (hpoint : ∀ x, Tendsto (fun n ↦ f n x) atTop (nhds (g x)))
    (hmass : Tendsto (fun n ↦ ∫ x, f n x ∂mu) atTop
      (nhds (∫ x, g x ∂mu)))
    (s : Set X) (hs : MeasurableSet s) :
    Tendsto
      (fun n ↦ (mu.withDensity (fun x ↦ ENNReal.ofReal (f n x))).real s)
      atTop
      (nhds ((mu.withDensity (fun x ↦ ENNReal.ofReal (g x))).real s)) := by
  have hL1 := _root_.GD.N0230.N0590.d000142
    mu f g hfmeas hgmeas hfint hgint hfnonneg hgnonneg hpoint hmass
  have hset := tendsto_setIntegral_of_L1 (l := atTop)
    g hgmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hfint) ?_ s
  · simpa only [_root_.GD.N0230.N0590.d000143 mu g hgmeas hgnonneg s hs,
        _root_.GD.N0230.N0590.d000143 mu (f _) (hfmeas _) (hfnonneg _) s hs]
      using hset
  · have hlintegral : Tendsto
        (fun n ↦ ∫⁻ x, ‖f n x - g x‖ₑ ∂mu) atTop (nhds 0) := by
      have hofReal := ENNReal.tendsto_ofReal hL1
      convert hofReal using 1
      · ext n
        simp_rw [Real.enorm_eq_ofReal_abs]
        exact (ofReal_integral_eq_lintegral_ofReal
          (hfint n |>.sub hgint).abs
          (ae_of_all mu fun x ↦ abs_nonneg (f n x - g x))).symm
      · simp
    exact hlintegral



theorem d000145
    (mu : Measure X) (f : ℕ → X → ℝ) (g : X → ℝ)
    (hfmeas : ∀ n, Measurable (f n)) (hgmeas : Measurable g)
    (hfint : ∀ n, Integrable (f n) mu) (hgint : Integrable g mu)
    (hfnonneg : ∀ n x, 0 ≤ f n x) (hgnonneg : ∀ x, 0 ≤ g x)
    (hpoint : ∀ x, Tendsto (fun n ↦ f n x) atTop (nhds (g x)))
    (hmass : Tendsto (fun n ↦ ∫ x, f n x ∂mu) atTop
      (nhds (∫ x, g x ∂mu)))
    (s : Set X) (hs : MeasurableSet s) (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ n in atTop,
      (mu.withDensity (fun x ↦ ENNReal.ofReal (f n x))).real s <
        (mu.withDensity (fun x ↦ ENNReal.ofReal (g x))).real s + delta := by
  have htendsto := _root_.GD.N0230.N0590.d000144
    mu f g hfmeas hgmeas hfint hgint hfnonneg hgnonneg hpoint hmass s hs
  exact htendsto.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hdelta))

end

end N0590
end N0230
end GD

#print axioms _root_.GD.N0230.N0590.d000142
#print axioms _root_.GD.N0230.N0590.d000144
#print axioms _root_.GD.N0230.N0590.d000145
