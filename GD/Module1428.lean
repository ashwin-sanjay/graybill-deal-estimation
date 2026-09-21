import GD.Module1426

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace GD.N0051
noncomputable section
open _root_.GD.N0232.N0719.N0954

def d022780 (a r u : ℝ) : ℝ :=
  (r ^ a / Real.Gamma a) / (r ^ (a + u) / Real.Gamma (a + u))

theorem d022781 {a r u : ℝ} (_ha : 0 < a) (hr : 0 < r)
    (hu : 0 < a + u) :
    (fun x => gammaPDFReal a r x * x ^ u) =ᵐ[(volume : Measure ℝ)]
      fun x => _root_.GD.N0051.d022780 a r u * gammaPDFReal (a + u) r x := by
  have hc : r ^ (a + u) / Real.Gamma (a + u) ≠ 0 :=
    (div_pos (Real.rpow_pos_of_pos hr _) (Real.Gamma_pos_of_pos hu)).ne'
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with x hx0
  by_cases hx : 0 < x
  · have he : a - 1 + u = a + u - 1 := by ring
    simp only [gammaPDFReal, if_pos hx.le, _root_.GD.N0051.d022780]
    calc
      _ = (r ^ a / Real.Gamma a) * (x ^ (a - 1) * x ^ u) * Real.exp (-(r * x)) := by ring
      _ = (r ^ a / Real.Gamma a) * x ^ (a + u - 1) * Real.exp (-(r * x)) := by
        rw [← Real.rpow_add hx, he]
      _ = _ := by rw [← mul_assoc, ← mul_assoc, div_mul_cancel₀ _ hc]
  · have hn : x < 0 := lt_of_le_of_ne (not_lt.mp hx) hx0
    simp [gammaPDFReal, not_le.mpr hn]

theorem d022782 {a r u : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hu : 0 < a + u) : Integrable (fun x : ℝ => x ^ u) (gammaMeasure a r) := by
  rw [gammaMeasure]
  change Integrable (fun x : ℝ => x ^ u)
    (volume.withDensity (fun x => ENNReal.ofReal (gammaPDFReal a r x)))
  rw [integrable_withDensity_iff_integrable_smul'
    ((measurable_gammaPDFReal a r).ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hh := ((_root_.GD.N0232.N0719.N0954.d009352 hu hr).const_mul (_root_.GD.N0051.d022780 a r u)).congr
    (_root_.GD.N0051.d022781 ha hr hu).symm
  apply hh.congr
  filter_upwards with x
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)]

theorem d022783 {a r u : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hu : 0 < a + u) :
    (∫ x, x ^ u ∂gammaMeasure a r) = _root_.GD.N0051.d022780 a r u := by
  letI := isProbabilityMeasure_gammaMeasure hu hr
  rw [_root_.GD.N0232.N0719.N0954.d009351 ha hr,
    integral_congr_ae (_root_.GD.N0051.d022781 ha hr hu), integral_const_mul]
  have hmass : (∫ x, gammaPDFReal (a + u) r x) = 1 := by
    simpa using (_root_.GD.N0232.N0719.N0954.d009351 hu hr (fun _ => (1 : ℝ))).symm
  rw [hmass, mul_one]

theorem d022784 {a r u : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hu : 0 < a + u) : 0 < _root_.GD.N0051.d022780 a r u := by
  unfold _root_.GD.N0051.d022780
  exact div_pos (div_pos (Real.rpow_pos_of_pos hr _) (Real.Gamma_pos_of_pos ha))
    (div_pos (Real.rpow_pos_of_pos hr _) (Real.Gamma_pos_of_pos hu))

#print axioms _root_.GD.N0051.d022782
#print axioms _root_.GD.N0051.d022783
end
end GD.N0051
