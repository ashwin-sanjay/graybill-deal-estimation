import GD.Module0657

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0960

noncomputable section




theorem d009681
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∀ᵐ x ∂gammaMeasure a r, 0 ≤ x := by
  rw [gammaMeasure]
  change
    ∀ᵐ x ∂volume.withDensity
      (fun x => ENNReal.ofReal (gammaPDFReal a r x)), 0 ≤ x
  refine (ae_withDensity_iff
    (μ := volume)
    ((measurable_gammaPDFReal a r).ennreal_ofReal)).2 ?_
  filter_upwards with x
  intro hpdf
  by_contra hx
  have hxneg : x < 0 := lt_of_not_ge hx
  have : gammaPDF a r x = 0 := gammaPDF_of_neg hxneg
  exact hpdf this


theorem d009682
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ x, x ∂gammaMeasure a r) = a / r := by
  rw [_root_.GD.N0232.N0719.N0954.d009351 ha hr]
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero
    (s := Set.Ioi 0)
    (f := fun x => gammaPDFReal a r x * x)]
  · have hkernel :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi
        (a := a + 1) (r := r) (by linarith) hr
    have hpoint :
        ∀ x ∈ Set.Ioi (0 : ℝ),
          gammaPDFReal a r x * x =
            (r ^ a / Real.Gamma a) *
              (x ^ a * Real.exp (-(r * x))) := by
      intro x hx
      have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
      have hxpow :
          x ^ (a - 1) * x = x ^ a := by
        calc
          x ^ (a - 1) * x =
              x ^ (a - 1) * x ^ (1 : ℝ) := by
                rw [Real.rpow_one]
          _ = x ^ ((a - 1) + 1) := by
                rw [Real.rpow_add hxpos]
          _ = x ^ a := by ring_nf
      calc
        gammaPDFReal a r x * x =
            (r ^ a / Real.Gamma a) *
              (x ^ (a - 1) * x) *
              Real.exp (-(r * x)) := by
                simp only [gammaPDFReal, if_pos hxpos.le]
                ring
        _ = (r ^ a / Real.Gamma a) *
              (x ^ a * Real.exp (-(r * x))) := by
                rw [hxpow]
                ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpoint]
    rw [integral_const_mul]
    have hkernel' :
        (∫ x in Set.Ioi (0 : ℝ),
            x ^ a * Real.exp (-(r * x))) =
          (1 / r) ^ (a + 1) * Real.Gamma (a + 1) := by
      simpa only [add_sub_cancel_right] using hkernel
    rw [hkernel', Real.Gamma_add_one ha.ne']
    have hpow :
        r ^ a * (1 / r) ^ (a + 1) = 1 / r := by
      rw [one_div, Real.inv_rpow hr.le,
        ← Real.rpow_neg hr.le,
        ← Real.rpow_add hr]
      rw [show a + -(a + 1) = -1 by ring,
        Real.rpow_neg_one]
    calc
      (r ^ a / Real.Gamma a) *
          ((1 / r) ^ (a + 1) *
            (a * Real.Gamma a)) =
          (r ^ a * (1 / r) ^ (a + 1)) * a := by
            field_simp [(Real.Gamma_pos_of_pos ha).ne']
      _ = (1 / r) * a := by rw [hpow]
      _ = a / r := by ring
  · filter_upwards with x
    intro hx
    have hxle : x ≤ 0 := le_of_not_gt hx
    by_cases hxzero : x = 0
    · simp [hxzero]
    · have hxneg : x < 0 := lt_of_le_of_ne hxle hxzero
      simp [gammaPDFReal, not_le.mpr hxneg]


theorem d009683
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ => x) (gammaMeasure a r) := by
  rw [gammaMeasure]
  change Integrable (fun x : ℝ => x)
    (volume.withDensity
      (fun x => ENNReal.ofReal (gammaPDFReal a r x)))
  rw [integrable_withDensity_iff_integrable_smul'
    ((measurable_gammaPDFReal a r).ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hkernel :
      IntegrableOn
        (fun x : ℝ =>
          (r ^ a / Real.Gamma a) *
            (x ^ a * Real.exp (-(r * x))))
        (Set.Ioi 0) := by
    have hbase :=
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := a) (b := r)
        (by linarith) (by norm_num) hr
    have hbase' :
        IntegrableOn
          (fun x : ℝ => x ^ a * Real.exp (-(r * x)))
          (Set.Ioi 0) := by
      simpa only [Real.rpow_one, neg_mul] using hbase
    exact hbase'.const_mul _
  have hkernelActual :
      IntegrableOn
        (fun x : ℝ => gammaPDFReal a r x * x)
        (Set.Ioi 0) := by
    apply hkernel.congr_fun
    · intro x hx
      have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
      have hxpow :
          x ^ (a - 1) * x = x ^ a := by
        calc
          x ^ (a - 1) * x =
              x ^ (a - 1) * x ^ (1 : ℝ) := by
                rw [Real.rpow_one]
          _ = x ^ ((a - 1) + 1) := by
                rw [Real.rpow_add hxpos]
          _ = x ^ a := by ring_nf
      symm
      calc
        gammaPDFReal a r x * x =
            (r ^ a / Real.Gamma a) *
              (x ^ (a - 1) * x) *
              Real.exp (-(r * x)) := by
                simp only [gammaPDFReal, if_pos hxpos.le]
                ring
        _ = (r ^ a / Real.Gamma a) *
              (x ^ a * Real.exp (-(r * x))) := by
                rw [hxpow]
                ring
    · exact measurableSet_Ioi
  have hdensity :
      Integrable
        (fun x : ℝ => gammaPDFReal a r x * x) := by
    apply hkernelActual.integrable_of_forall_notMem_eq_zero
    intro x hx
    have hxle : x ≤ 0 := le_of_not_gt hx
    by_cases hxzero : x = 0
    · simp [hxzero]
    · have hxneg : x < 0 := lt_of_le_of_ne hxle hxzero
      simp [gammaPDFReal, not_le.mpr hxneg]
  apply hdensity.congr'
  · fun_prop
  filter_upwards with x
  have hpdf : 0 ≤ gammaPDFReal a r x :=
    gammaPDFReal_nonneg ha hr x
  simp only [smul_eq_mul, gammaPDF,
    ENNReal.toReal_ofReal hpdf]


theorem d009684
    {a r V : ℝ} (ha : 0 < a) (hr : 0 < r) (hV : 0 < V) :
    Integrable (fun x : ℝ => 1 / (x + V))
      (gammaMeasure a r) := by
  letI : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  have hsupport := _root_.GD.N0232.N0719.N0960.d009681 ha hr
  apply Integrable.mono'
    (integrable_const (μ := gammaMeasure a r) (1 / V))
  · exact
      ((measurable_id'.add_const V).inv.const_mul 1).aestronglyMeasurable
  · filter_upwards [hsupport] with x hx
    have hxV : 0 < x + V := add_pos_of_nonneg_of_pos hx hV
    have hbound : 1 / (x + V) ≤ 1 / V :=
      one_div_le_one_div_of_le hV (by linarith)
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hxV)]
    exact hbound






theorem d009685
    {a r V : ℝ} (ha : 0 < a) (hr : 0 < r) (hV : 0 < V) :
    1 / (a / r + V) ≤
      ∫ ω, 1 / (ω + V) ∂gammaMeasure a r := by
  letI : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  apply _root_.GD.N0232.N0719.N0960.d009680
    (gammaMeasure a r) (fun x => x)
    (_root_.GD.N0232.N0719.N0960.d009683 ha hr)
    (_root_.GD.N0232.N0719.N0960.d009681 ha hr)
    (m := a / r) (V := V)
  · exact (div_pos ha hr).le
  · exact hV
  · rw [_root_.GD.N0232.N0719.N0960.d009682 ha hr]
  · exact _root_.GD.N0232.N0719.N0960.d009684 ha hr hV

end

end GD.N0232.N0719.N0960
