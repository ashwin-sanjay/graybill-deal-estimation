import Mathlib









open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0121

noncomputable section


def d006346 (d : ℕ) : Measure ℝ :=
  gammaMeasure ((d : ℝ) / 2) (1 / 2)


theorem d006347 {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    mgf id (gammaMeasure a r) t = (r / (r - t)) ^ a := by
  have hpdf : Measurable (gammaPDF a r) := by
    exact (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [mgf, gammaMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul
      hpdf (ae_of_all _ fun x ↦ by simp [gammaPDF])]
  simp only [id_eq, gammaPDF, ENNReal.toReal_ofReal
    (gammaPDFReal_nonneg ha hr _), smul_eq_mul]
  have hrestrict :
      (∫ x in Ici 0, gammaPDFReal a r x * Real.exp (t * x)) =
        ∫ x : ℝ, gammaPDFReal a r x * Real.exp (t * x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hx' : x < 0 := by
      simpa only [mem_compl_iff, mem_Ici, not_le] using hx
    simp [gammaPDFReal, not_le.mpr hx']
  rw [← hrestrict]
  rw [integral_Ici_eq_integral_Ioi]
  rw [show (∫ x in Ioi 0,
      gammaPDFReal a r x * Real.exp (t * x)) =
      ∫ x in Ioi 0,
        (r ^ a / Real.Gamma a * x ^ (a - 1) *
            Real.exp (-(r * x))) * Real.exp (t * x) by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    simp only [gammaPDFReal, if_pos hx0]]
  have hrate : 0 < r - t := sub_pos.mpr ht
  rw [show (∫ x in Ioi 0,
      (r ^ a / Real.Gamma a * x ^ (a - 1) *
          Real.exp (-(r * x))) * Real.exp (t * x)) =
      (r ^ a / Real.Gamma a) *
        ∫ x in Ioi 0,
          x ^ (a - 1) * Real.exp (-((r - t) * x)) by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    change
      ((r ^ a / Real.Gamma a * x ^ (a - 1)) *
          Real.exp (-(r * x))) * Real.exp (t * x) =
        r ^ a / Real.Gamma a *
          (x ^ (a - 1) * Real.exp (-((r - t) * x)))
    have hexp :
        Real.exp (-(r * x)) * Real.exp (t * x) =
          Real.exp (-((r - t) * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      ((r ^ a / Real.Gamma a * x ^ (a - 1)) *
          Real.exp (-(r * x))) * Real.exp (t * x) =
          r ^ a / Real.Gamma a * x ^ (a - 1) *
            (Real.exp (-(r * x)) * Real.exp (t * x)) := by ring
      _ = r ^ a / Real.Gamma a *
          (x ^ (a - 1) * Real.exp (-((r - t) * x))) := by
            rw [hexp]
            ring]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hrate]
  have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  field_simp [hGa]
  simp only [one_mul, div_eq_mul_inv]
  rw [Real.mul_rpow (le_of_lt hr) (inv_nonneg.mpr hrate.le)]



theorem d006348 :
    (1 / 2 : ℝ) ^ ((1 : ℝ) / 2) / Real.Gamma ((1 : ℝ) / 2)
      = (Real.sqrt (2 * Real.pi))⁻¹ := by
  rw [Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow]
  have htwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.sqrt_inv,
    Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ))]
  field_simp



theorem d006349 {z : ℝ} (hz : 0 < z) :
    (2 * z) * gammaPDFReal ((1 : ℝ) / 2) (1 / 2) (z ^ 2)
      = 2 * gaussianPDFReal 0 1 z := by
  rw [gammaPDFReal, if_pos (sq_nonneg z), _root_.GD.N0121.d006348]
  have hzsq : 0 < z ^ 2 := sq_pos_of_pos hz
  have hsqrt : (z ^ 2) ^ ((1 : ℝ) / 2) = z := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_pos hz]
  have hinv : (z ^ 2) ^ (-(1 : ℝ) / 2) = z⁻¹ := by
    rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg (le_of_lt hzsq), hsqrt]
  rw [show ((1 : ℝ) / 2 - 1) = -(1 : ℝ) / 2 by ring, hinv]
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  field_simp [hz.ne']



theorem d006350 (f : ℝ → ℝ) :
    (∫ z in Ioi 0, gaussianPDFReal 0 1 z * f (z ^ 2))
      = (1 / 2 : ℝ) *
          ∫ x in Ioi 0,
            gammaPDFReal ((1 : ℝ) / 2) (1 / 2) x * f x := by
  have h := integral_comp_rpow_Ioi_of_pos
    (g := fun x : ℝ ↦ gammaPDFReal ((1 : ℝ) / 2) (1 / 2) x * f x)
    (p := (2 : ℝ)) (by norm_num)
  have h' :
      (∫ z in Ioi 0,
          2 * (gaussianPDFReal 0 1 z * f (z ^ 2)))
        = ∫ x in Ioi 0,
            gammaPDFReal ((1 : ℝ) / 2) (1 / 2) x * f x := by
    convert h using 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    have hz' : 0 < z := hz
    norm_num only [smul_eq_mul, Real.rpow_one]
    have hd := _root_.GD.N0121.d006349 hz'
    calc
      2 * (gaussianPDFReal 0 1 z * f (z ^ 2)) =
          (2 * gaussianPDFReal 0 1 z) * f (z ^ 2) := by ring
      _ = ((2 * z) *
          gammaPDFReal ((1 : ℝ) / 2) (1 / 2) (z ^ 2)) * f (z ^ 2) := by
            exact congrArg (fun u : ℝ ↦ u * f (z ^ 2)) hd.symm
      _ = 2 * z *
          (gammaPDFReal ((1 : ℝ) / 2) (1 / 2) (z ^ 2) * f (z ^ 2)) := by
            ac_rfl
    all_goals
      have hp : z ^ (2 : ℝ) = z ^ (2 : ℕ) := Real.rpow_natCast z 2
      rw [hp]
  rw [integral_const_mul] at h'
  linarith

theorem d006351 (f : ℝ → ℝ) (z : ℝ) :
    gaussianPDFReal 0 1 (-z) * f ((-z) ^ 2)
      = gaussianPDFReal 0 1 z * f (z ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  ring_nf


theorem d006352 (f : ℝ → ℝ)
    (hf : Integrable
      (fun z : ℝ ↦ gaussianPDFReal 0 1 z * f (z ^ 2))) :
    (∫ z : ℝ, gaussianPDFReal 0 1 z * f (z ^ 2))
      = ∫ x in Ioi 0,
          gammaPDFReal ((1 : ℝ) / 2) (1 / 2) x * f x := by
  let w : ℝ → ℝ := fun z ↦ gaussianPDFReal 0 1 z * f (z ^ 2)
  have hneg : (∫ z in Iic 0, w z) = ∫ z in Ioi 0, w z := by
    conv_lhs => rw [← neg_zero]
    rw [← integral_comp_neg_Ioi (c := 0) w]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z _
    exact _root_.GD.N0121.d006351 f z
  have hsplit := integral_add_compl (s := Ioi (0 : ℝ))
    measurableSet_Ioi (show Integrable w from hf)
  rw [compl_Ioi, hneg] at hsplit
  have hpos := _root_.GD.N0121.d006350 f
  change (∫ z : ℝ, w z) =
    ∫ x in Ioi 0,
      gammaPDFReal ((1 : ℝ) / 2) (1 / 2) x * f x
  linarith



theorem d006353 (f : ℝ → ℝ) :
    (∫ x : ℝ, f x ∂_root_.GD.N0121.d006346 1)
      = ∫ x in Ioi 0,
          gammaPDFReal ((1 : ℝ) / 2) (1 / 2) x * f x := by
  have hpdf : Measurable (gammaPDF ((1 : ℝ) / 2) (1 / 2)) :=
    (measurable_gammaPDFReal ((1 : ℝ) / 2) (1 / 2)).ennreal_ofReal
  rw [_root_.GD.N0121.d006346, gammaMeasure]
  norm_num only [Nat.cast_one]
  rw [integral_withDensity_eq_integral_toReal_smul
      hpdf (ae_of_all _ fun x ↦ by simp [gammaPDF])]
  simp only [gammaPDF, smul_eq_mul]
  simp_rw [ENNReal.toReal_ofReal
    (gammaPDFReal_nonneg (by norm_num : 0 < (1 / 2 : ℝ))
      (by norm_num : 0 < (1 / 2 : ℝ)) _)]
  rw [← integral_Ici_eq_integral_Ioi]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hx' : x < 0 := by
    simpa only [mem_compl_iff, mem_Ici, not_le] using hx
  simp [gammaPDFReal, not_le.mpr hx']



theorem d006354
    (f : BoundedContinuousFunction ℝ ℝ) :
    (∫ z : ℝ, f (z ^ 2) ∂gaussianReal 0 1)
      = ∫ x : ℝ, f x ∂_root_.GD.N0121.d006346 1 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num),
    _root_.GD.N0121.d006353]
  simp only [smul_eq_mul]
  apply _root_.GD.N0121.d006352
  have hbase : Integrable (fun z : ℝ ↦ gaussianPDFReal 0 1 z) :=
    integrable_gaussianPDFReal 0 1
  exact hbase.mul_bdd
    ((f.continuous.comp (continuous_pow 2)).aestronglyMeasurable)
    (ae_of_all _ fun z ↦ f.norm_coe_le_norm (z ^ 2))


theorem d006355 :
    (gaussianReal 0 1).map (fun z : ℝ ↦ z ^ 2) = _root_.GD.N0121.d006346 1 := by
  letI : IsProbabilityMeasure (_root_.GD.N0121.d006346 1) := by
    unfold _root_.GD.N0121.d006346
    exact isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  calc
    (∫ x : ℝ, f x ∂(gaussianReal 0 1).map (fun z : ℝ ↦ z ^ 2)) =
        ∫ z : ℝ, f (z ^ 2) ∂gaussianReal 0 1 := by
          rw [integral_map
            (μ := gaussianReal 0 1)
            ((by fun_prop : Measurable (fun z : ℝ ↦ z ^ 2)).aemeasurable)
            f.continuous.aestronglyMeasurable]
    _ = ∫ x : ℝ, f x ∂_root_.GD.N0121.d006346 1 :=
      _root_.GD.N0121.d006354 f

end

end GD.N0121
