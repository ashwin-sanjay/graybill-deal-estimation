import GD.Module0641
import GD.Module0837
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

set_option warningAsError true











open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BoundedContinuousFunction

namespace GD
namespace N0228
namespace N0547
namespace N0779

noncomputable section

open _root_.GD.N0228.N0547.N0778

@[fun_prop]
theorem d012804 : Continuous _root_.GD.N0228.N0547.N0778.d009366 := by
  unfold _root_.GD.N0228.N0547.N0778.d009366
  fun_prop

@[fun_prop]
theorem d012805 : Measurable _root_.GD.N0155.d006306 := by
  unfold _root_.GD.N0155.d006306
  fun_prop

private theorem d012806 (a b : ℝ) :
    ∀ᵐ u ∂betaMeasure a b, u ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold betaMeasure betaPDF
  rw [ae_withDensity_iff
    ((measurable_betaPDFReal a b).ennreal_ofReal)]
  filter_upwards with u hu
  by_contra hnot
  have houtside : ¬(0 < u ∧ u < 1) := by
    simpa only [Set.mem_Ioo] using hnot
  simp [betaPDFReal, houtside] at hu

private theorem d012807
    {a r : ℝ} (_ha : 0 < a) (_hr : 0 < r) (g : ℝ → ℝ) :
    (∫ x, gammaPDFReal a r x * g x) =
      ∫ x in Set.Ioi (0 : ℝ), gammaPDFReal a r x * g x := by
  symm
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx hnot
  have hxle : x ≤ 0 := le_of_not_gt hnot
  have hxlt : x < 0 := lt_of_le_of_ne hxle hx
  simp [gammaPDFReal, not_le.mpr hxlt]

private theorem d012808
    {a b : ℝ} (g : ℝ → ℝ) :
    (∫ u, betaPDFReal a b u * g u) =
      ∫ u in Set.Ioo (0 : ℝ) 1, betaPDFReal a b u * g u := by
  symm
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards with u hu
  have houtside : ¬(0 < u ∧ u < 1) := by
    simpa only [Set.mem_Ioo] using hu
  simp [betaPDFReal, houtside]

private theorem d012809
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (f : ℝ × ℝ →ᵇ ℝ) :
    Integrable
      (fun p : ℝ × ℝ =>
        betaPDFReal a b p.1 * gammaPDFReal (a + b) r p.2 *
          f (_root_.GD.N0228.N0547.N0778.d009366 p)) := by
  have hpdf : Integrable
      (fun p : ℝ × ℝ =>
        betaPDFReal a b p.1 * gammaPDFReal (a + b) r p.2) :=
    (_root_.GD.N0232.N0720.N1091.d012772
      ha hb).mul_prod
      (_root_.GD.N0232.N0719.N0954.d009352
        (add_pos ha hb) hr)
  apply hpdf.norm.const_mul ‖f‖ |>.mono'
    (hpdf.aestronglyMeasurable.mul
      ((f.continuous.measurable.comp
        _root_.GD.N0228.N0547.N0778.d009368).aestronglyMeasurable))
  filter_upwards with p
  change
    ‖(betaPDFReal a b p.1 * gammaPDFReal (a + b) r p.2) *
        f (_root_.GD.N0228.N0547.N0778.d009366 p)‖ ≤
      ‖f‖ * ‖betaPDFReal a b p.1 * gammaPDFReal (a + b) r p.2‖
  rw [norm_mul]
  calc
    ‖betaPDFReal a b p.1 * gammaPDFReal (a + b) r p.2‖ *
          ‖f (_root_.GD.N0228.N0547.N0778.d009366 p)‖ ≤
        ‖betaPDFReal a b p.1 * gammaPDFReal (a + b) r p.2‖ * ‖f‖ :=
      mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)
    _ = ‖f‖ *
          ‖betaPDFReal a b p.1 * gammaPDFReal (a + b) r p.2‖ := by ring


theorem d012810
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (f : ℝ × ℝ →ᵇ ℝ) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        (gammaPDFReal a r (_root_.GD.N0228.N0547.N0778.d009366 p).1 *
            gammaPDFReal b r (_root_.GD.N0228.N0547.N0778.d009366 p).2 *
            f (_root_.GD.N0228.N0547.N0778.d009366 p)) * p.2)
      _root_.GD.N0155.d006307 := by
  apply (_root_.GD.N0228.N0547.N0779.d012809 ha hb hr f).integrableOn.congr
  have hS : MeasurableSet _root_.GD.N0155.d006307 :=
    measurableSet_Ioo.prod measurableSet_Ioi
  apply (ae_restrict_iff' hS).2
  filter_upwards with p hp
  obtain ⟨⟨hu0, hu1⟩, hT⟩ := hp
  rw [show
      gammaPDFReal a r (_root_.GD.N0228.N0547.N0778.d009366 p).1 *
            gammaPDFReal b r (_root_.GD.N0228.N0547.N0778.d009366 p).2 *
              f (_root_.GD.N0228.N0547.N0778.d009366 p) * p.2 =
        (gammaPDFReal a r (p.1 * p.2) *
            gammaPDFReal b r ((1 - p.1) * p.2) * p.2) *
              f (_root_.GD.N0228.N0547.N0778.d009366 p) by
      simp only [_root_.GD.N0228.N0547.N0778.d009366]
      ring]
  rw [← _root_.GD.N0228.N0547.N0778.d009372
    ha hb hr hu0 hu1 hT]



theorem d012811
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (f : ℝ × ℝ →ᵇ ℝ) :
    (∫ p, f (_root_.GD.N0228.N0547.N0778.d009366 p)
        ∂(betaMeasure a b).prod (gammaMeasure (a + b) r)) =
      ∫ q, f q ∂(gammaMeasure a r).prod (gammaMeasure b r) := by
  letI : IsProbabilityMeasure (betaMeasure a b) :=
    isProbabilityMeasureBeta ha hb
  letI : IsProbabilityMeasure (gammaMeasure (a + b) r) :=
    isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  letI : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  letI : IsProbabilityMeasure (gammaMeasure b r) :=
    isProbabilityMeasure_gammaMeasure hb hr
  let fs : ℝ × ℝ →ᵇ ℝ :=
    f.compContinuous ⟨_root_.GD.N0228.N0547.N0778.d009366, _root_.GD.N0228.N0547.N0779.d012804⟩
  change
    (∫ p, fs p ∂(betaMeasure a b).prod (gammaMeasure (a + b) r)) = _
  rw [integral_prod _ (fs.integrable _)]
  rw [integral_prod _ (f.integrable _)]
  simp_rw [_root_.GD.N0232.N0719.N0954.d009351
    (add_pos ha hb) hr]
  rw [_root_.GD.N0235.d004041 ha hb]
  simp_rw [_root_.GD.N0232.N0719.N0954.d009351
    hb hr]
  rw [_root_.GD.N0232.N0719.N0954.d009351
    ha hr]
  rw [_root_.GD.N0228.N0547.N0779.d012808]
  simp_rw [_root_.GD.N0228.N0547.N0779.d012807 (add_pos ha hb) hr]
  rw [_root_.GD.N0228.N0547.N0779.d012807 ha hr]
  simp_rw [_root_.GD.N0228.N0547.N0779.d012807 hb hr]
  let G : ℝ × ℝ → ℝ := fun q =>
    gammaPDFReal a r q.1 * gammaPDFReal b r q.2 * f q
  have hpolar :
      (∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), G (x, y)) =
        ∫ u in (0 : ℝ)..1, ∫ T in Set.Ioi (0 : ℝ),
          G (u * T, (1 - u) * T) * T := by
    apply _root_.GD.N0155.d006316
    simpa only [G, _root_.GD.N0228.N0547.N0778.d009366, _root_.GD.N0155.d006305] using
      _root_.GD.N0228.N0547.N0779.d012810 ha hb hr f
  calc
    (∫ u in Set.Ioo (0 : ℝ) 1,
        betaPDFReal a b u *
          ∫ T in Set.Ioi (0 : ℝ),
            gammaPDFReal (a + b) r T * fs (u, T)) =
        ∫ u in Set.Ioo (0 : ℝ) 1,
          ∫ T in Set.Ioi (0 : ℝ),
            G (u * T, (1 - u) * T) * T := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      change
        betaPDFReal a b u *
            (∫ T in Set.Ioi (0 : ℝ),
              gammaPDFReal (a + b) r T * fs (u, T)) =
          ∫ T in Set.Ioi (0 : ℝ), G (u * T, (1 - u) * T) * T
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro T hT
      change
        betaPDFReal a b u *
            (gammaPDFReal (a + b) r T * f (_root_.GD.N0228.N0547.N0778.d009366 (u, T))) =
          G (u * T, (1 - u) * T) * T
      rw [show
          betaPDFReal a b u *
              (gammaPDFReal (a + b) r T * f (_root_.GD.N0228.N0547.N0778.d009366 (u, T))) =
            (betaPDFReal a b u * gammaPDFReal (a + b) r T) *
              f (_root_.GD.N0228.N0547.N0778.d009366 (u, T)) by ring]
      rw [_root_.GD.N0228.N0547.N0778.d009372
        ha hb hr hu.1 hu.2 hT]
      simp only [G, _root_.GD.N0228.N0547.N0778.d009366]
      ring
    _ = ∫ u in (0 : ℝ)..1, ∫ T in Set.Ioi (0 : ℝ),
          G (u * T, (1 - u) * T) * T := by
      rw [intervalIntegral.integral_of_le zero_le_one,
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    _ = ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
          G (x, y) := hpolar.symm
    _ = ∫ x in Set.Ioi (0 : ℝ),
          gammaPDFReal a r x *
            ∫ y in Set.Ioi (0 : ℝ), gammaPDFReal b r y * f (x, y) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _hx
      change
        (∫ y in Set.Ioi (0 : ℝ), G (x, y)) =
          gammaPDFReal a r x *
            ∫ y in Set.Ioi (0 : ℝ), gammaPDFReal b r y * f (x, y)
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _hy
      simp only [G]
      ring



theorem d012812
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((betaMeasure a b).prod (gammaMeasure (a + b) r)).map
        _root_.GD.N0228.N0547.N0778.d009366 =
      (gammaMeasure a r).prod (gammaMeasure b r) := by
  letI : IsProbabilityMeasure (betaMeasure a b) :=
    isProbabilityMeasureBeta ha hb
  letI : IsProbabilityMeasure (gammaMeasure (a + b) r) :=
    isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  letI : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  letI : IsProbabilityMeasure (gammaMeasure b r) :=
    isProbabilityMeasure_gammaMeasure hb hr
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map _root_.GD.N0228.N0547.N0778.d009368.aemeasurable
    f.continuous.aestronglyMeasurable]
  exact _root_.GD.N0228.N0547.N0779.d012811 ha hb hr f





theorem d012813
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((gammaMeasure a r).prod (gammaMeasure b r)).map _root_.GD.N0155.d006306 =
      (betaMeasure a b).prod (gammaMeasure (a + b) r) := by
  let mu := (betaMeasure a b).prod (gammaMeasure (a + b) r)
  have hsupport : ∀ᵐ p ∂mu, p ∈ _root_.GD.N0155.d006307 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_Ioo.prod measurableSet_Ioi)).2
    filter_upwards [_root_.GD.N0228.N0547.N0779.d012806 a b] with u hu
    filter_upwards [_root_.GD.N0232.N0720.N1091.d012773
      (add_pos ha hb) hr] with T hT
    exact ⟨hu, hT⟩
  calc
    ((gammaMeasure a r).prod (gammaMeasure b r)).map _root_.GD.N0155.d006306 =
        (mu.map _root_.GD.N0228.N0547.N0778.d009366).map _root_.GD.N0155.d006306 := by
      rw [_root_.GD.N0228.N0547.N0779.d012812 ha hb hr]
    _ = mu.map (_root_.GD.N0155.d006306 ∘ _root_.GD.N0228.N0547.N0778.d009366) := by
      rw [Measure.map_map _root_.GD.N0228.N0547.N0779.d012805
        _root_.GD.N0228.N0547.N0778.d009368]
    _ = mu.map id := by
      apply Measure.map_congr
      filter_upwards [hsupport] with p hp
      exact _root_.GD.N0155.d006309 hp
    _ = mu := Measure.map_id




theorem d012814
    {d : ℕ} (hd : 1 < d) :
    ((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod (_root_.GD.N0228.N0547.N0778.d009365 d)).map
        _root_.GD.N0228.N0547.N0778.d009366 =
      (_root_.GD.N0228.N0547.N0778.d009365 1).prod
        (gammaMeasure (((d : ℝ) - 1) / 2) (1 / 2)) := by
  have hdR : (1 : ℝ) < d := by exact_mod_cast hd
  have hb : 0 < ((d : ℝ) - 1) / 2 := by positivity
  have h := _root_.GD.N0228.N0547.N0779.d012812
    (a := (1 / 2 : ℝ)) (b := ((d : ℝ) - 1) / 2)
    (r := 1 / 2) (by norm_num) hb (by norm_num)
  unfold _root_.GD.N0228.N0547.N0778.d009365 at h ⊢
  convert h using 1 <;> ring

end

end N0779
end N0547
end N0228
end GD

#print axioms _root_.GD.N0228.N0547.N0779.d012810
#print axioms _root_.GD.N0228.N0547.N0779.d012811
#print axioms _root_.GD.N0228.N0547.N0779.d012812
#print axioms _root_.GD.N0228.N0547.N0779.d012813
#print axioms _root_.GD.N0228.N0547.N0779.d012814
