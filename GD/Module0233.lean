import GD.Module0232
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.Distributions.Cauchy






















namespace GD.N0228.N0547.N0782

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Real

noncomputable section


def d003364 (k : ℝ) : ℝ :=
  (cauchyMeasure 0 1).real (Icc (-k) k)



private theorem d003365 (k : ℝ) :
    _root_.GD.N0228.N0547.N0782.d003364 k =
      ∫ x in Icc (-k) k, cauchyPDFReal 0 1 x := by
  rw [_root_.GD.N0228.N0547.N0782.d003364, cauchyMeasure_of_scale_ne_zero 0 (by norm_num),
    measureReal_def, withDensity_apply _ measurableSet_Icc]
  have hfi : IntegrableOn (cauchyPDFReal 0 1) (Icc (-k) k) :=
    (integrable_cauchyPDFReal 0).integrableOn
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc (-k) k)]
      cauchyPDFReal 0 1 :=
    Filter.Eventually.of_forall fun x => (cauchyPDF_pos 0 (by norm_num) x).le
  have hof := ofReal_integral_eq_lintegral_ofReal hfi hnonneg
  have hint_nonneg : 0 ≤ ∫ x in Icc (-k) k, cauchyPDFReal 0 1 x :=
    integral_nonneg_of_ae hnonneg
  calc
    (∫⁻ a in Icc (-k) k, cauchyPDF 0 1 a).toReal =
        (ENNReal.ofReal (∫ x in Icc (-k) k, cauchyPDFReal 0 1 x)).toReal := by
      apply congrArg ENNReal.toReal
      simpa only [cauchyPDF] using hof.symm
    _ = ∫ x in Icc (-k) k, cauchyPDFReal 0 1 x :=
      ENNReal.toReal_ofReal hint_nonneg


theorem d003366
    {k : ℝ} (hk : 0 ≤ k) :
    _root_.GD.N0228.N0547.N0782.d003364 k = 2 / Real.pi * Real.arctan k := by
  rw [_root_.GD.N0228.N0547.N0782.d003365,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (neg_le_self hk)]
  simp_rw [cauchyPDFReal_def]
  simp only [NNReal.coe_one, sub_zero, one_pow]
  rw [show (fun x : ℝ => Real.pi⁻¹ * 1 * (x ^ 2 + 1)⁻¹) =
      fun x : ℝ => Real.pi⁻¹ * (1 + x ^ 2)⁻¹ by
        funext x
        congr 2 <;> ring,
    intervalIntegral.integral_const_mul,
    integral_inv_one_add_sq,
    Real.arctan_neg]
  field_simp [Real.pi_ne_zero]
  ring


def d003367 (p : ℝ) : ℝ :=
  Real.tan (Real.pi * p / 2)

theorem d003368
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    0 ≤ _root_.GD.N0228.N0547.N0782.d003367 p := by
  apply Real.tan_nonneg_of_nonneg_of_le_pi_div_two
  · exact div_nonneg (mul_nonneg Real.pi_pos.le hp0) (by norm_num)
  · apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [mul_le_mul_of_nonneg_left hp1.le Real.pi_pos.le]

theorem d003369
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    Real.arctan (_root_.GD.N0228.N0547.N0782.d003367 p) = Real.pi * p / 2 := by
  apply Real.arctan_tan
  · have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith
  · have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith



theorem d003370
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    _root_.GD.N0228.N0547.N0782.d003364 (_root_.GD.N0228.N0547.N0782.d003367 p) = p := by
  rw [_root_.GD.N0228.N0547.N0782.d003366
      (_root_.GD.N0228.N0547.N0782.d003368 hp0 hp1),
    _root_.GD.N0228.N0547.N0782.d003369 hp0 hp1]
  field_simp [Real.pi_ne_zero]





theorem d003371
    {p M : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hM : _root_.GD.N0228.N0547.N0782.d003367 p ≤ M) :
    ∃ μ : Measure ℝ,
      μ Set.univ = 1 ∧
      μ (Icc 0 M) = 1 ∧
      ∫ k, (2 / Real.pi) * Real.arctan k ∂μ = p := by
  refine ⟨Measure.dirac (_root_.GD.N0228.N0547.N0782.d003367 p), by simp, ?_, ?_⟩
  · have hmem : _root_.GD.N0228.N0547.N0782.d003367 p ∈ Icc 0 M :=
      ⟨_root_.GD.N0228.N0547.N0782.d003368 hp0 hp1, hM⟩
    rw [Measure.dirac_apply' _ measurableSet_Icc,
      Set.indicator_of_mem hmem]
    rfl
  · rw [integral_dirac]
    rw [_root_.GD.N0228.N0547.N0782.d003369 hp0 hp1]
    field_simp [Real.pi_ne_zero]



def d003372 (k : ℝ) : Set (ℝ × ℝ) :=
  {z | |z.1| ≤ k * |z.2|}



def d003373 (z : ℝ × ℝ) : ℝ := z.1 / z.2

theorem d003374 : Measurable _root_.GD.N0228.N0547.N0782.d003373 :=
  measurable_fst.div measurable_snd

theorem d003375 (k : ℝ) :
    MeasurableSet (_root_.GD.N0228.N0547.N0782.d003372 k) := by
  unfold _root_.GD.N0228.N0547.N0782.d003372
  exact measurableSet_le measurable_fst.abs
    (measurable_const.mul measurable_snd.abs)



theorem d003376
    {k : ℝ} {z : ℝ × ℝ} (hz : z.2 ≠ 0) :
    z ∈ _root_.GD.N0228.N0547.N0782.d003372 k ↔ _root_.GD.N0228.N0547.N0782.d003373 z ∈ Icc (-k) k := by
  rw [_root_.GD.N0228.N0547.N0782.d003372, mem_setOf_eq, _root_.GD.N0228.N0547.N0782.d003373, mem_Icc, ← abs_le,
    abs_div]
  have hy : 0 < |z.2| := abs_pos.mpr hz
  exact (div_le_iff₀ hy).symm


structure d003377 (μ : Measure (ℝ × ℝ)) : Prop where
  second_ne_zero_ae : ∀ᵐ z ∂μ, z.2 ≠ 0
  ratio_law : Measure.map _root_.GD.N0228.N0547.N0782.d003373 μ = cauchyMeasure 0 1




def d003378 (t : ℝ) : ℝ × ℝ := (t, 1)

theorem d003379 : Measurable _root_.GD.N0228.N0547.N0782.d003378 := by
  exact measurable_id.prodMk measurable_const

def d003380 : Measure (ℝ × ℝ) :=
  Measure.map _root_.GD.N0228.N0547.N0782.d003378 (cauchyMeasure 0 1)

theorem d003381 :
    _root_.GD.N0228.N0547.N0782.d003377 _root_.GD.N0228.N0547.N0782.d003380 := by
  constructor
  · rw [_root_.GD.N0228.N0547.N0782.d003380]
    apply (ae_map_iff _root_.GD.N0228.N0547.N0782.d003379.aemeasurable
      (by measurability : MeasurableSet {z : ℝ × ℝ | z.2 ≠ 0})).2
    exact Filter.Eventually.of_forall fun _ => by norm_num [_root_.GD.N0228.N0547.N0782.d003378]
  · rw [_root_.GD.N0228.N0547.N0782.d003380,
      Measure.map_map _root_.GD.N0228.N0547.N0782.d003374 _root_.GD.N0228.N0547.N0782.d003379]
    simp [Function.comp_def, _root_.GD.N0228.N0547.N0782.d003373, _root_.GD.N0228.N0547.N0782.d003378]




theorem d003382
    {μ : Measure (ℝ × ℝ)} (hμ : _root_.GD.N0228.N0547.N0782.d003377 μ)
    {k : ℝ} (hk : 0 ≤ k) :
    μ.real (_root_.GD.N0228.N0547.N0782.d003372 k) = 2 / Real.pi * Real.arctan k := by
  have hset : _root_.GD.N0228.N0547.N0782.d003372 k =ᵐ[μ]
      _root_.GD.N0228.N0547.N0782.d003373 ⁻¹' Icc (-k) k := by
    filter_upwards [hμ.second_ne_zero_ae] with z hz
    exact propext (_root_.GD.N0228.N0547.N0782.d003376 hz)
  have hmeas : MeasurableSet (Icc (-k) k) := measurableSet_Icc
  calc
    μ.real (_root_.GD.N0228.N0547.N0782.d003372 k) =
        (cauchyMeasure 0 1).real (Icc (-k) k) := by
      rw [measureReal_def, measure_congr hset,
        ← Measure.map_apply _root_.GD.N0228.N0547.N0782.d003374 hmeas,
        hμ.ratio_law, ← measureReal_def]
    _ = 2 / Real.pi * Real.arctan k := by
      change _root_.GD.N0228.N0547.N0782.d003364 k = 2 / Real.pi * Real.arctan k
      exact _root_.GD.N0228.N0547.N0782.d003366 hk


theorem d003383
    {μ : Measure (ℝ × ℝ)} (hμ : _root_.GD.N0228.N0547.N0782.d003377 μ)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    μ.real (_root_.GD.N0228.N0547.N0782.d003372 (_root_.GD.N0228.N0547.N0782.d003367 p)) = p := by
  rw [_root_.GD.N0228.N0547.N0782.d003382 hμ
      (_root_.GD.N0228.N0547.N0782.d003368 hp0 hp1),
    _root_.GD.N0228.N0547.N0782.d003369 hp0 hp1]
  field_simp [Real.pi_ne_zero]

end

end GD.N0228.N0547.N0782

#print axioms _root_.GD.N0228.N0547.N0782.d003366
#print axioms _root_.GD.N0228.N0547.N0782.d003370
#print axioms _root_.GD.N0228.N0547.N0782.d003371
#print axioms _root_.GD.N0228.N0547.N0782.d003381
#print axioms _root_.GD.N0228.N0547.N0782.d003382
#print axioms _root_.GD.N0228.N0547.N0782.d003383
