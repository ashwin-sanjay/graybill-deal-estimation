import GD.Module0360
import GD.Module1285














set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0106.N0428.N0765.N1521
noncomputable section
open _root_.GD.N0235 _root_.GD.N0106.N0428.N0765.N1539 _root_.GD.N0106.N0428.N0765.N1529

def d020840 : Measure (ℝ × ℝ) :=
  (betaMeasure ((3 : ℝ) / 2) 10).prod (betaMeasure 5 5)

def d020841 (p : Fin 3 → ℝ) : ℝ × ℝ := (p 0, p 1 / (p 1 + p 2))

@[fun_prop] theorem d020842 : Measurable _root_.GD.N0106.N0428.N0765.N1521.d020841 := by
  unfold _root_.GD.N0106.N0428.N0765.N1521.d020841
  fun_prop

theorem d020843 {p : ℝ × ℝ} (hp : p.1 < 1) :
    _root_.GD.N0106.N0428.N0765.N1521.d020841 (_root_.GD.N0235.d004247 p) = p := by
  apply Prod.ext
  · simp [_root_.GD.N0106.N0428.N0765.N1521.d020841, _root_.GD.N0235.d004247]
  · change (1 - p.1) * p.2 / ((1 - p.1) * p.2 + (1 - p.1) * (1 - p.2)) = p.2
    rw [show (1 - p.1) * p.2 + (1 - p.1) * (1 - p.2) = 1 - p.1 by ring]
    have h : 1 - p.1 ≠ 0 := (sub_pos.mpr hp).ne'
    field_simp [h]

theorem d020844 : _root_.GD.N0106.N0428.N0765.N1521.d020840.map _root_.GD.N0235.d004247 = _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1521.d020840, _root_.GD.N0106.N0428.N0765.N1529.d020798, _root_.GD.N0235.d004250]

theorem d020845 : IsProbabilityMeasure _root_.GD.N0106.N0428.N0765.N1521.d020840 := by
  letI : IsProbabilityMeasure (betaMeasure ((3 : ℝ) / 2) 10) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (betaMeasure (5 : ℝ) 5) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  unfold _root_.GD.N0106.N0428.N0765.N1521.d020840
  infer_instance

theorem d020846 :
    ∀ᵐ p ∂_root_.GD.N0106.N0428.N0765.N1521.d020840, p ∈ (Ioo (0 : ℝ) 1) ×ˢ Ioo 0 1 := by
  letI : IsProbabilityMeasure (betaMeasure (5 : ℝ) 5) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.prod measurableSet_Ioo)).2
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1539.d005357 ((3 : ℝ) / 2) 10] with t ht
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1539.d005357 5 5] with s hs
  exact ⟨ht, hs⟩


theorem d020847 : _root_.GD.N0106.N0428.N0765.N1529.d020798.map _root_.GD.N0106.N0428.N0765.N1521.d020841 = _root_.GD.N0106.N0428.N0765.N1521.d020840 := by
  rw [← _root_.GD.N0106.N0428.N0765.N1521.d020844, Measure.map_map _root_.GD.N0106.N0428.N0765.N1521.d020842 _root_.GD.N0235.d004248]
  calc
    _root_.GD.N0106.N0428.N0765.N1521.d020840.map (_root_.GD.N0106.N0428.N0765.N1521.d020841 ∘ _root_.GD.N0235.d004247) = _root_.GD.N0106.N0428.N0765.N1521.d020840.map id := by
      apply Measure.map_congr
      filter_upwards [_root_.GD.N0106.N0428.N0765.N1521.d020846] with p hp
      exact _root_.GD.N0106.N0428.N0765.N1521.d020843 hp.1.2
    _ = _root_.GD.N0106.N0428.N0765.N1521.d020840 := Measure.map_id (μ := _root_.GD.N0106.N0428.N0765.N1521.d020840)

def d020848 (eta : ℝ) : _root_.GD.N0106.N0428.N0765.N1611.d012588 → ℝ × ℝ :=
  _root_.GD.N0106.N0428.N0765.N1521.d020841 ∘ _root_.GD.N0106.N0428.N0765.N1633.d014080 eta

theorem d020849 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta).map (_root_.GD.N0106.N0428.N0765.N1521.d020848 eta) = _root_.GD.N0106.N0428.N0765.N1521.d020840 := by
  rw [_root_.GD.N0106.N0428.N0765.N1521.d020848, ← Measure.map_map _root_.GD.N0106.N0428.N0765.N1521.d020842
    (_root_.GD.N0106.N0428.N0765.N1633.d014085 eta), _root_.GD.N0106.N0428.N0765.N1633.d014101 location eta heta]
  exact _root_.GD.N0106.N0428.N0765.N1521.d020847

theorem d020850 (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (w v : ℝ → ℝ) (hw : Measurable w) (hv : Measurable v)
    (hw0 : ∀ x ∈ s, 0 ≤ w x) (hv0 : ∀ y ∈ t, 0 ≤ v y) (f : ℝ × ℝ → ℝ) :
    (∫ p, f p ∂(_root_.GD.N0106.N0428.N0765.N1539.d005352 s w).prod (_root_.GD.N0106.N0428.N0765.N1539.d005352 t v)) =
      ∫ p in s ×ˢ t, w p.1 * v p.2 * f p := by
  simp only [_root_.GD.N0106.N0428.N0765.N1539.d005352]
  rw [prod_withDensity hw.ennreal_ofReal hv.ennreal_ofReal,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top),
    Measure.prod_restrict]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (hs.prod ht)] with p hp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw0 p.1 hp.1),
    ENNReal.toReal_ofReal (hv0 p.2 hp.2), smul_eq_mul]

theorem d020851
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (w v : ℝ → ℝ) (hw : Measurable w) (hv : Measurable v)
    (hw0 : ∀ x ∈ s, 0 ≤ w x) (hv0 : ∀ y ∈ t, 0 ≤ v y) (f : ℝ × ℝ → ℝ) :
    Integrable f ((_root_.GD.N0106.N0428.N0765.N1539.d005352 s w).prod (_root_.GD.N0106.N0428.N0765.N1539.d005352 t v)) ↔
      IntegrableOn (fun p => w p.1 * v p.2 * f p) (s ×ˢ t) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1539.d005352]
  rw [prod_withDensity hw.ennreal_ofReal hv.ennreal_ofReal,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top),
    Measure.prod_restrict]
  apply integrable_congr
  filter_upwards [ae_restrict_mem (hs.prod ht)] with p hp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw0 p.1 hp.1),
    ENNReal.toReal_ofReal (hv0 p.2 hp.2), smul_eq_mul]

def d020852 : Measure (ℝ × ℝ) :=
  (_root_.GD.N0106.N0428.N0765.N1539.d005352 (Ioo 0 1) _root_.GD.N0106.N0428.N0765.N1539.d005362).prod (betaMeasure 5 5)

def d020853 (p : ℝ × ℝ) : Fin 3 → ℝ := _root_.GD.N0235.d004247 (p.1 ^ 2, p.2)

@[fun_prop] theorem d020854 : Measurable _root_.GD.N0106.N0428.N0765.N1521.d020853 := by
  unfold _root_.GD.N0106.N0428.N0765.N1521.d020853
  exact _root_.GD.N0235.d004248.comp (by fun_prop)

theorem d020855 : _root_.GD.N0106.N0428.N0765.N1521.d020852.map _root_.GD.N0106.N0428.N0765.N1521.d020853 = _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  letI : IsProbabilityMeasure (betaMeasure ((3 : ℝ) / 2) 10) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure ((_root_.GD.N0106.N0428.N0765.N1539.d005352 (Ioo 0 1) _root_.GD.N0106.N0428.N0765.N1539.d005362).map
      (fun y : ℝ => y ^ 2)) := by
    rw [_root_.GD.N0106.N0428.N0765.N1539.d005366]
    infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0106.N0428.N0765.N1539.d005352 (Ioo 0 1) _root_.GD.N0106.N0428.N0765.N1539.d005362) :=
    Measure.isProbabilityMeasure_of_map (fun y : ℝ => y ^ 2)
  letI : IsProbabilityMeasure (betaMeasure (5 : ℝ) 5) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  have hfun : _root_.GD.N0106.N0428.N0765.N1521.d020853 = _root_.GD.N0235.d004247 ∘ Prod.map (fun y : ℝ => y ^ 2) id := rfl
  rw [hfun, ← Measure.map_map _root_.GD.N0235.d004248 (by fun_prop), _root_.GD.N0106.N0428.N0765.N1521.d020852,
    ← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    _root_.GD.N0106.N0428.N0765.N1539.d005366, Measure.map_id]
  exact _root_.GD.N0106.N0428.N0765.N1521.d020844

def d020856 (p : ℝ × ℝ) : ℝ :=
  ((4849845 / 65536 : ℝ) * p.1 ^ 2 * (1 - p.1 ^ 2) ^ 9) *
    (630 * p.2 ^ 4 * (1 - p.2) ^ 4)

theorem d020857 {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    betaPDFReal 5 5 s = 630 * s ^ 4 * (1 - s) ^ 4 := by
  rw [betaPDFReal, if_pos (show 0 < s ∧ s < 1 from hs), _root_.GD.N0106.N0428.N0765.N1539.d005360]
  norm_num [Real.rpow_natCast]

theorem d020858 {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1539.d005362 y := by
  have hy2 : y ^ 2 < 1 := by nlinarith [hy.2, mul_pos hy.1 (sub_pos.mpr hy.2)]
  unfold _root_.GD.N0106.N0428.N0765.N1539.d005362
  positivity

theorem d020859 (f : (Fin 3 → ℝ) → ℝ) (hf : Measurable f) :
    (∫ p, f p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) =
      ∫ p in (Ioo (0 : ℝ) 1) ×ˢ Ioo 0 1, _root_.GD.N0106.N0428.N0765.N1521.d020856 p * f (_root_.GD.N0106.N0428.N0765.N1521.d020853 p) := by
  rw [← _root_.GD.N0106.N0428.N0765.N1521.d020855,
    integral_map_of_stronglyMeasurable _root_.GD.N0106.N0428.N0765.N1521.d020854 hf.stronglyMeasurable,
    _root_.GD.N0106.N0428.N0765.N1521.d020852, _root_.GD.N0106.N0428.N0765.N1539.d005356,
    _root_.GD.N0106.N0428.N0765.N1521.d020850 _ _ measurableSet_Ioo measurableSet_Ioo _ _
      (by unfold _root_.GD.N0106.N0428.N0765.N1539.d005362; fun_prop) (measurable_betaPDFReal _ _)
      (fun _ hy => _root_.GD.N0106.N0428.N0765.N1521.d020858 hy)
      (fun s _ => _root_.GD.N0235.d004040 (by norm_num) (by norm_num) s)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
  rw [_root_.GD.N0106.N0428.N0765.N1521.d020857 hp.2]
  rfl

theorem d020860 (f : (Fin 3 → ℝ) → ℝ) (hf : Measurable f) :
    Integrable f _root_.GD.N0106.N0428.N0765.N1529.d020798 ↔
      IntegrableOn (fun p => _root_.GD.N0106.N0428.N0765.N1521.d020856 p * f (_root_.GD.N0106.N0428.N0765.N1521.d020853 p))
        ((Ioo (0 : ℝ) 1) ×ˢ Ioo 0 1) := by
  rw [← _root_.GD.N0106.N0428.N0765.N1521.d020855, integrable_map_measure hf.aestronglyMeasurable
    _root_.GD.N0106.N0428.N0765.N1521.d020854.aemeasurable, _root_.GD.N0106.N0428.N0765.N1521.d020852, _root_.GD.N0106.N0428.N0765.N1539.d005356,
    _root_.GD.N0106.N0428.N0765.N1521.d020851 _ _ measurableSet_Ioo measurableSet_Ioo _ _
      (by unfold _root_.GD.N0106.N0428.N0765.N1539.d005362; fun_prop) (measurable_betaPDFReal _ _)
      (fun _ hy => _root_.GD.N0106.N0428.N0765.N1521.d020858 hy)
      (fun s _ => _root_.GD.N0235.d004040 (by norm_num) (by norm_num) s)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
  rw [_root_.GD.N0106.N0428.N0765.N1521.d020857 hp.2]
  rfl

def d020861 : Measure (ℝ × ℝ) :=
  (_root_.GD.N0106.N0428.N0765.N1539.d005352 univ (_root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10)).prod
    (_root_.GD.N0106.N0428.N0765.N1539.d005352 univ (_root_.GD.N0106.N0428.N0765.N1539.d005373 5 5))

def d020862 (p : ℝ × ℝ) : Fin 3 → ℝ :=
  _root_.GD.N0235.d004247 (Real.sigmoid p.1, Real.sigmoid p.2)

@[fun_prop] theorem d020863 : Measurable _root_.GD.N0106.N0428.N0765.N1521.d020862 := by
  unfold _root_.GD.N0106.N0428.N0765.N1521.d020862
  exact _root_.GD.N0235.d004248.comp (by fun_prop)

theorem d020864 : _root_.GD.N0106.N0428.N0765.N1521.d020861.map _root_.GD.N0106.N0428.N0765.N1521.d020862 = _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  letI : IsProbabilityMeasure (betaMeasure ((3 : ℝ) / 2) 10) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (_root_.GD.N0106.N0428.N0765.N1539.d005352 univ (_root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10)) := by
    rw [← _root_.GD.N0106.N0428.N0765.N1539.d005378 (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (0 : ℝ) < 10)]
    exact Measure.isProbabilityMeasure_map (by unfold _root_.GD.N0106.N0428.N0765.N1539.d005368; fun_prop)
  letI : IsProbabilityMeasure (betaMeasure (5 : ℝ) 5) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (_root_.GD.N0106.N0428.N0765.N1539.d005352 univ (_root_.GD.N0106.N0428.N0765.N1539.d005373 (5 : ℝ) 5)) := by
    rw [← _root_.GD.N0106.N0428.N0765.N1539.d005378 (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 5)]
    exact Measure.isProbabilityMeasure_map (by unfold _root_.GD.N0106.N0428.N0765.N1539.d005368; fun_prop)
  have hfun : _root_.GD.N0106.N0428.N0765.N1521.d020862 = _root_.GD.N0235.d004247 ∘ Prod.map Real.sigmoid Real.sigmoid := rfl
  rw [hfun, ← Measure.map_map _root_.GD.N0235.d004248 (by fun_prop), _root_.GD.N0106.N0428.N0765.N1521.d020861,
    ← Measure.map_prod_map _ _ continuous_sigmoid.measurable continuous_sigmoid.measurable,
    _root_.GD.N0106.N0428.N0765.N1539.d005377 (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (0 : ℝ) < 10),
    _root_.GD.N0106.N0428.N0765.N1539.d005377 (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 5)]
  exact _root_.GD.N0106.N0428.N0765.N1521.d020844

def d020865 (eta : ℝ) : _root_.GD.N0106.N0428.N0765.N1611.d012588 → ℝ × ℝ :=
  Prod.map _root_.GD.N0106.N0428.N0765.N1539.d005368 _root_.GD.N0106.N0428.N0765.N1539.d005368 ∘ _root_.GD.N0106.N0428.N0765.N1521.d020848 eta


theorem d020866 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta).map (_root_.GD.N0106.N0428.N0765.N1521.d020865 eta) = _root_.GD.N0106.N0428.N0765.N1521.d020861 := by
  letI : IsProbabilityMeasure (betaMeasure ((3 : ℝ) / 2) 10) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (ProbabilityTheory.betaMeasure (5 : ℝ) 5) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  rw [_root_.GD.N0106.N0428.N0765.N1521.d020865, ← Measure.map_map (by unfold _root_.GD.N0106.N0428.N0765.N1539.d005368; fun_prop)
    (by unfold _root_.GD.N0106.N0428.N0765.N1521.d020848; fun_prop), _root_.GD.N0106.N0428.N0765.N1521.d020849 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1521.d020840, ← Measure.map_prod_map _ _ (by unfold _root_.GD.N0106.N0428.N0765.N1539.d005368; fun_prop)
      (by unfold _root_.GD.N0106.N0428.N0765.N1539.d005368; fun_prop),
    _root_.GD.N0106.N0428.N0765.N1539.d005378 (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (0 : ℝ) < 10),
    _root_.GD.N0106.N0428.N0765.N1539.d005378 (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 5)]
  rfl


theorem d020867 (a b : ℝ) :
    Real.log (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 0 / (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 + _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2)) = a ∧
      Real.log (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 / _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2) = b := by
  constructor
  · change Real.log (Real.sigmoid a / ((1 - Real.sigmoid a) * Real.sigmoid b +
        (1 - Real.sigmoid a) * (1 - Real.sigmoid b))) = a
    rw [show (1 - Real.sigmoid a) * Real.sigmoid b +
        (1 - Real.sigmoid a) * (1 - Real.sigmoid b) = 1 - Real.sigmoid a by ring]
    exact _root_.GD.N0106.N0428.N0765.N1539.d005371 a
  · change Real.log (((1 - Real.sigmoid a) * Real.sigmoid b) /
        ((1 - Real.sigmoid a) * (1 - Real.sigmoid b))) = b
    rw [mul_div_mul_left _ _ (sub_pos.mpr (Real.sigmoid_lt_one a)).ne']
    exact _root_.GD.N0106.N0428.N0765.N1539.d005371 b

def d020868 (p : ℝ × ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 p.1 * _root_.GD.N0106.N0428.N0765.N1539.d005373 5 5 p.2

theorem d020869 (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1521.d020868 p =
      ((4849845 / 131072 : ℝ) * Real.exp (3 * p.1 / 2) /
        (1 + Real.exp p.1) ^ ((23 : ℝ) / 2)) *
      (630 * Real.exp (5 * p.2) / (1 + Real.exp p.2) ^ (10 : ℕ)) := by
  unfold _root_.GD.N0106.N0428.N0765.N1521.d020868 _root_.GD.N0106.N0428.N0765.N1539.d005373
  rw [_root_.GD.N0106.N0428.N0765.N1539.d005359, _root_.GD.N0106.N0428.N0765.N1539.d005360]
  norm_num only [show (3 : ℝ) / 2 + 10 = 23 / 2 by norm_num,
    show (5 : ℝ) + 5 = (10 : ℕ) by norm_num, Real.rpow_natCast, Real.rpow_ofNat]
  rw [show (3 : ℝ) / 2 * p.1 = 3 * p.1 / 2 by ring]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_div, inv_one]
  ring

theorem d020870 (f : (Fin 3 → ℝ) → ℝ) (hf : Measurable f) :
    (∫ p, f p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) = ∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1521.d020868 p * f (_root_.GD.N0106.N0428.N0765.N1521.d020862 p) := by
  rw [← _root_.GD.N0106.N0428.N0765.N1521.d020864,
    integral_map_of_stronglyMeasurable _root_.GD.N0106.N0428.N0765.N1521.d020863 hf.stronglyMeasurable,
    _root_.GD.N0106.N0428.N0765.N1521.d020861, _root_.GD.N0106.N0428.N0765.N1521.d020850 _ _ MeasurableSet.univ MeasurableSet.univ _ _
      (_root_.GD.N0106.N0428.N0765.N1539.d005374 _ _) (_root_.GD.N0106.N0428.N0765.N1539.d005374 _ _)
      (fun x _ => (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) x).le)
      (fun x _ => (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) x).le)]
  simp only [Set.univ_prod_univ, Measure.restrict_univ, _root_.GD.N0106.N0428.N0765.N1521.d020868]

theorem d020871 (f : (Fin 3 → ℝ) → ℝ) (hf : Measurable f) :
    Integrable f _root_.GD.N0106.N0428.N0765.N1529.d020798 ↔
      Integrable (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1521.d020868 p * f (_root_.GD.N0106.N0428.N0765.N1521.d020862 p)) := by
  rw [← _root_.GD.N0106.N0428.N0765.N1521.d020864, integrable_map_measure hf.aestronglyMeasurable
    _root_.GD.N0106.N0428.N0765.N1521.d020863.aemeasurable,
    _root_.GD.N0106.N0428.N0765.N1521.d020861, _root_.GD.N0106.N0428.N0765.N1521.d020851 _ _ MeasurableSet.univ MeasurableSet.univ _ _
      (_root_.GD.N0106.N0428.N0765.N1539.d005374 _ _) (_root_.GD.N0106.N0428.N0765.N1539.d005374 _ _)
      (fun x _ => (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) x).le)
      (fun x _ => (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) x).le)]
  simp only [IntegrableOn, Set.univ_prod_univ, Measure.restrict_univ, _root_.GD.N0106.N0428.N0765.N1521.d020868,
    Function.comp_apply]

theorem d020872 (f : (Fin 3 → ℝ) → ℝ) (hf : Measurable f)
    (hfi : Integrable f _root_.GD.N0106.N0428.N0765.N1529.d020798) :
    (∫ p, f p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) =
      ∫ a : ℝ, ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1521.d020868 (a, b) * f (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) := by
  rw [_root_.GD.N0106.N0428.N0765.N1521.d020870 f hf]
  exact integral_prod _ ((_root_.GD.N0106.N0428.N0765.N1521.d020871 f hf).1 hfi)

theorem d020873 :
    (∫ p in (Ioo (0 : ℝ) 1) ×ˢ Ioo 0 1, _root_.GD.N0106.N0428.N0765.N1521.d020856 p) = 1 := by
  letI : IsProbabilityMeasure _root_.GD.N0106.N0428.N0765.N1529.d020798 :=
    _root_.GD.N0235.d004251 (by norm_num) (by norm_num) (by norm_num)
  simpa using (_root_.GD.N0106.N0428.N0765.N1521.d020859 (fun _ => (1 : ℝ)) measurable_const).symm

theorem d020874 : (∫ p, _root_.GD.N0106.N0428.N0765.N1521.d020868 p) = 1 := by
  letI : IsProbabilityMeasure _root_.GD.N0106.N0428.N0765.N1529.d020798 :=
    _root_.GD.N0235.d004251 (by norm_num) (by norm_num) (by norm_num)
  simpa using (_root_.GD.N0106.N0428.N0765.N1521.d020870 (fun _ => (1 : ℝ)) measurable_const).symm


theorem d020875 (location eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta
        (_root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 11)) -
      _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1611.d012593 =
        ((1 + eta) / 11) *
          ∫ p, _root_.GD.N0106.N0428.N0765.N1521.d020868 p * _root_.GD.N0106.N0428.N0765.N1529.d020802 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 p) := by
  rw [_root_.GD.N0106.N0428.N0765.N1529.d020832 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1521.d020870 _ (_root_.GD.N0106.N0428.N0765.N1529.d020812 eta)]

theorem d020876 (eta : ℝ) (heta : 0 < eta) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0765.N1521.d020868 p * _root_.GD.N0106.N0428.N0765.N1529.d020802 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 p)) :=
  (_root_.GD.N0106.N0428.N0765.N1521.d020871 _ (_root_.GD.N0106.N0428.N0765.N1529.d020812 eta)).1
    (_root_.GD.N0106.N0428.N0765.N1529.d020829 eta heta)

theorem d020877 (eta : ℝ) (heta : 0 < eta) (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0765.N1521.d020868 p * _root_.GD.N0106.N0428.N0765.N1529.d020804 j eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 p)) :=
  (_root_.GD.N0106.N0428.N0765.N1521.d020871 _ (_root_.GD.N0106.N0428.N0765.N1529.d020814 j eta)).1
    (_root_.GD.N0106.N0428.N0765.N1529.d020830 j eta heta)

theorem d020878 (location eta : ℝ) (heta : 0 < eta)
    (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    _root_.GD.N0106.N0428.N0765.N1607.d012683 location eta j = ((1 + eta) / 11) *
      ∫ p, _root_.GD.N0106.N0428.N0765.N1521.d020868 p * _root_.GD.N0106.N0428.N0765.N1529.d020804 j eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 p) := by
  rw [_root_.GD.N0106.N0428.N0765.N1529.d020833 location eta heta j,
    _root_.GD.N0106.N0428.N0765.N1521.d020870 _ (_root_.GD.N0106.N0428.N0765.N1529.d020814 j eta)]

theorem d020879 (eta : ℝ) (heta : 0 < eta)
    (i j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0765.N1521.d020868 p * _root_.GD.N0106.N0428.N0765.N1529.d020805 i j eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 p)) :=
  (_root_.GD.N0106.N0428.N0765.N1521.d020871 _ (_root_.GD.N0106.N0428.N0765.N1529.d020815 i j eta)).1
    (_root_.GD.N0106.N0428.N0765.N1529.d020831 i j eta heta)

theorem d020880 (location eta : ℝ) (heta : 0 < eta)
    (i j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    _root_.GD.N0106.N0428.N0765.N1607.d012677 location eta i j = ((1 + eta) / 11) *
      ∫ p, _root_.GD.N0106.N0428.N0765.N1521.d020868 p * _root_.GD.N0106.N0428.N0765.N1529.d020805 i j eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 p) := by
  rw [_root_.GD.N0106.N0428.N0765.N1529.d020834 location eta heta i j,
    _root_.GD.N0106.N0428.N0765.N1521.d020870 _ (_root_.GD.N0106.N0428.N0765.N1529.d020815 i j eta)]


theorem d020881 (eta : ℝ) (heta : 0 < eta)
    (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    IntegrableOn (fun p => _root_.GD.N0106.N0428.N0765.N1521.d020856 p * _root_.GD.N0106.N0428.N0765.N1529.d020802 eta (_root_.GD.N0106.N0428.N0765.N1521.d020853 p))
        ((Ioo (0 : ℝ) 1) ×ˢ Ioo 0 1) ∧
      IntegrableOn (fun p => _root_.GD.N0106.N0428.N0765.N1521.d020856 p * _root_.GD.N0106.N0428.N0765.N1529.d020804 j eta (_root_.GD.N0106.N0428.N0765.N1521.d020853 p))
        ((Ioo (0 : ℝ) 1) ×ˢ Ioo 0 1) := by
  exact ⟨(_root_.GD.N0106.N0428.N0765.N1521.d020860 _ (_root_.GD.N0106.N0428.N0765.N1529.d020812 eta)).1
    (_root_.GD.N0106.N0428.N0765.N1529.d020829 eta heta),
    (_root_.GD.N0106.N0428.N0765.N1521.d020860 _ (_root_.GD.N0106.N0428.N0765.N1529.d020814 j eta)).1
    (_root_.GD.N0106.N0428.N0765.N1529.d020830 j eta heta)⟩

end
end GD.N0106.N0428.N0765.N1521

#print axioms _root_.GD.N0106.N0428.N0765.N1521.d020847
#print axioms _root_.GD.N0106.N0428.N0765.N1521.d020849
#print axioms _root_.GD.N0106.N0428.N0765.N1521.d020855
#print axioms _root_.GD.N0106.N0428.N0765.N1521.d020864
#print axioms _root_.GD.N0106.N0428.N0765.N1521.d020866
#print axioms _root_.GD.N0106.N0428.N0765.N1521.d020867
#print axioms _root_.GD.N0106.N0428.N0765.N1521.d020859
#print axioms _root_.GD.N0106.N0428.N0765.N1521.d020860
#print axioms _root_.GD.N0106.N0428.N0765.N1521.d020870
#print axioms _root_.GD.N0106.N0428.N0765.N1521.d020871
#print axioms _root_.GD.N0106.N0428.N0765.N1521.d020872
#print axioms _root_.GD.N0106.N0428.N0765.N1521.d020873
#print axioms _root_.GD.N0106.N0428.N0765.N1521.d020874
#print axioms _root_.GD.N0106.N0428.N0765.N1521.d020875
#print axioms _root_.GD.N0106.N0428.N0765.N1521.d020878
#print axioms _root_.GD.N0106.N0428.N0765.N1521.d020880
#print axioms _root_.GD.N0106.N0428.N0765.N1521.d020881
