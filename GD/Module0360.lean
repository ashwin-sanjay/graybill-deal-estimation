import GD.Module0274
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic













set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace GD.N0106.N0428.N0765.N1539
noncomputable section
open _root_.GD.N0235

def d005352 (s : Set ℝ) (w : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict s).withDensity (fun x => ENNReal.ofReal (w x))


theorem d005353 {s t : Set ℝ} (hs : MeasurableSet s)
    (F D w v : ℝ → ℝ) (hF : Measurable F) (hw : Measurable w) (hv : Measurable v)
    (hD : ∀ x ∈ s, HasDerivWithinAt F (D x) s x)
    (hinj : InjOn F s) (himage : F '' s = t)
    (hweight : ∀ x ∈ s, w x = |D x| * v (F x)) :
    (_root_.GD.N0106.N0428.N0765.N1539.d005352 s w).map F = _root_.GD.N0106.N0428.N0765.N1539.d005352 t v := by
  apply Measure.ext_of_lintegral
  intro g hg
  calc
    (∫⁻ y, g y ∂(_root_.GD.N0106.N0428.N0765.N1539.d005352 s w).map F) =
        ∫⁻ x in s, ENNReal.ofReal (w x) * g (F x) := by
      rw [lintegral_map hg hF, _root_.GD.N0106.N0428.N0765.N1539.d005352]
      simpa only [Function.comp_apply, Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul (volume.restrict s)
          hw.ennreal_ofReal (hg.comp hF))
    _ = ∫⁻ y in t, ENNReal.ofReal (v y) * g y := by
      rw [← himage, lintegral_image_eq_lintegral_abs_deriv_mul hs hD hinj]
      apply setLIntegral_congr_fun hs
      intro x hx
      dsimp only
      rw [hweight x hx, ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]
    _ = ∫⁻ y, g y ∂_root_.GD.N0106.N0428.N0765.N1539.d005352 t v := by
      rw [_root_.GD.N0106.N0428.N0765.N1539.d005352]
      simpa only [Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul (volume.restrict t)
          hv.ennreal_ofReal hg).symm

theorem d005354 (s : Set ℝ) (hs : MeasurableSet s)
    (w g : ℝ → ℝ) (hw : Measurable w) (hw0 : ∀ x ∈ s, 0 ≤ w x) :
    (∫ x, g x ∂_root_.GD.N0106.N0428.N0765.N1539.d005352 s w) = ∫ x in s, w x * g x := by
  rw [_root_.GD.N0106.N0428.N0765.N1539.d005352, integral_withDensity_eq_integral_toReal_smul
    hw.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  simp only [ENNReal.toReal_ofReal (hw0 x hx), smul_eq_mul]

theorem d005355 (s : Set ℝ) (hs : MeasurableSet s)
    (w g : ℝ → ℝ) (hw : Measurable w) (hw0 : ∀ x ∈ s, 0 ≤ w x) :
    Integrable g (_root_.GD.N0106.N0428.N0765.N1539.d005352 s w) ↔ IntegrableOn (fun x => w x * g x) s := by
  rw [_root_.GD.N0106.N0428.N0765.N1539.d005352, integrable_withDensity_iff_integrable_smul'
    hw.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem hs] with x hx
  simp only [ENNReal.toReal_ofReal (hw0 x hx), smul_eq_mul]

theorem d005356 (a b : ℝ) :
    betaMeasure a b = _root_.GD.N0106.N0428.N0765.N1539.d005352 (Ioo 0 1) (betaPDFReal a b) := by
  unfold betaMeasure _root_.GD.N0106.N0428.N0765.N1539.d005352 betaPDF
  rw [← withDensity_indicator measurableSet_Ioo]
  congr 1
  funext x
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · simp [hx]
  · simp only [mem_Ioo] at hx
    simp [Set.indicator, betaPDFReal, hx]

theorem d005357 (a b : ℝ) :
    ∀ᵐ x ∂betaMeasure a b, x ∈ Ioo (0 : ℝ) 1 := by
  unfold betaMeasure betaPDF
  rw [ae_withDensity_iff (measurable_betaPDFReal a b).ennreal_ofReal]
  filter_upwards with x hx
  by_contra hnot
  have houtside : ¬(0 < x ∧ x < 1) := hnot
  simp [betaPDFReal, houtside] at hx

theorem d005358 {a : ℝ} (ha : 0 < a) : beta a 1 = 1 / a := by
  rw [beta, Real.Gamma_one, Real.Gamma_add_one ha.ne']
  field_simp [(Real.Gamma_pos_of_pos ha).ne', ha.ne'] <;> ring

theorem d005359 : beta ((3 : ℝ) / 2) 10 = 131072 / 4849845 := by
  have h1 := _root_.GD.N0106.N0428.N0765.N1539.d005358 (a := (3 : ℝ) / 2) (by norm_num)
  have h2 := _root_.GD.N0235.d004039 (α := (3 : ℝ) / 2) (β := 1) (by norm_num) (by norm_num)
  have h3 := _root_.GD.N0235.d004039 (α := (3 : ℝ) / 2) (β := 2) (by norm_num) (by norm_num)
  have h4 := _root_.GD.N0235.d004039 (α := (3 : ℝ) / 2) (β := 3) (by norm_num) (by norm_num)
  have h5 := _root_.GD.N0235.d004039 (α := (3 : ℝ) / 2) (β := 4) (by norm_num) (by norm_num)
  have h6 := _root_.GD.N0235.d004039 (α := (3 : ℝ) / 2) (β := 5) (by norm_num) (by norm_num)
  have h7 := _root_.GD.N0235.d004039 (α := (3 : ℝ) / 2) (β := 6) (by norm_num) (by norm_num)
  have h8 := _root_.GD.N0235.d004039 (α := (3 : ℝ) / 2) (β := 7) (by norm_num) (by norm_num)
  have h9 := _root_.GD.N0235.d004039 (α := (3 : ℝ) / 2) (β := 8) (by norm_num) (by norm_num)
  have h10 := _root_.GD.N0235.d004039 (α := (3 : ℝ) / 2) (β := 9) (by norm_num) (by norm_num)
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rw [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1]
  norm_num

theorem d005360 : beta (5 : ℝ) 5 = 1 / 630 := by
  have h1 := _root_.GD.N0106.N0428.N0765.N1539.d005358 (a := (5 : ℝ)) (by norm_num)
  have h2 := _root_.GD.N0235.d004039 (α := (5 : ℝ)) (β := 1) (by norm_num) (by norm_num)
  have h3 := _root_.GD.N0235.d004039 (α := (5 : ℝ)) (β := 2) (by norm_num) (by norm_num)
  have h4 := _root_.GD.N0235.d004039 (α := (5 : ℝ)) (β := 3) (by norm_num) (by norm_num)
  have h5 := _root_.GD.N0235.d004039 (α := (5 : ℝ)) (β := 4) (by norm_num) (by norm_num)
  norm_num at h1 h2 h3 h4 h5
  rw [h5, h4, h3, h2, h1]
  norm_num

theorem d005361 :
    (beta ((3 : ℝ) / 2) 10)⁻¹ = 4849845 / 131072 ∧
      (beta (5 : ℝ) 5)⁻¹ = 630 := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1539.d005359, _root_.GD.N0106.N0428.N0765.N1539.d005360]

def d005362 (y : ℝ) : ℝ :=
  (4849845 / 65536 : ℝ) * y ^ 2 * (1 - y ^ 2) ^ 9

theorem d005363 : (fun y : ℝ => y ^ 2) '' Ioo 0 1 = Ioo 0 1 := by
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨sq_pos_of_pos hy.1, by nlinarith [hy.2, mul_pos hy.1 (sub_pos.mpr hy.2)]⟩
  · intro ht
    refine ⟨Real.sqrt t, ⟨Real.sqrt_pos.2 ht.1, ?_⟩, Real.sq_sqrt ht.1.le⟩
    have hs := Real.sq_sqrt ht.1.le
    nlinarith [Real.sqrt_nonneg t, ht.2]

theorem d005364 : InjOn (fun y : ℝ => y ^ 2) (Ioo 0 1) := by
  intro x hx y hy hxy
  exact (sq_eq_sq₀ hx.1.le hy.1.le).1 hxy

theorem d005365 {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1539.d005362 y = |2 * y| * betaPDFReal ((3 : ℝ) / 2) 10 (y ^ 2) := by
  have ht : y ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    rw [← _root_.GD.N0106.N0428.N0765.N1539.d005363]
    exact mem_image_of_mem (fun z : ℝ => z ^ 2) hy
  rw [betaPDFReal, if_pos (show 0 < y ^ 2 ∧ y ^ 2 < 1 from ht), _root_.GD.N0106.N0428.N0765.N1539.d005359,
    abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hy.1)]
  norm_num only [show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num,
    show (10 : ℝ) - 1 = (9 : ℕ) by norm_num, Real.rpow_natCast, Real.rpow_ofNat]
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hy.1.le]
  unfold _root_.GD.N0106.N0428.N0765.N1539.d005362
  ring_nf

theorem d005366 :
    (_root_.GD.N0106.N0428.N0765.N1539.d005352 (Ioo 0 1) _root_.GD.N0106.N0428.N0765.N1539.d005362).map (fun y : ℝ => y ^ 2) =
      betaMeasure ((3 : ℝ) / 2) 10 := by
  rw [_root_.GD.N0106.N0428.N0765.N1539.d005356]
  exact _root_.GD.N0106.N0428.N0765.N1539.d005353 measurableSet_Ioo _ (fun y => 2 * y) _ _
    (by fun_prop) (by unfold _root_.GD.N0106.N0428.N0765.N1539.d005362; fun_prop) (measurable_betaPDFReal _ _)
    (fun y _ => by simpa using (hasDerivAt_pow 2 y).hasDerivWithinAt)
    _root_.GD.N0106.N0428.N0765.N1539.d005364 _root_.GD.N0106.N0428.N0765.N1539.d005363 (fun _ hy => _root_.GD.N0106.N0428.N0765.N1539.d005365 hy)

theorem d005367 :
    IntegrableOn _root_.GD.N0106.N0428.N0765.N1539.d005362 (Ioo (0 : ℝ) 1) ∧
      (∫ y in Ioo (0 : ℝ) 1, _root_.GD.N0106.N0428.N0765.N1539.d005362 y) = 1 := by
  letI : IsProbabilityMeasure (betaMeasure ((3 : ℝ) / 2) 10) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure ((_root_.GD.N0106.N0428.N0765.N1539.d005352 (Ioo 0 1) _root_.GD.N0106.N0428.N0765.N1539.d005362).map
      (fun y : ℝ => y ^ 2)) := by
    rw [_root_.GD.N0106.N0428.N0765.N1539.d005366]
    infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0106.N0428.N0765.N1539.d005352 (Ioo 0 1) _root_.GD.N0106.N0428.N0765.N1539.d005362) :=
    Measure.isProbabilityMeasure_of_map (fun y : ℝ => y ^ 2)
  have hw : Measurable _root_.GD.N0106.N0428.N0765.N1539.d005362 := by unfold _root_.GD.N0106.N0428.N0765.N1539.d005362; fun_prop
  have hw0 : ∀ y ∈ Ioo (0 : ℝ) 1, 0 ≤ _root_.GD.N0106.N0428.N0765.N1539.d005362 y := by
    intro y hy
    rw [_root_.GD.N0106.N0428.N0765.N1539.d005365 hy]
    exact mul_nonneg (abs_nonneg _) (_root_.GD.N0235.d004040 (by norm_num) (by norm_num) _)
  have hi := (_root_.GD.N0106.N0428.N0765.N1539.d005355 _ measurableSet_Ioo _root_.GD.N0106.N0428.N0765.N1539.d005362
    (fun _ => 1) hw hw0).1 (integrable_const 1)
  have hm := _root_.GD.N0106.N0428.N0765.N1539.d005354 _ measurableSet_Ioo _root_.GD.N0106.N0428.N0765.N1539.d005362 (fun _ => 1) hw hw0
  exact ⟨by simpa using hi, by simpa using hm.symm⟩

def d005368 (t : ℝ) : ℝ := Real.log (t / (1 - t))

theorem d005369 (x : ℝ) :
    Real.sigmoid x = Real.exp x / (1 + Real.exp x) := by
  rw [Real.sigmoid, Real.exp_neg]
  field_simp [(Real.exp_pos x).ne', show 1 + Real.exp x ≠ 0 by positivity] <;> ring

theorem d005370 (x : ℝ) :
    1 - Real.sigmoid x = (1 + Real.exp x)⁻¹ := by
  rw [_root_.GD.N0106.N0428.N0765.N1539.d005369]
  field_simp [show 1 + Real.exp x ≠ 0 by positivity] <;> ring

theorem d005371 (x : ℝ) : _root_.GD.N0106.N0428.N0765.N1539.d005368 (Real.sigmoid x) = x := by
  have hratio : Real.sigmoid x / (1 - Real.sigmoid x) = Real.exp x := by
    rw [_root_.GD.N0106.N0428.N0765.N1539.d005370, _root_.GD.N0106.N0428.N0765.N1539.d005369]
    field_simp [show 1 + Real.exp x ≠ 0 by positivity] <;> ring
  rw [_root_.GD.N0106.N0428.N0765.N1539.d005368, hratio, Real.log_exp]

theorem d005372 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Real.sigmoid (_root_.GD.N0106.N0428.N0765.N1539.d005368 t) = t := by
  rw [_root_.GD.N0106.N0428.N0765.N1539.d005369, _root_.GD.N0106.N0428.N0765.N1539.d005368, Real.exp_log (div_pos ht.1 (sub_pos.mpr ht.2))]
  field_simp [(sub_pos.mpr ht.2).ne']
  ring

def d005373 (a b x : ℝ) : ℝ :=
  Real.exp (a * x) / (beta a b * (1 + Real.exp x) ^ (a + b))

@[fun_prop] theorem d005374 (a b : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1539.d005373 a b) := by
  unfold _root_.GD.N0106.N0428.N0765.N1539.d005373
  fun_prop

theorem d005375 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    0 < _root_.GD.N0106.N0428.N0765.N1539.d005373 a b x := by
  unfold _root_.GD.N0106.N0428.N0765.N1539.d005373
  exact div_pos (Real.exp_pos _) (mul_pos (beta_pos ha hb)
    (Real.rpow_pos_of_pos (by positivity) _))

theorem d005376 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1539.d005373 a b x = |Real.sigmoid x * (1 - Real.sigmoid x)| *
      betaPDFReal a b (Real.sigmoid x) := by
  have he := Real.exp_pos x
  have hd : 0 < 1 + Real.exp x := by positivity
  rw [abs_of_pos (mul_pos (Real.sigmoid_pos x) (sub_pos.mpr (Real.sigmoid_lt_one x))),
    betaPDFReal, if_pos ⟨Real.sigmoid_pos x, Real.sigmoid_lt_one x⟩]
  simp only [_root_.GD.N0106.N0428.N0765.N1539.d005370]
  simp only [_root_.GD.N0106.N0428.N0765.N1539.d005369]
  rw [Real.div_rpow he.le hd.le, Real.inv_rpow hd.le,
    Real.rpow_sub_one he.ne', Real.rpow_sub_one hd.ne', Real.rpow_sub_one hd.ne']
  unfold _root_.GD.N0106.N0428.N0765.N1539.d005373
  rw [mul_comm a x, Real.exp_mul, Real.rpow_add hd]
  field_simp [(Real.rpow_pos_of_pos he a).ne',
    (Real.rpow_pos_of_pos hd a).ne', (Real.rpow_pos_of_pos hd b).ne', he.ne', hd.ne',
    (beta_pos ha hb).ne'] <;> ring

theorem d005377 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (_root_.GD.N0106.N0428.N0765.N1539.d005352 univ (_root_.GD.N0106.N0428.N0765.N1539.d005373 a b)).map Real.sigmoid = betaMeasure a b := by
  rw [_root_.GD.N0106.N0428.N0765.N1539.d005356]
  exact _root_.GD.N0106.N0428.N0765.N1539.d005353 MeasurableSet.univ _
    (fun x => Real.sigmoid x * (1 - Real.sigmoid x)) _ _
    continuous_sigmoid.measurable (_root_.GD.N0106.N0428.N0765.N1539.d005374 a b) (measurable_betaPDFReal a b)
    (fun x _ => (Real.hasDerivAt_sigmoid x).hasDerivWithinAt)
    Real.sigmoid_injective.injOn (by simpa using Real.range_sigmoid)
    (fun x _ => _root_.GD.N0106.N0428.N0765.N1539.d005376 ha hb x)

theorem d005378 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (betaMeasure a b).map _root_.GD.N0106.N0428.N0765.N1539.d005368 = _root_.GD.N0106.N0428.N0765.N1539.d005352 univ (_root_.GD.N0106.N0428.N0765.N1539.d005373 a b) := by
  rw [← _root_.GD.N0106.N0428.N0765.N1539.d005377 ha hb, Measure.map_map (by unfold _root_.GD.N0106.N0428.N0765.N1539.d005368; fun_prop)
    continuous_sigmoid.measurable]
  convert (Measure.map_id (μ := _root_.GD.N0106.N0428.N0765.N1539.d005352 univ (_root_.GD.N0106.N0428.N0765.N1539.d005373 a b))) using 1
  congr 1
  funext x
  exact _root_.GD.N0106.N0428.N0765.N1539.d005371 x

theorem d005379 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1539.d005373 a b) := by
  letI : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  letI : IsProbabilityMeasure (_root_.GD.N0106.N0428.N0765.N1539.d005352 univ (_root_.GD.N0106.N0428.N0765.N1539.d005373 a b)) := by
    rw [← _root_.GD.N0106.N0428.N0765.N1539.d005378 ha hb]
    exact Measure.isProbabilityMeasure_map (by unfold _root_.GD.N0106.N0428.N0765.N1539.d005368; fun_prop)
  have h := (_root_.GD.N0106.N0428.N0765.N1539.d005355 univ MeasurableSet.univ
    (_root_.GD.N0106.N0428.N0765.N1539.d005373 a b) (fun _ => 1) (_root_.GD.N0106.N0428.N0765.N1539.d005374 a b)
    (fun x _ => (_root_.GD.N0106.N0428.N0765.N1539.d005375 ha hb x).le)).1 (integrable_const 1)
  simpa using h

theorem d005380 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x, _root_.GD.N0106.N0428.N0765.N1539.d005373 a b x) = 1 := by
  letI : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  letI : IsProbabilityMeasure (_root_.GD.N0106.N0428.N0765.N1539.d005352 univ (_root_.GD.N0106.N0428.N0765.N1539.d005373 a b)) := by
    rw [← _root_.GD.N0106.N0428.N0765.N1539.d005378 ha hb]
    exact Measure.isProbabilityMeasure_map (by unfold _root_.GD.N0106.N0428.N0765.N1539.d005368; fun_prop)
  simpa using (_root_.GD.N0106.N0428.N0765.N1539.d005354 univ MeasurableSet.univ
    (_root_.GD.N0106.N0428.N0765.N1539.d005373 a b) (fun _ => 1) (_root_.GD.N0106.N0428.N0765.N1539.d005374 a b)
    (fun x _ => (_root_.GD.N0106.N0428.N0765.N1539.d005375 ha hb x).le)).symm

theorem d005381 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ t, f t ∂betaMeasure a b) =
      ∫ x, _root_.GD.N0106.N0428.N0765.N1539.d005373 a b x * f (Real.sigmoid x) := by
  rw [← _root_.GD.N0106.N0428.N0765.N1539.d005377 ha hb,
    integral_map_of_stronglyMeasurable continuous_sigmoid.measurable hf.stronglyMeasurable,
    _root_.GD.N0106.N0428.N0765.N1539.d005354 univ MeasurableSet.univ _ _ (_root_.GD.N0106.N0428.N0765.N1539.d005374 a b)
      (fun x _ => (_root_.GD.N0106.N0428.N0765.N1539.d005375 ha hb x).le)]
  simp only [Measure.restrict_univ]

theorem d005382 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (f : ℝ → ℝ) (hf : Measurable f) :
    Integrable f (betaMeasure a b) ↔
      Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1539.d005373 a b x * f (Real.sigmoid x)) := by
  rw [← _root_.GD.N0106.N0428.N0765.N1539.d005377 ha hb, integrable_map_measure hf.aestronglyMeasurable
    continuous_sigmoid.measurable.aemeasurable,
    _root_.GD.N0106.N0428.N0765.N1539.d005355 univ MeasurableSet.univ _ _ (_root_.GD.N0106.N0428.N0765.N1539.d005374 a b)
      (fun x _ => (_root_.GD.N0106.N0428.N0765.N1539.d005375 ha hb x).le)]
  simp only [IntegrableOn, Measure.restrict_univ, Function.comp_apply]

end
end GD.N0106.N0428.N0765.N1539

#print axioms _root_.GD.N0106.N0428.N0765.N1539.d005353
#print axioms _root_.GD.N0106.N0428.N0765.N1539.d005355
#print axioms _root_.GD.N0106.N0428.N0765.N1539.d005361
#print axioms _root_.GD.N0106.N0428.N0765.N1539.d005366
#print axioms _root_.GD.N0106.N0428.N0765.N1539.d005367
#print axioms _root_.GD.N0106.N0428.N0765.N1539.d005377
#print axioms _root_.GD.N0106.N0428.N0765.N1539.d005378
#print axioms _root_.GD.N0106.N0428.N0765.N1539.d005379
#print axioms _root_.GD.N0106.N0428.N0765.N1539.d005380
#print axioms _root_.GD.N0106.N0428.N0765.N1539.d005381
#print axioms _root_.GD.N0106.N0428.N0765.N1539.d005382
