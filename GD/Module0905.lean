import GD.Module0827
import GD.Module0612
import GD.Module0842





















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0106.N0428.N0765.N1633
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1611 _root_.GD.N0106.N0428.N0765.N1606
open _root_.GD.N0235
open _root_.GD.N0228.N0547.N0791

abbrev d014071 := _root_.GD.N0106.N0428.N0765.N1611.d012588
abbrev d014072 := ℝ × (ℝ × ℝ)


def d014073 (eta : ℝ) : ℝ := (1 + eta) / 11

theorem d014074 {eta : ℝ} (heta : 0 < eta) :
    0 < _root_.GD.N0106.N0428.N0765.N1633.d014073 eta := by
  unfold _root_.GD.N0106.N0428.N0765.N1633.d014073
  positivity

def d014075 (eta : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1633.d014071) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1611.d012591 x / Real.sqrt (_root_.GD.N0106.N0428.N0765.N1633.d014073 eta)

def d014076 (eta : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1633.d014071) : _root_.GD.N0106.N0428.N0765.N1633.d014072 :=
  (_root_.GD.N0106.N0428.N0765.N1633.d014075 eta x, _root_.GD.N0106.N0428.N0765.N1606.d012619 eta x)


def d014077 (eta : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1633.d014071) : _root_.GD.N0106.N0428.N0765.N1633.d014072 :=
  (_root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 / _root_.GD.N0106.N0428.N0765.N1633.d014073 eta, _root_.GD.N0106.N0428.N0765.N1606.d012619 eta x)


def d014078 (location eta : ℝ) : Measure _root_.GD.N0106.N0428.N0765.N1633.d014071 :=
  (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)).withDensity
    (fun x => ENNReal.ofReal (_root_.GD.N0106.N0428.N0765.N1633.d014075 eta x ^ 2))

def d014079 : Measure _root_.GD.N0106.N0428.N0765.N1633.d014072 :=
  (gammaMeasure ((3 : ℝ) / 2) ((1 : ℝ) / 2)).prod
    ((gammaMeasure 5 ((1 : ℝ) / 2)).prod (gammaMeasure 5 ((1 : ℝ) / 2)))

def d014080 (eta : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1633.d014071) : Fin 3 → ℝ :=
  _root_.GD.N0228.N0547.N0791.d012866 (_root_.GD.N0106.N0428.N0765.N1633.d014077 eta x)

def d014081 (eta : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1633.d014071) : ℝ :=
  _root_.GD.N0228.N0547.N0791.d012864 (_root_.GD.N0106.N0428.N0765.N1633.d014077 eta x)

@[fun_prop] theorem d014082 (eta : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1633.d014075 eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1633.d014075
  fun_prop

@[fun_prop] theorem d014083 (eta : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1633.d014076 eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1633.d014076
  fun_prop

@[fun_prop] theorem d014084 (eta : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1633.d014077 eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1633.d014077
  fun_prop

@[fun_prop] theorem d014085 (eta : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta) := by
  exact _root_.GD.N0228.N0547.N0791.d012867.comp (_root_.GD.N0106.N0428.N0765.N1633.d014084 eta)

@[fun_prop] theorem d014086 (eta : ℝ) : Measurable (_root_.GD.N0106.N0428.N0765.N1633.d014081 eta) := by
  exact _root_.GD.N0228.N0547.N0791.d012865.comp (_root_.GD.N0106.N0428.N0765.N1633.d014084 eta)

theorem d014087 (eta : ℝ) (heta : 0 < eta) (x : _root_.GD.N0106.N0428.N0765.N1633.d014071) :
    _root_.GD.N0106.N0428.N0765.N1633.d014075 eta x ^ 2 = _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 / _root_.GD.N0106.N0428.N0765.N1633.d014073 eta := by
  rw [_root_.GD.N0106.N0428.N0765.N1633.d014075, div_pow, Real.sq_sqrt (_root_.GD.N0106.N0428.N0765.N1633.d014074 heta).le]

theorem d014088 (eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1633.d014077 eta = Prod.map (fun z : ℝ => z ^ 2) id ∘ _root_.GD.N0106.N0428.N0765.N1633.d014076 eta := by
  funext x
  simp only [Function.comp_apply, Prod.map_apply, id_eq, _root_.GD.N0106.N0428.N0765.N1633.d014077,
    _root_.GD.N0106.N0428.N0765.N1633.d014076, _root_.GD.N0106.N0428.N0765.N1633.d014087 eta heta]

theorem d014089 (location eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1633.d014078 location eta =
      (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)).withDensity
        (fun x => ENNReal.ofReal (_root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 / ((1 + eta) / 11))) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1633.d014078, _root_.GD.N0106.N0428.N0765.N1633.d014087 eta heta, _root_.GD.N0106.N0428.N0765.N1633.d014073]


theorem d014090 {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) (T : X → Y) (w : Y → ℝ≥0∞)
    (hT : Measurable T) (hw : Measurable w) :
    (mu.withDensity (w ∘ T)).map T = (mu.map T).withDensity w := by
  apply Measure.ext_of_lintegral
  intro f hf
  calc
    (∫⁻ y, f y ∂(mu.withDensity (w ∘ T)).map T) =
        ∫⁻ x, f (T x) ∂mu.withDensity (w ∘ T) := lintegral_map hf hT
    _ = ∫⁻ x, w (T x) * f (T x) ∂mu :=
      lintegral_withDensity_eq_lintegral_mul mu (hw.comp hT) (hf.comp hT)
    _ = ∫⁻ y, (w * f) y ∂mu.map T := (lintegral_map (hw.mul hf) hT).symm
    _ = ∫⁻ y, f y ∂(mu.map T).withDensity w :=
      (lintegral_withDensity_eq_lintegral_mul (mu.map T) hw hf).symm


theorem d014091 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)).map (_root_.GD.N0106.N0428.N0765.N1633.d014076 eta) =
      (gaussianReal 0 1).prod
        ((_root_.GD.N0121.d006346 10).prod
          (_root_.GD.N0121.d006346 10)) := by
  letI : IsProbabilityMeasure (_root_.GD.N0121.d006346 10) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  have hfun : _root_.GD.N0106.N0428.N0765.N1633.d014076 eta =
      Prod.map (fun z : ℝ => z / Real.sqrt (_root_.GD.N0106.N0428.N0765.N1633.d014073 eta)) id ∘ _root_.GD.N0106.N0428.N0765.N1606.d012620 eta := rfl
  rw [hfun, ← Measure.map_map (by fun_prop) (_root_.GD.N0106.N0428.N0765.N1606.d012622 eta),
    _root_.GD.N0106.N0428.N0765.N1606.d012628 location eta heta,
    ← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    gaussianReal_map_div_const, Measure.map_id, zero_div]
  have hvariance :
      (⟨(1 + eta) / 11, by positivity⟩ : ℝ≥0) /
          ⟨Real.sqrt (_root_.GD.N0106.N0428.N0765.N1633.d014073 eta) ^ 2, sq_nonneg _⟩ = 1 := by
    apply NNReal.eq
    change ((1 + eta) / 11) / Real.sqrt (_root_.GD.N0106.N0428.N0765.N1633.d014073 eta) ^ 2 = (1 : ℝ)
    rw [Real.sq_sqrt (_root_.GD.N0106.N0428.N0765.N1633.d014074 heta).le]
    exact div_self (_root_.GD.N0106.N0428.N0765.N1633.d014074 heta).ne'
  exact congrArg (fun v : ℝ≥0 => (gaussianReal 0 v).prod
    ((_root_.GD.N0121.d006346 10).prod
      (_root_.GD.N0121.d006346 10))) hvariance


theorem d014092 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)).map (_root_.GD.N0106.N0428.N0765.N1633.d014077 eta) =
      (_root_.GD.N0121.d006346 1).prod
        ((_root_.GD.N0121.d006346 10).prod
          (_root_.GD.N0121.d006346 10)) := by
  letI : IsProbabilityMeasure (_root_.GD.N0121.d006346 10) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  rw [_root_.GD.N0106.N0428.N0765.N1633.d014088 eta heta,
    ← Measure.map_map (by fun_prop) (_root_.GD.N0106.N0428.N0765.N1633.d014083 eta),
    _root_.GD.N0106.N0428.N0765.N1633.d014091 location eta heta,
    ← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    _root_.GD.N0121.d006355, Measure.map_id]


theorem d014093 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta).map (_root_.GD.N0106.N0428.N0765.N1633.d014076 eta) =
      _root_.GD.N0125.d008853.prod
        ((_root_.GD.N0121.d006346 10).prod
          (_root_.GD.N0121.d006346 10)) := by
  letI : IsProbabilityMeasure (_root_.GD.N0121.d006346 10) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  have hw : Measurable (fun p : _root_.GD.N0106.N0428.N0765.N1633.d014072 => ENNReal.ofReal (p.1 ^ 2)) := by fun_prop
  have hfun : (fun x : _root_.GD.N0106.N0428.N0765.N1633.d014071 => ENNReal.ofReal (_root_.GD.N0106.N0428.N0765.N1633.d014075 eta x ^ 2)) =
      (fun p : _root_.GD.N0106.N0428.N0765.N1633.d014072 => ENNReal.ofReal (p.1 ^ 2)) ∘ _root_.GD.N0106.N0428.N0765.N1633.d014076 eta := rfl
  have hmap := _root_.GD.N0106.N0428.N0765.N1633.d014090 (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta))
    (_root_.GD.N0106.N0428.N0765.N1633.d014076 eta) (fun p : _root_.GD.N0106.N0428.N0765.N1633.d014072 => ENNReal.ofReal (p.1 ^ 2))
    (_root_.GD.N0106.N0428.N0765.N1633.d014083 eta) hw
  rw [← hfun, _root_.GD.N0106.N0428.N0765.N1633.d014091 location eta heta] at hmap
  have hprod := (prod_withDensity_left (μ := gaussianReal 0 1)
    (ν := (_root_.GD.N0121.d006346 10).prod
      (_root_.GD.N0121.d006346 10))
    (f := fun z : ℝ => ENNReal.ofReal (z ^ 2)) (by fun_prop)).symm
  simpa only [_root_.GD.N0106.N0428.N0765.N1633.d014078, _root_.GD.N0125.d008853] using hmap.trans hprod


theorem d014094 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta).map (_root_.GD.N0106.N0428.N0765.N1633.d014077 eta) = _root_.GD.N0106.N0428.N0765.N1633.d014079 := by
  letI : IsFiniteMeasure _root_.GD.N0125.d008853 :=
    _root_.GD.N0125.d008866
  letI : IsProbabilityMeasure (_root_.GD.N0121.d006346 10) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  rw [_root_.GD.N0106.N0428.N0765.N1633.d014088 eta heta,
    ← Measure.map_map (by fun_prop) (_root_.GD.N0106.N0428.N0765.N1633.d014083 eta),
    _root_.GD.N0106.N0428.N0765.N1633.d014093 location eta heta,
    ← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    _root_.GD.N0125.d008867, Measure.map_id]
  norm_num [_root_.GD.N0106.N0428.N0765.N1633.d014079, _root_.GD.N0125.d008851,
    _root_.GD.N0121.d006346]

theorem d014095 : IsProbabilityMeasure _root_.GD.N0106.N0428.N0765.N1633.d014079 := by
  letI : IsProbabilityMeasure (gammaMeasure ((3 : ℝ) / 2) ((1 : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (gammaMeasure 5 ((1 : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  unfold _root_.GD.N0106.N0428.N0765.N1633.d014079
  infer_instance


theorem d014096 (location eta : ℝ) (heta : 0 < eta) :
    IsProbabilityMeasure (_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta) := by
  letI : IsProbabilityMeasure ((_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta).map (_root_.GD.N0106.N0428.N0765.N1633.d014077 eta)) := by
    rw [_root_.GD.N0106.N0428.N0765.N1633.d014094 location eta heta]
    exact _root_.GD.N0106.N0428.N0765.N1633.d014095
  exact Measure.isProbabilityMeasure_of_map (_root_.GD.N0106.N0428.N0765.N1633.d014077 eta)


theorem d014097 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta).map (_root_.GD.N0106.N0428.N0765.N1606.d012619 eta) =
      (_root_.GD.N0121.d006346 10).prod
        (_root_.GD.N0121.d006346 10) := by
  letI : IsProbabilityMeasure (gammaMeasure ((3 : ℝ) / 2) ((1 : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (gammaMeasure 5 ((1 : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  have hfun : _root_.GD.N0106.N0428.N0765.N1606.d012619 eta = Prod.snd ∘ _root_.GD.N0106.N0428.N0765.N1633.d014077 eta := rfl
  rw [hfun, ← Measure.map_map measurable_snd (_root_.GD.N0106.N0428.N0765.N1633.d014084 eta),
    _root_.GD.N0106.N0428.N0765.N1633.d014094 location eta heta]
  convert (measurePreserving_snd
    (μ := gammaMeasure ((3 : ℝ) / 2) ((1 : ℝ) / 2))
    (ν := (gammaMeasure 5 ((1 : ℝ) / 2)).prod (gammaMeasure 5 ((1 : ℝ) / 2)))).map_eq using 1 <;>
      norm_num [_root_.GD.N0106.N0428.N0765.N1633.d014079, _root_.GD.N0121.d006346]


theorem d014098 (location eta : ℝ) (heta : 0 < eta) (f : _root_.GD.N0106.N0428.N0765.N1633.d014071 → ℝ) :
    Integrable f (_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta) ↔
      Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * f x) (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)) := by
  rw [_root_.GD.N0106.N0428.N0765.N1633.d014078, integrable_withDensity_iff_integrable_smul'
    (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  simp only [_root_.GD.N0106.N0428.N0765.N1633.d014087 eta heta]
  constructor
  · intro hf
    convert hf.const_mul (_root_.GD.N0106.N0428.N0765.N1633.d014073 eta) using 1
    funext x
    field_simp [(_root_.GD.N0106.N0428.N0765.N1633.d014074 heta).ne'] <;> ring
  · intro hf
    convert hf.div_const (_root_.GD.N0106.N0428.N0765.N1633.d014073 eta) using 1
    funext x
    ring


theorem d014099 (location eta : ℝ) (heta : 0 < eta) (f : _root_.GD.N0106.N0428.N0765.N1633.d014071 → ℝ) :
    (∫ x, _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * f x ∂_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)) =
      ((1 + eta) / 11) * ∫ x, f x ∂_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta := by
  rw [_root_.GD.N0106.N0428.N0765.N1633.d014078, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  simp only [_root_.GD.N0106.N0428.N0765.N1633.d014087 eta heta]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * f x = _root_.GD.N0106.N0428.N0765.N1633.d014073 eta *
      (_root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 / _root_.GD.N0106.N0428.N0765.N1633.d014073 eta * f x)
    field_simp [(_root_.GD.N0106.N0428.N0765.N1633.d014074 heta).ne'] <;> ring


theorem d014100 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta).map (fun x => (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x, _root_.GD.N0106.N0428.N0765.N1633.d014081 eta x)) =
      (_root_.GD.N0235.d004250 ((3 : ℝ) / 2) 5 5).prod
        (gammaMeasure ((23 : ℝ) / 2) ((1 : ℝ) / 2)) := by
  have hfun : (fun x : _root_.GD.N0106.N0428.N0765.N1633.d014071 => (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x, _root_.GD.N0106.N0428.N0765.N1633.d014081 eta x)) =
      _root_.GD.N0228.N0547.N0791.d012868 ∘ _root_.GD.N0106.N0428.N0765.N1633.d014077 eta := rfl
  rw [hfun, ← Measure.map_map _root_.GD.N0228.N0547.N0791.d012869
    (_root_.GD.N0106.N0428.N0765.N1633.d014084 eta), _root_.GD.N0106.N0428.N0765.N1633.d014094 location eta heta]
  simpa only [_root_.GD.N0106.N0428.N0765.N1633.d014079,
    show (3 : ℝ) / 2 + 5 + 5 = (23 : ℝ) / 2 by norm_num] using
    (_root_.GD.N0228.N0547.N0791.d012872 (a := (3 : ℝ) / 2) (b := 5) (c := 5) (r := (1 : ℝ) / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))

theorem d014101 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta).map (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta) =
      _root_.GD.N0235.d004250 ((3 : ℝ) / 2) 5 5 := by
  change (_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta).map (_root_.GD.N0228.N0547.N0791.d012866 ∘ _root_.GD.N0106.N0428.N0765.N1633.d014077 eta) = _
  rw [← Measure.map_map _root_.GD.N0228.N0547.N0791.d012867 (_root_.GD.N0106.N0428.N0765.N1633.d014084 eta),
    _root_.GD.N0106.N0428.N0765.N1633.d014094 location eta heta]
  exact _root_.GD.N0228.N0547.N0791.d012873 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem d014102 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta).map (_root_.GD.N0106.N0428.N0765.N1633.d014081 eta) =
      gammaMeasure ((23 : ℝ) / 2) ((1 : ℝ) / 2) := by
  letI : IsProbabilityMeasure (_root_.GD.N0235.d004250 ((3 : ℝ) / 2) 5 5) :=
    _root_.GD.N0235.d004251 (by norm_num) (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (gammaMeasure ((23 : ℝ) / 2) ((1 : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  have hfun : _root_.GD.N0106.N0428.N0765.N1633.d014081 eta = Prod.snd ∘ (fun x => (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x, _root_.GD.N0106.N0428.N0765.N1633.d014081 eta x)) := rfl
  rw [hfun, ← Measure.map_map measurable_snd (by fun_prop),
    _root_.GD.N0106.N0428.N0765.N1633.d014100 location eta heta]
  exact measurePreserving_snd.map_eq

theorem d014103 (location eta : ℝ) (heta : 0 < eta) :
    IndepFun (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta) (_root_.GD.N0106.N0428.N0765.N1633.d014081 eta) (_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta) := by
  letI : IsProbabilityMeasure (_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta) := _root_.GD.N0106.N0428.N0765.N1633.d014096 location eta heta
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (_root_.GD.N0106.N0428.N0765.N1633.d014085 eta).aemeasurable (_root_.GD.N0106.N0428.N0765.N1633.d014086 eta).aemeasurable).2
  rw [_root_.GD.N0106.N0428.N0765.N1633.d014100 location eta heta, _root_.GD.N0106.N0428.N0765.N1633.d014101 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1633.d014102 location eta heta]


theorem d014104 (location eta : ℝ) (heta : 0 < eta)
    (f : (Fin 3 → ℝ) → ℝ)
    (hf : Integrable f (_root_.GD.N0235.d004250 ((3 : ℝ) / 2) 5 5)) :
    Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * f (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x))
        (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)) ∧
      (∫ x, _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * f (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x) ∂_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)) =
        ((1 + eta) / 11) * ∫ p, f p ∂_root_.GD.N0235.d004250 ((3 : ℝ) / 2) 5 5 := by
  have hmap : Integrable f ((_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta).map (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta)) := by
    rw [_root_.GD.N0106.N0428.N0765.N1633.d014101 location eta heta]
    exact hf
  have hcomp : Integrable (fun x => f (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x)) (_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta) :=
    hmap.comp_aemeasurable (_root_.GD.N0106.N0428.N0765.N1633.d014085 eta).aemeasurable
  refine ⟨(_root_.GD.N0106.N0428.N0765.N1633.d014098 location eta heta _).1 hcomp, ?_⟩
  rw [_root_.GD.N0106.N0428.N0765.N1633.d014099 location eta heta]
  congr 1
  calc
    (∫ x, f (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x) ∂_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta) =
        ∫ p, f p ∂(_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta).map (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta) :=
      (integral_map (_root_.GD.N0106.N0428.N0765.N1633.d014085 eta).aemeasurable hmap.aestronglyMeasurable).symm
    _ = ∫ p, f p ∂_root_.GD.N0235.d004250 ((3 : ℝ) / 2) 5 5 := by
      rw [_root_.GD.N0106.N0428.N0765.N1633.d014101 location eta heta]

end
end GD.N0106.N0428.N0765.N1633

#print axioms _root_.GD.N0106.N0428.N0765.N1633.d014089
#print axioms _root_.GD.N0106.N0428.N0765.N1633.d014090
#print axioms _root_.GD.N0106.N0428.N0765.N1633.d014091
#print axioms _root_.GD.N0106.N0428.N0765.N1633.d014092
#print axioms _root_.GD.N0106.N0428.N0765.N1633.d014093
#print axioms _root_.GD.N0106.N0428.N0765.N1633.d014094
#print axioms _root_.GD.N0106.N0428.N0765.N1633.d014096
#print axioms _root_.GD.N0106.N0428.N0765.N1633.d014097
#print axioms _root_.GD.N0106.N0428.N0765.N1633.d014098
#print axioms _root_.GD.N0106.N0428.N0765.N1633.d014099
#print axioms _root_.GD.N0106.N0428.N0765.N1633.d014100
#print axioms _root_.GD.N0106.N0428.N0765.N1633.d014101
#print axioms _root_.GD.N0106.N0428.N0765.N1633.d014102
#print axioms _root_.GD.N0106.N0428.N0765.N1633.d014103
#print axioms _root_.GD.N0106.N0428.N0765.N1633.d014104
