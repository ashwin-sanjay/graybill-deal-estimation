import GD.Module1286
import GD.Module0361















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace GD.N0106.N0428.N0765.N1632
noncomputable section
open _root_.GD.N0235 _root_.GD.N0106.N0428.N0765.N1539 _root_.GD.N0106.N0428.N0765.N1521 _root_.GD.N0106.N0428.N0765.N1529

theorem d021341 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (f : ℝ → ℝ) :
    (∫ t, f t ∂betaMeasure a b) = ∫ t in Ioo (0 : ℝ) 1, betaPDFReal a b t * f t := by
  rw [_root_.GD.N0106.N0428.N0765.N1539.d005356,
    _root_.GD.N0106.N0428.N0765.N1539.d005354 _ measurableSet_Ioo _ _ (measurable_betaPDFReal a b)
      (fun t _ => _root_.GD.N0235.d004040 ha hb t)]

theorem d021342 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    betaPDFReal ((3 : ℝ) / 2) 10 t =
      (4849845 / 131072 : ℝ) * Real.sqrt t * (1 - t) ^ 9 := by
  rw [betaPDFReal, if_pos (show 0 < t ∧ t < 1 from ht), _root_.GD.N0106.N0428.N0765.N1539.d005359]
  norm_num only [show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num,
    show (10 : ℝ) - 1 = (9 : ℕ) by norm_num, Real.rpow_natCast, Real.rpow_ofNat]
  rw [← Real.sqrt_eq_rpow]

theorem d021343 (f : (Fin 3 → ℝ) → ℝ)
    (hf : Measurable f) (hfi : Integrable f _root_.GD.N0106.N0428.N0765.N1529.d020798) :
    (∫ p, f p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) =
      ∫ t, (∫ s, f (_root_.GD.N0235.d004247 (t, s)) ∂betaMeasure 5 5)
        ∂betaMeasure ((3 : ℝ) / 2) 10 := by
  letI : IsProbabilityMeasure (betaMeasure ((3 : ℝ) / 2) 10) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (betaMeasure (5 : ℝ) 5) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  have hm : Integrable f (_root_.GD.N0106.N0428.N0765.N1521.d020840.map _root_.GD.N0235.d004247) := by
    rw [_root_.GD.N0106.N0428.N0765.N1521.d020844]
    exact hfi
  have hc := hm.comp_measurable _root_.GD.N0235.d004248
  rw [← _root_.GD.N0106.N0428.N0765.N1521.d020844,
    integral_map_of_stronglyMeasurable _root_.GD.N0235.d004248 hf.stronglyMeasurable]
  exact integral_prod _ hc


theorem d021344 (u L : ℝ) (f : (Fin 3 → ℝ) → ℝ) :
    (∫ v in (0 : ℝ)..L, _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (L - v) * f ![u, v, L - v]) =
      L ^ 9 * Real.sqrt u *
        ∫ s in (0 : ℝ)..1, s ^ 4 * (1 - s) ^ 4 * f ![u, L * s, L * (1 - s)] := by
  have hchange := intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1)
    (fun v => _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (L - v) * f ![u, v, L - v]) L
  simp only [smul_eq_mul, mul_zero, mul_one] at hchange
  rw [← hchange]
  simp_rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [show L - L * s = L * (1 - s) by ring]
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005383
  ring

def d021345 : ℝ := (4849845 / 131072 : ℝ) * 630

theorem d021346 : 0 < _root_.GD.N0106.N0428.N0765.N1632.d021345 := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1632.d021345]


theorem d021347 (f : (Fin 3 → ℝ) → ℝ)
    (hf : Measurable f) (hfi : Integrable f _root_.GD.N0106.N0428.N0765.N1529.d020798) :
    (∫ p, f p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) = _root_.GD.N0106.N0428.N0765.N1632.d021345 *
      ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..(1 - u),
        _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * f ![u, v, 1 - u - v] := by
  rw [_root_.GD.N0106.N0428.N0765.N1632.d021343 f hf hfi,
    _root_.GD.N0106.N0428.N0765.N1632.d021341 (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (0 : ℝ) < 10),
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  rw [_root_.GD.N0106.N0428.N0765.N1632.d021342 hu]
  have hs : (∫ s, f (_root_.GD.N0235.d004247 (u, s)) ∂betaMeasure 5 5) =
      630 * ∫ s in (0 : ℝ)..1,
        s ^ 4 * (1 - s) ^ 4 * f ![u, (1 - u) * s, (1 - u) * (1 - s)] := by
    rw [_root_.GD.N0106.N0428.N0765.N1632.d021341 (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 5),
      intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    change betaPDFReal 5 5 s * f (_root_.GD.N0235.d004247 (u, s)) =
      630 * (s ^ 4 * (1 - s) ^ 4 * f ![u, (1 - u) * s, (1 - u) * (1 - s)])
    rw [_root_.GD.N0106.N0428.N0765.N1521.d020857 hs]
    unfold _root_.GD.N0235.d004247
    ring
  rw [hs, _root_.GD.N0106.N0428.N0765.N1632.d021344 u (1 - u) f]
  unfold _root_.GD.N0106.N0428.N0765.N1632.d021345
  ring

theorem d021348 :
    _root_.GD.N0106.N0428.N0765.N1543.d005384 = (131072 : ℝ) / (4849845 * 630) := by
  letI : IsProbabilityMeasure _root_.GD.N0106.N0428.N0765.N1529.d020798 :=
    _root_.GD.N0235.d004251 (by norm_num) (by norm_num) (by norm_num)
  have h := _root_.GD.N0106.N0428.N0765.N1632.d021347 (fun _ => (1 : ℝ)) measurable_const (integrable_const 1)
  have hmass : (∫ p : Fin 3 → ℝ, (1 : ℝ) ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) = 1 := by simp
  rw [hmass] at h
  simp only [mul_one] at h
  change 1 = _root_.GD.N0106.N0428.N0765.N1632.d021345 * _root_.GD.N0106.N0428.N0765.N1543.d005384 at h
  norm_num [_root_.GD.N0106.N0428.N0765.N1632.d021345] at h ⊢
  linarith


theorem d021349 (f : (Fin 3 → ℝ) → ℝ)
    (hf : Measurable f) (hfi : Integrable f _root_.GD.N0106.N0428.N0765.N1529.d020798) :
    _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w => f ![u, v, w]) = ∫ p, f p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  rw [_root_.GD.N0106.N0428.N0765.N1632.d021347 f hf hfi]
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005385
  rw [_root_.GD.N0106.N0428.N0765.N1632.d021348]
  unfold _root_.GD.N0106.N0428.N0765.N1632.d021345
  ring


theorem d021350 (eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1543.d005395 eta = _root_.GD.N0106.N0428.N0765.N1529.d020806 eta := by
  have h := _root_.GD.N0106.N0428.N0765.N1632.d021349 (_root_.GD.N0106.N0428.N0765.N1529.d020802 eta) (_root_.GD.N0106.N0428.N0765.N1529.d020812 eta)
    (_root_.GD.N0106.N0428.N0765.N1529.d020829 eta heta)
  have hprofile : (fun u v w => _root_.GD.N0106.N0428.N0765.N1529.d020802 eta ![u, v, w]) =
      fun u v w => (_root_.GD.N0106.N0428.N0765.N1543.d005393 eta v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 eta) ^ 2 -
        (_root_.GD.N0106.N0428.N0765.N1534.d005330 eta u v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 eta) ^ 2 := by
    funext u v w
    rfl
  rw [hprofile] at h
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005395 _root_.GD.N0106.N0428.N0765.N1529.d020806 _root_.GD.N0106.N0428.N0765.N1534.d005331
  rw [h]

theorem d021351 (eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1543.d005395 eta = ((1 + eta) / 11) *
      ∫ p, _root_.GD.N0106.N0428.N0765.N1521.d020868 p * _root_.GD.N0106.N0428.N0765.N1529.d020802 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 p) := by
  rw [_root_.GD.N0106.N0428.N0765.N1632.d021350 eta heta, _root_.GD.N0106.N0428.N0765.N1529.d020806,
    _root_.GD.N0106.N0428.N0765.N1521.d020870 _ (_root_.GD.N0106.N0428.N0765.N1529.d020812 eta)]


theorem d021352 (e : ℝ) (he : 0 < e) :
    _root_.GD.N0106.N0428.N0765.N1543.d005396 e = (e⁻¹ * ((1 + e⁻¹) / 11)) *
      ∫ p, _root_.GD.N0106.N0428.N0765.N1521.d020868 p * _root_.GD.N0106.N0428.N0765.N1529.d020802 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 p) := by
  rw [_root_.GD.N0106.N0428.N0765.N1543.d005396, _root_.GD.N0106.N0428.N0765.N1632.d021351 e⁻¹ (inv_pos.mpr he)]
  ring

theorem d021353 (e : ℝ) (he : 0 < e) :
    Integrable (fun p => (e⁻¹ * ((1 + e⁻¹) / 11)) *
      (_root_.GD.N0106.N0428.N0765.N1521.d020868 p * _root_.GD.N0106.N0428.N0765.N1529.d020802 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 p))) :=
  (_root_.GD.N0106.N0428.N0765.N1521.d020876 e⁻¹ (inv_pos.mpr he)).const_mul _

end
end GD.N0106.N0428.N0765.N1632

#print axioms _root_.GD.N0106.N0428.N0765.N1632.d021343
#print axioms _root_.GD.N0106.N0428.N0765.N1632.d021344
#print axioms _root_.GD.N0106.N0428.N0765.N1632.d021347
#print axioms _root_.GD.N0106.N0428.N0765.N1632.d021348
#print axioms _root_.GD.N0106.N0428.N0765.N1632.d021349
#print axioms _root_.GD.N0106.N0428.N0765.N1632.d021350
#print axioms _root_.GD.N0106.N0428.N0765.N1632.d021351
#print axioms _root_.GD.N0106.N0428.N0765.N1632.d021352
#print axioms _root_.GD.N0106.N0428.N0765.N1632.d021353
