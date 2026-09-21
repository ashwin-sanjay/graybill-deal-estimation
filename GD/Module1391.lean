import GD.Module1390
















set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set intervalIntegral

namespace GD.N0174
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0163 _root_.GD.N0178 _root_.GD.N0180
open _root_.GD.N0169

def d022394 (r : ℝ) (hr : 0 < r) : _root_.GD.N0232.N0720.N1441.d013676 :=
  ⟨Real.exp (-r), Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩

def d022395 (r : ℝ) (hr : 0 < r) : _root_.GD.N0232.N0720.N1441.d013676 :=
  ⟨1 - Real.exp (-r), by
    have ht : Real.exp (-r) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    constructor <;> linarith [Real.exp_pos (-r)]⟩


def d022396 (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (r : ℝ) (p : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  _root_.GD.N0178.d007131 (Real.exp (-r)) p.1 p.2 * (_root_.GD.N0163.d022211 g p - Real.exp (-r)) ^ 2 +
    _root_.GD.N0178.d007131 (1 - Real.exp (-r)) p.1 p.2 *
      (_root_.GD.N0163.d022211 g p - (1 - Real.exp (-r))) ^ 2


def d022397 (A T : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) : ℝ :=
  1 / (2 * T) * ∫ r in A..(A + T),
    ∫ p, _root_.GD.N0174.d022396 g r p ∂_root_.GD.N0232.N0720.N1436.d013288

theorem d022398 (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g) :
    Measurable (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0174.d022396 g z.1 z.2) := by
  have hv : Measurable (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0163.d022211 g z.2) :=
    (_root_.GD.N0163.d022213 g hg).comp measurable_snd
  unfold _root_.GD.N0174.d022396 _root_.GD.N0178.d007131 _root_.GD.N0178.d007130 _root_.GD.N0178.d007129
  fun_prop

theorem d022399 {r : ℝ} (hr : 0 < r) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ)
    {p : _root_.GD.N0232.N0720.N1436.d013217} (hp : p ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 ≤ _root_.GD.N0174.d022396 g r p :=
  add_nonneg (_root_.GD.N0169.d022360 (_root_.GD.N0174.d022394 r hr) g hp)
    (_root_.GD.N0169.d022360 (_root_.GD.N0174.d022395 r hr) g hp)


theorem d022400 {r : ℝ} (hr : 0 < r)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    Integrable (_root_.GD.N0174.d022396 g r) _root_.GD.N0232.N0720.N1436.d013288 := by
  exact (_root_.GD.N0169.d022359 (_root_.GD.N0174.d022394 r hr) g hg h01).add
    (_root_.GD.N0169.d022359 (_root_.GD.N0174.d022395 r hr) g hg h01)


theorem d022401 {r : ℝ} (hr : 0 < r)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    (∫ p, _root_.GD.N0174.d022396 g r p ∂_root_.GD.N0232.N0720.N1436.d013288) =
      _root_.GD.N0180.d022173 (_root_.GD.N0174.d022394 r hr) (_root_.GD.N0163.d022211 g) +
        _root_.GD.N0180.d022173 (_root_.GD.N0174.d022395 r hr) (_root_.GD.N0163.d022211 g) := by
  exact integral_add
    (_root_.GD.N0169.d022359 (_root_.GD.N0174.d022394 r hr) g hg h01)
    (_root_.GD.N0169.d022359 (_root_.GD.N0174.d022395 r hr) g hg h01)

private theorem d022402 {v t : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (v - t) ^ 2 ≤ 1 := by
  have habs : |v - t| ≤ 1 := abs_le.mpr ⟨by linarith [hv.1, ht.2], by linarith [hv.2, ht.1]⟩
  simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg (v - t)) habs 2

theorem d022403 {r : ℝ} (hr : 0 < r)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1)
    {p : _root_.GD.N0232.N0720.N1436.d013217} (hp : p ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0174.d022396 g r p ≤ _root_.GD.N0178.d007131 (Real.exp (-r)) p.1 p.2 +
      _root_.GD.N0178.d007131 (1 - Real.exp (-r)) p.1 p.2 := by
  have ht0 := (_root_.GD.N0174.d022394 r hr).property
  have ht1 := (_root_.GD.N0174.d022395 r hr).property
  have hv := _root_.GD.N0163.d022214 g h01 p
  have hk0 := _root_.GD.N0178.d007141 ht0.1 ht0.2 hp.1.1.le hp.1.2.le hp.2
  have hk1 := _root_.GD.N0178.d007141 ht1.1 ht1.2 hp.1.1.le hp.1.2.le hp.2
  exact add_le_add
    (mul_le_of_le_one_right hk0 (_root_.GD.N0174.d022402 hv ⟨ht0.1.le, ht0.2.le⟩))
    (mul_le_of_le_one_right hk1 (_root_.GD.N0174.d022402 hv ⟨ht1.1.le, ht1.2.le⟩))


theorem d022404 {r : ℝ} (hr : 0 < r)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    (∫ p, ‖_root_.GD.N0174.d022396 g r p‖ ∂_root_.GD.N0232.N0720.N1436.d013288) ≤
      2 / (Real.exp (-r) * (1 - Real.exp (-r))) := by
  have hi0 := _root_.GD.N0180.d022169 (_root_.GD.N0174.d022394 r hr)
  have hi1 := _root_.GD.N0180.d022169 (_root_.GD.N0174.d022395 r hr)
  calc
    _ = ∫ p, _root_.GD.N0174.d022396 g r p ∂_root_.GD.N0232.N0720.N1436.d013288 := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with p hp
      exact Real.norm_of_nonneg (_root_.GD.N0174.d022399 hr g hp)
    _ ≤ ∫ p, _root_.GD.N0178.d007131 (_root_.GD.N0174.d022394 r hr) p.1 p.2 + _root_.GD.N0178.d007131 (_root_.GD.N0174.d022395 r hr) p.1 p.2
        ∂_root_.GD.N0232.N0720.N1436.d013288 := by
      apply integral_mono_ae (_root_.GD.N0174.d022400 hr g hg h01) (hi0.add hi1)
      filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with p hp
      exact _root_.GD.N0174.d022403 hr g h01 hp
    _ = _ := by
      rw [integral_add hi0 hi1, _root_.GD.N0180.d022170, _root_.GD.N0180.d022170]
      change 1 / (Real.exp (-r) * (1 - Real.exp (-r))) +
        1 / ((1 - Real.exp (-r)) * (1 - (1 - Real.exp (-r)))) = _
      rw [show 1 - (1 - Real.exp (-r)) = Real.exp (-r) by ring,
        mul_comm (1 - Real.exp (-r)) (Real.exp (-r))]
      ring


theorem d022405 {A B r : ℝ} (hA : 0 < A) (hr : r ∈ Icc A B) :
    2 / (Real.exp (-r) * (1 - Real.exp (-r))) ≤
      2 / (Real.exp (-B) * (1 - Real.exp (-A))) := by
  have hAexp : Real.exp (-A) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hlo : Real.exp (-B) ≤ Real.exp (-r) := Real.exp_le_exp_of_le (by linarith [hr.2])
  have hhi : Real.exp (-r) ≤ Real.exp (-A) := Real.exp_le_exp_of_le (by linarith [hr.1])
  have hden : Real.exp (-B) * (1 - Real.exp (-A)) ≤
      Real.exp (-r) * (1 - Real.exp (-r)) :=
    mul_le_mul hlo (by linarith) (by linarith) (Real.exp_pos _).le
  exact div_le_div_of_nonneg_left (by norm_num)
    (mul_pos (Real.exp_pos _) (sub_pos.mpr hAexp)) hden

local instance d022406 : SFinite _root_.GD.N0232.N0720.N1436.d013288 := by
  unfold _root_.GD.N0232.N0720.N1436.d013288
  infer_instance


theorem d022407 {A : ℝ} (hA : 0 < A) (B : ℝ)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    Integrable (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0174.d022396 g z.1 z.2)
      ((volume.restrict (Ioc A B)).prod _root_.GD.N0232.N0720.N1436.d013288) := by
  have hm := _root_.GD.N0174.d022398 g hg
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact _root_.GD.N0174.d022400 (hA.trans hr.1) g hg h01
  · have hnorm : Measurable (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 => ‖_root_.GD.N0174.d022396 g z.1 z.2‖) :=
      hm.norm
    apply IntegrableOn.of_bound (by simp [Real.volume_Ioc])
      (hnorm.stronglyMeasurable.integral_prod_right'
        (ν := _root_.GD.N0232.N0720.N1436.d013288)).aestronglyMeasurable
      (2 / (Real.exp (-B) * (1 - Real.exp (-A))))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun p => norm_nonneg (_root_.GD.N0174.d022396 g r p)))]
    exact (_root_.GD.N0174.d022404 (hA.trans hr.1) g hg h01).trans
      (_root_.GD.N0174.d022405 hA ⟨hr.1.le, hr.2⟩)

theorem d022408 (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g) :
    Measurable (fun r => ∫ p, _root_.GD.N0174.d022396 g r p ∂_root_.GD.N0232.N0720.N1436.d013288) :=
  ((_root_.GD.N0174.d022398 g hg).stronglyMeasurable.integral_prod_right'
    (ν := _root_.GD.N0232.N0720.N1436.d013288)).measurable


theorem d022409 {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun r => ∫ p, _root_.GD.N0174.d022396 g r p ∂_root_.GD.N0232.N0720.N1436.d013288)
      volume A B :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hAB).mpr
    (_root_.GD.N0174.d022407 hA B g hg h01).integral_prod_left


theorem d022410 {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    (∫ r in A..B, ∫ p, _root_.GD.N0174.d022396 g r p ∂_root_.GD.N0232.N0720.N1436.d013288) =
      ∫ p, (∫ r in A..B, _root_.GD.N0174.d022396 g r p) ∂_root_.GD.N0232.N0720.N1436.d013288 := by
  have h := MeasureTheory.integral_integral_swap
    (f := fun r p => _root_.GD.N0174.d022396 g r p) (_root_.GD.N0174.d022407 hA B g hg h01)
  simpa only [intervalIntegral.integral_of_le hAB] using h


theorem d022411 {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    (∫ r in A..B, ∫ p, _root_.GD.N0174.d022396 g r p ∂_root_.GD.N0232.N0720.N1436.d013288) =
      ∫ u in Ioo (0 : ℝ) 1, ∫ s in Ioi (0 : ℝ), ∫ r in A..B, _root_.GD.N0174.d022396 g r (u, s) := by
  have hip : Integrable (fun p => ∫ r in A..B, _root_.GD.N0174.d022396 g r p) _root_.GD.N0232.N0720.N1436.d013288 := by
    simpa only [intervalIntegral.integral_of_le hAB] using
      (_root_.GD.N0174.d022407 hA B g hg h01).integral_prod_right
  rw [_root_.GD.N0174.d022410 hA hAB g hg h01]
  exact MeasureTheory.setIntegral_prod (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ)) (fun p => ∫ r in A..B, _root_.GD.N0174.d022396 g r p) hip


theorem d022412 {A T : ℝ} (hA : 0 < A) (hT : 0 < T)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0174.d022397 A T g = 1 / (2 * T) *
      (∫ u in Ioo (0 : ℝ) 1, ∫ s in Ioi (0 : ℝ),
        ∫ r in A..(A + T), _root_.GD.N0174.d022396 g r (u, s)) := by
  unfold _root_.GD.N0174.d022397
  rw [_root_.GD.N0174.d022411 hA (by linarith : A ≤ A + T) g hg h01]

end
end GD.N0174

#print axioms _root_.GD.N0174.d022398
#print axioms _root_.GD.N0174.d022399
#print axioms _root_.GD.N0174.d022400
#print axioms _root_.GD.N0174.d022401
#print axioms _root_.GD.N0174.d022403
#print axioms _root_.GD.N0174.d022404
#print axioms _root_.GD.N0174.d022405
#print axioms _root_.GD.N0174.d022407
#print axioms _root_.GD.N0174.d022408
#print axioms _root_.GD.N0174.d022409
#print axioms _root_.GD.N0174.d022410
#print axioms _root_.GD.N0174.d022411
#print axioms _root_.GD.N0174.d022412
