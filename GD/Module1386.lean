import GD.Module1385
import GD.Module0469














set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set intervalIntegral

namespace GD.N0176
noncomputable section

open _root_.GD.N0179 _root_.GD.N0203
open _root_.GD.N0205 _root_.GD.N0165
open _root_.GD.N0232.N0720.N1436

def d022338 (eta d a b : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (y : ℝ) : ℝ :=
  _root_.GD.N0205.d022324 eta d a b (fun u => g (u, Real.exp y))

def d022339 (eta d a b A T : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) : ℝ :=
  _root_.GD.N0165.d007234 d eta a / T * ∫ y in (A + Real.log b)..(A + T + Real.log a),
    _root_.GD.N0176.d022338 eta d a b (_root_.GD.N0163.d022211 g) y

private theorem d022340 (F : ℝ × ℝ → ℝ) (hF : Measurable F)
    (l r : ℝ) : Measurable (fun y => ∫ u in l..r, F (y, u)) := by
  change Measurable (fun y =>
    (∫ u, F (y, u) ∂volume.restrict (Ioc l r)) -
      ∫ u, F (y, u) ∂volume.restrict (Ioc r l))
  exact ((hF.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc l r))).sub
      (hF.stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (Ioc r l)))).measurable


theorem d022341 (a b : ℝ) : Measurable (_root_.GD.N0203.d007246 a b) := by
  exact _root_.GD.N0176.d022340 (fun z => _root_.GD.N0179.d006018 z.1 z.2)
    (by unfold _root_.GD.N0179.d006018; fun_prop) a b


theorem d022342 (eta d a b : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hg : Measurable g) : Measurable (_root_.GD.N0176.d022338 eta d a b g) := by
  have hx : Measurable (fun z : ℝ × ℝ => _root_.GD.N0203.d007246 a b z.2) :=
    (_root_.GD.N0176.d022341 a b).comp measurable_snd
  have hy : Measurable (fun z : ℝ × ℝ => _root_.GD.N0203.d007246 a b (1 - z.2)) :=
    (_root_.GD.N0176.d022341 a b).comp (measurable_const.sub measurable_snd)
  have hv : Measurable (fun z : ℝ × ℝ => g (z.2, Real.exp z.1)) :=
    hg.comp (measurable_snd.prodMk (Real.measurable_exp.comp measurable_fst))
  have hF : Measurable (fun z : ℝ × ℝ =>
      _root_.GD.N0205.d022323 d a b (fun u => g (u, Real.exp z.1)) z.2) := by
    unfold _root_.GD.N0205.d022323 _root_.GD.N0205.d022322
    fun_prop
  exact (_root_.GD.N0176.d022340 _ hF eta (1 - eta)).const_mul (1 / 2 : ℝ)

private theorem d022343 {x y v d : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hv : v ∈ Icc (0 : ℝ) 1) :
    ‖x * v ^ 2 + y * (1 - v) ^ 2 - 2 * d * (x + y)‖ ≤
      (1 + 2 * |d|) * (x + y) := by
  have hv2 := pow_le_pow_left₀ hv.1 hv.2 2
  have hw2 := pow_le_pow_left₀ (sub_nonneg.mpr hv.2)
    (show 1 - v ≤ (1 : ℝ) by linarith [hv.1]) 2
  simp only [one_pow] at hv2 hw2
  have hq0 : 0 ≤ x * v ^ 2 + y * (1 - v) ^ 2 := by positivity
  have hq := add_le_add (mul_le_mul_of_nonneg_left hv2 hx)
    (mul_le_mul_of_nonneg_left hw2 hy)
  have hS : 0 ≤ x + y := add_nonneg hx hy
  have hd := mul_le_mul_of_nonneg_right (le_abs_self d) hS
  have hd' := mul_le_mul_of_nonneg_right (neg_abs_le d) hS
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith


theorem d022344 {eta a b : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a < b) (d y : ℝ)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (h01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    ‖_root_.GD.N0176.d022338 eta d a b g y‖ ≤ (1 / 2 : ℝ) * (1 + 2 * |d|) * _root_.GD.N0203.d007250 eta a b := by
  have hwin : eta ≤ 1 - eta := by linarith
  have hm : IntervalIntegrable (fun u => _root_.GD.N0203.d007246 a b u + _root_.GD.N0203.d007246 a b (1 - u))
      volume eta (1 - eta) :=
    ContinuousOn.intervalIntegrable_of_Icc hwin (_root_.GD.N0203.d007262 heta ha hab.le)
  have henv := hm.const_mul (1 + 2 * |d|)
  have hpoint : ∀ u ∈ Icc eta (1 - eta),
      ‖_root_.GD.N0205.d022323 d a b (fun u => g (u, Real.exp y)) u‖ ≤
        (1 + 2 * |d|) * (_root_.GD.N0203.d007246 a b u + _root_.GD.N0203.d007246 a b (1 - u)) := by
    intro u hu
    exact _root_.GD.N0176.d022343
      (_root_.GD.N0205.d022325 (heta.trans_le hu.1) ha hab).le
      (_root_.GD.N0205.d022325 (show 0 < 1 - u by linarith [hu.2]) ha hab).le
      (h01 (u, Real.exp y))
  have hi := intervalIntegral.norm_integral_le_of_norm_le
    (f := _root_.GD.N0205.d022323 d a b (fun u => g (u, Real.exp y))) hwin
    (ae_of_all _ (fun u hu => hpoint u ⟨hu.1.le, hu.2⟩)) henv
  rw [intervalIntegral.integral_const_mul] at hi
  unfold _root_.GD.N0176.d022338 _root_.GD.N0205.d022324
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  simpa only [_root_.GD.N0203.d007250, mul_assoc] using
    mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 1 / 2)


theorem d022345 {eta a b : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a < b) (d l r : ℝ)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (h01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (_root_.GD.N0176.d022338 eta d a b g) volume l r := by
  apply intervalIntegrable_iff.mpr
  exact IntegrableOn.of_bound (by simp [uIoc, Real.volume_Ioc])
    (_root_.GD.N0176.d022342 eta d a b g hg).aestronglyMeasurable
    ((1 / 2 : ℝ) * (1 + 2 * |d|) * _root_.GD.N0203.d007250 eta a b)
    (ae_of_all _ (fun y => _root_.GD.N0176.d022344 heta hhalf ha hab d y g h01))

theorem d022346 (eta d a b : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ)
    (hg : Measurable g) :
    Measurable (_root_.GD.N0176.d022338 eta d a b (_root_.GD.N0163.d022211 g)) :=
  _root_.GD.N0176.d022342 eta d a b _ (_root_.GD.N0163.d022213 g hg)

theorem d022347 {eta a b : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a < b) (d l r : ℝ)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (_root_.GD.N0176.d022338 eta d a b (_root_.GD.N0163.d022211 g))
      volume l r :=
  _root_.GD.N0176.d022345 heta hhalf ha hab d l r _
    (_root_.GD.N0163.d022213 g hg)
    (_root_.GD.N0163.d022214 g h01)


theorem d022348 (eta d a b A T : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) :
    _root_.GD.N0176.d022339 eta d a b A T g =
      _root_.GD.N0165.d007234 d eta a / (2 * T) * ∫ y in (A + Real.log b)..(A + T + Real.log a),
        ∫ u in eta..(1 - eta), _root_.GD.N0205.d022323 d a b
          (fun u => _root_.GD.N0163.d022211 g (u, Real.exp y)) u := by
  unfold _root_.GD.N0176.d022339 _root_.GD.N0176.d022338 _root_.GD.N0205.d022324
  rw [intervalIntegral.integral_const_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem d022349 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (A T : ℝ) :
    (A + T + Real.log a) - (A + Real.log b) = T - Real.log (b / a) := by
  rw [Real.log_div hb.ne' ha.ne']
  ring

theorem d022350 {a b T : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hT : Real.log (b / a) < T) (A : ℝ) :
    A + Real.log b < A + T + Real.log a := by
  have h := sub_pos.mpr hT
  rw [← _root_.GD.N0176.d022349 ha hb A T] at h
  exact sub_pos.mp h

theorem d022351 {d eta a : ℝ} (hd0 : 0 < d) (hd1 : d < 1)
    (heta : 0 < eta) (ha : 0 < a) : 0 < _root_.GD.N0165.d007234 d eta a := by
  unfold _root_.GD.N0165.d007234 _root_.GD.N0165.d007233
  apply Real.rpow_pos_of_pos
  have h1 : 0 < 1 - d := sub_pos.mpr hd1
  have hden : 0 < (1 - d) * (a + 2 * eta) := mul_pos h1 (by positivity)
  positivity


theorem d022352 {eta a b d T : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a < b)
    (hd0 : 0 < d) (hd1 : d < 1) (hT : 0 < T)
    (hwindow : Real.log (b / a) < T) (A : ℝ)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0165.d007234 d eta a * (1 - Real.log (b / a) / T) * (_root_.GD.N0203.d007249 eta a b - d * _root_.GD.N0203.d007250 eta a b) ≤
      _root_.GD.N0176.d022339 eta d a b A T g := by
  have hw := (_root_.GD.N0176.d022350 ha (ha.trans hab) hwindow A).le
  have hi := _root_.GD.N0176.d022347 heta hhalf ha hab d
    (A + Real.log b) (A + T + Real.log a) g hg h01
  have h := intervalIntegral.integral_mono_on hw intervalIntegral.intervalIntegrable_const hi
    (fun y _ => _root_.GD.N0205.d022337 heta hhalf ha hab d y g hg h01)
  rw [intervalIntegral.integral_const, smul_eq_mul, _root_.GD.N0176.d022349 ha (ha.trans hab) A T] at h
  calc
    _root_.GD.N0165.d007234 d eta a * (1 - Real.log (b / a) / T) * (_root_.GD.N0203.d007249 eta a b - d * _root_.GD.N0203.d007250 eta a b) =
        (_root_.GD.N0165.d007234 d eta a / T) *
          ((T - Real.log (b / a)) * (_root_.GD.N0203.d007249 eta a b - d * _root_.GD.N0203.d007250 eta a b)) := by
      field_simp [hT.ne']
      <;> ring
    _ ≤ (_root_.GD.N0165.d007234 d eta a / T) * ∫ y in (A + Real.log b)..(A + T + Real.log a),
        _root_.GD.N0176.d022338 eta d a b (_root_.GD.N0163.d022211 g) y :=
      mul_le_mul_of_nonneg_left h (div_nonneg (_root_.GD.N0176.d022351 hd0 hd1 heta ha).le hT.le)
    _ = _root_.GD.N0176.d022339 eta d a b A T g := rfl


theorem d022353 {eta a b A T : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a < b)
    (hA : Real.log 2 < A) (hwindow : Real.log (b / a) < T)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0165.d007234 (Real.exp (-A)) eta a * (1 - Real.log (b / a) / T) *
        (_root_.GD.N0203.d007249 eta a b - Real.exp (-A) * _root_.GD.N0203.d007250 eta a b) ≤
      _root_.GD.N0176.d022339 eta (Real.exp (-A)) a b A T g := by
  have hA0 : 0 < A := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans hA
  have hd1 : Real.exp (-A) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hT : 0 < T := (Real.log_pos ((one_lt_div ha).mpr hab)).trans hwindow
  exact _root_.GD.N0176.d022352 heta hhalf ha hab (Real.exp_pos (-A)) hd1 hT hwindow A g hg h01

end
end GD.N0176

#print axioms _root_.GD.N0176.d022341
#print axioms _root_.GD.N0176.d022342
#print axioms _root_.GD.N0176.d022344
#print axioms _root_.GD.N0176.d022345
#print axioms _root_.GD.N0176.d022346
#print axioms _root_.GD.N0176.d022347
#print axioms _root_.GD.N0176.d022348
#print axioms _root_.GD.N0176.d022349
#print axioms _root_.GD.N0176.d022350
#print axioms _root_.GD.N0176.d022351
#print axioms _root_.GD.N0176.d022352
#print axioms _root_.GD.N0176.d022353
